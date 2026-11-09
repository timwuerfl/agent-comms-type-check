"""Gates: the component that decides, for every attempted message, whether it is delivered.

* ``LeanGate``  — runs the compiled Lean function ``SwarmGate.monStep`` (the deployed, verified gate).
* ``PyGate``    — a line-by-line Python mirror of ``monStep`` (reference; differential-tested).

Baselines used in the evaluation form an *ablation lattice*; each adds one dimension of checking:

* ``OpenGate``      — no checks (a free message bus).
* ``SchemaGate``    — payload must fit the type of *some* message with that label (A2A/structured-output style).
* ``TopologyGate``  — additionally, (sender, recipient, label) must be an edge of the protocol graph
                      (a static "who may talk to whom" ACL, as in agent-graph frameworks), ignoring the state.
* ``PyGate``/``LeanGate`` — additionally, the move must be enabled *now* (full session protocol).
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import threading
from dataclasses import dataclass, field
from typing import Any

from .protocol import Event, Protocol, Trans, has_ty, lowcap, pred_eval

REASONS = ("spoof", "notEnabled", "budget", "quarantined", "halted")


@dataclass(frozen=True)
class Verdict:
    delivered: bool
    blamed: int | None = None
    reason: str | None = None
    killed: bool = False

    def to_json(self) -> dict:
        if self.killed:
            return {"verdict": "killed"}
        if self.delivered:
            return {"verdict": "deliver"}
        return {"verdict": "reject", "blamed": self.blamed, "reason": self.reason}


DELIVER = Verdict(True)


class Gate:
    """Common interface."""

    name = "gate"
    protocol: Protocol

    def submit(self, sender: int, event: Event) -> Verdict:  # pragma: no cover - interface
        raise NotImplementedError

    def kill(self) -> None:  # pragma: no cover - interface
        raise NotImplementedError

    @property
    def state(self) -> int:  # pragma: no cover - interface
        raise NotImplementedError

    @property
    def finished(self) -> bool:
        return self.protocol.is_final(self.state) and not self.protocol.out(self.state)

    def allowed(self, role: int) -> list[Trans]:
        """Moves ``role`` may make now (used to guide agents; never trusted for enforcement)."""
        return self.protocol.enabled_for(self.state, role)

    def taint(self) -> set[int]:
        return set()

    def close(self) -> None:
        pass


# =============================================================================================
# The reference gate (mirror of Monitor.lean)
# =============================================================================================

@dataclass
class MState:
    s: int
    count: int = 0
    strikes: dict[int, int] = field(default_factory=dict)
    halted: bool = False


class PyGate(Gate):
    name = "session"

    def __init__(self, protocol: Protocol, budget: int | None = None, max_strikes: int | None = None):
        self.protocol = protocol
        self.budget = protocol.budget if budget is None else budget
        self.max_strikes = protocol.max_strikes if max_strikes is None else max_strikes
        self.m = MState(protocol.start)
        ifc = protocol.ifc
        self._ifc = ifc
        self._taint = 0
        if ifc:
            for r in ifc.get("untrusted", []):
                self._taint |= 1 << r

    def _quar(self, sigma: int) -> bool:
        return self.max_strikes != 0 and self.max_strikes <= self.m.strikes.get(sigma, 0)

    def _strike(self, sigma: int) -> None:
        self.m.strikes[sigma] = self.m.strikes.get(sigma, 0) + 1

    def submit(self, sender: int, event: Event) -> Verdict:
        m = self.m
        if m.halted:
            return Verdict(False, sender, "halted")
        if self._quar(sender):
            return Verdict(False, sender, "quarantined")
        if sender != event.src:
            self._strike(sender)
            return Verdict(False, sender, "spoof")
        if self.budget <= m.count:
            return Verdict(False, sender, "budget")
        t = self.protocol.matched(m.s, event)
        if t is None:
            self._strike(sender)
            return Verdict(False, sender, "notEnabled")
        if (self._ifc and (self._taint >> t.src) & 1 and not lowcap(t.ty, self._ifc.get("maxBits", 8))
                and t.dst not in self._ifc.get("endorsers", [])):
            self._taint |= 1 << t.dst
        m.s = t.next
        m.count += 1
        return DELIVER

    def kill(self) -> None:
        self.m.halted = True

    @property
    def state(self) -> int:
        return self.m.s

    def taint(self) -> set[int]:
        return {r for r in range(len(self.protocol.roles)) if (self._taint >> r) & 1}


# =============================================================================================
# The verified gate (compiled Lean, JSON-lines over a pipe)
# =============================================================================================

def find_binary() -> str | None:
    env = os.environ.get("SWARMGATE_BIN")
    if env and os.path.exists(env):
        return env
    here = os.path.dirname(os.path.abspath(__file__))
    for cand in (os.path.join(here, "..", "..", "lean", ".lake", "build", "bin", "swarmgate"),
                 shutil.which("swarmgate")):
        if cand and os.path.exists(cand):
            return os.path.abspath(cand)
    return None


class LeanServer:
    """One ``swarmgate serve`` process; many sessions can share it."""

    def __init__(self, protocol: Protocol, binary: str | None = None, path: str | None = None):
        self.binary = binary or find_binary()
        if not self.binary:
            raise FileNotFoundError("swarmgate binary not found; build it with `cd lean && lake build` "
                                    "or set SWARMGATE_BIN")
        if path is None:
            import tempfile
            fd, path = tempfile.mkstemp(suffix=".json", prefix="swarmgate-")
            with os.fdopen(fd, "w") as f:
                f.write(protocol.dumps())
        self.path = path
        self.proc = subprocess.Popen([self.binary, "serve", path], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, text=True, bufsize=1)
        self.lock = threading.Lock()

    def call(self, req: dict) -> dict:
        with self.lock:
            assert self.proc.stdin and self.proc.stdout
            self.proc.stdin.write(json.dumps(req) + "\n")
            self.proc.stdin.flush()
            line = self.proc.stdout.readline()
        if not line:
            raise RuntimeError("swarmgate server exited")
        resp = json.loads(line)
        if "error" in resp:
            raise ValueError(resp["error"])
        return resp

    def close(self) -> None:
        if self.proc.poll() is None:
            self.proc.stdin.close()  # type: ignore[union-attr]
            self.proc.wait(timeout=5)


class LeanGate(Gate):
    name = "session-lean"
    _counter = 0

    def __init__(self, protocol: Protocol, server: LeanServer | None = None, session: str | None = None):
        self.protocol = protocol
        self._own = server is None
        self.server = server or LeanServer(protocol)
        LeanGate._counter += 1
        self.session = session or f"s{LeanGate._counter}"
        self._last = self.server.call({"op": "reset", "session": self.session})
        self._last = self.server.call({"op": "state", "session": self.session})

    def submit(self, sender: int, event: Event) -> Verdict:
        r = self.server.call({"op": "send", "session": self.session, "sender": sender,
                              "event": event.to_json()})
        self._last = r
        if r["verdict"] == "deliver":
            return DELIVER
        return Verdict(False, r.get("blamed"), r.get("reason"))

    def kill(self) -> None:
        self._last = self.server.call({"op": "kill", "session": self.session})

    @property
    def state(self) -> int:
        return self._last["state"]

    def taint(self) -> set[int]:
        return set(self._last.get("taint", []))

    def close(self) -> None:
        if self._own:
            self.server.close()


# =============================================================================================
# Baselines (ablation lattice)
# =============================================================================================

class _Shadow(Gate):
    """Baselines still track the protocol state *for reporting only*; they never use it to decide."""

    def __init__(self, protocol: Protocol):
        self.protocol = protocol
        self._shadow = protocol.start
        self.count = 0
        self.halted = False
        self.edges = {(t.src, t.dst, t.label): [] for st in protocol.states for t in st}
        for st in protocol.states:
            for t in st:
                self.edges[(t.src, t.dst, t.label)].append(t)
        self.labels: dict[str, list[Trans]] = {}
        for st in protocol.states:
            for t in st:
                self.labels.setdefault(t.label, []).append(t)

    def _advance(self, e: Event) -> None:
        if self._shadow is not None:
            self._shadow = self.protocol.step(self._shadow, e)

    @property
    def state(self) -> int:
        return -1 if self._shadow is None else self._shadow

    @property
    def off_protocol(self) -> bool:
        return self._shadow is None

    def kill(self) -> None:
        self.halted = True

    def allowed(self, role: int) -> list[Trans]:
        if self._shadow is None:
            return []
        return self.protocol.enabled_for(self._shadow, role)

    def _ok(self, sender: int, e: Event) -> bool:
        raise NotImplementedError

    def submit(self, sender: int, event: Event) -> Verdict:
        if self.halted:
            return Verdict(False, sender, "halted")
        if not self._ok(sender, event):
            return Verdict(False, sender, "notEnabled")
        self._advance(event)
        self.count += 1
        return DELIVER


class OpenGate(_Shadow):
    name = "none"

    def _ok(self, sender, e):
        return True


class SchemaGate(_Shadow):
    name = "schema"

    def _ok(self, sender, e):
        return any(has_ty(t.ty, e.payload) and pred_eval(t.pred, e.payload) for t in self.labels.get(e.label, []))


class TopologyGate(_Shadow):
    name = "topology"

    def _ok(self, sender, e):
        if sender != e.src:
            return False
        return any(t.matches(e) for t in self.edges.get((e.src, e.dst, e.label), []))


GATES = {"none": OpenGate, "schema": SchemaGate, "topology": TopologyGate, "session": PyGate,
         "session-lean": LeanGate}


def make_gate(kind: str, protocol: Protocol, **kw) -> Gate:
    return GATES[kind](protocol, **kw)
