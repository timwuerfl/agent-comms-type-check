"""The swarm runtime: agents exchange messages *only* through a gate.

Execution model (complete mediation, THEORY.md §4): an agent is activated when it receives a message
(or is nudged because the protocol is waiting for it). During its activation it may call ``send`` any
number of times; each call is one *attempt* that the gate delivers or rejects. Delivered messages
activate their recipient. Agents never get a handle on each other.

Agents can be scripted Python objects, LLMs (``swarmgate.llm``), tools (``ToolAgent``), or remote
agents reached over A2A/MCP (``swarmgate.a2a``, ``swarmgate.mcp_gate``).
"""
from __future__ import annotations

import json
import time
from collections import deque
from dataclasses import dataclass, field
from typing import Any, Callable

from .gate import Gate, PyGate, Verdict
from .protocol import Event, Protocol, Trans, ty_str


def canonical(v: Any) -> Any:
    """Recursively sort record (dict) fields."""
    if isinstance(v, dict):
        return {k: canonical(v[k]) for k in sorted(v)}
    if isinstance(v, list):
        return [canonical(x) for x in v]
    return v


@dataclass
class Envelope:
    """A delivered message, as seen by its recipient."""
    step: int
    src: str
    dst: str
    label: str
    payload: Any
    sender: str | None = None   # the authenticated principal that actually sent it (src is the claimed role)


@dataclass
class Record:
    """One audit-log line (every attempt, delivered or not)."""
    step: int
    sender: str
    claimed_src: str
    dst: str
    label: str
    payload: Any
    verdict: dict
    state_before: int
    state_after: int
    taint: list[str]

    def to_json(self) -> dict:
        return self.__dict__.copy()


@dataclass
class SendResult:
    delivered: bool
    reason: str | None
    allowed_now: list[Trans]


class Context:
    """What an agent sees when activated."""

    def __init__(self, swarm: "Swarm", role: str, trigger: Envelope | None):
        self.swarm = swarm
        self.role = role
        self.trigger = trigger

    @property
    def protocol(self) -> Protocol:
        return self.swarm.protocol

    @property
    def inbox(self) -> list[Envelope]:
        return self.swarm.inbox[self.role]

    @property
    def outbox(self) -> list[Envelope]:
        return self.swarm.outbox[self.role]

    def allowed(self) -> list[Trans]:
        return self.swarm.gate.allowed(self.swarm.idx(self.role))

    def describe_allowed(self) -> str:
        P = self.protocol
        ms = self.allowed()
        if not ms:
            return "(no message is expected from you right now)"
        return "\n".join(f"- send `{t.label}` to {P.roles[t.dst]} with payload of type {ty_str(t.ty)}"
                         for t in ms)

    def send(self, dst: str, label: str, payload: Any = None, as_role: str | None = None) -> SendResult:
        return self.swarm._attempt(self.role, dst, label, payload, as_role)


class Agent:
    """Base class. Override ``act``."""

    def __init__(self, role: str):
        self.role = role

    def act(self, ctx: Context) -> None:  # pragma: no cover - interface
        raise NotImplementedError


class FnAgent(Agent):
    def __init__(self, role: str, fn: Callable[[Context], None]):
        super().__init__(role)
        self.fn = fn

    def act(self, ctx: Context) -> None:
        self.fn(ctx)


class ToolAgent(Agent):
    """A tool exposed as a role: each request label maps to a handler returning (reply_label, payload)."""

    def __init__(self, role: str, handlers: dict[str, Callable[[Any], tuple[str, Any]]]):
        super().__init__(role)
        self.handlers = handlers
        self.calls: list[tuple[str, Any]] = []

    def act(self, ctx: Context) -> None:
        m = ctx.trigger
        if m is None or m.label not in self.handlers:
            return
        self.calls.append((m.label, m.payload))
        out = self.handlers[m.label](m.payload)
        if out is None:          # a sink: no reply
            return
        label, payload = out
        ctx.send(m.src, label, payload)


@dataclass
class RunResult:
    log: list[Record]
    delivered: list[Envelope]
    final_state: int
    completed: bool
    stalled: bool
    rejections: int
    activations: int
    seconds: float
    taint: list[str]
    extra: dict = field(default_factory=dict)

    def summary(self) -> dict:
        return {"completed": self.completed, "stalled": self.stalled, "delivered": len(self.delivered),
                "rejections": self.rejections, "activations": self.activations,
                "seconds": round(self.seconds, 3), "taint": self.taint}


class Swarm:
    def __init__(self, protocol: Protocol, agents: dict[str, Agent] | list[Agent], gate: Gate | None = None,
                 max_activations: int = 200, nudges: int = 2, on_record: Callable[[Record], None] | None = None):
        self.protocol = protocol
        self.agents = agents if isinstance(agents, dict) else {a.role: a for a in agents}
        self.gate = gate or PyGate(protocol)
        self.max_activations = max_activations
        self.nudges = nudges
        self.on_record = on_record
        self.inbox: dict[str, list[Envelope]] = {r: [] for r in protocol.roles}
        self.outbox: dict[str, list[Envelope]] = {r: [] for r in protocol.roles}
        self.log: list[Record] = []
        self.delivered: list[Envelope] = []
        self.queue: deque[tuple[str, Envelope | None]] = deque()
        self.step = 0
        self.crashes: list[str] = []

    def idx(self, role: str) -> int:
        return self.protocol.roles.index(role) if role in self.protocol.roles else len(self.protocol.roles) + 1000

    # -- the only path between agents -----------------------------------------------------------
    def _attempt(self, sender: str, dst: str, label: str, payload: Any, as_role: str | None) -> SendResult:
        claimed = as_role or sender
        before = self.gate.state
        ev = Event(self.idx(claimed), self.idx(dst), str(label), payload)
        try:
            json.dumps(payload)
            v = self.gate.submit(self.idx(sender), ev)
        except (TypeError, ValueError):
            v = Verdict(False, self.idx(sender), "notEnabled")
        if v.delivered and dst not in self.agents and dst not in self.protocol.roles:
            v = Verdict(False, self.idx(sender), "notEnabled")
        self.step += 1
        P = self.protocol
        rec = Record(self.step, sender, claimed, dst, label, payload, v.to_json(), before, self.gate.state,
                     [P.roles[r] for r in sorted(self.gate.taint())])
        self.log.append(rec)
        if self.on_record:
            self.on_record(rec)
        if v.delivered:
            # canonical form on delivery (sorted record fields): field order cannot be used as a covert
            # channel, so the capacity bound of Theorem T9b is sound for what recipients actually see
            payload = canonical(payload)
            env = Envelope(self.step, claimed, dst, label, payload, sender=sender)
            self.delivered.append(env)
            if dst in self.inbox:
                self.inbox[dst].append(env)
            if sender in self.outbox:
                self.outbox[sender].append(env)
            if dst in self.agents:
                self.queue.append((dst, env))
        return SendResult(v.delivered, v.reason, self.gate.allowed(self.idx(sender)))

    # -- scheduling ----------------------------------------------------------------------------------
    def run(self, kickoff: str | list[tuple[str, Envelope | None]]) -> RunResult:
        t0 = time.time()
        if isinstance(kickoff, str):
            self.queue.append((kickoff, None))
        else:
            self.queue.extend(kickoff)
        activations = 0
        nudges_left = self.nudges
        while activations < self.max_activations:
            if not self.queue:
                if self._done() or nudges_left <= 0:
                    break
                waiting = [self.protocol.roles[r] for r in sorted(self.gate.protocol.waiting_for(self.gate.state))
                           if self.gate.state >= 0]
                waiting = [r for r in waiting if r in self.agents]
                if not waiting:
                    break
                nudges_left -= 1
                self.queue.extend((r, None) for r in waiting)
            role, trig = self.queue.popleft()
            agent = self.agents.get(role)
            if agent is None:
                continue
            activations += 1
            try:
                agent.act(Context(self, role, trig))
            except Exception as exc:  # an agent crashing must not crash the swarm ...
                if type(exc).__name__ == "BudgetExceeded":   # ... but budget exhaustion must stop the run
                    raise
                self.crashes.append(f"{role}: {exc!r}"[:300])
                self.log.append(Record(self.step, role, role, "-", "<crash>", repr(exc)[:300], {"verdict": "crash"},
                                       self.gate.state, self.gate.state, []))
        P = self.protocol
        st = self.gate.state
        return RunResult(self.log, self.delivered, st, P.is_final(st) and st >= 0,
                         not self._done(), sum(1 for r in self.log if r.verdict.get("verdict") == "reject"),
                         activations, time.time() - t0, [P.roles[r] for r in sorted(self.gate.taint())],
                         extra={"crashes": list(self.crashes)})

    def _done(self) -> bool:
        st = self.gate.state
        return st >= 0 and self.protocol.is_final(st) and not self.protocol.out(st)
