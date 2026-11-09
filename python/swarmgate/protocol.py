"""Protocol model shared by the DSL compiler, the monitors and the runtime.

This module mirrors ``lean/SwarmGate/Basic.lean`` and ``Protocol.lean`` one-to-one. The Python
reference monitor (``monitor.PyMonitor``) is differential-tested against the Lean binary, so every
function here must behave *exactly* like its Lean counterpart (see ``tests/test_differential.py``).

Payload values are plain JSON values: ``None`` (unit), ``bool``, ``int``, ``str``, ``list``, ``dict``.
Types (``ty``) and refinements (``pred``) use the JSON encoding documented in ``docs/FORMAT.md``.
"""
from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Any, Iterable

INT64_MIN = -(2**63)
INT64_MAX = 2**63 - 1


# ---------------------------------------------------------------------------------------------
# Types and values (Basic.lean: hasTy)
# ---------------------------------------------------------------------------------------------

def has_ty(ty: Any, v: Any) -> bool:
    """Decidable typing judgement ``v ⊨ ty`` (closed records, 64-bit ints)."""
    if ty == "unit":
        return v is None
    if ty == "bool":
        return isinstance(v, bool)
    if ty == "int":
        return isinstance(v, int) and not isinstance(v, bool) and INT64_MIN <= v <= INT64_MAX
    if ty == "str":
        return isinstance(v, str)
    if isinstance(ty, dict):
        if "enum" in ty:
            return isinstance(v, str) and v in ty["enum"]
        if "list" in ty:
            return isinstance(v, list) and all(has_ty(ty["list"], x) for x in v)
        if "record" in ty:
            if not isinstance(v, dict):
                return False
            fields = ty["record"]
            names = [n for n, _ in fields]
            if len(v) != len(fields):
                return False
            if not all(k in names for k in v):
                return False
            for n, t in fields:
                if n not in v or not has_ty(t, v[n]):
                    return False
            return True
    return False


def cap_bits(ty: Any) -> int | None:
    """Information capacity in bits (``None`` = unbounded). Mirrors ``Ty.capBits``."""
    if ty == "unit":
        return 0
    if ty == "bool":
        return 1
    if ty == "int":
        return 64
    if ty == "str":
        return None
    if isinstance(ty, dict):
        if "enum" in ty:
            n = max(len(ty["enum"]) - 1, 0)          # Lean: Nat.log2 (k - 1) + 1
            return (n.bit_length() - 1 if n > 0 else 0) + 1
        if "list" in ty:
            return None
        if "record" in ty:
            total = 0
            for _, t in ty["record"]:
                b = cap_bits(t)
                if b is None:
                    return None
                total += b
            return total
    return None


def lowcap(ty: Any, max_bits: int) -> bool:
    b = cap_bits(ty)
    return b is not None and b <= max_bits


def _get(v: Any, path: list[str]) -> tuple[bool, Any]:
    for k in path:
        if not isinstance(v, dict) or k not in v:
            return False, None
        v = v[k]
    return True, v


def _is_int(x: Any) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


def pred_eval(p: Any, v: Any) -> bool:
    """Evaluate a refinement. Mirrors ``Pred.eval``."""
    if p is True:
        return True
    if p is False:
        return False
    (op, arg), = p.items()
    if op == "and":
        return pred_eval(arg[0], v) and pred_eval(arg[1], v)
    if op == "or":
        return pred_eval(arg[0], v) or pred_eval(arg[1], v)
    if op == "not":
        return not pred_eval(arg, v)
    path, k = arg
    ok, x = _get(v, path)
    if not ok:
        return False
    if op == "intLe":
        return _is_int(x) and x <= k
    if op == "intGe":
        return _is_int(x) and k <= x
    if op == "lenLe":
        return isinstance(x, (str, list)) and len(x) <= k
    if op == "strIn":
        return isinstance(x, str) and x in k
    if op == "strNotContains":
        # Lean: !containsL needle s  (the empty needle is contained in every string)
        return isinstance(x, str) and k not in x
    if op == "eqStr":
        return isinstance(x, str) and x == k
    if op == "eqBool":
        return isinstance(x, bool) and x == k
    raise ValueError(f"unknown refinement {op}")


# ---------------------------------------------------------------------------------------------
# Protocols (Protocol.lean)
# ---------------------------------------------------------------------------------------------

@dataclass(frozen=True)
class Event:
    src: int
    dst: int
    label: str
    payload: Any = None

    def to_json(self) -> dict:
        return {"src": self.src, "dst": self.dst, "label": self.label, "payload": self.payload}


@dataclass(frozen=True)
class Trans:
    src: int
    dst: int
    label: str
    ty: Any
    pred: Any
    next: int

    def matches(self, e: Event) -> bool:
        return (self.src == e.src and self.dst == e.dst and self.label == e.label
                and has_ty(self.ty, e.payload) and pred_eval(self.pred, e.payload))

    @property
    def abs(self) -> tuple[int, int, str]:
        return (self.src, self.dst, self.label)

    def to_json(self) -> dict:
        return {"src": self.src, "dst": self.dst, "label": self.label, "ty": self.ty,
                "pred": self.pred, "next": self.next}


def _freeze(x: Any) -> Any:
    return json.loads(json.dumps(x))


@dataclass
class Protocol:
    name: str
    roles: list[str]
    states: list[list[Trans]]
    start: int = 0
    final: list[int] = field(default_factory=list)
    budget: int = 1000
    max_strikes: int = 3
    properties: list[tuple[str, Any]] = field(default_factory=list)
    ifc: dict | None = None
    locals: list[dict] | None = None
    source: str | None = None

    # -- basics -------------------------------------------------------------------------------
    def role(self, name: str) -> int:
        try:
            return self.roles.index(name)
        except ValueError:
            raise KeyError(f"unknown role {name!r}; roles are {self.roles}") from None

    def out(self, s: int) -> list[Trans]:
        return self.states[s] if 0 <= s < len(self.states) else []

    def is_final(self, s: int) -> bool:
        return s in self.final

    def step(self, s: int, e: Event) -> int | None:
        for t in self.out(s):
            if t.matches(e):
                return t.next
        return None

    def matched(self, s: int, e: Event) -> Trans | None:
        for t in self.out(s):
            if t.matches(e):
                return t
        return None

    def run(self, s: int, events: Iterable[Event]) -> int | None:
        for e in events:
            s2 = self.step(s, e)
            if s2 is None:
                return None
            s = s2
        return s

    def enabled_for(self, s: int, role: int) -> list[Trans]:
        """Transitions role ``role`` may take now as a sender."""
        return [t for t in self.out(s) if t.src == role]

    def waiting_for(self, s: int) -> set[int]:
        """Roles that have a legal send in state ``s``."""
        return {t.src for t in self.out(s)}

    # -- JSON ---------------------------------------------------------------------------------
    def to_json(self) -> dict:
        d: dict[str, Any] = {
            "name": self.name, "roles": self.roles, "start": self.start, "final": self.final,
            "states": [[t.to_json() for t in st] for st in self.states],
            "budget": self.budget, "maxStrikes": self.max_strikes,
            "properties": [{"name": n, "formula": f} for n, f in self.properties],
        }
        if self.ifc is not None:
            d["ifc"] = self.ifc
        if self.locals is not None:
            d["locals"] = self.locals
        return d

    def dumps(self, **kw) -> str:
        return json.dumps(self.to_json(), **kw)

    @staticmethod
    def from_json(d: dict) -> "Protocol":
        states = [[Trans(t["src"], t["dst"], t["label"], _freeze(t.get("ty", "unit")),
                         _freeze(t.get("pred", True)), t["next"]) for t in st] for st in d["states"]]
        return Protocol(
            name=d.get("name", "protocol"), roles=list(d["roles"]), states=states,
            start=d.get("start", 0), final=list(d.get("final", [])), budget=d.get("budget", 1000),
            max_strikes=d.get("maxStrikes", 3),
            properties=[(p.get("name", "property"), p["formula"]) for p in d.get("properties", [])],
            ifc=d.get("ifc"), locals=d.get("locals"))

    @staticmethod
    def load(path: str) -> "Protocol":
        with open(path) as f:
            return Protocol.from_json(json.load(f))

    # -- pretty printing ------------------------------------------------------------------------
    def describe_trans(self, t: Trans) -> str:
        return f"{self.roles[t.src]} -> {self.roles[t.dst]} : {t.label}({ty_str(t.ty)})" + (
            "" if t.pred is True else f" where {pred_str(t.pred)}")

    def summary(self) -> str:
        n_t = sum(len(s) for s in self.states)
        return f"protocol {self.name}: {len(self.roles)} roles, {len(self.states)} states, {n_t} transitions"


def ty_str(ty: Any) -> str:
    if isinstance(ty, str):
        return ty
    if "enum" in ty:
        return "enum{" + ", ".join(ty["enum"]) + "}"
    if "list" in ty:
        return f"list<{ty_str(ty['list'])}>"
    if "record" in ty:
        return "{" + ", ".join(f"{n}: {ty_str(t)}" for n, t in ty["record"]) + "}"
    return str(ty)


def pred_str(p: Any) -> str:
    if p is True:
        return "true"
    if p is False:
        return "false"
    (op, a), = p.items()
    if op in ("and", "or"):
        return f"({pred_str(a[0])} {op} {pred_str(a[1])})"
    if op == "not":
        return f"not {pred_str(a)}"
    path = ".".join(a[0]) or "value"
    sym = {"intLe": "<=", "intGe": ">=", "lenLe": "len <=", "strIn": "in", "strNotContains": "!contains",
           "eqStr": "==", "eqBool": "=="}[op]
    if op == "lenLe":
        return f"{'.'.join(a[0]) + '.' if a[0] else ''}len <= {a[1]}"
    return f"{path} {sym} {json.dumps(a[1])}"
