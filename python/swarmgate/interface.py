"""Deployer interfaces (meta-policies) — the only security metadata SwarmGate trusts in v2.

An *interface* lists the roles, the message kinds the tools and agents understand (the capability catalog),
the IFC policy (untrusted sources, endorsers, sensitive actions, low-capacity threshold), properties every
protocol must satisfy, and a maximum session length. Protocols — possibly written by an LLM — are admitted
only if the verified Lean check (`swarmgate admit`, Theorem T8) accepts them against the interface.

    interface Ops {
      roles User, Planner, Web, Executor, Shell;
      untrusted Web; endorser Approver; sensitive Executor -> Shell : Exec; lowcap 8;
      bound 30;
      type Cmd = enum{df_h, uptime};
      message User -> Planner : Task(str) where len <= 2000;
      message Executor -> Shell : Exec(Cmd);
      message Executor -> Shell : Exec(str);     // a richer variant the tool also accepts
      property ExecAfterApproval: Executor -> Shell : Exec implies once Approver -> Executor : Approved;
    }

The protocol's own `untrusted/endorser/sensitive/property` declarations are ignored at admission; its
roles are re-indexed by name into the interface's role order.
"""
from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Any

from .dsl import DSLError, Parser, ProtocolAST, compile_source, lex
from .protocol import Protocol, Trans, ty_str, pred_str


@dataclass
class Interface:
    name: str
    roles: list[str]
    untrusted: list[str] = field(default_factory=list)
    endorsers: list[str] = field(default_factory=list)
    sensitive: list[dict] = field(default_factory=list)       # patterns with role names / None
    lowcap: int = 8
    bound: int | None = None
    messages: list[dict] = field(default_factory=list)        # {src,dst,label,ty,pred} with role names
    properties: list[tuple[str, Any]] = field(default_factory=list)   # formulas with role names
    types: dict[str, Any] = field(default_factory=dict)
    source: str = ""

    # -- JSON for the Lean admission checker -------------------------------------------------------
    def _r(self, name):
        return None if name is None else self.roles.index(name)

    def _pat(self, p):
        return {"src": self._r(p["src"]), "dst": self._r(p["dst"]), "label": p["label"]}

    def _formula(self, f):
        if f is True or f is False:
            return f
        (k, a), = f.items()
        if k == "atom":
            return {"atom": self._pat(a)}
        if k in ("not", "prev", "once", "hist"):
            return {k: self._formula(a)}
        return {k: [self._formula(a[0]), self._formula(a[1])]}

    def ifc_json(self) -> dict:
        return {"untrusted": [self._r(r) for r in self.untrusted], "maxBits": self.lowcap,
                "sensitive": [self._pat(p) for p in self.sensitive],
                "endorsers": [self._r(r) for r in self.endorsers]}

    def to_json(self) -> dict:
        return {"name": self.name, "roles": self.roles,
                "catalog": [{"src": self._r(m["src"]), "dst": self._r(m["dst"]), "label": m["label"],
                             "ty": m["ty"], "pred": m["pred"]} for m in self.messages],
                "ifc": self.ifc_json(),
                "properties": [{"name": n, "formula": self._formula(f)} for n, f in self.properties],
                "maxLen": self.bound}

    # -- binding a (possibly LLM-written) protocol to this interface ----------------------------------
    def bind(self, P: Protocol) -> Protocol:
        """Re-index P's roles into the interface order and replace its security metadata by ours."""
        for r in P.roles:
            if r not in self.roles:
                raise DSLError(f"protocol uses role {r!r} that is not in interface {self.name}")
        perm = [self.roles.index(r) for r in P.roles]
        states = [[Trans(perm[t.src], perm[t.dst], t.label, t.ty, t.pred, t.next) for t in st] for st in P.states]
        # runtime limits come from the interface, never from the (possibly LLM-written) protocol text
        Q = Protocol(name=P.name, roles=list(self.roles), states=states, start=P.start, final=list(P.final),
                     budget=self.bound if self.bound else 1000, max_strikes=3, ifc=self.ifc_json(),
                     properties=[(n, self._formula(f)) for n, f in self.properties])
        Q.source = P.source
        return Q

    # -- prompt rendering ------------------------------------------------------------------------------
    def describe(self) -> str:
        lines = [f"interface {self.name}:", f"  roles: {', '.join(self.roles)}"]
        if self.untrusted:
            lines.append(f"  untrusted sources (their output may contain prompt injections): {', '.join(self.untrusted)}")
        if self.endorsers:
            lines.append(f"  endorsers (deterministic, non-LLM, cannot be injected): {', '.join(self.endorsers)}")
        if self.sensitive:
            sens = [f"{p['src'] or '*'} -> {p['dst'] or '*'} : {p['label'] or '*'}" for p in self.sensitive]
            lines.append(f"  sensitive actions: {'; '.join(sens)}")
        lines.append(f"  low-capacity threshold: messages whose type carries <= {self.lowcap} bits "
                     f"(bool, small enums, records of those) do not propagate taint; str/list/int do")
        if self.bound:
            lines.append(f"  every session must provably deliver at most {self.bound} messages")
        lines.append("  allowed message kinds (a protocol may only use these, with exactly these types):")
        for m in self.messages:
            w = "" if m["pred"] is True else f" where {pred_str(m['pred'])}"
            lines.append(f"    {m['src']} -> {m['dst']} : {m['label']}({ty_str(m['ty'])}){w}")
        for n, _ in self.properties:
            lines.append(f"  required property: {n}")
        return "\n".join(lines)


class _IfaceParser(Parser):
    def interface(self) -> Interface:
        self.eat("interface")
        name = self.ident()
        I = Interface(name=name, roles=[])
        self.eat("{")
        while not self.at("}"):
            if self.at("roles"):
                self.eat(); I.roles += self.ident_list(); self.eat(";")
            elif self.at("untrusted"):
                self.eat(); I.untrusted += self.ident_list(); self.eat(";")
            elif self.at("endorser"):
                self.eat(); I.endorsers += self.ident_list(); self.eat(";")
            elif self.at("sensitive"):
                self.eat(); I.sensitive.append(self.evpat())
                while self.at(","):
                    self.eat(","); I.sensitive.append(self.evpat())
                self.eat(";")
            elif self.at("lowcap"):
                self.eat(); I.lowcap = int(self.eat(kind="num").val); self.eat(";")
            elif self.at("bound"):
                self.eat(); I.bound = int(self.eat(kind="num").val); self.eat(";")
            elif self.at("type"):
                self.eat(); n = self.ident(); self.eat("="); I.types[n] = self.ty(I.types); self.eat(";")
            elif self.at("property"):
                self.eat(); n = self.ident(); self.eat(":"); f = self.formula(); self.eat(";")
                I.properties.append((n, f))
            elif self.at("message"):
                self.eat(); src = self.ident(); self.eat("->"); dst = self.ident(); self.eat(":")
                label = self.ident(); ty: Any = "unit"
                if self.at("("):
                    self.eat("("); ty = self.ty(I.types); self.eat(")")
                pred: Any = True
                if self.at("where"):
                    self.eat(); pred = self.pred()
                self.eat(";")
                for r in (src, dst):
                    if r not in I.roles:
                        raise DSLError(f"interface {name}: undeclared role {r!r}")
                I.messages.append({"src": src, "dst": dst, "label": label, "ty": ty, "pred": pred})
            else:
                raise self.err("unexpected token in interface")
        self.eat("}")
        for r in I.untrusted + I.endorsers:
            if r not in I.roles:
                raise DSLError(f"interface {name}: undeclared role {r!r}")
        return I


def parse_interface(src: str) -> Interface:
    p = _IfaceParser(lex(src))
    I = p.interface()
    I.source = src
    return I


def load_interface(path: str) -> Interface:
    with open(path) as f:
        return parse_interface(f.read())


def compile_against(I: Interface, protocol_src: str) -> Protocol:
    """Compile a protocol (e.g. LLM-written) and bind it to the interface (roles + security metadata)."""
    P = compile_source(protocol_src)
    return I.bind(P)
