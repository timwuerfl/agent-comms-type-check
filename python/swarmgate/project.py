"""Projection of a global protocol onto one role (automata projection, THEORY.md §6).

Events not involving the role are hidden (ε); the local automaton is the subset construction of the
ε-closure. This code is *untrusted*: the Lean checker (`checkDecentralised`, Theorem T6a) validates that
the resulting sidecars never jointly admit a trace outside the global protocol.
"""
from __future__ import annotations

import json
from typing import Any

from .protocol import Protocol


def _closure(P: Protocol, states: frozenset[int], role: int) -> frozenset[int]:
    seen = set(states)
    stack = list(states)
    while stack:
        s = stack.pop()
        for t in P.out(s):
            if role not in (t.src, t.dst) and t.next not in seen:
                seen.add(t.next)
                stack.append(t.next)
    return frozenset(seen)


def project(P: Protocol, role: int) -> dict[str, Any]:
    """Local automaton for ``role`` in the JSON format read by the Lean checker."""
    start = _closure(P, frozenset([P.start]), role)
    ids: dict[frozenset[int], int] = {start: 0}
    order = [start]
    rows: list[list[dict]] = []
    conflicts: list[str] = []
    i = 0
    while i < len(order):
        S = order[i]
        i += 1
        groups: dict[tuple, list] = {}
        for s in sorted(S):
            for t in P.out(s):
                if t.src == role:
                    key = ("send", t.dst, t.label)
                elif t.dst == role:
                    key = ("recv", t.src, t.label)
                else:
                    continue
                groups.setdefault(key, []).append(t)
        row = []
        for (d, peer, label), ts in groups.items():
            guards = {json.dumps([t.ty, t.pred], sort_keys=True) for t in ts}
            if len(guards) > 1:
                conflicts.append(f"{P.roles[role]}: {d} {label} has different payload types in merged states")
            target = _closure(P, frozenset(t.next for t in ts), role)
            if target not in ids:
                ids[target] = len(order)
                order.append(target)
            row.append({"dir": d, "peer": peer, "label": label, "ty": ts[0].ty, "pred": ts[0].pred,
                        "next": ids[target]})
        rows.append(row)
    return {"role": P.roles[role], "start": 0, "states": rows, "conflicts": conflicts,
            "global_states": [sorted(S) for S in order]}


def project_all(P: Protocol) -> list[dict[str, Any]]:
    return [project(P, r) for r in range(len(P.roles))]


def with_locals(P: Protocol) -> Protocol:
    """Attach projections so that ``swarmgate check`` also validates decentralised enforcement."""
    P.locals = [{"start": L["start"], "states": L["states"]} for L in project_all(P)]
    return P


def local_str(P: Protocol, L: dict) -> str:
    lines = [f"local protocol of {L['role']}:"]
    for i, row in enumerate(L["states"]):
        for t in row:
            arrow = "!" if t["dir"] == "send" else "?"
            lines.append(f"  {i}: {arrow}{P.roles[t['peer']]} {t['label']} -> {t['next']}")
    return "\n".join(lines)
