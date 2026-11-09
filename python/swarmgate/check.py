"""Front-end to the verified checker (``swarmgate check``) and the kernel-proof emitter."""
from __future__ import annotations

import json
import os
import subprocess
import tempfile
from typing import Any

from .gate import find_binary
from .protocol import Protocol, cap_bits


def _write(P: Protocol) -> str:
    fd, path = tempfile.mkstemp(suffix=".json", prefix="swarmgate-")
    with os.fdopen(fd, "w") as f:
        f.write(P.dumps())
    return path


def verify(P: Protocol, binary: str | None = None) -> dict[str, Any]:
    """Run all verified checks; returns the JSON report of ``swarmgate check``."""
    binary = binary or find_binary()
    if not binary:
        raise FileNotFoundError("swarmgate binary not found (cd lean && lake build)")
    path = _write(P)
    try:
        out = subprocess.run([binary, "check", path], capture_output=True, text=True, check=True).stdout
    finally:
        os.unlink(path)
    return json.loads(out)


def emit_lean(P: Protocol, name: str, native: bool = False, binary: str | None = None) -> str:
    binary = binary or find_binary()
    path = _write(P)
    try:
        args = [binary, "emit-lean", path, name] + (["--native"] if native else [])
        return subprocess.run(args, capture_output=True, text=True, check=True).stdout
    finally:
        os.unlink(path)


def summarize(report: dict[str, Any]) -> str:
    def mark(ok):
        return "✓" if ok else "✗"
    lines = [f"{report['name']}: {report['states']} states, well-formed {mark(report['wellFormed']['ok'])}"]
    for i in report["wellFormed"]["issues"]:
        lines.append(f"    ! {i}")
    for p in report.get("properties", []):
        lines.append(f"  {mark(p['verified'])} property {p['name']}"
                     + ("" if p["verified"] else f"   counterexample: {_trace(p['counterexample'])}"))
    if "ifc" in report:
        r = report["ifc"]
        lines.append(f"  {mark(r['verified'])} information flow (no tainted sensitive action)"
                     + ("" if r["verified"] else f"   counterexample: {_trace(r['counterexample'])}"))
    lines.append(f"  {mark(report['noStuck']['verified'])} no stuck states")
    lines.append(f"  {mark(report['completion']['verified'])} completion always possible")
    b = report["bounded"]
    lines.append(f"  {mark(b['verified'])} bounded" + (f" (≤ {b['maxMessages']} messages)" if b["verified"] else
                                                     " (unbounded loops; runtime budget applies)"))
    if "decentralised" in report:
        r = report["decentralised"]
        lines.append(f"  {mark(r['verified'])} decentralised enforcement sound"
                     + ("" if r["verified"] else f"   counterexample: {_trace(r['counterexample'])}"))
    return "\n".join(lines)


def _trace(c) -> str:
    if c is None:
        return ""
    if isinstance(c, str):
        return c
    if isinstance(c, dict):
        s = _trace(c.get("path", []))
        if c.get("then"):
            s += f" ⇒ then {c['then']['src']}→{c['then']['dst']}:{c['then']['label']}"
        if c.get("thenUnjustified"):
            u = c["thenUnjustified"]
            s += f" ⇒ sidecars also allow {u['src']}→{u['dst']}:{u['label']}"
        if c.get("taintedRoles"):
            s += f" (tainted: {', '.join(c['taintedRoles'])})"
        return s
    return " · ".join(f"{e['src']}→{e['dst']}:{e['label']}" for e in c)


# ---------------------------------------------------------------------------------------------
# Quantitative containment (unverified analysis): attacker-controlled bits reaching each role
# ---------------------------------------------------------------------------------------------

def influence_bits(P: Protocol, max_steps: int | None = None) -> dict[str, float]:
    """Max number of attacker-chosen bits that can reach each *untainted* role along any run.

    Tainted roles (reachable by high-capacity untrusted content) get ``inf``. Low-capacity edges out of
    tainted roles contribute their capacity. Loops make the bound infinite unless the protocol is bounded.
    """
    ifc = P.ifc or {"untrusted": [], "maxBits": 8}
    maxb = ifc.get("maxBits", 8)
    INF = float("inf")
    # explore (state, taint) with per-role accumulated bits (max over paths, by fixpoint up to a cap)
    best: dict[tuple[int, int], tuple[float, ...]] = {}
    t0 = 0
    for r in ifc.get("untrusted", []):
        t0 |= 1 << r
    n = len(P.roles)
    init = (P.start, t0)
    best[init] = tuple(0.0 for _ in range(n))
    work = [init]
    iters = 0
    while work and iters < 200000:
        iters += 1
        c = work.pop()
        s, T = c
        bits = best[c]
        for t in P.out(s):
            T2, b2 = T, list(bits)
            src_t = (T >> t.src) & 1
            if src_t:
                cb = cap_bits(t.ty)
                if t.dst in ifc.get("endorsers", []):
                    pass
                elif cb is None or cb > maxb:
                    T2 = T | (1 << t.dst)
                else:
                    b2[t.dst] = b2[t.dst] + cb
            c2 = (t.next, T2)
            old = best.get(c2)
            new = tuple(b2) if old is None else tuple(max(a, b) for a, b in zip(old, b2))
            if old is None or new != old:
                if old is not None and iters > 20000:
                    new = tuple(INF if a != b else a for a, b in zip(old, new))
                best[c2] = new
                work.append(c2)
    out: dict[str, float] = {}
    for (s, T), bits in best.items():
        for r in range(n):
            v = INF if (T >> r) & 1 else bits[r]
            out[P.roles[r]] = max(out.get(P.roles[r], 0.0), v)
    return out
