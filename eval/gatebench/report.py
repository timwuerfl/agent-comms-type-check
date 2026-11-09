"""Aggregate GateBench results (JSONL) into tables."""
from __future__ import annotations

import collections
import json
import math
import sys

DEF_ORDER = ["none", "topology", "session_naive", "hardened", "synth_unverified", "synth_verified"]


def wilson(k: int, n: int, z: float = 1.96) -> tuple[float, float]:
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, c - h), min(1.0, c + h))


def load(paths, keep_errors=False):
    """Rows with an agent/API error or without a protocol are excluded from rates (reported separately)."""
    rows = []
    for p in paths:
        for line in open(p):
            try:
                r = json.loads(line)
            except Exception:
                continue
            if not keep_errors and (r.get("error") or r.get("no_protocol")):
                continue
            rows.append(r)
    return rows


def table(rows, by=("defense",), filt=lambda r: True, metrics=("utility", "attack", "ctrl", "data")):
    g = collections.defaultdict(list)
    for r in rows:
        if filt(r):
            g[tuple(r.get(k) for k in by)].append(r)
    out = {}
    for k, rs in g.items():
        d = {"n": len(rs)}
        for m in metrics:
            vals = [bool(r.get(m)) for r in rs]
            d[m] = sum(vals) / len(vals)
            d[m + "_ci"] = wilson(sum(vals), len(vals))
        d["rejections"] = sum(r.get("rejections", 0) for r in rs) / len(rs)
        bv = [r for r in rs if r.get("bound_violated") is not None]
        d["bound_violations"] = sum(1 for r in bv if r["bound_violated"])
        d["bound_checked"] = len(bv)
        d["no_protocol"] = sum(1 for r in rs if r.get("no_protocol"))
        d["errors"] = sum(1 for r in rs if r.get("error"))
        d["infected_mean"] = sum(len(r.get("infected", [])) for r in rs) / len(rs)
        out[k] = d
    return out


def show(rows):
    order = {d: i for i, d in enumerate(DEF_ORDER)}
    print("\n== utility (benign) | ASR inject | ASR compromised | infected roles (compromised) | bound violations ==")
    U = table(rows, filt=lambda r: r["threat"] == "benign")
    I = table(rows, filt=lambda r: r["threat"] == "inject")
    C = table(rows, filt=lambda r: r["threat"] == "compromised")
    keys = sorted({k for t in (U, I, C) for k in t}, key=lambda k: order.get(k[0], 99))
    for k in keys:
        u, i, c = U.get(k, {}), I.get(k, {}), C.get(k, {})
        f = lambda d, m: f"{100*d[m]:5.1f}% (n={d['n']})" if d else "   -   "
        bv = sum(t.get(k, {}).get("bound_violations", 0) for t in (U, I, C))
        bc = sum(t.get(k, {}).get("bound_checked", 0) for t in (U, I, C))
        print(f"{k[0]:17s} util {f(u,'utility')}  inj {f(i,'attack')}  comp {f(c,'attack')} "
              f"[ctrl {100*c.get('ctrl',0):4.0f}% data {100*c.get('data',0):4.0f}%] "
              f"infected {c.get('infected_mean',0):.2f}  boundviol {bv}/{bc}")
    print("\n== injection ASR by family ==")
    F = table(rows, by=("defense", "injection"), filt=lambda r: r["threat"] == "inject")
    for k in sorted(F, key=lambda k: (order.get(k[0], 99), str(k[1]))):
        print(f"  {k[0]:17s} {str(k[1]):12s} ASR {100*F[k]['attack']:5.1f}%  util {100*F[k]['utility']:5.1f}%  n={F[k]['n']}")
    print("\n== per domain (compromised ASR / benign utility) ==")
    D = table(rows, by=("domain", "defense"))
    for k in sorted(D, key=lambda k: (k[0], order.get(k[1], 99))):
        cu = table([r for r in rows if r["domain"] == k[0] and r["defense"] == k[1]],
                   by=("threat",))
        print(f"  {k[0]:8s} {k[1]:17s} " + "  ".join(f"{th}:util={100*v['utility']:.0f}% atk={100*v['attack']:.0f}%"
                                                 for (th,), v in sorted(cu.items())))


if __name__ == "__main__":
    show(load(sys.argv[1:]))
