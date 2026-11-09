"""E5: per-message gate latency (Python mirror vs compiled Lean binary) and check-time scaling."""
from __future__ import annotations

import json
import os
import random
import statistics
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "python"))

from swarmgate.check import verify  # noqa: E402
from swarmgate.dsl import compile_file  # noqa: E402
from swarmgate.fuzz import honest_walk, rand_protocol  # noqa: E402
from swarmgate.gate import LeanGate, LeanServer, PyGate  # noqa: E402
from swarmgate.project import with_locals  # noqa: E402


def bench_gate(n=20000):
    rng = random.Random(3)
    P = compile_file(os.path.join(ROOT, "protocols", "ops_hardened.sg"))
    P.budget = 10**9
    walks = [honest_walk(rng, P, 16) for _ in range(400)]
    events = [e for w in walks for e in w] or []
    # Python
    py = PyGate(P)
    t0 = time.perf_counter()
    done = 0
    while done < n:
        for e in events:
            if py.state < 0 or P.is_final(py.state):
                py = PyGate(P)
            py.submit(e.src, e)
            done += 1
            if done >= n:
                break
    py_us = 1e6 * (time.perf_counter() - t0) / n
    # Lean binary (round-trip over the pipe)
    server = LeanServer(P)
    le = LeanGate(P, server=server)
    t0 = time.perf_counter()
    done = 0
    while done < n:
        for e in events:
            if le.state < 0 or P.is_final(le.state):
                le = LeanGate(P, server=server)
            le.submit(e.src, e)
            done += 1
            if done >= n:
                break
    le_us = 1e6 * (time.perf_counter() - t0) / n
    server.close()
    return {"python_us_per_msg": round(py_us, 2), "lean_us_per_msg": round(le_us, 2),
            "python_msgs_per_s": round(1e6 / py_us), "lean_msgs_per_s": round(1e6 / le_us)}


def bench_check_scaling():
    rng = random.Random(5)
    rows = []
    for n in [4, 8, 16, 32, 64, 128]:
        times = []
        for _ in range(5):
            P = rand_protocol(rng, n_states=n, n_roles=4)
            with_locals(P)
            t0 = time.perf_counter()
            verify(P)
            times.append(time.perf_counter() - t0)
        rows.append({"states": n, "check_ms": round(1000 * statistics.median(times), 1)})
    return rows


def main():
    out = {"per_message": bench_gate(), "check_scaling": bench_check_scaling()}
    os.makedirs(os.path.join(ROOT, "eval", "results"), exist_ok=True)
    with open(os.path.join(ROOT, "eval", "results", "overhead.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
