"""Differential testing: the Python reference gate must agree with the verified Lean gate on everything."""
import os
import random

import pytest

from swarmgate.fuzz import adversarial_attempt, honest_walk, rand_protocol
from swarmgate.gate import LeanGate, LeanServer, PyGate, find_binary

N_PROTOCOLS = int(os.environ.get("SG_FUZZ_PROTOCOLS", "40"))
N_ATTEMPTS = int(os.environ.get("SG_FUZZ_ATTEMPTS", "300"))

needs_lean = pytest.mark.skipif(find_binary() is None, reason="swarmgate binary not built")


@needs_lean
def test_gates_agree_on_adversarial_streams():
    rng = random.Random(1234)
    total = 0
    for i in range(N_PROTOCOLS):
        P = rand_protocol(rng)
        server = LeanServer(P)
        try:
            for run in range(3):
                py, le = PyGate(P), LeanGate(P, server=server, session=f"p{i}r{run}")
                if run == 2:
                    py.kill(); le.kill()
                for _ in range(N_ATTEMPTS // 3):
                    sender, e = adversarial_attempt(rng, P, py.state)
                    v1, v2 = py.submit(sender, e), le.submit(sender, e)
                    total += 1
                    assert v1 == v2, (P.to_json(), sender, e, v1, v2)
                    assert py.state == le.state
                    assert py.taint() == le.taint()
        finally:
            server.close()
    assert total > 0


@needs_lean
def test_transparency_honest_walks():
    """T2 empirically: conformant, in-budget traffic is never rejected (by either gate)."""
    rng = random.Random(99)
    for _ in range(N_PROTOCOLS):
        P = rand_protocol(rng)
        P.budget = 10_000
        server = LeanServer(P)
        try:
            for _ in range(5):
                walk = honest_walk(rng, P)
                py, le = PyGate(P), LeanGate(P, server=server)
                for e in walk:
                    assert py.submit(e.src, e).delivered
                    assert le.submit(e.src, e).delivered
        finally:
            server.close()
