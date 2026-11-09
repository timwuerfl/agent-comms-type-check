"""Unit tests for the DSL compiler, the runtime, and enforcement behaviour (no network / no Lean needed)."""
import os

import pytest

from swarmgate.dsl import DSLError, compile_source
from swarmgate.gate import PyGate, SchemaGate, TopologyGate
from swarmgate.protocol import Event, cap_bits, has_ty, pred_eval
from swarmgate.runtime import Agent, Context, FnAgent, Swarm, ToolAgent

PROTO_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "protocols")


def test_has_ty_and_refinements():
    assert has_ty({"record": [["cmd", {"enum": ["ls", "cat"]}], ["arg", "str"]]},
                  {"cmd": "ls", "arg": "x"})
    assert not has_ty({"record": [["cmd", {"enum": ["ls"]}]]}, {"cmd": "ls", "extra": 1})  # closed
    assert not has_ty("int", True)
    assert pred_eval({"lenLe": [["arg"], 3]}, {"arg": "abc"})
    assert not pred_eval({"lenLe": [["arg"], 3]}, {"arg": "abcd"})
    assert pred_eval({"strNotContains": [[], ";"]}, "safe")
    assert not pred_eval({"strNotContains": [[], ";"]}, "a;b")


def test_cap_bits():
    assert cap_bits("bool") == 1
    assert cap_bits({"enum": ["a", "b", "c", "d"]}) == 2
    assert cap_bits({"enum": ["a"]}) == 1
    assert cap_bits("str") is None
    assert cap_bits({"record": [["x", "bool"], ["y", {"enum": ["a", "b"]}]]}) == 2


def test_compile_choice_and_recursion():
    P = compile_source("""
    protocol P {
      roles A, B;
      A -> B : Start;
      rec L max 2 {
        choice at B { B -> A : More; A -> B : Ack; continue L; } or { B -> A : Done; }
      }
    }""")
    assert P.run(P.start, [Event(0, 1, "Start"), Event(1, 0, "Done")]) in P.final
    s = P.run(P.start, [Event(0, 1, "Start")])
    assert P.step(s, Event(1, 0, "Nope")) is None  # only More/Done enabled


def test_self_message_rejected():
    with pytest.raises(DSLError):
        compile_source("protocol P { roles A, B; A -> A : X; }")


def test_undeclared_role_rejected():
    with pytest.raises(DSLError):
        compile_source("protocol P { roles A, B; A -> C : X; }")


def test_enforcement_spoof_and_order():
    P = compile_source("protocol P { roles A, B, C; A -> B : X; B -> C : Y; }")
    g = PyGate(P)
    assert not g.submit(P.role("B"), Event(0, 1, "X")).delivered       # spoof: C claims to be A? no, B as A
    assert g.submit(P.role("A"), Event(0, 1, "X")).delivered            # honest
    assert not g.submit(P.role("A"), Event(0, 1, "X")).delivered       # out of order (already past)
    assert g.submit(P.role("B"), Event(1, 2, "Y")).delivered


def test_budget_and_quarantine():
    P = compile_source("protocol P { roles A, B; rec L { A -> B : X; B -> A : Y; continue L; } }")
    P.budget = 3
    g = PyGate(P)
    assert g.submit(0, Event(0, 1, "X")).delivered
    assert g.submit(1, Event(1, 0, "Y")).delivered
    assert g.submit(0, Event(0, 1, "X")).delivered
    r = g.submit(1, Event(1, 0, "Y"))
    assert not r.delivered and r.reason == "budget"


def test_runtime_handoff():
    P = compile_source("""
    protocol P { roles User, Agent, Tool;
      User -> Agent : Ask(str);
      Agent -> Tool : Do(str);
      Tool -> Agent : Res(str);
      Agent -> User : Reply(str);
    }""")

    def agent(ctx: Context):
        m = ctx.trigger
        if m.label == "Ask":
            ctx.send("Tool", "Do", "work")
        elif m.label == "Res":
            ctx.send("User", "Reply", "ok")

    tool = ToolAgent("Tool", {"Do": lambda p: ("Res", "42")})
    user = FnAgent("User", lambda ctx: ctx.send("Agent", "Ask", "hi") if ctx.trigger is None else None)
    sw = Swarm(P, [user, FnAgent("Agent", agent), tool])
    res = sw.run("User")
    assert res.completed
    assert [e.label for e in res.delivered] == ["Ask", "Do", "Res", "Reply"]


def test_gate_rejects_offprotocol_agent():
    P = compile_source("protocol P { roles User, A, B; User -> A : T; A -> B : M; B -> User : R; }")

    def rogue(ctx: Context):
        if ctx.trigger and ctx.trigger.label == "T":
            # A tries to skip B and answer the user directly
            r = ctx.send("User", "R", "forged")
            assert not r.delivered
            ctx.send("B", "M", "ok")

    sw = Swarm(P, [FnAgent("User", lambda c: c.send("A", "T", "x") if c.trigger is None else None),
                   FnAgent("A", rogue),
                   ToolAgent("B", {"M": lambda p: ("R", "done")})])
    res = sw.run("User")
    assert res.rejections >= 1
    assert all(not (e.src == "A" and e.dst == "User") for e in res.delivered)
