#!/usr/bin/env python3
"""A 30-line tour: compile a protocol, verify it, run a swarm, watch the gate reject an off-protocol move.

    python examples/demo.py
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))

from swarmgate.check import summarize, verify
from swarmgate.dsl import compile_file
from swarmgate.gate import PyGate
from swarmgate.runtime import Context, FnAgent, Swarm, ToolAgent

P = compile_file(os.path.join(os.path.dirname(__file__), "..", "protocols", "approval_gate.sg"))

print("=== Verified guarantees ===")
print(summarize(verify(P)))

print("\n=== A run (the Agent tries to skip the human, then behaves) ===")


def agent(ctx: Context):
    m = ctx.trigger
    if m.label == "Task":
        bad = ctx.send("Shell", "exec", {"cmd": "ls", "arg": "-l"})       # skip approval
        print(f"  Agent->Shell (unapproved): delivered={bad.delivered} reason={bad.reason}")
        ctx.send("Human", "Propose", {"cmd": "ls", "arg": "-l"})          # the legal move
    elif m.label == "Approve":
        ctx.send("Shell", "exec", m.payload)
    elif m.label == "exec_result":
        ctx.send("User", "Done", "finished")


human = FnAgent("Human", lambda ctx: ctx.send("Agent", "Approve", ctx.trigger.payload)
                if ctx.trigger and ctx.trigger.label == "Propose" else None)
shell = ToolAgent("Shell", {"exec": lambda p: ("exec_result", "total 0")})
user = FnAgent("User", lambda ctx: ctx.send("Agent", "Task", "list the files") if ctx.trigger is None else None)

res = Swarm(P, [user, FnAgent("Agent", agent), human, shell], gate=PyGate(P)).run("User")
print("  result:", res.summary())
print("  delivered:", " -> ".join(f"{e.src}:{e.label}" for e in res.delivered))
