"""Tests for the A2A gateway core and the MCP proxy (in-process, no network)."""
from swarmgate.dsl import compile_source
from swarmgate.gateway import Gateway
from swarmgate.mcp_gate import McpGatewaySession, ProtocolViolation

PROTO = """
protocol P {
  roles User, Agent, Tool;
  User -> Agent : Ask(str);
  call Agent -> Tool : run({cmd: enum{ls, cat}}) returns str;
  Agent -> User : Reply(str);
}"""


def test_gateway_enforces_and_authenticates():
    forwarded = []
    gw = Gateway(forward=lambda url, env: forwarded.append((url, env)))
    P = compile_source(PROTO)
    info = gw.create_session(P, endpoints={"Agent": "http://agent.local/hook"})
    sid, tok = info["session"], info["tokens"]

    # wrong token is rejected and blamed
    r = gw.send(sid, "User", "Agent", "Ask", "hi", token="wrong")
    assert not r["delivered"] and r["reason"] == "auth"

    # honest first move, forwarded to the Agent endpoint
    r = gw.send(sid, "User", "Agent", "Ask", "hi", token=tok["User"])
    assert r["delivered"] and r["forwarded"]
    assert forwarded and forwarded[-1][0] == "http://agent.local/hook"

    # Agent cannot skip the tool and answer directly
    r = gw.send(sid, "Agent", "User", "Reply", "done", token=tok["Agent"])
    assert not r["delivered"]

    # impersonation: Tool tries to speak as the Agent (right token, wrong claimed source)
    r = gw.send(sid, "Agent", "Tool", "run", {"cmd": "ls"}, token=tok["Agent"])
    assert r["delivered"]
    r = gw.send(sid, "Tool", "Agent", "run_result", "listing", token=tok["Tool"])
    assert r["delivered"]
    r = gw.send(sid, "Agent", "User", "Reply", "done", token=tok["Agent"])
    assert r["delivered"] and r["final"]

    log = gw.log(sid)["log"]
    assert any(e["verdict"] == "reject" for e in log)


def test_next_moves_guidance():
    gw = Gateway()
    P = compile_source(PROTO)
    info = gw.create_session(P)
    sid = info["session"]
    moves = gw.next_moves(sid, "User")["moves"]
    assert [m["label"] for m in moves] == ["Ask"]
    assert moves[0]["payload_schema"]["type"] == "string"


def test_mcp_proxy_least_privilege():
    P = compile_source(PROTO)
    calls = []

    def call_tool(name, args):
        calls.append((name, args))
        return "listing"

    sess = McpGatewaySession(P, agent_role="Agent", tool_roles={"run": "Tool"}, call_tool=call_tool)
    # before the Agent is addressed, it still owns the first tool call only after User->Agent.
    # drive the session: User asks first (through the same gate)
    from swarmgate.protocol import Event
    sess.gate.submit(0, Event(0, 1, "Ask", "hi"))   # User -> Agent
    assert [t["name"] for t in sess.allowed_tools()] == ["run"]
    out = sess.call("run", {"cmd": "ls"})
    assert out == "listing" and calls == [("run", {"cmd": "ls"})]
    # calling again is now illegal (protocol moved on)
    try:
        sess.call("run", {"cmd": "cat"})
        assert False, "should have raised"
    except ProtocolViolation as e:
        assert "run" not in [t["name"] for t in sess.allowed_tools()]


def test_mcp_proxy_selects_tool_by_name():
    """Regression: two tools served by the same role must map to their own labels."""
    P = compile_source("""
    protocol Q { roles User, Agent, Srv;
      User -> Agent : Ask(str);
      choice at Agent {
        call Agent -> Srv : search(str) returns str;
      } or {
        call Agent -> Srv : fetch(str) returns str;
      }
      Agent -> User : Reply(str);
    }""")
    seen = []
    sess = McpGatewaySession(P, "Agent", {"search": "Srv", "fetch": "Srv"},
                             lambda n, a: seen.append(n) or "ok")
    from swarmgate.protocol import Event
    sess.gate.submit(0, Event(0, 1, "Ask", "hi"))
    assert sorted(t["name"] for t in sess.allowed_tools()) == ["fetch", "search"]
    sess.call("fetch", "x")
    assert seen == ["fetch"]
    log = [t.label for t in sess.gate.protocol.out(0)]  # sanity: protocol unchanged
    assert "Ask" in log
