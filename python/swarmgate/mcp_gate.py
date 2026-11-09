"""Protocol-enforcing MCP proxy.

Model Context Protocol (MCP) tool calls become protocol messages: a ``tools/call`` of tool ``T`` by the
agent is the message ``agent → T : <tool>``, and the tool's result is ``T → agent : <tool>_result``.
Wrapping the agent↔server channel in the gate means an agent can only call the tools that the session
protocol permits *in the current state* — least privilege per step (cf. Concordat), but driven by a
Lean-verified multiparty protocol and usable across a whole swarm of agents and tools.

``McpGatewaySession`` is transport-agnostic: give it a ``call_tool(name, args) -> result`` callable (e.g.
wrapping ``mcp.ClientSession``), and it enforces the protocol around it. ``allowed_tools()`` returns the
tool list to advertise to the model, filtered to what is legal now.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable

from .gate import Gate, PyGate
from .llm import json_schema
from .protocol import Event, Protocol, ty_str


class ProtocolViolation(Exception):
    def __init__(self, reason: str, allowed: list[str]):
        super().__init__(f"call rejected by protocol gate ({reason}); allowed now: {allowed}")
        self.reason = reason
        self.allowed = allowed


@dataclass
class McpGatewaySession:
    protocol: Protocol
    agent_role: str
    tool_roles: dict[str, str]          # tool name -> role name
    call_tool: Callable[[str, dict], Any]
    gate: Gate | None = None

    def __post_init__(self):
        self.gate = self.gate or PyGate(self.protocol)
        self._ridx = {r: i for i, r in enumerate(self.protocol.roles)}

    def _allowed_calls(self) -> list[tuple[str, Any]]:
        """(tool_name, request_transition) legal now for the agent."""
        a = self._ridx[self.agent_role]
        out = []
        for t in self.gate.allowed(a):
            if self.tool_roles.get(t.label) == self.protocol.roles[t.dst]:
                out.append((t.label, t))
        return out

    def allowed_tools(self) -> list[dict]:
        """MCP tool descriptors for exactly the calls that are legal now (for the model)."""
        res = []
        for name, t in self._allowed_calls():
            res.append({"name": name, "description": f"(payload type {ty_str(t.ty)})",
                        "inputSchema": json_schema(t.ty)})
        return res

    def call(self, tool: str, args: Any = None) -> Any:
        """Gate a tool call. Raises ProtocolViolation if not permitted; otherwise runs it and records
        the result as the tool's reply message."""
        if tool not in self.tool_roles:
            raise ProtocolViolation("unknown tool", [n for n, _ in self._allowed_calls()])
        trole = self._ridx[self.tool_roles[tool]]
        a = self._ridx[self.agent_role]
        # find the request transition for this tool
        req = next((t for t in self.gate.allowed(a) if t.dst == trole and t.label == tool), None)
        if req is None:
            raise ProtocolViolation("not enabled", [n for n, _ in self._allowed_calls()])
        v = self.gate.submit(a, Event(a, trole, req.label, args))
        if not v.delivered:
            raise ProtocolViolation(v.reason or "rejected", [n for n, _ in self._allowed_calls()])
        result = self.call_tool(tool, args if isinstance(args, dict) else {"value": args})
        # record the tool's reply so the session advances; find the reply transition tool->agent
        reply = next((t for t in self.gate.allowed(trole) if t.dst == a and t.label == f"{tool}_result"), None) or \
            next((t for t in self.gate.allowed(trole) if t.dst == a), None)
        if reply is not None:
            self.gate.submit(trole, Event(trole, a, reply.label, result))
        return result

    @property
    def finished(self) -> bool:
        return self.gate.finished
