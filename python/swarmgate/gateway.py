"""A protocol-enforcing gateway for agent-to-agent (A2A) messaging and MCP tool calls.

This is the *reference monitor* as a network service, so that agents written in any language or framework
can be constrained by a Lean-verified session protocol: they only have to speak HTTP + JSON. The gateway
mediates every message; an agent never gets a direct handle on another. The decision is computed by the
gate (``PyGate`` by default, or the verified ``LeanGate`` via ``swarmgate serve``).

Design (framework-agnostic):

* A *session* is one run of a protocol with a chosen set of participant endpoints.
* ``POST /sessions`` creates a session from a compiled protocol and a role→endpoint map.
* ``POST /sessions/{id}/send`` is the only way to communicate. Body:
  ``{"sender": <role>, "to": <role>, "label": <str>, "payload": <json>, "token": <role token>}``.
  The gateway authenticates ``sender`` against its per-role bearer token (this is the "role-bound
  identity" the threat model assumes), checks the move with the gate, and on delivery forwards the
  message to the recipient's endpoint (webhook) if one is registered.
* ``GET /sessions/{id}/next?role=R`` returns the moves ``R`` may legally make now (so a dumb client can
  be protocol-guided), plus the JSON schema of each payload.
* ``GET /sessions/{id}/log`` returns the audit log (every attempt, with its verdict and blame).
* ``GET /.well-known/agent-protocol`` advertises the protocol (an "agent card"-style descriptor).

MCP tool calls are modelled uniformly: a tool is a role, ``tools/call`` is a message ``agent→tool`` and the
result is ``tool→agent``. ``McpGatewaySession`` wraps a real MCP client so that only protocol-legal tool
calls at the current session state are forwarded (see ``mcp_gate.py``).
"""
from __future__ import annotations

import json
import secrets
import time
from dataclasses import dataclass, field
from typing import Any, Callable

from .gate import Gate, PyGate, Verdict
from .llm import json_schema
from .protocol import Event, Protocol, ty_str


@dataclass
class Session:
    id: str
    protocol: Protocol
    gate: Gate
    endpoints: dict[str, str] = field(default_factory=dict)       # role -> webhook URL (optional)
    tokens: dict[str, str] = field(default_factory=dict)          # role -> bearer token
    log: list[dict] = field(default_factory=list)
    created: float = field(default_factory=time.time)

    def next_moves(self, role: str) -> list[dict]:
        r = self.protocol.role(role)
        out = []
        for t in self.gate.allowed(r):
            out.append({"to": self.protocol.roles[t.dst], "label": t.label, "type": ty_str(t.ty),
                        "payload_schema": json_schema(t.ty)})
        return out


class Gateway:
    """Transport-agnostic core. ``aiohttp_app()`` wraps it in an HTTP server; it is also usable in-process."""

    def __init__(self, gate_factory: Callable[[Protocol], Gate] = PyGate,
                 forward: Callable[[str, dict], None] | None = None):
        self.sessions: dict[str, Session] = {}
        self.gate_factory = gate_factory
        self.forward = forward  # (url, envelope) -> None; injected so tests need no real network

    # -- lifecycle ----------------------------------------------------------------------------------
    def create_session(self, protocol: Protocol, endpoints: dict[str, str] | None = None,
                        issue_tokens: bool = True) -> dict:
        sid = secrets.token_urlsafe(8)
        tokens = {r: secrets.token_urlsafe(12) for r in protocol.roles} if issue_tokens else {}
        s = Session(sid, protocol, self.gate_factory(protocol), endpoints or {}, tokens)
        self.sessions[sid] = s
        return {"session": sid, "tokens": tokens, "roles": protocol.roles,
                "start_moves": {r: s.next_moves(r) for r in protocol.roles}}

    def _auth(self, s: Session, role: str, token: str | None) -> bool:
        if not s.tokens:
            return True
        return secrets.compare_digest(s.tokens.get(role, ""), token or "")

    # -- the one communication primitive ------------------------------------------------------------
    def send(self, sid: str, sender: str, to: str, label: str, payload: Any = None,
             token: str | None = None) -> dict:
        s = self.sessions.get(sid)
        if s is None:
            return {"error": "no such session", "status": 404}
        P = s.protocol
        if sender not in P.roles:
            return {"error": f"unknown sender role {sender}", "status": 400}
        if not self._auth(s, sender, token):
            # authentication failure is itself a (blamed) rejection
            s.log.append({"t": time.time(), "sender": sender, "to": to, "label": label,
                          "verdict": "reject", "reason": "auth", "blamed": sender})
            return {"delivered": False, "reason": "auth", "status": 401}
        dst = P.role(to) if to in P.roles else len(P.roles) + 1000
        ev = Event(P.role(sender), dst, str(label), payload)
        before = s.gate.state
        try:
            json.dumps(payload)
            v: Verdict = s.gate.submit(P.role(sender), ev)
        except (TypeError, ValueError):
            v = Verdict(False, P.role(sender), "notEnabled")
        rec = {"t": time.time(), "sender": sender, "to": to, "label": label, "payload": payload,
               "verdict": v.to_json()["verdict"], "reason": v.reason,
               "blamed": None if v.blamed is None else P.roles[v.blamed] if v.blamed < len(P.roles) else v.blamed,
               "state_before": before, "state_after": s.gate.state,
               "taint": [P.roles[r] for r in sorted(s.gate.taint())]}
        s.log.append(rec)
        forwarded = False
        if v.delivered and to in s.endpoints and self.forward is not None:
            self.forward(s.endpoints[to], {"session": sid, "from": sender, "to": to, "label": label,
                                           "payload": payload})
            forwarded = True
        return {"delivered": v.delivered, "reason": v.reason,
                "blamed": rec["blamed"], "forwarded": forwarded,
                "next": s.next_moves(sender), "final": P.is_final(s.gate.state),
                "taint": rec["taint"], "status": 200}

    def next_moves(self, sid: str, role: str) -> dict:
        s = self.sessions.get(sid)
        if s is None:
            return {"error": "no such session", "status": 404}
        return {"role": role, "moves": s.next_moves(role), "final": s.protocol.is_final(s.gate.state)}

    def log(self, sid: str) -> dict:
        s = self.sessions.get(sid)
        if s is None:
            return {"error": "no such session", "status": 404}
        return {"session": sid, "log": s.log}

    def card(self, protocol: Protocol) -> dict:
        """An 'agent card'-style descriptor advertising the enforced protocol."""
        return {"protocol": protocol.name, "roles": protocol.roles,
                "enforced_by": "swarmgate (Lean-verified session monitor)",
                "messages": [{"from": protocol.roles[t.src], "to": protocol.roles[t.dst],
                              "label": t.label, "type": ty_str(t.ty)}
                             for st in protocol.states for t in st],
                "properties": [n for n, _ in protocol.properties]}


# =============================================================================================
# aiohttp server (optional; `pip install swarmgate[gateway]`)
# =============================================================================================

def aiohttp_app(gw: Gateway, protocols: dict[str, Protocol] | None = None):
    from aiohttp import ClientSession, web

    async def forward(url: str, envelope: dict):
        try:
            async with ClientSession() as cs:
                await cs.post(url, json=envelope, timeout=10)
        except Exception:
            pass

    # use a real async forwarder
    import asyncio

    def sync_forward(url, env):
        asyncio.ensure_future(forward(url, env))

    gw.forward = sync_forward
    protocols = protocols or {}

    async def create(request):
        body = await request.json()
        name = body.get("protocol")
        P = protocols.get(name)
        if P is None and "protocol_json" in body:
            P = Protocol.from_json(body["protocol_json"])
        if P is None:
            return web.json_response({"error": "unknown protocol"}, status=400)
        return web.json_response(gw.create_session(P, body.get("endpoints"), body.get("issue_tokens", True)))

    async def send(request):
        sid = request.match_info["sid"]
        body = await request.json()
        token = body.get("token") or (request.headers.get("Authorization", "").removeprefix("Bearer ").strip()
                                      or None)
        r = gw.send(sid, body["sender"], body["to"], body["label"], body.get("payload"), token)
        return web.json_response(r, status=r.pop("status", 200))

    async def nxt(request):
        r = gw.next_moves(request.match_info["sid"], request.query.get("role", ""))
        return web.json_response(r, status=r.pop("status", 200))

    async def logh(request):
        r = gw.log(request.match_info["sid"])
        return web.json_response(r, status=r.pop("status", 200))

    async def card(request):
        name = request.query.get("protocol")
        P = protocols.get(name) if name else (next(iter(protocols.values()), None))
        if P is None:
            return web.json_response({"protocols": list(protocols)})
        return web.json_response(gw.card(P))

    app = web.Application()
    app.add_routes([
        web.post("/sessions", create),
        web.post("/sessions/{sid}/send", send),
        web.get("/sessions/{sid}/next", nxt),
        web.get("/sessions/{sid}/log", logh),
        web.get("/.well-known/agent-protocol", card),
    ])
    return app
