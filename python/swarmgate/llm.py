"""LLM agents (Anthropic Messages API) that communicate only through the gate.

Two interface styles, so that *guidance* and *enforcement* can be measured separately:

* ``guided=True``  — one typed tool per message this role can ever send (derived from the protocol), and
  every tool result tells the model which moves are legal *now*. ("protocol-guided decoding")
* ``guided=False`` — a single free-form ``send_message(to, label, payload)`` tool, as in an ordinary
  message-bus framework.

In both cases every tool call is an *attempt* that the gate delivers or rejects; the model's tool schema
is a convenience, never a security boundary. The conversation is append-only (thinking blocks are passed
back unchanged) and the tool list is constant for the whole run.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from typing import Any

from .protocol import Protocol, Trans, ty_str
from .runtime import Agent, Context

DEFAULT_MODEL = "claude-haiku-5-5"
PRICES = {  # USD per million tokens (input, output) — see the claude-api skill model table
    "claude-haiku-5-5": (0.10, 0.50),
    "claude-sonnet-5-5": (2.00, 10.00),
    "claude-opus-5-5": (4.00, 20.00),
}


def json_schema(ty: Any) -> dict:
    if ty == "unit":
        return {"type": "null"}
    if ty == "bool":
        return {"type": "boolean"}
    if ty == "int":
        return {"type": "integer"}
    if ty == "str":
        return {"type": "string"}
    if "enum" in ty:
        return {"type": "string", "enum": list(ty["enum"])}
    if "list" in ty:
        return {"type": "array", "items": json_schema(ty["list"])}
    if "record" in ty:
        return {"type": "object", "properties": {n: json_schema(t) for n, t in ty["record"]},
                "required": [n for n, _ in ty["record"]], "additionalProperties": False}
    return {}


def _tool_name(label: str, dst: str) -> str:
    return re.sub(r"[^A-Za-z0-9_-]", "_", f"send_{label}_to_{dst}")[:64]


@dataclass
class Usage:
    input_tokens: int = 0
    output_tokens: int = 0
    calls: int = 0

    def cost(self, model: str) -> float:
        pi, po = PRICES.get(model, (0.0, 0.0))
        return (self.input_tokens * pi + self.output_tokens * po) / 1e6


@dataclass
class LLMAgent(Agent):
    role: str
    persona: str
    protocol: Protocol
    guided: bool = True
    model: str = DEFAULT_MODEL
    client: Any = None
    max_tool_calls: int = 6
    effort: str | None = "low"
    hint_on_reject: bool = False        # unguided agents behind a session gate: the gate's rejection lists legal moves
    usage: Usage = field(default_factory=Usage)
    messages: list = field(default_factory=list)
    transcript: list = field(default_factory=list)

    def __post_init__(self):
        if self.client is None:
            import anthropic
            self.client = anthropic.Anthropic()
        self._tools, self._tool_map = self._build_tools()

    # -- tools ------------------------------------------------------------------------------------
    def _moves(self) -> list[Trans]:
        r = self.protocol.role(self.role)
        seen, out = set(), []
        for st in self.protocol.states:
            for t in st:
                k = (t.dst, t.label, json.dumps(t.ty, sort_keys=True), json.dumps(t.pred, sort_keys=True))
                if t.src == r and k not in seen:
                    seen.add(k)
                    out.append(t)
        return out

    def _build_tools(self):
        P = self.protocol
        if not self.guided:
            tool = {"name": "send_message",
                    "description": "Send a message to another agent. `to` is the recipient's role name, `label` "
                                   "the message kind, `payload` any JSON value.",
                    "input_schema": {"type": "object", "properties": {
                        "to": {"type": "string"}, "label": {"type": "string"}, "payload": {}},
                        "required": ["to", "label"]}}
            return [tool], {"send_message": None}
        tools, tmap = [], {}
        for t in self._moves():
            dst = P.roles[t.dst]
            name = _tool_name(t.label, dst)
            if name in tmap:            # same label/recipient with another type: disambiguate
                name = _tool_name(f"{t.label}_v{sum(1 for n in tmap if n.startswith(name)) + 1}", dst)
            if t.ty == "unit":
                schema = {"type": "object", "properties": {}, "additionalProperties": False}
                wrap = "unit"
            elif isinstance(t.ty, dict) and "record" in t.ty:
                schema = json_schema(t.ty)
                wrap = "record"
            else:
                schema = {"type": "object", "properties": {"value": json_schema(t.ty)}, "required": ["value"],
                          "additionalProperties": False}
                wrap = "value"
            tools.append({"name": name, "description": f"Send message `{t.label}` to {dst} "
                                                       f"(payload type {ty_str(t.ty)}).", "input_schema": schema})
            tmap[name] = (dst, t.label, wrap)
        return tools, tmap

    def _decode(self, name: str, inp: Any) -> tuple[str, str, Any]:
        if not self.guided:
            inp = inp or {}
            return str(inp.get("to", "")), str(inp.get("label", "")), inp.get("payload")
        dst, label, wrap = self._tool_map[name]
        if wrap == "unit":
            return dst, label, None
        if wrap == "value":
            return dst, label, (inp or {}).get("value")
        return dst, label, inp

    # -- prompting ----------------------------------------------------------------------------------
    def _system(self) -> str:
        P = self.protocol
        others = ", ".join(r for r in P.roles if r != self.role)
        how = ("You act only by calling the tools; each call sends one message. "
               "When you have nothing (more) to send, reply with a short text and no tool call.")
        if self.guided:
            how += (" After each send you are told whether it was delivered and which messages are allowed "
                    "next; the communication protocol is enforced, so other messages are rejected.")
        return (f"You are the agent playing the role `{self.role}` in a multi-agent system.\n"
                f"Other roles: {others}.\n{self.persona}\n\n{how}")

    def _activation_text(self, ctx: Context) -> str:
        m = ctx.trigger
        head = ("You have been activated." if m is None else
                f"New message from {m.src}: `{m.label}` with payload:\n{json.dumps(m.payload, ensure_ascii=False)}")
        if self.guided:
            head += f"\n\nMessages you may send now:\n{ctx.describe_allowed()}"
        return head

    # -- the agent loop -------------------------------------------------------------------------------
    def act(self, ctx: Context) -> None:
        content: Any = self._activation_text(ctx)
        last = self.messages[-1] if self.messages else None
        if last and last["role"] == "assistant":   # close tool calls left open by a truncated turn
            dangling = [b for b in last["content"] if getattr(b, "type", None) == "tool_use"]
            if dangling:
                content = [{"type": "tool_result", "tool_use_id": b.id, "is_error": True,
                            "content": "Not executed (turn ended)."} for b in dangling] + \
                          [{"type": "text", "text": content}]
        self.messages.append({"role": "user", "content": content})
        calls = 0
        while True:
            kw: dict[str, Any] = dict(model=self.model, max_tokens=4000, system=self._system(),
                                      tools=self._tools, messages=self.messages)
            if self.effort:
                kw["output_config"] = {"effort": self.effort}
            resp = self.client.messages.create(**kw)
            self.usage.calls += 1
            u = getattr(resp, "usage", None)
            if u is not None:
                self.usage.input_tokens += getattr(u, "input_tokens", 0) or 0
                self.usage.output_tokens += getattr(u, "output_tokens", 0) or 0
            self.messages.append({"role": "assistant", "content": resp.content})
            uses = [b for b in resp.content if getattr(b, "type", None) == "tool_use"]
            self.transcript.append({"text": " ".join(getattr(b, "text", "") for b in resp.content
                                                     if getattr(b, "type", None) == "text"),
                                    "tools": [(b.name, b.input) for b in uses]})
            if resp.stop_reason != "tool_use" or not uses:
                return
            results = []
            for b in uses:
                calls += 1
                if calls > self.max_tool_calls:
                    results.append({"type": "tool_result", "tool_use_id": b.id, "is_error": True,
                                    "content": "Too many messages in one turn; stop now."})
                    continue
                if self.guided and b.name not in self._tool_map:
                    results.append({"type": "tool_result", "tool_use_id": b.id, "is_error": True,
                                    "content": "Unknown tool."})
                    continue
                dst, label, payload = self._decode(b.name, b.input)
                r = ctx.send(dst, label, payload)
                if r.delivered:
                    txt = f"Delivered `{label}` to {dst}."
                else:
                    txt = f"REJECTED by the protocol gate ({r.reason}); the message was not delivered."
                if self.guided or (self.hint_on_reject and not r.delivered):
                    txt += f"\nMessages you may send now:\n{ctx.describe_allowed()}"
                results.append({"type": "tool_result", "tool_use_id": b.id, "content": txt,
                                **({} if r.delivered else {"is_error": True})})
            self.messages.append({"role": "user", "content": results})
            if calls > self.max_tool_calls:
                return


# =============================================================================================
# A deterministic stand-in for tests (no network)
# =============================================================================================

@dataclass
class _Block:
    type: str
    text: str = ""
    id: str = ""
    name: str = ""
    input: Any = None


@dataclass
class _Resp:
    content: list
    stop_reason: str
    usage: Any = None


class ScriptedClient:
    """Fake ``anthropic`` client: ``policy(system, messages, tools) -> list[(tool_name, input)]``."""

    def __init__(self, policy):
        self.policy = policy
        self.messages = self
        self.n = 0

    def create(self, **kw):
        calls = self.policy(kw["system"], kw["messages"], kw["tools"])
        if not calls:
            return _Resp([_Block("text", text="done")], "end_turn")
        blocks = []
        for name, inp in calls:
            self.n += 1
            blocks.append(_Block("tool_use", id=f"t{self.n}", name=name, input=inp))
        return _Resp(blocks, "tool_use")
