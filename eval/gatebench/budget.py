"""Shared, process-safe API budget ledger and a budget-enforcing Anthropic client wrapper.

Every LLM call in the evaluation goes through ``BudgetedAnthropic``. Costs are computed from the returned
usage (including prompt-cache tokens) and appended to a JSON-lines ledger under a file lock. Before each
call the running total is checked against the hard cap; when it is reached, ``BudgetExceeded`` is raised.

Environment:
  SG_LEDGER      path of the ledger (default: eval/results/api_ledger.jsonl)
  SG_BUDGET_USD  hard cap in USD (default 55)
  ANTHROPIC_API_KEY  or  SG_KEY_FILE (a file containing the key; never commit it)
"""
from __future__ import annotations

import fcntl
import json
import os
import time
from typing import Any

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEDGER = os.environ.get("SG_LEDGER", os.path.join(ROOT, "eval", "results", "api_ledger.jsonl"))
CAP = float(os.environ.get("SG_BUDGET_USD", "55"))

# USD per million tokens (input, output). Cache reads 0.1x input, cache writes 1.25x input (conservative).
PRICES = {
    "claude-haiku-5-5": (0.10, 0.50),
    "claude-haiku-4-5": (1.00, 5.00),
    "claude-sonnet-5-5": (2.00, 10.00),
    "claude-opus-5-5": (4.00, 20.00),
}


class BudgetExceeded(RuntimeError):
    pass


def _cost(model: str, u: Any) -> float:
    pi, po = PRICES.get(model, (4.0, 20.0))
    g = (lambda k: (getattr(u, k, None) if not isinstance(u, dict) else u.get(k)) or 0)
    inp, out = g("input_tokens"), g("output_tokens")
    cw, cr = g("cache_creation_input_tokens"), g("cache_read_input_tokens")
    return (inp * pi + cw * pi * 1.25 + cr * pi * 0.1 + out * po) / 1e6


def spent(ledger: str = LEDGER) -> float:
    if not os.path.exists(ledger):
        return 0.0
    tot = 0.0
    with open(ledger) as f:
        for line in f:
            try:
                tot += json.loads(line)["usd"]
            except Exception:
                pass
    return tot


def spent_by(tag_prefix: str = "", ledger: str = LEDGER) -> float:
    if not os.path.exists(ledger):
        return 0.0
    tot = 0.0
    with open(ledger) as f:
        for line in f:
            try:
                d = json.loads(line)
                if d.get("tag", "").startswith(tag_prefix):
                    tot += d["usd"]
            except Exception:
                pass
    return tot


def _record(model: str, usage: Any, tag: str) -> float:
    usd = _cost(model, usage)
    os.makedirs(os.path.dirname(LEDGER), exist_ok=True)
    g = (lambda k: getattr(usage, k, 0) or 0)
    with open(LEDGER, "a") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        f.write(json.dumps({"t": time.time(), "model": model, "tag": tag, "usd": usd,
                            "in": g("input_tokens"), "out": g("output_tokens"),
                            "cr": g("cache_read_input_tokens"), "cw": g("cache_creation_input_tokens")}) + "\n")
        fcntl.flock(f, fcntl.LOCK_UN)
    return usd


def _key() -> str | None:
    if os.environ.get("ANTHROPIC_API_KEY"):
        return os.environ["ANTHROPIC_API_KEY"]
    kf = os.environ.get("SG_KEY_FILE")
    if kf and os.path.exists(kf):
        return open(kf).read().strip()
    return None


class _Messages:
    def __init__(self, outer: "BudgetedAnthropic"):
        self.outer = outer

    def create(self, **kw):
        o = self.outer
        if spent() >= o.cap:
            raise BudgetExceeded(f"API budget cap ${o.cap:.2f} reached")
        last_err = None
        for attempt in range(5):
            try:
                resp = o.client.messages.create(**kw)
                break
            except Exception as e:  # retry transient errors (rate limit, overload, 5xx)
                last_err = e
                name = type(e).__name__
                if name in ("RateLimitError", "InternalServerError", "APIConnectionError", "APITimeoutError",
                            "OverloadedError", "ServiceUnavailableError") or "529" in str(e):
                    time.sleep(2 * (2 ** attempt))
                    continue
                raise
        else:
            raise last_err  # type: ignore[misc]
        o.last_cost = _record(kw.get("model", "?"), getattr(resp, "usage", None), o.tag)
        o.total += o.last_cost
        return resp


class BudgetedAnthropic:
    """Drop-in for ``anthropic.Anthropic()`` exposing ``.messages.create``."""

    def __init__(self, tag: str = "", cap: float | None = None):
        import anthropic
        key = _key()
        if not key:
            raise RuntimeError("no API key: set ANTHROPIC_API_KEY or SG_KEY_FILE")
        self.client = anthropic.Anthropic(api_key=key, max_retries=2)
        self.cap = CAP if cap is None else cap
        self.tag = tag
        self.total = 0.0
        self.last_cost = 0.0
        self.messages = _Messages(self)


if __name__ == "__main__":
    print(f"spent so far: ${spent():.4f} of cap ${CAP:.2f}")
