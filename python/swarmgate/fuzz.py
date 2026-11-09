"""Random protocols, honest traces and adversarial attempts (used by tests and the evaluation)."""
from __future__ import annotations

import random
from typing import Any

from .protocol import INT64_MAX, INT64_MIN, Event, Protocol, Trans, has_ty, pred_eval

LABELS = ["Task", "Plan", "Run", "Out", "Ok", "No", "Data", "Ask"]
STRS = ["", "ls", "cat", "a;b", "rm -rf /", "héllo", "x" * 40, "approve", ";"]


def rand_ty(rng: random.Random, depth: int = 0) -> Any:
    k = rng.randrange(8 if depth < 2 else 5)
    if k == 0:
        return "unit"
    if k == 1:
        return "bool"
    if k == 2:
        return "int"
    if k == 3:
        return "str"
    if k == 4:
        return {"enum": rng.sample(["ls", "cat", "grep", "a", "b"], rng.randrange(1, 4))}
    if k == 5:
        return {"list": rand_ty(rng, depth + 1)}
    names = rng.sample(["cmd", "arg", "n", "ok"], rng.randrange(1, 4))
    return {"record": [[n, rand_ty(rng, depth + 1)] for n in names]}


def rand_pred(rng: random.Random, ty: Any, depth: int = 0) -> Any:
    if rng.random() < 0.5:
        return True
    paths = _paths(ty)
    if not paths:
        return True
    path, t = rng.choice(paths)
    k = rng.randrange(6)
    if depth < 2 and k == 0:
        return {rng.choice(["and", "or"]): [rand_pred(rng, ty, depth + 1), rand_pred(rng, ty, depth + 1)]}
    if depth < 2 and k == 1:
        return {"not": rand_pred(rng, ty, depth + 1)}
    if t == "int":
        return {rng.choice(["intLe", "intGe"]): [path, rng.randint(-5, 5)]}
    if t == "str" or (isinstance(t, dict) and "enum" in t):
        c = rng.randrange(4)
        if c == 0:
            return {"lenLe": [path, rng.randint(0, 8)]}
        if c == 1:
            return {"strIn": [path, rng.sample(["ls", "cat", "", "a;b"], 2)]}
        if c == 2:
            return {"strNotContains": [path, rng.choice([";", "rm", "", "a"])]}
        return {"eqStr": [path, rng.choice(STRS)]}
    if t == "bool":
        return {"eqBool": [path, rng.random() < 0.5]}
    if isinstance(t, dict) and "list" in t:
        return {"lenLe": [path, rng.randint(0, 3)]}
    return True


def _paths(ty: Any, prefix: list[str] | None = None) -> list[tuple[list[str], Any]]:
    prefix = prefix or []
    out = [(prefix, ty)]
    if isinstance(ty, dict) and "record" in ty:
        for n, t in ty["record"]:
            out += _paths(t, prefix + [n])
    return out


def rand_value(rng: random.Random, ty: Any | None = None, depth: int = 0) -> Any:
    """A value that *usually* has type ``ty`` (sometimes deliberately not)."""
    if ty is None or rng.random() < 0.1:
        k = rng.randrange(9 if depth < 2 else 7)
        choices = [lambda: None, lambda: True, lambda: False, lambda: rng.randint(-3, 3),
                   lambda: rng.choice(STRS), lambda: 2**63, lambda: -(2**63) - 1,
                   lambda: [rand_value(rng, None, depth + 1)], lambda: {"cmd": rand_value(rng, None, depth + 1)}]
        return choices[k]()
    if ty == "unit":
        return None
    if ty == "bool":
        return rng.random() < 0.5
    if ty == "int":
        return rng.choice([rng.randint(-6, 6), INT64_MAX, INT64_MIN])
    if ty == "str":
        return rng.choice(STRS)
    if "enum" in ty:
        return rng.choice(ty["enum"] + ["zzz"])
    if "list" in ty:
        return [rand_value(rng, ty["list"], depth + 1) for _ in range(rng.randrange(3))]
    if "record" in ty:
        d = {n: rand_value(rng, t, depth + 1) for n, t in ty["record"]}
        if rng.random() < 0.1:
            d["extra"] = "smuggled"
        if rng.random() < 0.1 and d:
            d.pop(next(iter(d)))
        return d
    return None


def rand_protocol(rng: random.Random, n_states: int | None = None, n_roles: int | None = None) -> Protocol:
    n = n_states or rng.randint(2, 8)
    k = n_roles or rng.randint(2, 4)
    roles = [f"R{i}" for i in range(k)]
    states: list[list[Trans]] = []
    for s in range(n):
        row: list[Trans] = []
        used = set()
        for _ in range(rng.randrange(0 if s > 0 else 1, 4)):
            a, b = rng.sample(range(k), 2)
            lab = rng.choice(LABELS)
            if (a, b, lab) in used:
                continue
            used.add((a, b, lab))
            ty = rand_ty(rng)
            row.append(Trans(a, b, lab, ty, rand_pred(rng, ty), rng.randrange(n)))
        states.append(row)
    final = [s for s in range(n) if not states[s] or rng.random() < 0.2]
    untrusted = [rng.randrange(k)]
    ifc = {"untrusted": untrusted, "maxBits": rng.choice([0, 1, 8, 64]),
           "sensitive": [{"src": None, "dst": rng.randrange(k), "label": None}],
           "endorsers": [r for r in range(k) if rng.random() < 0.2]}
    return Protocol("random", roles, states, 0, final, budget=rng.randint(3, 30),
                    max_strikes=rng.choice([0, 1, 3]), ifc=ifc)


def witness(rng: random.Random, t: Trans, tries: int = 40) -> Any | None:
    for _ in range(tries):
        v = rand_value(rng, t.ty)
        if has_ty(t.ty, v) and pred_eval(t.pred, v):
            return v
    return None


def honest_walk(rng: random.Random, P: Protocol, max_len: int = 30) -> list[Event]:
    s, out = P.start, []
    for _ in range(max_len):
        opts = P.out(s)
        if not opts:
            break
        t = rng.choice(opts)
        v = witness(rng, t)
        if v is None:
            break
        e = Event(t.src, t.dst, t.label, v)
        nxt = P.step(s, e)
        if nxt is None:
            break
        out.append(e)
        s = nxt
    return out


def adversarial_attempt(rng: random.Random, P: Protocol, s: int) -> tuple[int, Event]:
    """Mix of honest moves, near-misses and noise."""
    opts = P.out(s)
    k = len(P.roles)
    all_t = [t for st in P.states for t in st]
    mode = rng.randrange(6)
    if opts and mode <= 1:
        t = rng.choice(opts)
        v = witness(rng, t)
        e = Event(t.src, t.dst, t.label, v if v is not None else rand_value(rng, t.ty))
        return (t.src if mode == 0 else rng.randrange(k + 1)), e
    if all_t and mode <= 3:
        t = rng.choice(all_t)
        e = Event(t.src, t.dst, t.label, rand_value(rng, t.ty))
        return t.src, e
    a, b = rng.randrange(k), rng.randrange(k)
    e = Event(a, b, rng.choice(LABELS), rand_value(rng))
    return (a if rng.random() < 0.8 else rng.randrange(k + 2)), e
