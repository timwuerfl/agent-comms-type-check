"""The SwarmGate protocol language (``.sg`` files) and its compiler to guarded automata.

Example::

    protocol Approval {
      roles User, Planner, Human, Executor, Shell;
      sensitive Executor -> Shell;
      User -> Planner : Task(str) where len <= 2000;
      Planner -> Human : Propose({cmd: enum{ls, cat}, arg: str});
      choice at Human {
        Human -> Planner : Approve;
        Planner -> Executor : Run({cmd: enum{ls, cat}, arg: str});
        Executor -> Shell : Exec({cmd: enum{ls, cat}, arg: str});
        Shell -> Executor : Out(str);
        Executor -> User : Result(str);
      } or {
        Human -> Planner : Deny;
        Planner -> User : Refused;
      }
      property ApprovedExec: Executor -> Shell : Exec implies once Human -> Planner : Approve;
    }

The meaning of a protocol is the automaton produced here; the DSL is only notation. The compiler is
*not* trusted: everything that matters is checked on the automaton by the verified Lean checker.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from typing import Any

from .protocol import Protocol, Trans

# =============================================================================================
# Lexer
# =============================================================================================

_TOKEN = re.compile(r"""
    (?P<ws>\s+|//[^\n]*|\#[^\n]*|/\*.*?\*/)
  | (?P<str>"(?:[^"\\]|\\.)*")
  | (?P<num>-?\d+)
  | (?P<id>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<sym>->|<=|>=|==|!=|!contains|[{}()\[\]<>;:,.*=|_])
""", re.VERBOSE | re.DOTALL)


@dataclass
class Tok:
    kind: str
    val: str
    line: int


class DSLError(Exception):
    pass


def lex(src: str) -> list[Tok]:
    toks: list[Tok] = []
    pos, line = 0, 1
    while pos < len(src):
        m = _TOKEN.match(src, pos)
        if not m:
            raise DSLError(f"line {line}: unexpected character {src[pos]!r}")
        kind = m.lastgroup
        text = m.group()
        if kind != "ws":
            toks.append(Tok(kind, text, line))
        line += text.count("\n")
        pos = m.end()
    toks.append(Tok("eof", "", line))
    return toks


# =============================================================================================
# AST
# =============================================================================================

@dataclass
class Msg:
    src: str
    dst: str
    label: str
    ty: Any
    pred: Any
    line: int


@dataclass
class Choice:
    at: str
    branches: list[list]
    line: int


@dataclass
class Rec:
    var: str
    bound: int | None
    body: list
    line: int


@dataclass
class Continue:
    var: str
    line: int


@dataclass
class Par:
    branches: list[list]
    line: int


@dataclass
class End:
    line: int


@dataclass
class ProtocolAST:
    name: str
    roles: list[str] = field(default_factory=list)
    untrusted: list[str] = field(default_factory=list)
    endorsers: list[str] = field(default_factory=list)
    sensitive: list[tuple] = field(default_factory=list)
    lowcap: int = 8
    budget: int = 1000
    strikes: int = 3
    types: dict[str, Any] = field(default_factory=dict)
    properties: list[tuple[str, Any]] = field(default_factory=list)
    body: list = field(default_factory=list)


# =============================================================================================
# Parser
# =============================================================================================

KEYWORDS = {"protocol", "roles", "untrusted", "endorser", "sensitive", "lowcap", "budget", "strikes", "type",
            "property", "choice", "at", "or", "rec", "max", "continue", "par", "and", "end", "where", "call",
            "returns"}


class Parser:
    def __init__(self, toks: list[Tok]):
        self.toks = toks
        self.i = 0

    # -- helpers --------------------------------------------------------------------------------
    @property
    def cur(self) -> Tok:
        return self.toks[self.i]

    def peek(self, k: int = 1) -> Tok:
        return self.toks[min(self.i + k, len(self.toks) - 1)]

    def err(self, msg: str) -> DSLError:
        return DSLError(f"line {self.cur.line}: {msg} (at {self.cur.val!r})")

    def eat(self, val: str | None = None, kind: str | None = None) -> Tok:
        t = self.cur
        if val is not None and t.val != val:
            raise self.err(f"expected {val!r}")
        if kind is not None and t.kind != kind:
            raise self.err(f"expected {kind}")
        self.i += 1
        return t

    def at(self, val: str) -> bool:
        return self.cur.val == val and self.cur.kind in ("id", "sym")

    def ident(self) -> str:
        return self.eat(kind="id").val

    def ident_list(self) -> list[str]:
        out = [self.ident()]
        while self.at(","):
            self.eat(",")
            out.append(self.ident())
        return out

    # -- top level ------------------------------------------------------------------------------
    def file(self) -> list[ProtocolAST]:
        out = []
        while self.cur.kind != "eof":
            out.append(self.protocol())
        return out

    def protocol(self) -> ProtocolAST:
        self.eat("protocol")
        p = ProtocolAST(self.ident())
        self.eat("{")
        while not self.at("}"):
            if self.at("roles"):
                self.eat(); p.roles += self.ident_list(); self.eat(";")
            elif self.at("untrusted"):
                self.eat(); p.untrusted += self.ident_list(); self.eat(";")
            elif self.at("endorser"):
                self.eat(); p.endorsers += self.ident_list(); self.eat(";")
            elif self.at("sensitive"):
                self.eat()
                p.sensitive.append(self.evpat())
                while self.at(","):
                    self.eat(","); p.sensitive.append(self.evpat())
                self.eat(";")
            elif self.at("lowcap"):
                self.eat(); p.lowcap = int(self.eat(kind="num").val); self.eat(";")
            elif self.at("budget"):
                self.eat(); p.budget = int(self.eat(kind="num").val); self.eat(";")
            elif self.at("strikes"):
                self.eat(); p.strikes = int(self.eat(kind="num").val); self.eat(";")
            elif self.at("type"):
                self.eat(); n = self.ident(); self.eat("="); p.types[n] = self.ty(p.types); self.eat(";")
            elif self.at("property"):
                self.eat(); n = self.ident(); self.eat(":"); f = self.formula(); self.eat(";")
                p.properties.append((n, f))
            else:
                st = self.stmt(p.types)
                p.body.extend(st if isinstance(st, list) else [st])
        self.eat("}")
        return p

    # -- statements -----------------------------------------------------------------------------
    def block(self, types) -> list:
        self.eat("{")
        out = []
        while not self.at("}"):
            st = self.stmt(types)
            out.extend(st if isinstance(st, list) else [st])
        self.eat("}")
        return out

    def stmt(self, types):
        line = self.cur.line
        if self.at("choice"):
            self.eat(); self.eat("at"); who = self.ident()
            branches = [self.block(types)]
            while self.at("or"):
                self.eat(); branches.append(self.block(types))
            return Choice(who, branches, line)
        if self.at("rec"):
            self.eat(); var = self.ident(); bound = None
            if self.at("max"):
                self.eat(); bound = int(self.eat(kind="num").val)
                if bound < 1:
                    raise self.err("loop bound must be ≥ 1")
            return Rec(var, bound, self.block(types), line)
        if self.at("continue"):
            self.eat(); v = self.ident(); self.eat(";")
            return Continue(v, line)
        if self.at("par"):
            self.eat(); branches = [self.block(types)]
            while self.at("and"):
                self.eat(); branches.append(self.block(types))
            return Par(branches, line)
        if self.at("end"):
            self.eat(); self.eat(";")
            return End(line)
        if self.at("call"):
            # call A -> T : tool(Args) returns R [where pred];   ≡   A -> T : tool(Args); T -> A : tool_result(R);
            self.eat(); src = self.ident(); self.eat("->"); dst = self.ident(); self.eat(":")
            label = self.ident(); ty: Any = "unit"
            if self.at("("):
                self.eat("("); ty = self.ty(types); self.eat(")")
            rty: Any = "unit"
            pred: Any = True
            for _ in range(2):
                if self.at("returns"):
                    self.eat(); rty = self.ty(types)
                elif self.at("where"):
                    self.eat(); pred = self.pred()
            self.eat(";")
            return [Msg(src, dst, label, ty, pred, line), Msg(dst, src, label + "_result", rty, True, line)]
        src = self.ident(); self.eat("->"); dst = self.ident(); self.eat(":"); label = self.ident()
        ty: Any = "unit"
        if self.at("("):
            self.eat("("); ty = self.ty(types); self.eat(")")
        pred: Any = True
        if self.at("where"):
            self.eat(); pred = self.pred()
        self.eat(";")
        return Msg(src, dst, label, ty, pred, line)

    # -- types ----------------------------------------------------------------------------------
    def ty(self, types) -> Any:
        t = self.cur
        if t.val in ("unit", "bool", "int", "str"):
            self.eat(); return t.val
        if t.val == "string":
            self.eat(); return "str"
        if t.val == "enum":
            self.eat(); self.eat("{")
            cases = [self.enum_case()]
            while self.at(","):
                self.eat(","); cases.append(self.enum_case())
            self.eat("}")
            return {"enum": cases}
        if t.val == "list":
            self.eat(); self.eat("<"); inner = self.ty(types); self.eat(">")
            return {"list": inner}
        if t.val == "record":
            self.eat()
        if self.at("{"):
            self.eat("{"); fields = []
            if not self.at("}"):
                fields.append(self.field(types))
                while self.at(","):
                    self.eat(","); fields.append(self.field(types))
            self.eat("}")
            names = [n for n, _ in fields]
            if len(set(names)) != len(names):
                raise self.err("duplicate record field")
            return {"record": fields}
        if t.kind == "id" and t.val in types:
            self.eat(); return types[t.val]
        raise self.err("expected a type")

    def enum_case(self) -> str:
        if self.cur.kind == "str":
            return json.loads(self.eat().val)
        return self.ident()

    def field(self, types):
        n = self.ident(); self.eat(":")
        return [n, self.ty(types)]

    # -- refinements ----------------------------------------------------------------------------
    def pred(self):
        p = self.pred_and()
        while self.at("or"):
            self.eat(); p = {"or": [p, self.pred_and()]}
        return p

    def pred_and(self):
        p = self.pred_not()
        while self.at("and"):
            self.eat(); p = {"and": [p, self.pred_not()]}
        return p

    def pred_not(self):
        if self.at("not"):
            self.eat(); return {"not": self.pred_not()}
        return self.pred_atom()

    def literal(self):
        t = self.cur
        if t.kind == "str":
            self.eat(); return json.loads(t.val)
        if t.kind == "num":
            self.eat(); return int(t.val)
        if t.val in ("true", "false"):
            self.eat(); return t.val == "true"
        if t.kind == "id":
            self.eat(); return t.val
        raise self.err("expected a literal")

    def pred_atom(self):
        if self.at("("):
            self.eat("("); p = self.pred(); self.eat(")"); return p
        if self.at("true"):
            self.eat(); return True
        if self.at("false"):
            self.eat(); return False
        # path
        path = [self.ident()]
        while self.at("."):
            self.eat("."); path.append(self.ident())
        is_len = path[-1] == "len"
        if is_len:
            path = path[:-1]
        if path == ["value"]:
            path = []
        op = self.cur.val
        if is_len:
            if op not in ("<=", "<", "=="):
                raise self.err("length supports <=, <, ==")
            self.eat(); k = int(self.eat(kind="num").val)
            if op == "<":
                k -= 1
            if op == "==":
                return {"and": [{"lenLe": [path, k]}, {"not": {"lenLe": [path, k - 1]}}]}
            return {"lenLe": [path, k]}
        if op in ("<=", ">=", "<", ">"):
            self.eat(); k = int(self.eat(kind="num").val)
            return {"<=": {"intLe": [path, k]}, ">=": {"intGe": [path, k]},
                    "<": {"intLe": [path, k - 1]}, ">": {"intGe": [path, k + 1]}}[op]
        if op in ("==", "!="):
            self.eat(); v = self.literal()
            if isinstance(v, bool):
                p = {"eqBool": [path, v]}
            elif isinstance(v, int):
                p = {"and": [{"intLe": [path, v]}, {"intGe": [path, v]}]}
            else:
                p = {"eqStr": [path, v]}
            return p if op == "==" else {"not": p}
        if op == "in":
            self.eat(); self.eat("{"); cs = [str(self.literal())]
            while self.at(","):
                self.eat(","); cs.append(str(self.literal()))
            self.eat("}")
            return {"strIn": [path, cs]}
        if op == "contains":
            self.eat(); s = json.loads(self.eat(kind="str").val)
            return {"not": {"strNotContains": [path, s]}}
        if op == "!contains":
            self.eat(); s = json.loads(self.eat(kind="str").val)
            return {"strNotContains": [path, s]}
        raise self.err("expected a comparison")

    # -- temporal formulas -----------------------------------------------------------------------
    def formula(self):
        f = self.f_or()
        if self.at("implies"):
            self.eat(); return {"imp": [f, self.formula()]}
        return f

    def f_or(self):
        f = self.f_and()
        while self.at("or"):
            self.eat(); f = {"or": [f, self.f_and()]}
        return f

    def f_and(self):
        f = self.f_since()
        while self.at("and"):
            self.eat(); f = {"and": [f, self.f_since()]}
        return f

    def f_since(self):
        f = self.f_un()
        while self.at("since"):
            self.eat(); f = {"since": [f, self.f_un()]}
        return f

    def f_un(self):
        for kw, key in (("not", "not"), ("once", "once"), ("prev", "prev"),
                        ("historically", "hist"), ("always", "hist")):
            if self.at(kw):
                self.eat(); return {key: self.f_un()}
        if self.at("("):
            self.eat("("); f = self.formula(); self.eat(")"); return f
        if self.at("true"):
            self.eat(); return True
        if self.at("false"):
            self.eat(); return False
        return {"atom": self.evpat()}

    def evpat(self) -> dict:
        def role_or_star():
            if self.at("*") or self.at("_"):
                self.eat(); return None
            return self.ident()
        src = role_or_star(); self.eat("->"); dst = role_or_star(); label = None
        if self.at(":"):
            self.eat(":")
            if self.at("*") or self.at("_"):
                self.eat()
            else:
                label = self.ident()
        return {"src": src, "dst": dst, "label": label}


# =============================================================================================
# Compiler: AST → guarded automaton
# =============================================================================================

class _Builder:
    def __init__(self):
        self.trans: list[list[tuple]] = []   # (src, dst, label, ty, pred, next)
        self.eps: list[list[int]] = []
        self.final: list[bool] = []

    def new(self, final: bool = False) -> int:
        self.trans.append([]); self.eps.append([]); self.final.append(final)
        return len(self.trans) - 1

    def closure(self, s: int) -> list[int]:
        seen, stack, out = {s}, [s], []
        while stack:
            x = stack.pop(); out.append(x)
            for y in self.eps[x]:
                if y not in seen:
                    seen.add(y); stack.append(y)
        return out

    def ctrans(self, s: int) -> list[tuple]:
        res = []
        for x in self.closure(s):
            for t in self.trans[x]:
                if t not in res:
                    res.append(t)
        return res

    def cfinal(self, s: int, target: int) -> bool:
        return target in self.closure(s)


def _key(x):
    return json.dumps(x, sort_keys=True)


class Compiler:
    def __init__(self, ast: ProtocolAST):
        self.ast = ast
        self.b = _Builder()
        self.END = self.b.new(final=True)
        self.DEAD = self.b.new()
        roles = set(ast.roles)
        self.roles = list(ast.roles)
        self._check_roles(ast.body, roles)

    def _check_roles(self, body, roles):
        for s in body:
            if isinstance(s, Msg):
                for r in (s.src, s.dst):
                    if r not in roles:
                        raise DSLError(f"line {s.line}: undeclared role {r!r} (declare it with `roles`)")
                if s.src == s.dst:
                    raise DSLError(f"line {s.line}: a role cannot message itself")
            elif isinstance(s, (Choice, Par)):
                for br in s.branches:
                    self._check_roles(br, roles)
            elif isinstance(s, Rec):
                self._check_roles(s.body, roles)

    # -- compilation (continuation-passing, built backwards) ---------------------------------------
    def block(self, stmts: list, k: int, env: dict[str, int]) -> int:
        cur = k
        for st in reversed(stmts):
            cur = self.stmt(st, cur, env)
        return cur

    def stmt(self, st, k: int, env: dict[str, int]) -> int:
        b = self.b
        if isinstance(st, Msg):
            s = b.new()
            b.trans[s].append((self.roles.index(st.src), self.roles.index(st.dst), st.label,
                               st.ty, st.pred, k))
            return s
        if isinstance(st, End):
            return self.END
        if isinstance(st, Continue):
            if st.var not in env:
                raise DSLError(f"line {st.line}: `continue {st.var}` outside of `rec {st.var}`")
            return env[st.var]
        if isinstance(st, Choice):
            s = b.new()
            for br in st.branches:
                e = self.block(br, k, env)
                b.eps[s].append(e)
            return s
        if isinstance(st, Rec):
            if st.bound is None:
                r = b.new()
                body = self.block(st.body, k, {**env, st.var: r})
                if body == r:
                    raise DSLError(f"line {st.line}: empty loop body")
                b.eps[r].append(body)
                return r
            heads = [b.new() for _ in range(st.bound)]
            for i in reversed(range(st.bound)):
                nxt = heads[i + 1] if i + 1 < st.bound else self.DEAD
                body = self.block(st.body, k, {**env, st.var: nxt})
                b.eps[heads[i]].append(body)
            return heads[0]
        if isinstance(st, Par):
            return self.par(st, k, env)
        raise DSLError(f"unknown statement {st!r}")

    def par(self, st: Par, k: int, env: dict[str, int]) -> int:
        b = self.b
        ends, entries = [], []
        for br in st.branches:
            fin = b.new()
            ends.append(fin)
            # loops of the enclosing scope are not visible inside a parallel branch
            entries.append(self.block(br, fin, {}))
        ids: dict[tuple, int] = {}
        work: list[tuple] = []

        def get(tup: tuple) -> int:
            if tup not in ids:
                ids[tup] = b.new(); work.append(tup)
            return ids[tup]

        root = get(tuple(entries))
        while work:
            tup = work.pop()
            s = ids[tup]
            for i, q in enumerate(tup):
                for t in b.ctrans(q):
                    nt = list(tup); nt[i] = t[5]
                    b.trans[s].append(t[:5] + (get(tuple(nt)),))
            if all(b.cfinal(q, ends[i]) for i, q in enumerate(tup)):
                b.eps[s].append(k)
        return root

    # -- finalisation --------------------------------------------------------------------------------
    def compile(self) -> Protocol:
        ast = self.ast
        start = self.block(ast.body, self.END, {})
        b = self.b
        n = len(b.trans)
        trans = [b.ctrans(s) for s in range(n)]
        final = [self.END in b.closure(s) for s in range(n)]
        # prune transitions into dead states (exhausted bounded loops), to a fixpoint
        alive = [True] * n
        changed = True
        while changed:
            changed = False
            for s in range(n):
                if alive[s] and not final[s] and not any(alive[t[5]] for t in trans[s]):
                    alive[s] = False; changed = True
        trans = [[t for t in ts if alive[t[5]]] for ts in trans]
        if not alive[start]:
            raise DSLError("the protocol can never complete")
        # renumber reachable states (BFS from start)
        order, idx = [start], {start: 0}
        i = 0
        while i < len(order):
            for t in trans[order[i]]:
                if t[5] not in idx:
                    idx[t[5]] = len(order); order.append(t[5])
            i += 1
        states = []
        for s in order:
            seen, row = set(), []
            for t in trans[s]:
                tt = Trans(t[0], t[1], t[2], t[3], t[4], idx[t[5]])
                key = _key(tt.to_json())
                if key not in seen:
                    seen.add(key); row.append(tt)
            states.append(row)
        finals = [idx[s] for s in order if final[s]]
        ifc = None
        if ast.untrusted or ast.sensitive:
            ifc = {"untrusted": [self.roles.index(r) for r in ast.untrusted], "maxBits": ast.lowcap,
                   "sensitive": [self._pat(p) for p in ast.sensitive],
                   "endorsers": [self.roles.index(r) for r in ast.endorsers]}
        props = [(n, self._formula(f)) for n, f in ast.properties]
        return Protocol(name=ast.name, roles=self.roles, states=states, start=0, final=finals,
                        budget=ast.budget, max_strikes=ast.strikes, properties=props, ifc=ifc)

    def _role(self, r):
        if r is None:
            return None
        if r not in self.roles:
            raise DSLError(f"undeclared role {r!r} in property/policy")
        return self.roles.index(r)

    def _pat(self, p):
        return {"src": self._role(p["src"]), "dst": self._role(p["dst"]), "label": p["label"]}

    def _formula(self, f):
        if f is True or f is False:
            return f
        (k, a), = f.items()
        if k == "atom":
            return {"atom": self._pat(a)}
        if k in ("not", "prev", "once", "hist"):
            return {k: self._formula(a)}
        return {k: [self._formula(a[0]), self._formula(a[1])]}


# =============================================================================================
# Public API
# =============================================================================================

def parse(src: str) -> list[ProtocolAST]:
    return Parser(lex(src)).file()


def compile_source(src: str, name: str | None = None) -> Protocol:
    asts = parse(src)
    if not asts:
        raise DSLError("no protocol found")
    ast = asts[0] if name is None else next(a for a in asts if a.name == name)
    P = Compiler(ast).compile()
    P.source = src
    return P


def compile_file(path: str, name: str | None = None) -> Protocol:
    with open(path) as f:
        return compile_source(f.read(), name)
