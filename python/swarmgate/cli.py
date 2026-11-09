"""``swarmgate-py`` — compile, verify, project and prove protocols.

    swarmgate-py check protocols/ops_hardened.sg          # verified checks, human-readable
    swarmgate-py check --json protocols/ops_naive.sg      # full JSON report
    swarmgate-py compile protocols/x.sg -o x.json         # automaton JSON (input of `swarmgate serve`)
    swarmgate-py project protocols/x.sg                   # local protocols per role
    swarmgate-py emit-lean protocols/x.sg Name -o X.lean   # kernel-checked Lean theorems for this protocol
    swarmgate-py influence protocols/x.sg                 # attacker-controlled bits per role
"""
from __future__ import annotations

import argparse
import json
import sys

from .check import emit_lean, influence_bits, summarize, verify
from .dsl import compile_file
from .project import local_str, project_all, with_locals


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="swarmgate-py")
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("compile"); c.add_argument("file"); c.add_argument("-o", "--out")
    k = sub.add_parser("check"); k.add_argument("files", nargs="+"); k.add_argument("--json", action="store_true")
    k.add_argument("--no-decentralised", action="store_true")
    p = sub.add_parser("project"); p.add_argument("file")
    e = sub.add_parser("emit-lean"); e.add_argument("file"); e.add_argument("name"); e.add_argument("-o", "--out")
    e.add_argument("--native", action="store_true")
    i = sub.add_parser("influence"); i.add_argument("file")
    a = ap.parse_args(argv)

    if a.cmd == "compile":
        P = compile_file(a.file)
        txt = P.dumps(indent=1)
        if a.out:
            open(a.out, "w").write(txt)
        else:
            print(txt)
        return 0
    if a.cmd == "check":
        ok = True
        for f in a.files:
            P = compile_file(f)
            if not a.no_decentralised:
                with_locals(P)
            r = verify(P)
            print(json.dumps(r, indent=1) if a.json else summarize(r))
            ok &= r["wellFormed"]["ok"]
        return 0 if ok else 1
    if a.cmd == "project":
        P = compile_file(a.file)
        for L in project_all(P):
            print(local_str(P, L))
        return 0
    if a.cmd == "emit-lean":
        P = compile_file(a.file)
        txt = emit_lean(P, a.name, a.native)
        if a.out:
            open(a.out, "w").write(txt)
        else:
            print(txt)
        return 0
    if a.cmd == "influence":
        P = compile_file(a.file)
        for r, b in influence_bits(P).items():
            print(f"{r:>14}: {'∞ (tainted)' if b == float('inf') else f'{int(b)} bits'}")
        return 0
    return 2


if __name__ == "__main__":
    sys.exit(main())
