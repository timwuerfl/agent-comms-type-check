"""Statistics on LLM protocol synthesis (results/synth/<model>/<domain>/<task>_<variant>.json)."""
from __future__ import annotations

import collections
import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(os.path.dirname(HERE), "results", "synth")


def load(model: str):
    rows = []
    for p in sorted(glob.glob(os.path.join(RES, model, "*", "*.json"))):
        r = json.load(open(p))
        r["_file"] = p
        rows.append(r)
    return rows


def stats(model: str) -> dict:
    rows = load(model)
    out: dict = {"model": model}
    ver = [r for r in rows if r.get("variant") == "verified"]
    unv = [r for r in rows if r.get("variant") == "unverified"]
    # first *checked* draft of every run = what an unverified pipeline would deploy
    firsts = []
    for r in rows:
        chk = [x for x in r.get("rounds", []) if x.get("stage") == "checked"]
        if chk:
            firsts.append(chk[0])
    fail_kinds = collections.Counter()
    for f in firsts:
        for k in f.get("failed", []):
            fail_kinds["property" if k not in ("catalog", "ifc", "bound", "wellFormed") else k] += 1
    out["n_tasks"] = len(ver)
    out["verified_admitted"] = sum(1 for r in ver if r.get("admitted"))
    out["verified_rounds_mean"] = (sum(r["n_rounds"] for r in ver if r.get("admitted")) /
                                   max(1, sum(1 for r in ver if r.get("admitted"))))
    out["first_draft_checked"] = len(firsts)
    out["first_draft_admissible"] = sum(1 for f in firsts if f.get("admitted"))
    out["first_draft_ifc_violations"] = sum(1 for f in firsts if "ifc" in f.get("failed", []))
    out["first_draft_fail_kinds"] = dict(fail_kinds)
    out["unverified_deployed"] = len([r for r in unv if r.get("ok")])
    out["unverified_unsafe"] = sum(1 for r in unv if r.get("ok") and not r.get("admitted"))
    out["unverified_ifc_unsafe"] = sum(1 for r in unv if r.get("ok") and "ifc" in (r.get("report_failed") or []))
    compile_err = sum(1 for r in rows for x in r.get("rounds", []) if x.get("stage") == "compile_error")
    out["compile_errors_total"] = compile_err
    out["usd"] = sum(r.get("usd") or 0 for r in rows)
    per_dom = collections.defaultdict(lambda: [0, 0, 0])
    for r in ver:
        per_dom[r["domain"]][0] += 1
        per_dom[r["domain"]][1] += int(bool(r.get("admitted")))
    for r in unv:
        if r.get("ok") and "ifc" in (r.get("report_failed") or []):
            per_dom[r["domain"]][2] += 1
    out["per_domain"] = {d: {"tasks": v[0], "admitted": v[1], "unverified_ifc_unsafe": v[2]} for d, v in per_dom.items()}
    return out


if __name__ == "__main__":
    for m in (sys.argv[1:] or sorted(os.listdir(RES))):
        print(json.dumps(stats(m), indent=1))
