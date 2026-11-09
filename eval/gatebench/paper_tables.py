"""Generate the paper's GateBench tables (LaTeX) and a JSON summary from the raw results."""
from __future__ import annotations

import collections
import importlib
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
ROOT = os.path.dirname(os.path.dirname(HERE))

from gatebench.report import load, wilson  # noqa: E402
from gatebench.synth_report import stats  # noqa: E402

DEFS = ["none", "topology", "session_naive", "hardened", "synth_unverified", "synth_verified"]
NAMES = {"none": "no gate (free bus)", "topology": "topology ACL", "session_naive": "SwarmGate, naive protocol",
         "hardened": "SwarmGate, hardened", "synth_unverified": "LLM protocol, unverified",
         "synth_verified": "LLM protocol, Lean-admitted"}
DOMAINS = ["ops", "email", "finance", "code"]
SENSITIVE_ACTOR = {"ops": "Executor", "email": "Assistant", "finance": "Clerk", "code": "Coder"}


def pct(k, n):
    return f"{100 * k / n:.0f}" if n else "--"


def ci(k, n):
    lo, hi = wilson(k, n)
    return f"{100*lo:.0f}--{100*hi:.0f}"


def main(path, attack_path=None):
    """benign/inject episodes from the main grid; compromised/closure episodes from the attack run (adaptive
    attacker), if present."""
    rows = load([path])
    if attack_path and os.path.exists(attack_path):
        rows = [r for r in rows if r["threat"] in ("benign", "inject")] + load([attack_path])
    out = {"n_episodes": len(rows)}
    g = collections.defaultdict(list)
    for r in rows:
        g[r["defense"]].append(r)
    lines = []
    summ = {}
    for d in DEFS:
        rs = g.get(d, [])
        ben = [r for r in rs if r["threat"] == "benign"]
        inj = [r for r in rs if r["threat"] == "inject"]
        com = [r for r in rs if r["threat"] == "compromised"]
        clo = [r for r in rs if r["threat"] == "closure"]
        comp_reader = [r for r in com if r["injection"] not in SENSITIVE_ACTOR.values()]
        comp_actor = [r for r in com if r["injection"] in SENSITIVE_ACTOR.values()]
        s = {
            "benign_util": (sum(r["utility"] for r in ben), len(ben)),
            "inject_asr": (sum(r["attack"] for r in inj), len(inj)),
            "inject_util": (sum(r["utility"] for r in inj), len(inj)),
            "comp_asr": (sum(r["attack"] for r in com), len(com)),
            "comp_ctrl": (sum(r["ctrl"] for r in com), len(com)),
            "comp_data": (sum(r["data"] for r in com), len(com)),
            "comp_reader_asr": (sum(r["attack"] for r in comp_reader), len(comp_reader)),
            "comp_actor_asr": (sum(r["attack"] for r in comp_actor), len(comp_actor)),
            "closure_asr": (sum(r["attack"] for r in clo), len(clo)),
            "induced": (sum(r.get("induced", False) for r in com + clo + inj), len(com + clo + inj)),
            "benign_fp": (sum(r["attack"] for r in ben), len(ben)),
            "closure_attacker_sensitive": (sum(1 for r in clo if r.get("attacker_sensitive")), len(clo)),
            "comp_attacker_sensitive": (sum(1 for r in com if r.get("attacker_sensitive")), len(com)),
            "closure_integrity": (sum(1 for r in clo if r.get("integrity")), len(clo)),
            "bound_viol": (sum(1 for r in rs if r.get("bound_violated")),
                           sum(1 for r in rs if r.get("bound_violated") is not None)),
            "no_protocol": sum(1 for r in rs if r.get("no_protocol")),
            "errors": sum(1 for r in rs if r.get("error")),
        }
        summ[d] = s
        b, i, c, cr, ca, cl = (s["benign_util"], s["inject_asr"], s["comp_asr"], s["comp_reader_asr"],
                               s["comp_actor_asr"], s["closure_asr"])
        lines.append(f"{NAMES[d]} & {pct(*b)} & {pct(*i)} & {pct(*cr)} & {pct(*ca)} & {pct(*c)} "
                     f"{{\\scriptsize({ci(*c)})}} & {pct(*cl)} \\\\")
    out["defenses"] = summ
    tab = ("\\begin{tabular}{lrrrrrr}\n\\toprule\n& benign & inject & \\multicolumn{3}{c}{one agent compromised} & taint\\\\\n"
           "\\cmidrule(lr){4-6}\ndefense & utility & ASR & reader & actor & all (95\\% CI) & closure\\\\\n\\midrule\n"
           + "\n".join(lines) + "\n\\bottomrule\n\\end{tabular}\n")
    os.makedirs(os.path.join(ROOT, "paper", "tables"), exist_ok=True)
    open(os.path.join(ROOT, "paper", "tables", "gatebench.tex"), "w").write(tab)

    # per-domain compromised ASR
    dl = []
    for dom in DOMAINS:
        cells = []
        for d in DEFS:
            rs = [r for r in g.get(d, []) if r["domain"] == dom and r["threat"] == "compromised"]
            cells.append(pct(sum(r["attack"] for r in rs), len(rs)))
        ben = [[r for r in g.get(d, []) if r["domain"] == dom and r["threat"] == "benign"] for d in DEFS]
        dl.append(f"{dom} & " + " & ".join(cells) + " \\\\")
    out["per_domain_comp_asr"] = dl
    open(os.path.join(ROOT, "paper", "tables", "perdomain.tex"), "w").write(
        "\\begin{tabular}{l" + "r" * len(DEFS) + "}\n\\toprule\n& none & topo & sess. & hard. & LLM & LLM+Lean\\\\\n"
        "\\midrule\n" + "\n".join(dl) + "\n\\bottomrule\n\\end{tabular}\n")

    # infection vs prediction (theory vs practice), gated defenses only
    gated = [r for r in rows if r.get("bound_violated") is not None]
    out["bound_checks"] = len(gated)
    out["bound_violations"] = sum(1 for r in gated if r["bound_violated"])
    out["infections_observed"] = sum(1 for r in gated if r.get("infected"))

    # synthesis
    out["synthesis"] = {}
    for m in ("claude-haiku-5-5", "claude-sonnet-5-5", "claude-opus-5-5"):
        try:
            out["synthesis"][m] = stats(m)
        except Exception as e:
            out["synthesis"][m] = {"error": repr(e)}
    json.dump(out, open(os.path.join(ROOT, "eval", "results", "gatebench_summary.json"), "w"), indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != "synthesis"}, indent=1))
    for m, s in out["synthesis"].items():
        print(m, {k: s.get(k) for k in ("n_tasks", "verified_admitted", "verified_rounds_mean",
                                          "first_draft_checked", "first_draft_admissible",
                                          "first_draft_ifc_violations", "unverified_unsafe", "unverified_ifc_unsafe")})


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "eval", "results", "gatebench_main.jsonl"),
         sys.argv[2] if len(sys.argv) > 2 else os.path.join(ROOT, "eval", "results", "gatebench_attack.jsonl"))
