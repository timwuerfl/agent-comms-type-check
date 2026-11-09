"""Certified attacker budget B (Theorem T9b) for naive, hardened and admitted LLM-written protocols.
Writes results/synth_bits.json and paper/tables/bits.tex.   cd eval && python gatebench/bits_table.py"""
import collections, glob, importlib, json, os, statistics, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.dirname(HERE))
EVAL = os.path.dirname(HERE); ROOT = os.path.dirname(EVAL)
from swarmgate.gate import find_binary  # noqa: E402
from swarmgate.interface import compile_against  # noqa: E402

DOMAINS = ["ops", "email", "finance", "code"]


def bits(P):
    """None if the influence certificate is not finite (unbounded attacker channel)."""
    f = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False); f.write(P.dumps()); f.close()
    try:
        r = json.loads(subprocess.run([find_binary(), "influence", f.name], capture_output=True, text=True).stdout)
    finally:
        os.unlink(f.name)
    return r["bits"] if r["verified"] else None


def main():
    res = collections.defaultdict(lambda: collections.defaultdict(list))
    for m in ("claude-haiku-5-5", "claude-sonnet-5-5", "claude-opus-5-5"):
        for p in glob.glob(os.path.join(EVAL, "results", "synth", m, "*", "*_verified.json")):
            r = json.load(open(p))
            if not r.get("admitted"):
                continue
            D = importlib.import_module(f"gatebench.domains.{r['domain']}").DOMAIN
            res[m][r["domain"]].append(bits(compile_against(D.interface(), r["src"])))
    summary = {}
    for m, dd in res.items():
        for d, v in sorted(dd.items()):
            fin = [x for x in v if x is not None]
            summary[f"{m}/{d}"] = {"n": len(v), "finite": len(fin), "median": statistics.median(fin) if fin else None,
                                   "max": max(fin) if fin else None}
    json.dump(summary, open(os.path.join(EVAL, "results", "synth_bits.json"), "w"), indent=1)
    show = lambda b: "$\\infty$" if b is None else str(b)
    rows = []
    for d in DOMAINS:
        D = importlib.import_module(f"gatebench.domains.{d}").DOMAIN
        s = summary[f"claude-sonnet-5-5/{d}"]
        rows.append(f"{d} & {show(bits(D.protocol('naive')))} & {show(bits(D.protocol('hardened')))} & "
                    f"{int(s['median'])} ({int(s['max'])}) \\\\")
    tab = ("\\begin{tabular}{lrrr}\n\\toprule\ndomain & naive & hardened & LLM-written, admitted: median (max)\\\\\n"
           "\\midrule\n" + "\n".join(rows) + "\n\\bottomrule\n\\end{tabular}\n")
    open(os.path.join(ROOT, "paper", "tables", "bits.tex"), "w").write(tab)
    print(tab)


if __name__ == "__main__":
    main()
