"""Figure: attack success per defense (GateBench, Haiku 5.5 agents). Data: eval/results/gatebench_summary.json."""
import json, os, sys
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "eval"))
from gatebench.report import wilson
S = json.load(open(os.path.join(ROOT, "eval", "results", "gatebench_summary.json")))["defenses"]
DEFS = [("none", "No gate (free bus)"), ("topology", "Topology ACL"), ("session_naive", "Typed gate, naive protocol"),
        ("hardened", "Typed gate, hardened protocol"), ("synth_unverified", "LLM-written protocol, unverified"),
        ("synth_verified", "LLM-written protocol, Lean-admitted")]
SER = [("comp_asr", "One agent compromised", "#2a78d6"), ("closure_asr", "Taint closure (worst case)", "#eb6834")]
INK, MUTED, GRID = "#0b0b0b", "#52514e", "#e4e3df"
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9})
fig, ax = plt.subplots(figsize=(6.5, 2.75), dpi=300)
h = 0.36
for j, (k, lab, col) in enumerate(SER):
    for i, (d, _) in enumerate(DEFS):
        kk, n = S[d][k]; v = 100 * kk / n; lo, hi = wilson(kk, n)
        y = i + (j - 0.5) * (h + 0.04)
        ax.barh(y, max(v, 0.6), height=h, color=col, label=lab if i == 0 else None, zorder=2)
        ax.errorbar(v, y, xerr=[[v - 100 * lo], [100 * hi - v]], fmt="none", ecolor=MUTED, elinewidth=0.8,
                    capsize=1.8, zorder=3)
        ax.text(100 * hi + 1.5, y, f"{v:.0f}%", va="center", ha="left", fontsize=8, color=INK)
ax.set_yticks(range(len(DEFS))); ax.set_yticklabels([l for _, l in DEFS], color=INK)
ax.invert_yaxis(); ax.set_xlim(0, 112); ax.set_xticks([0, 25, 50, 75, 100])
ax.set_xlabel("Attack success rate (% of episodes; bars show 95% Wilson CI)", color=MUTED)
ax.grid(axis="x", color=GRID, lw=0.6, zorder=0)
for s in ("top", "right", "left"): ax.spines[s].set_visible(False)
ax.spines["bottom"].set_color(GRID); ax.tick_params(colors=MUTED, length=0)
ax.legend(loc="lower center", bbox_to_anchor=(0.4, 1.0), ncol=2, frameon=False, fontsize=8.5)
fig.tight_layout()
fig.savefig(os.path.join(HERE, "results.png"), dpi=300)
