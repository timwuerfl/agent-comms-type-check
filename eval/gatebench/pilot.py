"""Tiny pilot: one task per (defense, threat) to validate the pipeline and measure cost."""
import json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from gatebench.budget import BudgetedAnthropic, spent
from gatebench.framework import run_episode
import importlib

dom = importlib.import_module(f"gatebench.domains.{sys.argv[1] if len(sys.argv) > 1 else 'ops'}").DOMAIN
client = BudgetedAnthropic(tag=f"pilot:{dom.name}")
cases = [("hardened", "benign", None), ("session_naive", "benign", None), ("none", "inject", "action"),
         ("session_naive", "inject", "action"), ("hardened", "inject", "action"), ("none", "compromised", None),
         ("hardened", "compromised", None)]
for d, th, inj in cases:
    t0 = time.time(); c0 = client.total
    r = run_episode(dom, dom.tasks[0], d, th, inj, client)
    print(f"{d:14s} {th:11s} {str(inj):8s} util={r['utility']} attack={r['attack']} (ctrl={r['ctrl']} data={r['data']}) "
          f"del={r['delivered']} rej={r['rejections']} infected={r['infected']} pred={r['predicted_taint']} "
          f"err={r['error']} ${client.total-c0:.4f} {time.time()-t0:.0f}s", flush=True)
    print("   trace:", " ".join(f"{a}>{b}:{l}" for a, b, l in r["trace"])[:400])
print(f"total spent ${spent():.4f}")
