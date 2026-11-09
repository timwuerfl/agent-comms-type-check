"""Run verified synthesis for all GateBench tasks with a given architect model (cached)."""
import concurrent.futures as cf, importlib, os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.dirname(HERE))
from gatebench.budget import BudgetedAnthropic, spent_by
from gatebench.synth import get_or_synthesize
model = sys.argv[1]
doms = [importlib.import_module(f"gatebench.domains.{d}").DOMAIN for d in ("ops", "email", "finance", "code")]
client = BudgetedAnthropic(tag=f"synthcmp:{model}")
jobs = [(d, t) for d in doms for t in d.tasks]
def go(j):
    d, t = j
    try:
        r = get_or_synthesize(d, t, client, model, "verified")
        return f"{d.name}/{t.id}: admitted={r.get('admitted')} rounds={r.get('n_rounds')}"
    except Exception as e:
        return f"{d.name}/{t.id}: ERROR {e!r}"[:200]
with cf.ThreadPoolExecutor(8) as ex:
    for line in ex.map(go, jobs):
        print(line, flush=True)
print("spent", spent_by(f"synthcmp:{model}"))
