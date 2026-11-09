"""Classify why LLM first-draft protocols are rejected (offline; re-runs admission on stored drafts)."""
import collections, glob, importlib, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.dirname(HERE))
from gatebench.admit import admit
from swarmgate.interface import compile_against

def classify(I, rep):
    kinds = []
    c = rep["catalog"]
    if not c["ok"] and c["counterexample"] and c["counterexample"].get("notInCatalog"):
        n = c["counterexample"]["notInCatalog"]
        same = [m for m in I.messages if m["src"] == n["src"] and m["dst"] == n["dst"] and m["label"] == n["label"]]
        if not same:
            kinds.append("capability: message kind not in catalog")
        elif "Pred.tt" in n["pred"] or "tt" == n["pred"]:
            kinds.append("refinement dropped")
        else:
            kinds.append("type/refinement mismatch")
    if not rep["ifc"]["ok"]:
        kinds.append("information flow")
    for p in rep["properties"]:
        if not p["ok"]:
            kinds.append("required property")
    if not rep["bound"]["ok"]:
        kinds.append("length bound")
    return kinds or ["admitted"]

for m in sys.argv[1:] or ["claude-haiku-5-5", "claude-sonnet-5-5", "claude-opus-5-5"]:
    cnt = collections.Counter(); n = 0
    for p in sorted(glob.glob(f"results/synth/{m}/*/*.json")):
        r = json.load(open(p))
        D = importlib.import_module(f"gatebench.domains.{r['domain']}").DOMAIN
        I = D.interface()
        first = next((x for x in r.get("rounds", []) if x.get("stage") == "checked"), None)
        if not first or not first.get("src"):
            continue
        n += 1
        rep = admit(I, compile_against(I, first["src"]))
        for k in classify(I, rep):
            cnt[k] += 1
    print(m, "first drafts:", n, dict(cnt))
