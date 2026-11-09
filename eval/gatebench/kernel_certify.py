"""Emit and kernel-check the admission certificate (Theorem T8) of every LLM-written, admitted protocol."""
import concurrent.futures as cf, glob, importlib, json, os, re, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.dirname(HERE))
ROOT = os.path.dirname(os.path.dirname(HERE))
from swarmgate.gate import find_binary
from swarmgate.interface import compile_against
LEAN = os.path.join(ROOT, "lean"); OUT = os.path.join(LEAN, "Admitted", "synth"); os.makedirs(OUT, exist_ok=True)
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])

def one(p):
    r = json.load(open(p))
    if not (r.get("admitted") and r.get("src")):
        return None
    model = p.split(os.sep)[-3]
    D = importlib.import_module(f"gatebench.domains.{r['domain']}").DOMAIN
    I = D.interface(); P = compile_against(I, r["src"])
    name = re.sub(r"[^A-Za-z0-9]", "", f"{model}_{r['task']}")
    with tempfile.TemporaryDirectory() as d:
        pol, pf = os.path.join(d, "pol.json"), os.path.join(d, "p.json")
        json.dump(I.to_json(), open(pol, "w")); open(pf, "w").write(P.dumps())
        src = subprocess.run([find_binary(), "emit-admit", pol, pf, name], capture_output=True, text=True)
    if src.returncode != 0:
        return {"file": p, "model": model, "task": r["task"], "ok": False, "stage": "emit", "err": src.stderr[-300:]}
    f = os.path.join(OUT, f"{name}.lean"); open(f, "w").write(src.stdout)
    t = time.time()
    k = subprocess.run(["lake", "env", "lean", f], cwd=LEAN, capture_output=True, text=True, env=ENV)
    return {"model": model, "domain": r["domain"], "task": r["task"], "ok": k.returncode == 0,
            "seconds": round(time.time() - t, 2), "bytes": len(src.stdout),
            "err": (k.stdout + k.stderr)[-300:] if k.returncode else ""}

files = sorted(glob.glob(os.path.join(ROOT, "eval", "results", "synth", "*", "*", "*_verified.json")))
res = []
with cf.ThreadPoolExecutor(3) as ex:
    for r in ex.map(one, files):
        if r:
            res.append(r); print(r["model"], r.get("task"), r["ok"], r.get("seconds"), flush=True)
json.dump(res, open(os.path.join(ROOT, "eval", "results", "kernel_certificates.json"), "w"), indent=1)
print("kernel-checked:", sum(r["ok"] for r in res), "/", len(res))
