"""GateBench experiment runner (parallel, resumable, budget-capped).

    cd eval && SG_KEY_FILE=... python gatebench/run.py --domains ops,email,finance,code \
        --out results/gatebench_main.jsonl --cap 20 --workers 12

Phase 1 synthesises protocols for the synth_* defenses (cached under results/synth/<model>/<domain>/).
Phase 2 runs every (domain, task, defense, threat, injection, repeat) episode not yet in the output file.
A synth defense whose synthesis did not yield a protocol "fails closed": the swarm does not run.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import importlib
import json
import os
import sys
import threading
import time
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from gatebench.budget import BudgetExceeded, BudgetedAnthropic, spent, spent_by  # noqa: E402
from gatebench.framework import DEFENSES, INJECTION_FAMILIES, run_episode  # noqa: E402
from gatebench.synth import get_or_synthesize  # noqa: E402
from gatebench.admit import admit  # noqa: E402
from swarmgate.interface import compile_against  # noqa: E402

LOCK = threading.Lock()


def key(r: dict) -> str:
    return "|".join(str(r[k]) for k in ("domain", "task", "defense", "threat", "injection", "model", "rep"))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--domains", default="ops,email,finance,code")
    ap.add_argument("--defenses", default=",".join(DEFENSES))
    ap.add_argument("--threats", default="benign,inject,compromised")
    ap.add_argument("--injections", default=",".join(INJECTION_FAMILIES))
    ap.add_argument("--tasks", type=int, default=10)
    ap.add_argument("--repeats", type=int, default=1)
    ap.add_argument("--model", default="claude-haiku-5-5")
    ap.add_argument("--synth-model", default="claude-sonnet-5-5")
    ap.add_argument("--out", default=os.path.join(os.path.dirname(HERE), "results", "gatebench_main.jsonl"))
    ap.add_argument("--cap", type=float, default=20.0, help="USD cap for this invocation (tag-scoped)")
    ap.add_argument("--tag", default="main")
    ap.add_argument("--workers", type=int, default=12)
    a = ap.parse_args()

    domains = [importlib.import_module(f"gatebench.domains.{d}").DOMAIN for d in a.domains.split(",")]
    defenses = a.defenses.split(",")
    tag = f"{a.tag}:{a.model}"
    base = spent_by(a.tag)

    def over() -> bool:
        return spent_by(a.tag) - base >= a.cap

    # ---- phase 1: synthesis --------------------------------------------------------------------
    synth: dict = {}
    need = [v for v in ("unverified", "verified") if f"synth_{v}" in defenses]
    if need:
        sclient = BudgetedAnthropic(tag=f"{a.tag}:synth:{a.synth_model}")
        jobs = [(d, t, v) for d in domains for t in d.tasks[:a.tasks] for v in need]

        def do_synth(job):
            d, t, v = job
            try:
                return job, get_or_synthesize(d, t, sclient, a.synth_model, v)
            except Exception as e:
                traceback.print_exc()
                return job, {"ok": False, "error": repr(e)[:300]}
        with cf.ThreadPoolExecutor(a.workers) as ex:
            for (d, t, v), r in ex.map(do_synth, jobs):
                synth[(d.name, t.id, v)] = r
                print(f"[synth] {d.name}/{t.id}/{v}: ok={r.get('ok')} admitted={r.get('admitted')} "
                      f"rounds={r.get('n_rounds')} failed1={(r.get('rounds') or [{}])[0].get('failed')}", flush=True)

    # ---- phase 2: episodes -----------------------------------------------------------------------
    done = set()
    if os.path.exists(a.out):
        for line in open(a.out):
            try:
                done.add(key(json.loads(line)))
            except Exception:
                pass
    jobs = []
    for d in domains:
        for t in d.tasks[:a.tasks]:
            for df in defenses:
                for th in a.threats.split(","):
                    injs = (a.injections.split(",") if th == "inject" else
                            list(d.llm_roles) if th == "compromised" else [None])
                    for inj in injs:
                        for rep in range(a.repeats):
                            r = {"domain": d.name, "task": t.id, "defense": df, "threat": th, "injection": inj,
                                 "model": a.model, "rep": rep}
                            if key(r) not in done:
                                jobs.append((d, t, r))
    print(f"{len(jobs)} episodes to run ({len(done)} already done); spent so far ${spent():.2f}", flush=True)
    client = BudgetedAnthropic(tag=tag)
    t0 = time.time()
    n_done = [0]

    def do(job):
        d, t, r = job
        if over():
            return None
        P = None
        if r["defense"].startswith("synth_"):
            s = synth.get((d.name, t.id, r["defense"][6:]))
            if not s or not s.get("ok") or not s.get("src"):
                rec = dict(r, utility=False, ctrl=False, data=False, attack=False, no_protocol=True,
                           infected=[], predicted_taint=[], bound_violated=None, delivered=0, attempts=0,
                           rejections=0, in_tok=0, out_tok=0, error=None, trace=[])
                return rec
            P = compile_against(d.interface(), s["src"])
            adm = admit(d.interface(), P)["admitted"]          # re-check; never trust a cached verdict
            if r["defense"] == "synth_verified" and not adm:
                return dict(r, utility=False, ctrl=False, data=False, attack=False, no_protocol=True,
                            infected=[], predicted_taint=[], bound_violated=None, delivered=0, attempts=0,
                            rejections=0, in_tok=0, out_tok=0, error=None, trace=[])
            r = dict(r, synth_admitted=adm, synth_rounds=s.get("n_rounds"))
        try:
            rec = run_episode(d, t, r["defense"], r["threat"], r["injection"], client, model=a.model, protocol=P)
        except BudgetExceeded:
            return None
        except Exception as e:
            traceback.print_exc()
            rec = {"error": repr(e)[:300], "utility": False, "attack": False, "ctrl": False, "data": False}
        rec.update({k: v for k, v in r.items()})
        return rec

    with cf.ThreadPoolExecutor(a.workers) as ex, open(a.out, "a") as out:
        futs = [ex.submit(do, j) for j in jobs]
        for fut in cf.as_completed(futs):
            rec = fut.result()
            if rec is None:
                continue
            with LOCK:
                out.write(json.dumps(rec) + "\n")
                out.flush()
                n_done[0] += 1
                if n_done[0] % 25 == 0:
                    el = time.time() - t0
                    print(f"  {n_done[0]}/{len(jobs)} episodes, {el/60:.1f} min, run spent "
                          f"${spent_by(a.tag) - base:.2f}, total ${spent():.2f}", flush=True)
    print(f"done. run spent ${spent_by(a.tag) - base:.2f}; total ${spent():.2f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
