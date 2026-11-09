#!/usr/bin/env bash
# Reproduce the SwarmGate evaluation. Requires: lean/lake built, python/ installed (see README).
set -e
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
echo "== Building the verified monitor and checker =="
( cd lean && lake build )
echo "== E1/E2: verify library + kernel-check emitted proofs =="
python eval/e2_library.py
( cd lean && lake build Protocols )          # kernel-check all emitted theorems
echo "== E3: structural attack suite =="
python eval/e3_structural.py 40
echo "== E3b: scenario (control vs data plane) =="
python eval/e3b_scenario.py 10
echo "== E5: overhead =="
python eval/e5_overhead.py
echo "== Differential test (Python vs Lean gate) =="
( cd python && python -m pytest -q )
echo "== E4 (optional, needs ANTHROPIC_API_KEY) =="
[ -n "$ANTHROPIC_API_KEY" ] && python eval/e4_llm.py --n 10 || echo "  skipped (no API key)"
echo "== GateBench (offline parts): domain tests, certified bit budgets, kernel-checked admission certificates =="
( cd eval && for t in gatebench/tests_*.py; do python "$t"; done )
( cd eval && python gatebench/bits_table.py && python gatebench/kernel_certify.py )
echo "== GateBench tables from the recorded episodes (no API calls) =="
( cd eval && python gatebench/paper_tables.py )
echo "== GateBench re-run (optional, needs SG_KEY_FILE; resumable, budget-capped; ~\$25 for the full grid) =="
if [ -n "$SG_KEY_FILE" ]; then
  ( cd eval && python gatebench/run.py --threats benign,inject,compromised --out results/gatebench_main.jsonl --cap 20 \
      && python gatebench/run.py --threats compromised,closure --out results/gatebench_attack.jsonl --cap 15 --tag attack )
else echo "  skipped (no SG_KEY_FILE)"; fi
echo "Done. Results in eval/results/."
