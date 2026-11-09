# SwarmGate v2 — plan for the "untrusted protocol author" and "data-plane theorem" extension

## Red line (unchanged, sharpened)

> **The protocol is the security boundary; a small verified checker is the only thing we trust.**
> v1: agents are untrusted, the protocol is trusted, the monitor is verified.
> v2: agents are untrusted, **the protocol author is untrusted too** (an LLM designs a protocol per task),
> and the *data plane* gets a semantic theorem — attacker influence on clean agents is bounded by **B bits**,
> certified per protocol. Trusted computing base = deployer meta-policy + Lean checker + gate.

Three contributions, one story:

| # | Contribution | Kind | Evidence |
|---|---|---|---|
| C1 | **T8 Admission / capability confinement**: for *any* protocol (e.g. LLM-written), if the verified admission check accepts it against the deployer's meta-policy (message catalog, IFC policy, required properties, length bound), every enforced run confines all messages to catalog capabilities and satisfies IFC + properties + bound. | Lean theorem | `lean/SwarmGate/Admission.lean` |
| C2 | **T9 Noninterference for arbitrary agents**: model clean agents as *arbitrary* deterministic functions of their view; the adversary controls a role set `A` with full information. Then all clean agents' views are a function of the declassified attacker channel δ (A's control choices + payloads sent to clean roles). **T9b**: with a certified potential, the total attacker decision budget on any run is ≤ B bits. | Lean theorems | `lean/SwarmGate/Noninterference.lean` |
| C3 | **GateBench + verified protocol synthesis (CEGIS)**: 4 domains × 10 tasks, prompt-injection and compromised-agent threat models, real Claude agents; an LLM architect writes protocols, Lean admits or refutes with counterexamples, the LLM repairs. Compare against no gate / topology ACL / session-naive / hand-hardened / LLM-synthesized-but-unverified (ControlValve-style). Validate theory against practice: empirical infection ⊆ predicted taint set; attacker bits ≤ B. | Benchmark + experiments | `eval/gatebench/` |

## C1 design (Lean)

```
structure CatEntry where src dst : Nat; label : String; ty : Ty; pred : Pred
structure MetaPolicy where
  nRoles : Nat; catalog : List CatEntry; ifc : IFCPolicy; props : List F; maxLen : Option Nat
```
`admit Π P certs` = `P.nRoles = Π.nRoles` ∧ catalog-conformance certificate (every reachable transition has a
catalog entry with equal endpoints/label/type and a refinement the transition's refinement implies,
`predImplies`) ∧ `checkIFC` ∧ all `checkProp` ∧ (`checkBounded` with `rk ρ start ≤ maxLen`).
Theorem `admitted_secure`: every delivered event is an instance of some catalog entry (capability
confinement), IFC holds, every property holds, length ≤ maxLen — for every adversary.
The protocol's own `untrusted/sensitive/endorser` declarations are ignored: the security metadata comes
from Π (an LLM cannot declare the web trusted).

## C2 design (Lean) — see the subagent brief in the session; summary

* `Strat := List Event → Option Event` (clean role: deterministic function of its *view*).
* Adversary: `List Event → Option Event` on the *full* trace, plays every role in `A`.
* Deterministic turn function `turn : Nat → Option Nat` (protocol state ↦ whose turn), payload-independent.
* `exec n` runs n turns through the gate; a rejected or absent move halts.
* `δ t` = for each event: `inl (dst,label, payload if dst ∉ A)` if src ∈ A, else `inr ()`.
* **T9**: `δ t₁ = δ t₂ → ∀ r ∉ A, view r t₁ = view r t₂` (and the clean-sent events coincide), for any two
  adversaries, assuming determinism (W1) at reachable states.
* **T9b**: certificate ρ with `ρ(t.next) + cost(t) ≤ ρ(s)`, `cost(t) = [src∈A]·(clog2 k_s + [dst∉A]·capBits ty)`;
  then Σ cost along every run ≤ ρ(start) = B.

## C3 design (Python, `eval/gatebench/`)

* `framework.py` — `Domain` interface, `run_episode(domain, task, injection, defense, threat, models)`.
* `budget.py` — shared JSON ledger + `BudgetedAnthropic` (hard cap $55 across all processes; file lock).
* `domains/{ops,email,finance,code}.py` + `protocols/gatebench/<domain>_{naive,hardened}.sg`.
* `synth.py` — architect prompt (DSL reference + catalog + meta-policy + task), compile → admit → counterexample
  → repair, ≤ 4 rounds; unverified variant = first compilable protocol.
* `run.py` — experiment grid, resumable JSONL results, cost tracking.

Defenses: `none` (free bus, unguided agents) · `topology` (naive-protocol ACL, unguided) · `session_naive`
(unguided) · `hardened` (hand-written, guided) · `synth_unverified` (guided) · `synth_verified` (guided).
Threats: `inject` (indirect prompt injection in untrusted tool output) · `compromised` (the agent reading
untrusted data gets an attacker system prompt). Payloads are **inert placeholders** (`ROGUE-ACTION`,
`attacker.example`, a fake token) — no functional exploits anywhere.

Budget (hard cap $55 of the $60): pilot ≤ $6 · synthesis ≤ $12 · main grid ≤ $25 · robustness (Sonnet agents) ≤ $8.

## Phases

0. Review fixes (done), plan (this file), budget ledger, GateBench framework + `ops` reference domain. *(me)*
1. In parallel: T9 Lean (subagent, worktree) · domains email/finance/code (3 subagents) · T8 Lean + `swarmgate admit` *(me)*.
2. Synthesis pipeline (subagent) · runner + pilot *(me)*.
3. Full grid, robustness subset, static-vs-empirical validation *(me)*.
4. Paper v2 rewrite, README, independent review subagent, push.
