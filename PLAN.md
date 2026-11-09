# swarmgate — research plan

**Challenge (Apart Research sprint):** *A swarm runtime with typed messages. Build a swarm runtime where
inter-agent messages are typed by a Lean-checked session protocol, so agents can only communicate in ways
the declared protocol allows.*

## 0. One-paragraph thesis

LLM agents cannot be type-checked: their "code" is a stochastic policy that an attacker can steer through
prompt injection. Classical session types guarantee protocol conformance *statically*, by checking each
participant's program. Our setting turns that around: **participants are untrusted, the protocol is trusted, and
the guarantee must come from runtime enforcement whose decision procedure is itself proven correct in Lean.**
We formalise multiparty session protocols (global types → projection → local monitors) in Lean 4, prove an
**enforcement theorem**: *for every possible behaviour of every agent (including fully adversarial ones), the
sequence of delivered messages is a prefix of a protocol trace*. We then lift protocol-level security
properties (e.g. "no shell command without prior human approval", "data derived from the web never reaches the
payments role unsanitised", "at most k rounds") from the protocol to the running system for free. The runtime
runs the *same compiled Lean function* as its message filter, so the proof and the enforcement code don't drift
apart.

## 1. Theory (done first)

### 1.1 Core calculus (Lean 4, no Mathlib)
- Roles, labels, payload sorts (`unit | bool | nat | int | string | enum | record | list`), values with a
  typing judgement, decidable **refinements** on payloads (e.g. `amount ≤ 100`, `target ∈ allowlist`).
- Global types `G ::= p → q : {ℓᵢ(Sᵢ){φᵢ}. Gᵢ} | μX.G | X | end`; local types with internal/external choice.
- Global LTS (states = reachable subterms after unfolding, finite), **deterministic** under distinct labels.
- Projection `G ↾ r` with plain merging (and full merging for receive branches).

### 1.2 Theorems to prove (target: no `sorry`, no axioms beyond Lean's core)
| # | Statement | Why it matters for security |
|---|---|---|
| T1 | **Enforcement (central monitor).** For every adversary (arbitrary function from histories to attempted sends), the delivered trace ∈ prefix-closure of `traces(G)`. | Compromised agents cannot step outside the protocol. |
| T2 | **Transparency.** If every attempt is protocol-conformant, nothing is rejected. | No false positives for honest agents. |
| T3 | **Blame soundness.** A rejection is always attributed to the actual sender, and only non-conforming senders are blamed. | Accountability/forensics; identifies the infected agent. |
| T4 | **Property transfer.** If a safety property P (past-time LTL over events) holds on all traces of `G` (checked by a verified model checker), P holds on every enforced run. | Security policies are proven once, on the protocol. |
| T5 | **Decentralised enforcement / projection validation.** For protocols accepted by a verified checker, the product of per-agent local monitors (obtained by projection) is trace-equivalent to `G`. Certificate-checking approach (bisimulation certificate validated in Lean). | No central trusted router required; each agent's sidecar enforces its local type. |
| T6 | **Progress / no stuck protocol.** Well-formed `G` has an enabled move in every non-terminal state; with honest agents, runs reach `end` or continue. | Liveness for benign workloads; the monitor never "locks up". |
| T7 | **Budget enforcement** (bounded recursion / message budgets) bounds run length. | Anti-runaway-loop / cost-DoS. |

### 1.3 Security model (explicit)
- *Trusted:* the router/sidecar, Lean kernel + compiler, transport authenticity (sender identity can't be spoofed).
- *Untrusted:* every agent (LLM, tool, human-proxy), every payload.
- *In scope:* structural attacks — wrong recipient, out-of-order/skip step (e.g. skip approval), forged label,
  ill-typed or out-of-bounds payload, role impersonation, replay, infinite loops, unauthorised tool invocation
  (tools are modelled as roles).
- *Out of scope (and we say so loudly):* semantic attacks *inside* a well-typed free-text field. We quantify this
  residual risk and show how narrowing payload types (enums/refinements) and taint/IFC properties shrink it.

## 2. Artefacts (applied)

```
swarmgate/
  lean/            Lean 4 library  SwarmGate  (calculus, semantics, projection, monitors, checker, proofs)
                   + executable `swarmgate` (check / project / monitor server over JSON-lines)
  python/          pip package `swarmgate`
                   - protocol DSL (Scribble-like text) → JSON AST → Lean checker
                   - asyncio Swarm runtime: router, envelopes, audit log, blame, budgets
                   - monitors: LeanMonitor (verified binary) + PyMonitor (reference, differential-tested)
                   - LLM agent adapter: allowed next moves from the local type become the tool schema
                     ("protocol-guided decoding")
                   - adapters to existing frameworks (decided with you)
  protocols/       library of real MAS patterns encoded as protocols
  eval/            attack suite, fuzzing, LLM experiments, overhead benchmarks
  paper/           6-page paper (LaTeX)
```

## 3. Evaluation
- **E1 formal:** theorem inventory, LoC, `#print axioms` clean.
- **E2 expressiveness:** encode ~12 widely used MAS patterns (supervisor/worker, plan-execute, ReAct tool loop,
  human-approval gate, debate, map-reduce, critic/reviser, two-phase commit, auction, group chat w/ manager,
  handoff chains, RAG pipeline). Report what fits, what needs extensions, what is out of reach (dynamic
  spawning, unbounded participants, content-dependent routing).
- **E3 security:** ~10 attack classes × 4 defences (none / message-schema only (A2A-style) / static ACL
  graph / session monitor). Scripted adversaries + large-scale random/adversarial fuzzing (≥10⁶ attempts) +
  prompt-injected real LLM agents.
- **E4 utility & reliability:** benign tasks with real LLMs: false-reject rate, how often unconstrained LLMs
  violate protocol, effect of protocol-guided decoding.
- **E5 overhead:** per-message monitor latency (Lean binary vs Python), check-time scaling.
- **E6 differential testing:** Lean monitor vs Python monitor on ≥10⁶ random traces.

## 4. Milestones
1. Literature review & novelty positioning
2. Lean core + T1–T3 (+T6)
3. Property checker (T4), projection certificates (T5), budgets (T7)
4. Lean executable + JSON interface
5. Python runtime + DSL + monitors + LLM adapter
6. Protocol library (E2)
7. Evaluation E3–E6
8. Paper + README + docs
