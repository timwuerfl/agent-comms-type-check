# Theory of protocol-typed swarms

This document fixes the formal model that the Lean development (`lean/SwarmGate`) mechanises and that the
Python runtime implements. Section numbers are referenced from code comments and the paper.

## 1. Design principles

**P1. Agents are untrusted, the protocol is the policy.** Classical session types guarantee conformance by
type-checking every participant's program. LLM agents have no program to check: their behaviour is a
stochastic, attacker-steerable function of their context. We therefore treat the declared protocol as a
*security policy* and enforce it by a *reference monitor* that completely mediates communication
(Anderson 1972; Schneider 2000). Every guarantee is stated for **all** agent behaviours.

**P2. Semantics = guarded automata over typed events.** A protocol denotes a finite, deterministic,
guarded automaton whose transitions are labelled by typed interaction events `p → q : ℓ(S){φ}`. Multiparty
global types with tail recursion (Honda–Yoshida–Carbone) compile to such automata. So does bounded
recursion (unrolled) and parallel composition (interleaving product). Working with automata, as in Li,
Stutz, Wies and Zufferey (CAV 2023) and the global-LTS view of Castro-Perez, Ferreira and Jongmans
(POPL 2026), avoids coinduction over μ-types and makes every check decidable.

**P3. Translation validation over meta-theory.** Projection, protocol-level model checking, taint analysis
and liveness analysis are done by unverified (fast) code that emits a **certificate**: a candidate invariant
set or ranking. A small checker validates the certificate, and *its* soundness is proved once in Lean. So
each protocol gets a machine-checked guarantee without our having to mechanise all of MPST meta-theory.
For maximal assurance a protocol can also be checked by the Lean **kernel** (`decide`), giving a
per-protocol proof term.

**P4. The proven function is the deployed function.** The runtime's accept/reject decision is computed by
the compiled Lean function `Monitor.step` about which the theorems are stated. A Python reference monitor
exists for convenience and is differential-tested against it.

## 2. Syntax

- Roles `r ∈ Fin n` (named).
- Sorts `S ::= unit | bool | int | str | enum{c₁..cₖ} | list S | record{f₁:S₁..}`; values `v` are JSON-like.
  Typing is decidable (`v ⊨ S`).
- Refinements `φ ::= ⊤ | ⊥ | φ∧φ | φ∨φ | ¬φ | path ≤ k | path ≥ k | len(path) ≤ k | path ∈ {..} | path = v`,
  decidable on values.
- A transition `τ = (src, dst, ℓ, S, φ, next)`. An abstract event is `⌊τ⌋ = (src, dst, ℓ)`.
- A protocol `P = (n, Δ, s₀, F)` with `Δ : State → List Transition`, start state `s₀` and final states `F`.
- A concrete event `e = (src, dst, ℓ, v)`. `τ` *matches* `e` iff the endpoints and label agree, `v ⊨ S` and `φ(v)`.

**Well-formedness (decidable):** (W1) *determinism*: in each state, abstract events of transitions are
pairwise distinct; (W2) all `next` are in range; (W3) role indices `< n`.

## 3. Semantics

`step(P, s, e) = next` of the first transition in `Δ(s)` matching `e`, else `none`.
`run(P, s, e₁…eₖ)` folds `step`. The *prefix language* is `Pref(P) = { t | run(P, s₀, t) ≠ none }`. It is
prefix-closed, i.e. a safety property in the sense of Alpern–Schneider. *Complete* traces end in `F`.

**Relational spec.** `Path(P, s, t, s')` holds iff each event is matched by *some* transition. *Lemma 3.1
(adequacy):* `run(P,s,t) = some s' ⇒ Path(P,s,t,s')`, and under (W1) the converse holds. The executable
monitor and the declarative semantics therefore coincide.

## 4. The enforcement game

An **attempt** `a = (σ, e)` is a claimed event `e` submitted over an authenticated channel by principal `σ`.
The transport authenticates `σ`. The monitor state is `m = (s, k, Q, halted)`: protocol state, delivered
count, a strike counter per role (quarantine), and a kill-switch flag. One monitor step:

```
deliver  iff  ¬halted ∧ σ ∉ quarantined ∧ σ = e.src ∧ k < budget ∧ step(P,s,e) = some s'
otherwise reject with a reason ∈ {Spoof, NotEnabled, Budget, Quarantined, Halted}, blaming σ
```

An **adversary** is any function `A : List Verdict → Attempt` (adaptive, full information about every past
verdict). It may control every agent at once. `play(A, N)` is the resulting run of length `N`.
Quantifying over all finite attempt lists subsumes all adversaries (Lemma 4.0).

**T1 Enforcement (soundness).** For every attempt list `as`, the delivered sequence `D(as)` satisfies
`run(P, s₀, D(as)) = some s` where `s` is the monitor's protocol state. Hence `D(as) ∈ Pref(P)`.
Corollary: the same holds for every adaptive adversary `A` and horizon `N`.

**T2 Transparency.** If `as` is *conformant*, meaning every attempt is authentic (`σ = e.src`), the events
form a protocol prefix, and `|as| ≤ budget`, then everything is delivered (`D(as) = map e as`) and nothing
is rejected.

**T3 Blame.**
- *Soundness:* every rejection with reason `Spoof` or `NotEnabled` blames a principal whose attempt was not
  an enabled authentic protocol move at that moment.
- *Honest-never-blamed:* if principal `h` only ever submits authentic events enabled at the current state,
  no verdict of reason `Spoof`/`NotEnabled` blames `h`, whatever all other principals do.

**T3′ Containment.** Once a principal is quarantined (strikes ≥ q), none of its later attempts is delivered.
Once halted, nothing is delivered. The number of delivered events never exceeds the budget.

## 5. Protocol-level properties and their transfer

### 5.1 Generic certificate lemma
For a transition system `(α, init, succ)` with decidable equality, a candidate set `V : List α` *certifies*
invariant `I` iff `init ∈ V`, `∀ c ∈ V, I c`, and `∀ c ∈ V, ∀ c' ∈ succ c, c' ∈ V`.
**Lemma 5.1.** If `V` certifies `I`, then `I` holds on every reachable configuration.
All checks below are instances of this lemma, with certificates produced by an unverified explorer.

### 5.2 Past-time LTL (T4)
Formulas `ψ ::= ⊤ | at(p?,q?,ℓ?) | ¬ψ | ψ∧ψ | ψ∨ψ | Yψ | Oψ | Hψ | ψ S ψ` over abstract events, with
the standard semantics on non-empty finite traces (Havelund & Roşu 2002). The incremental monitor stores
one bit per subformula. **Lemma 5.2:** the incremental update is correct with respect to the recursive
semantics. The checker explores `(protocol state, monitor bits)`.

**T4 Property transfer.** If `check(P, ψ) = true`, then for every attempt list (every adversary), every
non-empty prefix of the delivered trace satisfies `ψ`. Equivalently, `□ψ` holds on the actual run.
Examples: `H(at(Exec,Shell,run) → O at(Human,Exec,approve))`, meaning no shell command without prior
approval; `H ¬at(Worker,Payments,_)`; separation of duty.

### 5.3 Context taint and information-flow (T5)
LLM context windows do not separate data from instructions, so taint is *sticky per agent*. Policy:
- `U ⊆ Roles`: untrusted sources (web, mail, external agents);
- `lowcap(S)`: sorts too narrow to carry instructions (`unit`, `bool`, `enum`, bounded ints and records
  of those);
- `sensitive(⌊τ⌋)`: privileged actions.

Taint state `T ⊆ Roles` starts at `U`. On a delivered event `p→q:ℓ(S)` with `p ∈ T ∧ ¬lowcap(S)`, set
`T := T ∪ {q}`. The **IFC policy** is that every delivered sensitive event has an untainted sender.

**T5 IFC transfer.** If `checkIFC(P, pol) = true`, then for every adversary, every delivered sensitive
event is sent by a role not in `T` (taint computed on the delivered prefix). This is the protocol-level
version of the *dual-LLM / plan-then-execute / quarantined-reader* patterns (Willison 2023;
Beurer-Kellner et al. 2025; CaMeL). The check proves the pattern is actually *implemented by the protocol*:
attacker-controlled text cannot reach a privileged actor, only bounded choices can.

**Capacity.** `bits(S)` is `0` for unit, `1` for bool, `⌈log₂ k⌉` for an enum with `k` cases, and so on;
free text has unbounded capacity. The influence an attacker exerts on clean roles is bounded by the sum of
`bits` over tainted→clean low-capacity edges along a run. This is reported by the analyser (unverified);
§5.4 states and proves the corresponding guarantee (T9b).

### 5.4 Noninterference for arbitrary agents (T9)
LLM agents cannot be modelled, so we do not model them. A **system** `S = (P, turn, A, clean)` consists of a
protocol `P`, a payload-independent scheduler `turn : State → Option Role`, a set `A` of attacker-controlled
roles (e.g. the untrusted web tool plus every agent that read attacker text), and for every other role `r`
an *arbitrary* strategy `clean r : List Event → Option Event` applied to its **view**
`view r t = [e ∈ t | e.src = r ∨ e.dst = r]`. An **adversary** is an arbitrary `adv : List Event → Option
Event` that sees the *whole* trace, payloads included. One step (`sysStep`): the role `r = turn s` proposes
`adv t` (if `r ∈ A`) or `clean r (view r t)`; the proposal is delivered iff it is authentic (`e.src = r`) and
`step(P, s, e) = some s'`; otherwise the run halts. `exec S adv n` iterates this with fuel `n`.

The **declassified channel** is `δ(t) = map obs t` with
`obs(e) = att(e.dst, e.label, if e.dst ∈ A then none else some e.payload)` for `e.src ∈ A`, and `obs(e) = cl`
otherwise: A's control choices and the payloads A sends to clean roles. Payloads A sends among
themselves (a whole attacker-written web page read by a quarantined reader) are *not* part of `δ`.

**T9 Noninterference** (`noninterference`, `noninterference_inv`). Assume (W1) determinism at every state.
For all adversaries `adv₁, adv₂` and fuel `n`, writing `Tᵢ = exec S advᵢ n s₀ []`:
```
δ(T₁) = δ(T₂)  ⇒  ∀ r ∉ A, view r T₁ = view r T₂
```
and moreover both runs end in the same protocol state and `Agree(T₁, T₂)`: the traces have the same length
and are equal pointwise except for the payloads of A→A events. Hence every clean role's view — and with
it its entire behaviour — is a function of `δ` alone. The proof is an induction on fuel over the
agreement relation, using: agreeing traces have equal clean views (an event in a clean view is never
A→A); under W1 the successor state depends only on `(src, dst, label)`; a clean role's proposal is a
function of its view; the adversary's proposal is pinned by `δ` up to A→A payloads, and its `src` by the
authenticity check; and both runs halt at the same point (otherwise `δ` would differ in length).
`noninterference_detB` discharges W1 by the decidable check `detB`.

**Assumptions.** Deterministic, payload-independent scheduler; determinism W1; clean agents are
deterministic functions of their view. LLM sampling randomness is handled by fixing each agent's random
seed (a coupling argument: the theorem holds for every seed, hence for the joint distribution). The
adversary is omniscient and adaptive. Complete mediation (no side channels) as in §8.

**T9b Attacker decision budget** (`influence_bound`, `influence_monitor`, `influence_exec`). Let
`cost(s, τ) = clog2(k_s + 1) + (τ.dst ∈ A ? 0 : bits(τ.S))` for an A-sent `τ` (where `k_s` is the number of
A-sent transitions out of `s`; the `+1` accounts for the option to stop, which clean roles can observe),
and `0` for clean transitions. `checkInfluence(S, ρ, V)` certifies (Lemma 5.1) that on every reachable state
`ρ(τ.next) + cost(s, τ) ≤ ρ(s)` for all outgoing `τ`, and that every A→clean transition has a finite-capacity
sort. Then for every protocol run `t` from `s₀`, `runCost(s₀, t) ≤ ρ(s₀) =: B`; in particular for every
delivered trace of the gate (via T1) and every `exec` of a system. Reading: at each attacker turn the
attacker picks one of `k_s` transitions or stops and, towards a clean role, a payload of `≤ bits(S)` bits;
by T9 `δ` is determined by these choices, so it ranges over at most `2^B` values and clean behaviour
depends on at most `B` attacker-chosen bits. The counting step is not mechanised; it presupposes that
`bits` is a sound capacity bound, which holds for scalars and enums. For records it holds because records
are canonicalised in transit: the Lean gate reads JSON objects into sorted field lists, and the Python
runtime sorts record fields on delivery (`runtime.canonical`), so field order carries no information.
`bits(int)` is a coarse 64 ignoring refinements: sound but loose.

**Bridge to the deployed gate** (`Bridge.lean`).
- `exec_deliverable`: every trace of the model is delivered verbatim by the gate (`monRun`) when its events are
  submitted as authentic attempts within budget. So T9 speaks about traces the deployed monitor produces.
- `admitted_noninterference`: T9 holds for every admitted protocol without the extra determinism hypothesis,
  because admission now checks W1 on every state (`detAll`).

*Modelling choices, and why they lose no generality for delivered traces.*
- In the model a rejected proposal halts the run. The real gate absorbs rejections and lets the sender retry.
- Rejected attempts are invisible to other roles: the gate reports a rejection only to its sender. So any
  retrying adversary produces the same delivered trace as the non-retrying adversary that directly proposes
  the attempt that was eventually delivered.
- A retrying clean agent is likewise still a function of its own view plus gate feedback, and that feedback
  depends only on the protocol state and its own attempts.
- This argument is on paper; the Lean model fixes the non-retrying form.

*What T9 does and does not say.*
- δ contains every payload the attacker sends to clean roles, so T9 alone is close to definitional.
- Its content is that **nothing else leaks**. A→A traffic, for example a whole attacker-written page read by a
  quarantined reader, and the attacker's rejected attempts have no effect on clean agents.
- The quantitative strength comes from T9b. The attacker set `A` for T9b is computed by unverified exploration
  (the static taint closure), but any `A` works: the certificate is checked for the `A` it is given.

### 5.5 Untrusted protocol authors: admission against a meta-policy (T8)

In v1 the protocol was trusted. It need not be. The deployer writes an **interface** (meta-policy) `Π`:

- the roles;
- a **catalog** of message kinds `src → dst : ℓ(S){φ}`, i.e. what the tools and agents understand;
- the IFC policy: untrusted sources, endorsers, sensitive actions and the capacity threshold;
- required past-time properties;
- a maximum session length.

Any protocol `P`, for example one written per task by an LLM, is bound to `Π`. Its roles are re-indexed by
name, and its own security declarations are discarded. It is used only if `admit Π P C = true` for a
certificate `C`. The certificate is produced by untrusted search.

`admit` checks:
1. **catalog conformance** on every reachable transition: same endpoints, label and type, and the
   transition's refinement syntactically implies the catalog's (`predImplies`);
2. `checkIFC`;
3. `checkProp` for every required property;
4. `checkBounded` with `ρ(start) ≤ maxLen`;
5. determinism (W1) on every state (`detAll`), so that T9 applies.

Role *names* are glue: the verified check sees role indices. So the `swarmgate admit` CLI refuses a protocol
whose role names differ from the interface's, and `Interface.bind` re-indexes roles by name. The runtime limits
(budget and strikes) are taken from the interface, never from the protocol text.

**Theorem T8 (`admitted_secure`).** If `admit Π P C = true`, then on every run of the gate, for every
adversary:
- **(capability confinement)** every delivered message is an instance of a catalog entry, so an admitted
  protocol can never grant a capability the deployer did not list;
- every delivered sensitive action has an untainted sender;
- every required property holds after every delivered event;
- at most `maxLen` messages are delivered.

**Consequence.** The trusted computing base becomes the meta-policy, the checker and the gate. The protocol
author, the agents and every certificate generator are untrusted. `swarmgate emit-admit` turns an admitted
protocol into a Lean file whose `admitted` theorem the kernel re-checks with `decide +kernel`.

**Counterexample-guided synthesis.** A rejection comes with diagnostics: the offending message kind, the
information-flow path, the property trace, or the length. These are fed back to the LLM architect, which
repairs its protocol (`eval/gatebench/synth.py`).

## 6. Decentralised enforcement via projection (T6)

For mutually distrusting organisations no single router may be trusted. Each role `r` gets a local
automaton `L_r`. It is computed by automata projection: hide events not involving `r`, take the ε-closure,
then apply subset construction. Its transitions are labelled `!q ℓ(S){φ}` and `?p ℓ(S){φ}`. A sidecar
enforces `L_r` on `r`'s sends and receives. Delivery of `p→q` needs both sidecars to accept (mediated
rendezvous). The product configuration is the vector of local states.

Two certificate checks over pairs `(g, l⃗)`:
- **(T6a) Decentralised soundness:** every product step is a global step with identical guard. Then all
  decentralised runs are in `Pref(P)`, so T1, T4 and T5 hold without a central router.
- **(T6b) Decentralised transparency:** every global step is accepted by both sidecars, so honest runs are
  never blocked.

If T6a fails, the explorer returns the shortest offending interleaving. This is the classic
*unrealisability* witness (Alur–Etessami–Yannakakis; Castagna–Dezani–Padovani), and the protocol must then
run in central mode.

**Assumptions of T6.**
- Delivery is an atomic rendezvous of the sender's and the receiver's sidecars.
- Every sidecar is honest: each organisation trusts its own sidecar, and the theorem needs all of them to
  enforce. Trust is therefore *distributed* across organisations, not removed.
- An asynchronous deployment with queues is not covered.

## 7. Liveness-flavoured guarantees (T7)

- **No stuck state:** every reachable non-final state has a transition with a *witness payload* (checked
  `v ⊨ S ∧ φ(v)`). So honest agents always have a legal move, and the monitor never dead-ends a session.
- **Completion possible:** a ranking `ρ` with `ρ(f) = 0` on finals, where every non-final reachable state
  has a successor of strictly smaller rank. Then from every reachable state a final state is reachable.
- **Bounded length (anti-runaway):** a ranking that strictly decreases on *every* transition. Then every
  trace has length ≤ `ρ(s₀)`. Bounded `rec X [max k]` compiles to such protocols.

## 8. Trusted computing base and assumptions

- **Trusted:** the Lean kernel (the kernel only, for `decide`-checked protocols), the Lean compiler (for the
  compiled monitor and checker), the JSON glue in the `swarmgate` binary, the transport's sender
  authentication, and complete mediation (no side channels between agents outside the router).
- **Not trusted:** agents, tools, the DSL front-end, projection, explorers, certificate generators. Their
  errors cause rejections at check time, never unsoundness.
- **Assumptions:** synchronous mediated delivery (router or sidecar rendezvous); payload-independent
  control (refinements are local to a message).

## 9. What this does *not* give (and why)

- **Ordering, not content binding.** Protocols order messages but do not relate their contents.
  - "Exec after Approved" does not force the executed command to equal the approved one.
  - "Send after Confirmed" does not force the sent body to equal the confirmed draft.
  - A compromised executor can therefore run a *different allowlisted* command.
  - Data-dependent refinements across messages are future work.
- **Blame wording.** `honest_never_blamed` still allows an honest sender's message to be rejected with
  reason `budget` or `halted`; it excludes `spoof`, `notEnabled` and quarantine.
- **Replays.** A replay is rejected unless the protocol itself allows the same message again (e.g. inside
  a `rec` loop).

- **Semantic integrity of free text.** A well-typed `str` field can carry an injected instruction. T5
  bounds *where* such text can flow but does not judge its content.
- **Correctness of choices.** A compromised approver can legitimately choose `approve`. Use k-of-n
  approval, encoded in the protocol and checked by T4.
- **Specification adequacy.** We prove the system obeys the spec and the spec obeys the stated properties,
  not that these are the right properties.
- **Liveness under adversaries.** A silent agent stalls a session. Enforcement is a safety mechanism
  (Schneider), so liveness needs timeouts and failure branches (crash-stop MPST). The runtime implements
  timeouts as explicit `timeout` transitions taken by a trusted `Clock` role.
