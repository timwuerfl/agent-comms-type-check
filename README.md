# SwarmGate — trust only the checker

**SwarmGate makes a declared communication protocol the security boundary of an LLM agent swarm, and
reduces what you must trust to a small Lean-verified checker.**

Multi-agent LLM systems fail through their messages: one prompt-injected agent infects the others, a fooled
orchestrator hands an executor malicious work, a required approval is skipped. Session types are the
classical tool for disciplined communication, but they work by type-checking each participant's program, and
an LLM has no program to check. SwarmGate makes the protocol the security boundary and removes trust in three steps:

| step | what becomes untrusted | what replaces the trust | Lean theorem |
|---|---|---|---|
| 1 | **the agents** | a reference monitor mediates every message; the delivered trace stays inside the protocol for *every* agent behaviour | `enforcement`, `blame_sound`, `honest_never_blamed`, `property_transfer` |
| 2 | **the content** (free text can carry injections) | noninterference for *arbitrary* agents: clean agents depend on the attacker only through a declassified channel of at most **B bits**, certified per protocol | `ifc_transfer`, `noninterference`, `influence_monitor` |
| 3 | **the protocol author** (an LLM writes a protocol per task) | verified admission against the deployer's meta-policy; counterexamples drive the LLM's repair | `admitted_secure` |

What remains trusted: the deployer's interface (meta-policy), the checker and the gate (plus the Lean kernel
and compiler). The gate's decision is the compiled Lean function the theorems are about, so the proofs and the
deployed system cannot drift apart. All proofs: Lean 4, ~2.7k lines, no `sorry`, only Lean's standard axioms.

Paper: `paper/swarmgate.pdf` · theory: [`docs/THEORY.md`](docs/THEORY.md) · related work: [`docs/RELATED.md`](docs/RELATED.md)

---

## How it fits together

```
 deployer: interface (roles, message catalog, untrusted sources, endorsers, sensitive actions, properties, bound)
        │
        ▼
 LLM architect writes a protocol for the task ──► swarmgate admit (Lean, T8) ──✗──► counterexample ─┐
        ▲                                               │ ✓                                          │
        └───────────────────── repair ◄─────────────────┼────────────────────────────────────────────┘
                                                        ▼
 agents (LLMs, tools, humans) ──attempt──► gate = compiled Lean monStep (T1–T3) ──deliver/reject+blame──► agents
                                                        │
                       certified: attacker influence on clean agents ≤ B bits (T9b)
```

## Quickstart

```bash
# 1. Build the verified checker/monitor (Lean 4; ~2 min the first time)
cd lean && lake build && cd ..
# 2. Python runtime + benchmark
python -m venv .venv && . .venv/bin/activate && pip install -e ./python anthropic
# 3. Verify a protocol; admit one against an interface; certify the attacker-bit bound
swarmgate-py check protocols/ops_hardened.sg
cd eval && python -m gatebench.tests_email          # offline benchmark self-test
```

The protocol language (`.sg`):

```
protocol ApprovalGate {
  roles User, Agent, Human, Shell;
  endorser Human;                      // a non-LLM role that cannot be prompt-injected
  sensitive Agent -> Shell;            // the privileged action
  User -> Agent : Task(str) where len <= 2000;
  rec Step max 5 {                     // bounded loop: no runaway sessions
    Agent -> Human : Propose({cmd: enum{ls, cat, grep, df}, arg: str}) where arg.len <= 120 and arg !contains ";";
    choice at Human {
      Human -> Agent : Approve({cmd: enum{ls, cat, grep, df}, arg: str});
      call Agent -> Shell : exec({cmd: enum{ls, cat, grep, df}, arg: str}) returns str;
      choice at Agent { continue Step; } or { Agent -> User : Done(str); }
    } or { Human -> Agent : Deny(str); Agent -> User : Aborted(str); }
  }
  property NoUnapprovedExec: Agent -> Shell : exec implies prev Human -> Agent : Approve;
}
```

Interfaces (meta-policies) use `interface Name { roles ...; untrusted ...; endorser ...; sensitive ...; lowcap n;
bound n; message A -> B : L(T) where ...; property ...; }` — see `protocols/gatebench/*.interface.sg`.

## The `swarmgate` binary (Lean)

| command | what it does | soundness theorem |
|---|---|---|
| `swarmgate serve P.json` | the gate, as a JSON-lines server | T1–T3 (`Monitor.lean`) |
| `swarmgate check P.json` | properties, IFC, no-stuck, completion, bound, decentralisation | T4–T7 |
| `swarmgate admit I.json P.json` | admission against an interface + counterexamples | T8 (`Admission.lean`) |
| `swarmgate influence P.json [Role…]` | certified attacker-bit bound B | T9b (`Noninterference.lean`) |
| `swarmgate emit-lean P.json Name` / `emit-admit I.json P.json Name` | Lean files whose theorems the **kernel** re-checks | — |

## Use it from any framework: the gateway

Agents in any language talk to the gate over HTTP/JSON (`python/swarmgate/gateway.py`): `POST
/sessions/{id}/send` is the only channel (per-role bearer tokens authenticate senders), `GET …/next?role=R`
returns the moves `R` may make now, `GET …/log` is the audit trail with blame. MCP tool calls are gated by
`swarmgate.mcp_gate.McpGatewaySession`: an agent can only call the tools its protocol permits in the current
state.

## GateBench

`eval/gatebench/`: four domains (ops, email, finance, code), each with an interface, a naive and a hardened
protocol, simulated tools, deterministic endorsers, 10 tasks, injection and compromised-agent threats and
precise goal detectors. All attacker payloads are inert placeholders.

```bash
cd eval
python -m gatebench.tests_email; python -m gatebench.tests_finance; python -m gatebench.tests_code
SG_KEY_FILE=/path/to/key python gatebench/run.py --domains ops,email,finance,code --repeats 2 --out results/gatebench_main.jsonl
python gatebench/report.py results/gatebench_main.jsonl
python gatebench/paper_tables.py
```

## Results

**GateBench** (4 domains: ops, email, finance, code; 10 tasks each; Claude Haiku 5.5 agents; 4,080 episodes;
compromised and taint-closure threats use a scripted adaptive attacker). Numbers are % of episodes
(`eval/results/gatebench_summary.json`, `paper/tables/gatebench.tex`):

| defense | benign utility | injection ASR | one agent compromised: reader / actor / all | taint closure |
|---|---|---|---|---|
| no gate (free bus) | 79 | 0 | 100 / 98 / **99** | 100 |
| topology ACL | 85 | 0 | 17 / 99 / 50 | 100 |
| SwarmGate, naive protocol | 86 | 0 | 9 / 78 / 36 | 75 |
| SwarmGate, hardened protocol | **100** | 0 | 0 / 25 / **10** | **0** |
| LLM protocol, unverified | 82 | 0 | 0 / 12 / 5 | 0 (2/8 integrity attacks on the 4 IFC-unsafe ones) |
| LLM protocol, Lean-admitted | 86 | 0 | 0 / 15 / **6** | **0** |

* Every remaining compromised-actor success is a coder that writes attacker text into the free-text commit message
  after CI passed: protocols order and type messages but don't bind free-text content (see Limitations).
* Indirect injection almost never works against current Claude models (1/1,920; Haiku 4.5 probe 0/48). That is why
  the paper evaluates the *taint closure* (every exposed agent obeys the attacker), where T5/T9 still hold.
* **Agent model:** with Claude Sonnet 5.5 as every agent (2 tasks/domain, 180 episodes) a compromised agent succeeds
  in 95% (free bus) → 50% (ACL) → 25% (naive) → 10% / 5% (hardened / admitted LLM protocol); closure 100% → 0%.
* **0** of 2,720 gated episodes had an infection outside the statically predicted taint set.
* **Synthesis:** Haiku, Sonnet and Opus 5.5 architects get admitted protocols for every task they answer (Opus
  refused 4 ops tasks) in 1.4–2.0 repair rounds; 116/116 admission certificates are re-checked by the Lean kernel.
  Without verification, 4/40 Sonnet protocols are information-flow-unsafe.
* **Certified attacker budget:** hardened protocols get B = 12–20 bits (finance 140), admitted LLM protocols about
  half of that; naive protocols ∞.
* **Structural attacks:** 28,561 scripted attacks on 20 protocols: free bus 100% accepted, schema validation 81%,
  topology ACL 35%, SwarmGate 0%; 100% of honest traffic delivered.

## Layout

```
lean/SwarmGate/     calculus, gate, checkers and proofs (T1–T9)        docs/THEORY.md
lean/Main.lean      swarmgate CLI: serve · check · admit · influence · emit-lean · emit-admit
lean/Protocols/, lean/Admitted/   generated kernel-checked certificates
python/swarmgate/   runtime, DSL + interfaces, gates, gateway (A2A/MCP), LLM adapter, projection
protocols/          20 multi-agent patterns + GateBench interfaces/protocols
eval/               v1 evaluation (structural attacks, overhead) and GateBench (eval/gatebench)
paper/              the paper
```

## Trust & scope

Trusted: the interface, the Lean kernel and compiler, the JSON glue, sender authentication and complete
mediation. Untrusted: agents, tools, protocol authors, the DSL front-end and all certificate generators — their
mistakes cause rejections, never unsound enforcement. Not covered: the meaning of text an endorser reads
(endorsers are an explicit trust assumption), the correctness of a compromised role's legitimate choices, attacks
outside the mediated channel, and liveness under adversaries. Apache-2.0.
