"""Content of the Apart Research submission (Word). Markup: **bold**, *italic*, `code`, [@key,key] citations.
Numbers are taken from eval/results (gatebench_summary.json, gatebench_sonnet.jsonl, synth_bits.json)."""

AUTHORS = ["Mauricio Neubecker", "Tim Würfl", "Maximilian Eder"]
AFFILIATIONS = ["Technical University of Munich", "Safe AI Germany"]

TITLE = "Lean-Verified Session Protocols as the Security Boundary of LLM Agent Swarms"

ABSTRACT = (
    "Teams of LLM agents increasingly work together by messaging each other and calling tools, and a single "
    "manipulated agent can steer the whole team into harmful actions. We present **SwarmGate**, a first-of-a-kind "
    "runtime in which agents can only communicate in ways a declared protocol allows, with Lean-proved guarantees "
    "that hold even for compromised agents. Classical session types enforce such protocols by checking each "
    "participant's program, but an LLM has no program to check. SwarmGate instead makes the protocol the security "
    "boundary and enforces it with a small **Lean-verified checker**, the only component that must be trusted. "
    "*Untrusted agents:* every delivered message provably follows the protocol. *Untrusted content:* a "
    "noninterference theorem bounds how many attacker-chosen bits can reach uncompromised agents. *Untrusted "
    "protocol authors:* an LLM writes a protocol per task, and a verified admission check decides whether it may run. "
    "On **GateBench**, a new benchmark of 4 domains and 40 tasks with real Claude agents (4,080 episodes), a "
    "compromised agent reaches its goal in 99% of episodes without a gate; under verified protocols it succeeds only "
    "through a free-text field the deployer explicitly allows (0% in three of four domains, 6–10% overall), and the "
    "worst-case taint-closure attack drops from 75–100% to 0%. LLM-written protocols admitted by Lean are as secure "
    "as hand-written ones, while 10% of unverified ones are unsafe.")

# Blocks: ("h2"|"h3", text) ("p", text) ("num", [items]) ("thm", name, lean, statement) ("fig"|"tab"|"code", key)
BODY = [
("h2", "1. Introduction"),
("p", "A single language model makes mistakes. A *swarm* of them fails in new ways that run through the "
      "messages the agents exchange. Prompt Infection spreads one compromise across a network of agents "
      "[@lee2024promptinfection,gu2024agentsmith]; a fooled orchestrator hands malicious code to an executor "
      "[@triedman2025mas]; an agent-in-the-middle rewrites traffic [@he2025aitm]; and many multi-agent failures are "
      "skipped verification steps and broken role boundaries [@cemri2025mast]. Multi-agent security is now an open "
      "problem of its own [@schroederdewitt2025open,hammond2025multiagent], and it grows with every framework that "
      "wires LLMs to each other (A2A) and to tools (MCP)."),
("p", "These are failures of **communication structure**: who may talk to whom, in what order, carrying what. "
      "Multiparty session types [@honda2008mpst,honda2016mpst] describe exactly this structure, but enforce it by "
      "type-checking every participant's program. An LLM agent has no such program. It samples its next message from "
      "a context an attacker may have poisoned. The classical guarantee therefore does not carry over to LLM agents."),
("p", "**Threat model.** Any agent may be fully controlled by an attacker, any free text may carry an injected "
      "instruction, and the protocol itself may be written by a fallible LLM. The attacker wants concrete harm: run a "
      "non-allowlisted command, pay the wrong payee, mail a secret out, or commit attacker content. We assume that "
      "all inter-agent and tool traffic passes through the gate."),
("p", "**Approach.** SwarmGate keeps the protocol but removes trust in "
      "the agents that run it, in the content they exchange, and in whoever wrote it. Each "
      "step replaces a trusted component with a theorem proved in Lean 4 (Figure 1). Every deployed protocol carries "
      "a certificate the Lean kernel re-checks, and the gate that the theorems describe is the same compiled function "
      "that runs in production."),
("fig", "overview"),
("p", "***Our main contributions are:***"),
("num", [
    "**A verified security boundary for agent swarms.** To our knowledge, the first system that turns a session "
    "protocol into a security policy against fully compromised LLM agents, with enforcement, blame, information-flow "
    "and liveness guarantees mechanised in Lean 4 (2.7k lines, no `sorry`).",
    "**Noninterference with a certified attacker budget.** Uncompromised agents depend on the attacker only through "
    "a declassified channel, for *arbitrary* agent behaviour, and we certify per protocol how many bits it carries.",
    "**Verified admission of LLM-written protocols.** An LLM writes a protocol per task; Lean admits it only within "
    "the deployer's policy, and its counterexamples drive the repair. All 116 admitted protocols carry "
    "kernel-checked certificates.",
    "**GateBench.** A benchmark of 4 domains and 40 tasks with injection, compromised-agent and worst-case "
    "taint-closure threats, run with real Claude agents over A2A-style messaging and MCP tool calls.",
]),

("h2", "2. Related Work"),
("p", "**Session types and monitoring.** Multiparty session types and their mechanisations are mature "
      "[@honda2016mpst,castroperez2021zooid], as are runtime monitoring of session types "
      "[@bocchi2017monitoring,larsen2026nest], blame [@jia2016blame], execution monitors "
      "[@schneider2000enforceable,ligatti2005edit] and information flow, also in multiparty sessions "
      "[@sabelfeld2003language,capecchi2016ifsafety], but all assume that participants are programs rather than adversarial "
      "language models steered by untrusted content."),
("p", "**Protocols for LLM agents** are emerging concurrently: Lean-verified message-sequence-chart workflows "
      "[@bollig2026provable], single-agent typestate via tool masking [@sikaroudi2026concordat], choreographies "
      "[@gopinathan2026pact], BSPL enactment [@joshi2026ahoy] and LLM-synthesised refinements [@li2026syntropy]. They "
      "use protocols for *coordination* among agents assumed to cooperate. **Agent security** defences such as "
      "ControlValve [@jha2026controlvalve], CaMeL [@debenedetti2025camel] and the prompt-injection design patterns "
      "[@beurerkellner2025designpatterns] isolate untrusted data. They give no machine-checked guarantee or "
      "quantitative bound, and they do not check policies generated by an LLM."),
("p", "**What is new.** SwarmGate is the first to combine all three. The protocol acts as a *security policy* against "
      "fully compromised agents, the data plane gets noninterference for arbitrary agents with a certified bit "
      "bound, and LLM-written protocols run only after verified admission. A practitioner would use it whenever a "
      "swarm both reads untrusted content and takes consequential actions, and “the model will probably refuse” is "
      "not an acceptable security argument. For a concrete protocol it gives what was missing before, "
      "namely a proof of which agents the attacker can ever influence and by how many bits."),

("h2", "3. Methods"),
("h3", "3.1 Protocols, the gate and the deployer's interface"),
("p", "A **protocol** names roles (LLM agents, tools, deterministic validators, humans) and fixes how they may "
      "interact. It is written in a small Scribble-like language and compiled to a finite guarded automaton whose "
      "transitions carry sender, recipient, label, payload type and a decidable refinement such as `len <= 200`, "
      "so every check remains decidable [@li2023complete,castroperez2026synthetic]. Each type has a capacity in "
      "bits. An enum of k values carries ⌈log₂ k⌉ bits, and a free-text string is unbounded (example in Appendix B). "
      "Agents never hold references to each other. Each message is an *attempt* sent to the **gate**, which "
      "delivers it and advances the protocol, or rejects it and blames the sender. The gate's decision is the "
      "compiled Lean function `monStep`, served to A2A-style messaging and MCP tool calls (68 µs per message). The "
      "deployer writes only an **interface**, which lists the roles, a *catalog* of allowed message kinds, the untrusted sources, "
      "the *endorsers* (deterministic non-LLM checkers such as an allowlist approver), the sensitive actions, "
      "required properties and a maximum length. A protocol cannot declare its own security metadata."),
("h3", "3.2 Step 1: untrusted agents"),
("thm", "T1 (Enforcement)", "enforcement_adaptive",
 "For every protocol and every adversary, even one controlling all agents and adapting to the gate's verdicts, the "
 "sequence of delivered messages is a run of the protocol."),
("p", "Out-of-order actions (executing before approval), forged labels, impersonation, ill-typed payloads and "
      "replays are therefore impossible. Conformant traffic is never rejected (T2), every rejection names the true "
      "deviator so honest agents are never blamed (T3), and temporal properties such as “no `Exec` unless "
      "`Approved` earlier”, no stuck states and bounded length, checked once, hold on every run (T4, T7)."),
("h3", "3.3 Step 2: untrusted content"),
("p", "A well-typed string can still carry an injected instruction, and an LLM cannot separate data from "
      "instructions. We therefore treat *taint as sticky per agent*. A role that receives high-capacity content derived "
      "from an untrusted source stays tainted, while low-capacity messages (enums, booleans) and endorsers stop the spread."),
("thm", "T5 (Information flow)", "ifc_transfer",
 "If the verified checker accepts a protocol, no tainted role ever performs a sensitive action."),
("thm", "T9 (Noninterference for arbitrary agents)", "noninterference",
 "Let clean agents be arbitrary deterministic functions of what they have seen, and let the attacker control a set "
 "of roles A. If two attackers produce the same declassified channel δ (recipients and labels of A's messages, "
 "payloads only to clean roles), every clean agent sees exactly the same in both runs."),
("thm", "T9b (Attacker bit budget)", "influence_monitor",
 "The attacker's choices along every enforced run that reach clean agents amount to at most B bits, certified per "
 "protocol."),
("p", "T9 needs *no model of LLM behaviour at all*. Whatever the clean models do, they depend on at most B "
      "attacker-chosen bits. This turns the informal quarantined-reader pattern "
      "[@beurerkellner2025designpatterns,debenedetti2025camel] into a machine-checked number for a concrete "
      "protocol."),
("h3", "3.4 Step 3: untrusted protocol authors"),
("p", "A fixed hand-written protocol cannot fit open-ended tasks, so an LLM *architect* writes one per task, before "
      "any untrusted data is read, and only the admission check is trusted."),
("thm", "T8 (Admission)", "admitted_secure",
 "If a protocol from any source is admitted against an interface, then on every run, for every adversary, every "
 "message is an instance of a catalog entry, no tainted role acts, all required properties hold, and the length "
 "bound is respected."),
("p", "Rejections come with a counterexample (an out-of-catalog message, an information-flow path, a violating "
      "trace), which is fed back to the architect for repair (Figure 2), in a counterexample-guided synthesis loop with Lean "
      "as the oracle. Each admitted protocol is emitted as a Lean file whose admission the kernel re-checks."),
("code", "repair"),
("h3", "3.5 GateBench"),
("p", "GateBench has four domains, each with an interface, a *naive* protocol (plausible, but failing the "
      "information-flow check), a *hardened* protocol (admitted), simulated tools, endorsers, 10 tasks and precise "
      "goal detectors: **ops** (a researcher reads untrusted runbooks, an executor runs shell commands), **email** "
      "(an inbox reader, a password-reset code to protect), **finance** (an invoice reader, a clerk paying vendors "
      "via approvers) and **code** (a researcher reads package docs, a coder commits after CI). Every task requires "
      "reading untrusted content. An attack "
      "*succeeds* if a control goal (non-allowlisted command, wrong payee, mail to the attacker, attacker content in "
      "a commit) or a data goal (a secret reaches an attacker-readable sink) is reached. All payloads are inert."),
("p", "**Threats.** *Inject:* untrusted tool output carries one of four injection families. *Compromised:* one LLM "
      "role is replaced by an adaptive attacker that probes every catalog message, impersonates others, mimics "
      "honest traffic and strikes with the most damaging payload the gate accepts. *Taint closure:* the attacker "
      "controls *every* agent that reads attacker-derived text, the worst case T5 and T9 address. **Defenses:** no "
      "gate (free bus), topology ACL (who-may-talk-to-whom), SwarmGate with the naive or hardened protocol, and an "
      "LLM-written protocol either enforced unverified (like ControlValve [@jha2026controlvalve]) or Lean-admitted. "
      "Honest agents get identical tools and hints under every defense, so only enforcement differs."),
("h3", "3.6 Setup"),
("p", "Agents are Claude Haiku 5.5; the architect is Claude Sonnet 5.5 (Haiku and Opus 5.5 as alternatives). "
      "Every configuration runs twice, for 4,080 episodes at about $0.004 each. The unverified ablation gets the same "
      "prompt and interface feedback and lacks only the security check. For robustness we re-ran 2 tasks per domain with "
      "Sonnet 5.5 as every agent (180 episodes). **What did not work:** Claude declined to play the attacker, so it "
      "is scripted (stronger and reproducible); a first random attacker was too weak and was replaced by the "
      "goal-directed one; and kernel re-checking needed structurally recursive checkers."),

("h2", "4. Results"),
("fig", "results"),
("tab", "main"),
("p", "**RQ1: Does the gate contain a compromised agent?** Without mediation, one compromised agent reaches its "
      "goal in 99% of episodes (Figure 3, Table 1). A topology ACL stops a compromised *reader* (17%) but not an "
      "*actor* (99%), since the actor legitimately talks to the sensitive tool. The naive protocol enforces order but "
      "its free-text types still let actors do harm (78%). Typed protocols confine both. Hardened and LLM-written "
      "protocols cut reader attacks to **0%** and overall success to **6–10%** (0% in ops, email and finance). Every "
      "remaining success has the same cause. A compromised coder writes attacker text into the free-text message of its own "
      "commit after CI passed, a field the interface explicitly allows (Section 5)."),
("p", "**RQ2: Does the data plane hold in the worst case?** Indirect injection almost never succeeded (1 of 1,920 "
      "episodes; Claude Haiku 4.5 probe 0 of 48), so today's swarms rely on model robustness that nobody can "
      "certify. Under the taint-closure threat, where every exposed agent obeys the attacker, the naive protocol "
      "fails in 75% and the ACL in 100% of episodes, while with every IFC-verified protocol, hand- or LLM-written, "
      "**no attacker-controlled agent ever performed a sensitive action** (0 of 160), as T5 predicts. The 4 "
      "LLM-written protocols that skipped verification and fail the information-flow check were exploited. In 2 of "
      "their 8 episodes the tainted clerk paid an attacker-chosen vendor and amount."),
("tab", "bits"),
("p", "**RQ3: Can LLMs write admissible protocols?** Every architect produced an admitted protocol for every "
      "task it answered, in 1.4–2.0 repair rounds on average, and all 116 carry certificates the Lean kernel "
      "re-checks in 2 s (Table A2). Without verification, 4 of 40 deployed protocols stayed information-flow-unsafe. Admitted LLM protocols are even *tighter* than "
      "hand-written ones, with about half the certified attacker budget (Table 2), because a per-task protocol needs "
      "fewer free choices. Admission does not, however, guarantee usefulness. Haiku's and Opus's protocols are equally "
      "secure (1% and 3% compromised success, 0% taint closure) but reach different utility (57% vs. 89%)."),
("p", "**RQ4: Does practice stay inside the theory?** In every gated episode we compared the agents that actually "
      "received attacker-marked content with the statically predicted taint set and found **0 violations in 2,720 gated "
      "episodes**. **RQ5: Utility and cost.** Security did not cost utility. Benign success is 79% on a free bus and "
      "**100%** with hardened protocols (86% with admitted LLM protocols), so structure helps agents finish. Synthesis "
      "costs about $0.03 per task, and checking a protocol takes milliseconds."),
("p", "**Robustness.** The 95% Wilson intervals of ungated (96–100%) and gated (3–15%) compromised-agent success do "
      "not overlap (n = 200 per defense), and taint closure is 80/80 against 0/80. With Claude Sonnet 5.5 as every "
      "agent the ordering is unchanged (95% without a gate, 50% with an ACL, 25% with the naive protocol and 10% / 5% "
      "with hardened / admitted protocols). Taint closure falls from 100% to 0%, and 0 of 108 gated episodes left the "
      "predicted taint set. Finally, of 28,561 scripted structural attacks (impersonation, out of order, ill-typed, "
      "replay, ...), a free bus accepts 100%, schema validation 81%, a topology ACL 35% and SwarmGate **0%**."),

("h2", "5. Discussion and Limitations"),
("p", "**Implications for AI safety.** Today the safety of agent swarms rests on each model resisting manipulation. "
      "That held in our injection experiments, but it cannot be certified and may fail with the next model or "
      "attack. SwarmGate moves the guarantee from the models to the structure between them. Once a protocol is "
      "admitted, what any number of compromised or misaligned agents can do is bounded by a proof, and their "
      "influence on the rest of the swarm by a number. The approach scales with the number of agents and needs no insight into "
      "model internals. It also lets AI write its own rules, since each rule is checked. The pattern "
      "of an untrusted generator plus a verified checker applies wherever AI systems propose policies for other AI "
      "systems."),
("h3", "Limitations"),
("p", "Protocols order messages and type their fields, but do not bind the *content* of a free-text field to an "
      "earlier message. This gap accounts for all residual successes in RQ1, and an interface closes it by routing such fields "
      "through an endorser. Endorsers are a trust assumption, and a compromised role keeps the capabilities the "
      "protocol grants it (but no more). The theorems assume complete mediation and authenticated senders. Attacks "
      "outside the gate (tool poisoning, model backdoors) need other defences, and no monitor can guarantee "
      "liveness against a silent agent. Integer capacities ignore refinements (sound but loose: finance's 140 bits). "
      "The step from B bits to 2^B attacker strategies is argued on paper and not yet mechanised. Our attacker is scripted. "
      "A learned attacker might find other paths inside the permitted envelope, though never outside it (T1)."),
("h3", "Future Work"),
("p", "The most direct extension is *content binding* (a field must equal or hash-match an earlier endorsed "
      "message), which removes the residual commit-message attacks. *Refinement-aware capacities* would "
      "substantially shrink finance's 140-bit budget. A further step is deployment in production MCP/A2A stacks against "
      "learned attackers and larger, open-ended task suites."),

("h2", "6. Conclusion"),
("p", "The security of an LLM agent swarm does not have to rest on the agents. SwarmGate trusts only a small "
      "Lean-verified checker and gate, and proves that whatever the agents do, messages follow the protocol, tainted "
      "agents cannot act, and clean agents see at most B attacker-chosen bits, even when an LLM wrote the protocol. "
      "With real Claude agents this cuts a compromised agent's success from 99% to 0% in three of four domains (the "
      "rest only through a free-text field the interface allows) and the worst-case attack from up to 100% to 0%, at no utility cost, with every observed infection inside the predicted set. In the "
      "resulting division of labour, LLMs write the protocols and a proof decides which ones "
      "may run."),
]

CODE_AND_DATA = [
    ("Code repository", "https://github.com/timwuerfl/agent-comms-type-check",
     " (Lean proofs, Python runtime, MCP/A2A gateway, GateBench, synthesis loop, paper sources; `reproduce.sh` "
     "re-runs all offline experiments)."),
    ("Data", None, " all episode logs, synthesised protocols, kernel certificates and the API cost ledger are in "
     "`eval/results/` of the repository."),
    ("Info-hazard note", None, " all attacker payloads in GateBench are inert placeholders (fake commands, "
     "example.com addresses, fake tokens); no functional exploits are included."),
]

ETHICS = [
    "SwarmGate is a defensive technology. It restricts what LLM agents can do and keeps their failures contained "
    "and attributable. The work involves no human subjects and no personal data; all tools, inboxes, invoices and "
    "repositories in GateBench are simulated, and every secret is a fake placeholder.",
    "**Dual use.** GateBench contains attack scenarios and a scripted adaptive attacker. Its techniques (message "
    "spraying, impersonation, mimicking honest traffic) are well known from prior multi-agent security work, and all "
    "payloads are inert placeholders without functional exploit strings, so the benchmark gives attackers little "
    "uplift while letting defenders measure their systems. We did not try to circumvent model safeguards. When "
    "Claude declined to play the attacker, we scripted the attacker instead, and the synthesis tasks Opus refused are "
    "reported as refusals.",
    "**Risk of over-reliance.** The main risk is a false sense of security. Our guarantees hold only under the stated "
    "assumptions (complete mediation, authenticated senders, trusted endorsers and a correct deployer interface), and "
    "they bound where content flows rather than what it means. Deployers should treat an admitted protocol as one "
    "verified layer of defence in depth and keep model-level safeguards, monitoring and human "
    "oversight of high-stakes actions in place.",
]

LLM_STATEMENT = ("We used Claude for implementation support and drafting. All results were verified. Every number "
                 "in this report comes from logged, reproducible runs in the repository, and all theorems are "
                 "checked by the Lean kernel.")

APPENDIX = [
("h3", "A. Theorem overview"),
("tab", "theorems"),
("h3", "B. Example protocol and the gate"),
("code", "dsl"),
("code", "gate"),
("h3", "C. Protocol synthesis and per-domain results"),
("tab", "synth"),
("tab", "perdomain"),
("p", "Residual successes under hardened and admitted protocols occur only in the code domain (commit-message "
      "content, see Limitations), while ops, email and finance reach 0% for both."),
("h3", "D. Architect prompt (excerpt)"),
("code", "prompt"),
]
