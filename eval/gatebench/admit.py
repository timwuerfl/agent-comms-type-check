"""Python front-end to the verified admission check (`swarmgate admit`, Theorem T8)."""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "python"))

from swarmgate.gate import find_binary  # noqa: E402
from swarmgate.interface import Interface  # noqa: E402
from swarmgate.protocol import Protocol  # noqa: E402


def admit(I: Interface, P: Protocol) -> dict:
    """P must already be bound to I (``I.bind``). Returns the JSON admission report."""
    with tempfile.TemporaryDirectory() as d:
        pol, prot = os.path.join(d, "policy.json"), os.path.join(d, "protocol.json")
        with open(pol, "w") as f:
            json.dump(I.to_json(), f)
        with open(prot, "w") as f:
            f.write(P.dumps())
        out = subprocess.run([find_binary(), "admit", pol, prot], capture_output=True, text=True, timeout=600)
        if out.returncode != 0:
            raise RuntimeError(out.stderr[-1000:])
        return json.loads(out.stdout)


def feedback(report: dict) -> str:
    """Human/LLM-readable rejection reasons with counterexamples (for counterexample-guided repair)."""
    msgs = []

    def trace(path):
        return " -> ".join(f"{e['src']}→{e['dst']}:{e['label']}" for e in (path or [])) or "(start)"
    if not report["roles"]["ok"]:
        msgs.append("The protocol must use only the interface's roles.")
    c = report["catalog"]
    if not c["ok"] and c["counterexample"]:
        n = c["counterexample"]["notInCatalog"] or {}
        msgs.append(f"CAPABILITY VIOLATION: after {trace(c['counterexample']['path'])}, the message "
                    f"{n.get('src')} -> {n.get('dst')} : {n.get('label')} (type {n.get('ty')}, refinement "
                    f"{n.get('pred')}) is not an allowed message kind. Use exactly a message kind listed in the "
                    f"interface (same sender, receiver, label and type; keep its `where` refinement or a stronger one "
                    f"of the form `<catalog refinement> and <extra>`).")
    f = report["ifc"]
    if not f["ok"] and f["counterexample"]:
        cx = f["counterexample"]
        th = cx.get("then") or {}
        msgs.append(f"INFORMATION-FLOW VIOLATION: after {trace(cx['path'])}, the roles "
                    f"{', '.join(cx.get('taintedRoles', []))} may carry attacker-controlled text, and then "
                    f"{th.get('src')} could perform the sensitive action {th.get('src')} -> {th.get('dst')} : "
                    f"{th.get('label')}. Untrusted content must only reach the role that performs a sensitive action "
                    f"through low-capacity messages (enums/bools) or via an endorser.")
    for p in report["properties"]:
        if not p["ok"]:
            msgs.append(f"PROPERTY VIOLATION ({p['name']}): counterexample trace {trace(p['counterexample'])}.")
    b = report["bound"]
    if not b["ok"]:
        msgs.append(f"LENGTH VIOLATION: sessions must provably deliver at most {b['maxLen']} messages; this protocol: "
                    f"{b['protocolMax']}. Use bounded loops `rec X max k {{ ... }}`.")
    if not report["wellFormed"]["ok"]:
        msgs.append("WELL-FORMEDNESS: " + "; ".join(report["wellFormed"]["issues"][:5]))
    return "\n".join(msgs) if msgs else "admitted"
