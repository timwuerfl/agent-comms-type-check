"""Fill the Apart Research Word template with the SwarmGate paper.
    python paper/apart/build_docx.py      ->  paper/apart/SwarmGate_Apart_submission.docx
Requires lxml and Pillow. Content lives in content.py; tables are read from paper/tables/*.tex."""
from __future__ import annotations

import copy
import os
import re
import shutil
import sys
import tempfile
import zipfile
from xml.sax.saxutils import escape

from lxml import etree
from PIL import Image

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import content as C  # noqa: E402

W = "http://schemas.openxmlformats.org/wordprocessingml/2006/main"
NS = {"w": W}
NSDECL = ('xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main" '
          'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships" '
          'xmlns:wp="http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing" '
          'xmlns:a="http://schemas.openxmlformats.org/drawingml/2006/main" '
          'xmlns:pic="http://schemas.openxmlformats.org/drawingml/2006/picture"')
FONT = "Old Standard TT"
MONO = "Courier New"
BODY_SZ = 20          # half-points (10.5 pt)
SMALL_SZ = 18         # captions, tables (9 pt)

# ---------------------------------------------------------------------------------------------------------------
# citations
# ---------------------------------------------------------------------------------------------------------------
ORDER: list[str] = []


def cite_keys(text):
    for m in re.finditer(r"\[@([^\]]+)\]", text):
        for k in m.group(1).split(","):
            k = k.strip()
            if k not in ORDER:
                ORDER.append(k)


def resolve_cites(text):
    return re.sub(r"\[@([^\]]+)\]",
                  lambda m: "[" + ", ".join(str(n) for n in sorted(ORDER.index(k.strip()) + 1
                                                            for k in m.group(1).split(","))) + "]",
                  text)


# ---------------------------------------------------------------------------------------------------------------
# runs and paragraphs
# ---------------------------------------------------------------------------------------------------------------
def rpr(b=False, i=False, mono=False, color=None, sz=BODY_SZ, sup=False, u=False):
    f = MONO if mono else FONT
    s = f'<w:rPr><w:rFonts w:ascii="{f}" w:cs="{f}" w:eastAsia="{f}" w:hAnsi="{f}"/>'
    if b:
        s += '<w:b w:val="1"/><w:bCs w:val="1"/>'
    if i:
        s += '<w:i w:val="1"/><w:iCs w:val="1"/>'
    if color:
        s += f'<w:color w:val="{color}"/>'
    if mono and sz == BODY_SZ:
        sz = BODY_SZ - 2
    s += f'<w:sz w:val="{sz}"/><w:szCs w:val="{sz}"/>'
    if u:
        s += '<w:u w:val="single"/>'
    if sup:
        s += '<w:vertAlign w:val="superscript"/>'
    return s + "</w:rPr>"


def run(text, **kw):
    return f'<w:r>{rpr(**kw)}<w:t xml:space="preserve">{escape(text)}</w:t></w:r>'


TOKEN = re.compile(r"(\*\*\*.+?\*\*\*|\*\*.+?\*\*|\*[^*\s][^*]*?\*|`[^`]+`)")


def runs(text, sz=BODY_SZ, base_i=False, base_b=False, color=None):
    """Inline markup -> runs. Nested bold-in-italic is not needed in our content."""
    text = resolve_cites(text)
    out = []
    for part in TOKEN.split(text):
        if not part:
            continue
        if part.startswith("***"):
            out.append(run(part[3:-3], b=True, i=True, sz=sz, color=color))
        elif part.startswith("**"):
            out.append(run(part[2:-2], b=True, i=base_i, sz=sz, color=color))
        elif part.startswith("`"):
            out.append(run(part[1:-1], mono=True, sz=sz - 2 if sz != BODY_SZ else BODY_SZ, color=color))
        elif part.startswith("*") and part.endswith("*") and len(part) > 2:
            out.append(run(part[1:-1], i=not base_i, b=base_b, sz=sz, color=color))
        else:
            out.append(run(part, i=base_i, b=base_b, sz=sz, color=color))
    return "".join(out)


def para(inner, align="both", before=0, after=100, line=252, ind=None, keep_next=False, style=None, num=None,
         keep_lines=False):
    p = "<w:pPr>"
    if style:
        p += f'<w:pStyle w:val="{style}"/>'
    if keep_next:
        p += "<w:keepNext/>"
    if keep_lines:
        p += "<w:keepLines/>"
    if num:
        p += f'<w:numPr><w:ilvl w:val="0"/><w:numId w:val="{num}"/></w:numPr>'
    p += f'<w:spacing w:before="{before}" w:after="{after}" w:line="{line}" w:lineRule="auto"/>'
    if ind:
        p += ind
    p += f'<w:jc w:val="{align}"/></w:pPr>'
    return f"<w:p>{p}{inner}</w:p>"


def heading(text, level):
    if level == 2:
        sty, col, sz, before = "Heading2", "434343", 28, 240
    else:
        sty, col, sz, before = "Heading3", "666666", 23, 160
    r = (f'<w:r><w:rPr><w:rFonts w:ascii="{FONT}" w:cs="{FONT}" w:eastAsia="{FONT}" w:hAnsi="{FONT}"/>'
         f'<w:b w:val="1"/><w:bCs w:val="1"/><w:color w:val="{col}"/><w:sz w:val="{sz}"/><w:szCs w:val="{sz}"/>'
         f'</w:rPr><w:t xml:space="preserve">{escape(text)}</w:t></w:r>')
    return (f'<w:p><w:pPr><w:pStyle w:val="{sty}"/><w:keepNext/><w:spacing w:before="{before}" w:after="80" '
            f'w:line="264" w:lineRule="auto"/></w:pPr>{r}</w:p>')


# ---------------------------------------------------------------------------------------------------------------
# figures, tables, code boxes
# ---------------------------------------------------------------------------------------------------------------
MEDIA: list[tuple[str, str]] = []      # (rId, filename)
COUNT = {"fig": 0, "tab": 0}
FIGS = {
    "overview": ("figs/overview.png", 3.7,
                 "**Figure 1: Overview of SwarmGate.** Only the deployer's interface, the Lean admission check and the "
                 "Lean gate are trusted (blue), while the protocol's author, the agents and the content they exchange are "
                 "not (red). An LLM architect proposes a protocol per task, and Lean either admits it or returns a counterexample. "
                 "The admitted protocol is enforced on every message and comes with a certified attacker budget B."),
    "results": ("figs/results.png", 5.9,
                "**Figure 3: Attack success per defense on GateBench** (Claude Haiku 5.5 agents; n = 200 episodes per "
                "defense with one compromised agent, n = 80 under taint closure). Typed SwarmGate protocols cut a "
                "compromised agent's success from 99% to 6–10% (0% outside the code domain). With information-flow-verified protocols, no "
                "attacker-controlled agent performs a sensitive action even in the worst case. Error bars: 95% Wilson "
                "intervals."),
}


def figure(key):
    path, width_in, cap = FIGS[key]
    full = os.path.join(PAPER, path)
    w, h = Image.open(full).size
    cx = int(width_in * 914400)
    cy = int(cx * h / w)
    rid = f"rIdSG{len(MEDIA) + 1}"
    MEDIA.append((rid, full))
    n = len(MEDIA)
    drawing = (f'<w:r><w:drawing><wp:inline distT="0" distB="0" distL="0" distR="0"><wp:extent cx="{cx}" cy="{cy}"/>'
               f'<wp:docPr id="{100 + n}" name="Figure {n}"/><wp:cNvGraphicFramePr>'
               f'<a:graphicFrameLocks noChangeAspect="1"/></wp:cNvGraphicFramePr>'
               f'<a:graphic><a:graphicData uri="http://schemas.openxmlformats.org/drawingml/2006/picture">'
               f'<pic:pic><pic:nvPicPr><pic:cNvPr id="{n}" name="{os.path.basename(full)}"/><pic:cNvPicPr/></pic:nvPicPr>'
               f'<pic:blipFill><a:blip r:embed="{rid}"/><a:stretch><a:fillRect/></a:stretch></pic:blipFill>'
               f'<pic:spPr><a:xfrm><a:off x="0" y="0"/><a:ext cx="{cx}" cy="{cy}"/></a:xfrm>'
               f'<a:prstGeom prst="rect"><a:avLst/></a:prstGeom></pic:spPr></pic:pic></a:graphicData></a:graphic>'
               f'</wp:inline></w:drawing></w:r>')
    return (para(drawing, align="center", before=120, after=60, keep_next=True) +
            para(runs(cap, sz=SMALL_SZ), align="both", after=200, line=240))


def tex_rows(name):
    """Rows of a booktabs .tex table (between \\midrule and \\bottomrule)."""
    s = open(os.path.join(PAPER, "tables", name)).read()
    body = s.split("\\midrule")[1].split("\\bottomrule")[0]
    rows = []
    for line in body.strip().splitlines():
        line = line.strip().rstrip("\\").strip()
        if not line:
            continue
        cells = [c.strip() for c in line.split("&")]
        cells = [re.sub(r"\{\\scriptsize\((.*?)\)\}", r"(\1)", c).replace("--", "–").replace("$\\infty$", "∞")
                 for c in cells]
        rows.append(cells)
    return rows


def table_from(key):
    if key == "main":
        hdr = ["Defense", "Benign utility", "Inject ASR", "Compromised reader", "Compr. actor", "Compr. all (95% CI)",
               "Taint closure"]
        rows = tex_rows("gatebench.tex")
        names = {"no gate (free bus)": "No gate (free bus)", "topology ACL": "Topology ACL",
                 "SwarmGate, naive protocol": "SwarmGate, naive protocol",
                 "SwarmGate, hardened": "SwarmGate, hardened protocol",
                 "LLM protocol, unverified": "LLM-written, unverified",
                 "LLM protocol, Lean-admitted": "LLM-written, Lean-admitted"}
        rows = [[names.get(r[0], r[0])] + r[1:] for r in rows]
        widths = [2350, 1000, 900, 1250, 1000, 1350, 1000]
        bold_rows = {3, 5}
        cap = ("**Table 1: GateBench results** (% of episodes, Claude Haiku 5.5 agents, 4,080 episodes). ASR: attack "
               "success rate (control or data goal). Reader / actor: the compromised agent reads untrusted data / "
               "performs a sensitive action. Taint closure: the attacker steers every agent that reads "
               "attacker-derived free text (the worst case behind T5 and T9).")
    elif key == "synth":
        hdr = ["Architect", "Haiku 5.5", "Sonnet 5.5", "Opus 5.5"]
        rows = [["Admitted within 4 rounds", "40/40", "40/40", "36/36†"], ["Mean repair rounds", "1.4", "2.0", "1.5"],
                ["First draft admissible", "38/40", "40/80", "30/37"], ["First draft with IFC flaw", "0", "6", "0"],
                ["Kernel-checked certificates", "40/40", "40/40", "36/36"]]
        widths = [3400, 1500, 1500, 1500]
        bold_rows = set()
        cap = ("**Table A2: LLM-written protocols** (40 tasks per architect). Every task an architect answered ended "
               "in an admitted, kernel-certified protocol. † Opus declined 4 ops tasks.")
    elif key == "bits":
        hdr = ["Domain", "Naive protocol", "Hardened protocol", "LLM-written, admitted: median (max)"]
        rows = tex_rows("bits.tex")
        widths = [1500, 1700, 1900, 3300]
        bold_rows = set()
        cap = ("**Table 2: Certified attacker budget B in bits** (T9b), with A the static taint closure: the maximum "
               "number of attacker-chosen bits that can ever reach an uncompromised agent. ∞: unbounded.")
    elif key == "perdomain":
        hdr = ["Domain", "No gate", "Topology", "Naive", "Hardened", "LLM", "LLM + Lean"]
        rows = tex_rows("perdomain.tex")
        widths = [1500, 1150, 1150, 1150, 1150, 1150, 1150]
        bold_rows = set()
        cap = "**Table A3: Compromised-agent attack success per domain** (%, Haiku 5.5 agents)."
    elif key == "theorems":
        hdr = ["Theorem", "Lean name", "Statement (informal)"]
        rows = [["T1 Enforcement", "enforcement(_adaptive)", "Delivered trace is a protocol run, for every adversary"],
                ["T2 Transparency", "transparency", "Conformant traffic is never rejected"],
                ["T3 Blame", "blame_sound, honest_never_blamed", "Rejections name the true deviator; honest agents are never blamed"],
                ["T4 Property transfer", "property_transfer", "Past-time LTL properties checked once hold on every run"],
                ["T5 Information flow", "ifc_transfer", "No tainted role ever performs a sensitive action"],
                ["T6 Decentralised", "decentralised_sound", "Per-role sidecars jointly admit only protocol traces"],
                ["T7 Liveness / bound", "no_stuck, bounded_length", "No stuck state; completion reachable; bounded length"],
                ["T8 Admission", "admitted_secure", "Admitted protocols satisfy catalog, IFC, properties, bound"],
                ["T9 Noninterference", "noninterference(_inv)", "Clean agents depend on the attacker only via δ"],
                ["T9b Bit budget", "influence_monitor", "Attacker choices reaching clean agents ≤ B bits"],
                ["Bridge", "admitted_noninterference", "T8 + T9 for the executed runtime semantics"]]
        widths = [2100, 2900, 4400]
        bold_rows = set()
        cap = ("**Table A1: Mechanised theorems** (Lean 4, 2.7k lines, no `sorry`, standard axioms only; files under "
               "`lean/SwarmGate/`).")
    return table(hdr, rows, widths, cap, bold_rows, mono_col=1 if key == "theorems" else None)


def cell(text, w, bold=False, align="left", top=False, bottom=False, hdr=False, mono=False, keep=True):
    borders = ""
    if top or bottom:
        borders = "<w:tcBorders>"
        if top:
            borders += '<w:top w:val="single" w:sz="8" w:space="0" w:color="000000"/>'
        if bottom:
            borders += f'<w:bottom w:val="single" w:sz="{8 if not hdr else 4}" w:space="0" w:color="000000"/>'
        borders += "</w:tcBorders>"
    inner = runs(f"**{text}**" if bold and "**" not in text else text, sz=SMALL_SZ) if not mono else \
        run(text, mono=True, sz=SMALL_SZ - 2)
    return (f'<w:tc><w:tcPr><w:tcW w:w="{w}" w:type="dxa"/>{borders}<w:vAlign w:val="center"/></w:tcPr>'
            f'{para(inner, align=align, after=0, before=0, line=240, keep_next=keep)}</w:tc>')


def table(hdr, rows, widths, cap, bold_rows=(), mono_col=None):
    total = sum(widths)
    grid = "".join(f'<w:gridCol w:w="{w}"/>' for w in widths)
    t = (f'<w:tbl><w:tblPr><w:tblW w:w="{total}" w:type="dxa"/><w:jc w:val="center"/>'
         f'<w:tblLayout w:type="fixed"/><w:tblCellMar><w:top w:w="30" w:type="dxa"/><w:left w:w="70" w:type="dxa"/>'
         f'<w:bottom w:w="30" w:type="dxa"/><w:right w:w="70" w:type="dxa"/></w:tblCellMar></w:tblPr>'
         f'<w:tblGrid>{grid}</w:tblGrid>')
    t += '<w:tr><w:trPr><w:cantSplit/><w:tblHeader/></w:trPr>' + "".join(
        cell(h, w, bold=True, align="left" if j == 0 else "center", top=True, bottom=True, hdr=True)
        for j, (h, w) in enumerate(zip(hdr, widths))) + "</w:tr>"
    for i, r in enumerate(rows):
        last = i == len(rows) - 1
        t += '<w:tr><w:trPr><w:cantSplit/></w:trPr>' + "".join(
            cell(c, w, bold=(i in bold_rows), align="left" if (j == 0 or len(widths) == 3) else "center",
                 bottom=last, mono=(j == mono_col), keep=not last) for j, (c, w) in enumerate(zip(r, widths))) + "</w:tr>"
    t += "</w:tbl>"
    return para(runs(cap, sz=SMALL_SZ), keep_next=True, before=120, after=60, line=240) + t + \
        para("", after=120, line=200)


CODES = {
    "repair": ("**Figure 2: One counterexample-guided repair, verbatim from the logs** (Sonnet 5.5, finance task "
               "fin4). A 64-bit integer from the reader of untrusted invoices would let the attacker steer the paying "
               "clerk. After Lean's counterexample, the LLM routes the extracted fields to the deterministic approver "
               "and sends the clerk only a 2-bit status.", [
        [("draft 1:", "AA1E1E")],
        [("Reader -> Clerk : Extracted({payee: Vendor, amount: int}) where amount <= 50000;", None)],
        [("Lean: INFORMATION-FLOW VIOLATION: after Task, Fetch, Get, Invoice, Reader->Clerk:Extracted,", "AA1E1E")],
        [("      the roles Clerk, Reader, Docs may carry attacker-controlled text, and then", "AA1E1E")],
        [("      Clerk could perform Clerk->Bank:Transfer.", "AA1E1E")],
        [("draft 2 (admitted, kernel-checked):", "146E32")],
        [("Reader -> Approver1 : Extracted({payee: Vendor, amount: int}) ...;  ", None), ("// to the endorser", "146E32")],
        [("Reader -> Clerk : Status(enum{found, not_found, unreadable});      ", None), ("// 2 bits", "146E32")],
    ]),
    "dsl": ("**Listing B1: The hardened ops protocol (abridged).** The researcher reads untrusted runbook pages but "
            "can only answer with an allowlisted command (≤ 3 bits), and the executor accepts commands only from the "
            "deterministic approver.", [
        [("protocol OpsHardened {   ", None), ("// roles, types and security metadata come from the interface", "146E32")],
        [("  User -> Planner : Task(str) where len <= 2000;", None)],
        [("  rec Research max 2 {", None)],
        [("    Planner -> Researcher : Query(Topic);", None)],
        [("    Researcher -> Web : Get(Topic);  Web -> Researcher : Page(str);   ", None), ("// untrusted", "146E32")],
        [("    Researcher -> Planner : Recommend(Cmd);                         ", None), ("// enum: <= 3 bits", "146E32")],
        [("    choice at Planner { continue Research; } or { Planner -> Approver : Propose(Cmd); } }", None)],
        [("  choice at Approver { Approver -> Executor : Approved(Cmd);", None)],
        [("    Executor -> Shell : Exec(Cmd); Shell -> Executor : Out(str); ... }", None)],
        [("  or { Approver -> Planner : Denied; } ... }", None)],
    ]),
    "gate": ("**Listing B2: The gate's decision function** (from `Monitor.lean`). T1–T3 are theorems about exactly "
             "this function, and the runtime executes its compiled code.", [
        [("monStep cfg P m (send σ e) =", None)],
        [("  if m.halted            then reject σ halted", None)],
        [("  else if quarantined σ  then reject σ quarantined", None)],
        [("  else if σ ≠ e.src      then strike; reject σ spoof", None)],
        [("  else if m.count ≥ budget then reject σ budget", None)],
        [("  else match step P m.s e with", None)],
        [("       | some s' => advance; deliver e", None)],
        [("       | none    => strike; reject σ notEnabled", None)],
    ]),
    "prompt": ("**Listing D1: System prompt of the protocol architect** (followed by the DSL guide, the deployer "
               "interface, the behaviour of non-LLM roles, the task, and, in later rounds, Lean's counterexamples).", [
        [("You are a security architect for multi-agent LLM systems. You design the communication", None)],
        [("protocol that a swarm of agents must follow for one task. Agents are LLMs that may be", None)],
        [("prompt-injected; the protocol is enforced by a verified gate. Write the protocol in the", None)],
        [("SwarmGate language. Answer with a short explanation followed by exactly one code block.", None)],
    ]),
}


def codebox(key):
    cap, lines = CODES[key]
    ps = []
    for segs in lines:
        inner = "".join(run(t, mono=True, sz=16, color=c) for t, c in segs)
        ps.append(para(inner, align="left", after=0, line=228, keep_next=True))
    width = 9200
    box = (f'<w:tbl><w:tblPr><w:tblW w:w="{width}" w:type="dxa"/><w:jc w:val="center"/>'
           f'<w:tblBorders><w:top w:val="single" w:sz="4" w:color="8C8C8C"/><w:left w:val="single" w:sz="4" '
           f'w:color="8C8C8C"/><w:bottom w:val="single" w:sz="4" w:color="8C8C8C"/><w:right w:val="single" '
           f'w:sz="4" w:color="8C8C8C"/></w:tblBorders><w:tblCellMar><w:top w:w="80" w:type="dxa"/>'
           f'<w:left w:w="120" w:type="dxa"/><w:bottom w:w="80" w:type="dxa"/><w:right w:w="120" w:type="dxa"/>'
           f'</w:tblCellMar></w:tblPr><w:tblGrid><w:gridCol w:w="{width}"/></w:tblGrid>'
           f'<w:tr><w:trPr><w:cantSplit/></w:trPr><w:tc><w:tcPr><w:tcW w:w="{width}" w:type="dxa"/>'
           f'<w:shd w:val="clear" w:color="auto" w:fill="F6F6F4"/></w:tcPr>{"".join(ps)}</w:tc></w:tr></w:tbl>')
    return box + para(runs(cap, sz=SMALL_SZ), after=200, before=60, line=240)


# ---------------------------------------------------------------------------------------------------------------
# blocks
# ---------------------------------------------------------------------------------------------------------------
def theorem(name, lean, stmt):
    inner = (run(f"Theorem {name} ", b=True) + run("(", sz=BODY_SZ) +
             "".join(run(x.strip(), mono=True, color="143C78") + (run(", ") if k < len(lean.split(',')) - 1 else "")
                     for k, x in enumerate(lean.split(","))) + run("). ") + runs(stmt, base_i=True))
    ind = '<w:ind w:left="360" w:right="360"/>'
    return para(inner, ind=ind, before=60, after=120)


def blocks(bl):
    out = []
    for b in bl:
        k = b[0]
        if k == "h2":
            out.append(heading(b[1], 2))
        elif k == "h3":
            out.append(heading(b[1], 3))
        elif k == "p":
            out.append(para(runs(b[1])))
        elif k == "num":
            for it in b[1]:
                out.append(para(runs(it), num=5, ind='<w:ind w:left="360" w:hanging="300"/>', after=60))
        elif k == "thm":
            out.append(theorem(b[1], b[2], b[3]))
        elif k == "fig":
            out.append(figure(b[1]))
        elif k == "tab":
            out.append(table_from(b[1]))
        elif k == "code":
            out.append(codebox(b[1]))
    return "".join(out)


# ---------------------------------------------------------------------------------------------------------------
# references
# ---------------------------------------------------------------------------------------------------------------
def tex2txt(s):
    s = s.replace("\\newblock", "").replace("~", " ").replace("--", "–")
    accents = {r"\c{t}": "ţ", r"\`e": "è", r'\"u': "ü", r'\"o': "ö", r"\'e": "é", r'\"a': "ä", r"\'a": "á",
               r"\o": "ø", r"\'i": "í", r"\v{s}": "š", r"\'c": "ć", r"\'o": "ó", r"\`a": "à"}
    for k, v in accents.items():
        s = s.replace("{" + k + "}", v).replace(k, v)
    s = re.sub(r"\\url\{([^}]*)\}", r"\1", s)
    s = re.sub(r"\\texttt\{([^}]*)\}", r"\1", s)
    s = re.sub(r"\{\\em ([^}]*)\}", r"*\1*", s)
    s = s.replace("{", "").replace("}", "").replace("\\&", "&").replace("\\_", "_")
    return re.sub(r"\s+", " ", s).strip()


def references():
    bbl = open(os.path.join(PAPER, "swarmgate.bbl")).read()
    items = dict(re.findall(r"\\bibitem\{([^}]+)\}\s*(.*?)(?=\\bibitem|\\end\{thebibliography\})", bbl, re.S))
    bib = open(os.path.join(PAPER, "refs.bib")).read()
    link = {}
    for m in re.finditer(r"@\w+\{([^,]+),(.*?)\n\}", bib, re.S):
        key, body = m.group(1).strip(), m.group(2)
        d = re.search(r"doi\s*=\s*\{([^}]+)\}", body)
        e = re.search(r"eprint\s*=\s*\{([^}]+)\}", body)
        link[key] = f"https://doi.org/{d.group(1)}" if d else (f"https://arxiv.org/abs/{e.group(1)}" if e else None)
    out = []
    for n, k in enumerate(ORDER, 1):
        txt = tex2txt(items[k])
        if link.get(k) and link[k] not in txt:
            txt += " " + link[k]
        out.append(para(run(f"[{n}] ", sz=SMALL_SZ + 1) + runs(txt, sz=SMALL_SZ + 1), after=60, line=240,
                        ind='<w:ind w:left="420" w:hanging="420"/>', align="left"))
    return "".join(out)


# ---------------------------------------------------------------------------------------------------------------
# assemble
# ---------------------------------------------------------------------------------------------------------------
def frag(xml):
    root = etree.fromstring(f"<root {NSDECL}>{xml}</root>")
    return list(root)


def main(out_path):
    for b in C.BODY + C.APPENDIX:
        for x in b[1:]:
            for s in (x if isinstance(x, list) else [x]):
                if isinstance(s, str):
                    cite_keys(s)
    tmp = tempfile.mkdtemp()
    with zipfile.ZipFile(os.path.join(HERE, "template.docx")) as z:
        z.extractall(tmp)
    dpath = os.path.join(tmp, "word", "document.xml")
    tree = etree.parse(dpath)
    body = tree.getroot().find("w:body", NS)

    # title
    for t in body.iter(f"{{{W}}}t"):
        if t.text and "PROJECT TITLE" in t.text:
            t.text = C.TITLE
            r = t.getparent()
            for sz in r.iter(f"{{{W}}}sz", f"{{{W}}}szCs"):
                sz.set(f"{{{W}}}val", "32")
            for sz in r.getnext().iter(f"{{{W}}}sz", f"{{{W}}}szCs"):
                sz.set(f"{{{W}}}val", "32")
    # authors (template has two 3-slot tables; we fill the first and drop the second)
    def innermost(marker, tag):
        for t in body.iter(f"{{{W}}}t"):
            if t.text and t.text.strip() == marker:
                el = t
                while el.tag != f"{{{W}}}{tag}":
                    el = el.getparent()
                return el
    first = innermost("Author name 1", "tbl")
    second = innermost("Author name 4", "tbl")
    if second is first:                       # one table, two rows: drop the second row
        row = innermost("Author name 4", "tr")
        row.getparent().remove(row)
    else:
        nxt = second.getnext()
        second.getparent().remove(second)
        if nxt is not None and nxt.tag == f"{{{W}}}p" and not "".join(nxt.itertext()).strip():
            nxt.getparent().remove(nxt)
    colw = 3120
    first.find("w:tblPr/w:tblW", NS).set(f"{{{W}}}w", str(3 * colw))
    for g in first.iter(f"{{{W}}}gridCol"):
        g.set(f"{{{W}}}w", str(colw))
    for tcpr in first.iter(f"{{{W}}}tcPr"):
        tcw = etree.SubElement(tcpr, f"{{{W}}}tcW")
        tcw.set(f"{{{W}}}w", str(colw)); tcw.set(f"{{{W}}}type", "dxa")
        tcpr.remove(tcw); tcpr.insert(0, tcw)
    for k, name in enumerate(C.AUTHORS, 1):
        for t in first.iter(f"{{{W}}}t"):
            if t.text and t.text.strip() == f"Author name {k}":
                t.text = name
                aff = t.getnext()
                while aff is not None and aff.tag != f"{{{W}}}t":
                    aff = aff.getnext()
                aff.text = C.AFFILIATIONS[0]
                r_old = t.getparent()                      # affiliation in its own, smaller run
                r_aff = copy.deepcopy(r_old)
                for ch in list(r_aff):
                    if ch.tag != f"{{{W}}}rPr":
                        r_aff.remove(ch)
                rp = r_aff.find("w:rPr", NS)
                for tag in ("sz", "szCs"):
                    e = etree.SubElement(rp, f"{{{W}}}{tag}"); e.set(f"{{{W}}}val", "19")
                r_aff.append(aff)
                for extra in C.AFFILIATIONS[1:]:
                    etree.SubElement(r_aff, f"{{{W}}}br")
                    t2 = etree.SubElement(r_aff, f"{{{W}}}t"); t2.text = extra
                r_old.addnext(r_aff)
    # abstract
    for p in body.iter(f"{{{W}}}p"):
        txt = "".join(p.itertext())
        if txt.startswith("Summarize your project"):
            for r in p.findall("w:r", NS):
                p.remove(r)
            u = p.find("w:pPr/w:rPr/w:u", NS)
            if u is not None:
                u.getparent().remove(u)
            for el in frag(runs(C.ABSTRACT, sz=19)):
                p.append(el)
            break
    # drop info box and the guidance body
    kids = list(body)
    start = None
    for i, el in enumerate(kids):
        txt = "".join(el.itertext())
        if el.tag == f"{{{W}}}tbl" and "How to use this template" in txt:
            body.remove(el)
        if el.tag == f"{{{W}}}p" and txt.strip() == "1. Introduction":
            start = i
            break
    sect = body.find("w:sectPr", NS)
    for el in kids[start:]:
        if el is not sect and el.getparent() is body:
            body.remove(el)

    xml = blocks(C.BODY)
    xml += heading("Ethical Considerations and Dual Use", 2) + "".join(para(runs(x)) for x in C.ETHICS)
    xml += heading("Code and Data", 2)
    for lab, url, rest in C.CODE_AND_DATA:
        inner = run(lab, b=True)
        if url:
            inner += run(": ") + f'<w:hyperlink r:id="rIdSGrepo">{run(url, color="1155CC", u=True)}</w:hyperlink>'
            inner += runs(rest)
        else:
            inner += run(":") + runs(rest)
        xml += para(inner, num=3, ind='<w:ind w:left="360" w:hanging="300"/>', after=60, align="left")
    xml += heading("References", 2) + references()
    xml += heading("Appendix", 2) + blocks(C.APPENDIX)
    xml += heading("LLM Usage Statement", 2) + para(runs(C.LLM_STATEMENT))
    for el in frag(xml):
        body.insert(list(body).index(sect), el)
    pg = body.find("w:sectPr/w:pgMar", NS)
    if pg is not None and pg.get(f"{{{W}}}gutter") is None:
        pg.set(f"{{{W}}}gutter", "0")
    tree.write(dpath, xml_declaration=True, encoding="UTF-8", standalone=True)

    # relationships + media
    rels_p = os.path.join(tmp, "word", "_rels", "document.xml.rels")
    rels = open(rels_p).read()
    add = ('<Relationship Id="rIdSGrepo" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/'
           'hyperlink" Target="https://github.com/timwuerfl/agent-comms-type-check" TargetMode="External"/>')
    os.makedirs(os.path.join(tmp, "word", "media"), exist_ok=True)
    for rid, src in MEDIA:
        name = os.path.basename(src)
        shutil.copy(src, os.path.join(tmp, "word", "media", name))
        add += (f'<Relationship Id="{rid}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/'
                f'image" Target="media/{name}"/>')
    open(rels_p, "w").write(rels.replace("</Relationships>", add + "</Relationships>"))
    ct_p = os.path.join(tmp, "[Content_Types].xml")
    ct = open(ct_p).read()
    if 'Extension="png"' not in ct:
        ct = ct.replace("<Types ", "<Types ", 1).replace(
            "<Default ", '<Default Extension="png" ContentType="image/png"/><Default ', 1)
        open(ct_p, "w").write(ct)

    if os.path.exists(out_path):
        os.remove(out_path)
    with zipfile.ZipFile(out_path, "w", zipfile.ZIP_DEFLATED) as z:
        for root, _, files in os.walk(tmp):
            for f in files:
                full = os.path.join(root, f)
                z.write(full, os.path.relpath(full, tmp))
    shutil.rmtree(tmp)
    print("wrote", out_path, "| references:", len(ORDER), "| figures:", len(MEDIA))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "SwarmGate_Apart_submission.docx"))
