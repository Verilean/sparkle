#!/usr/bin/env python3
"""The threading theorems over MachineRan, split IN PLACE (branch fix/ran-threading-split).

Reviewer ruling 2026-10-14 (second message, item 4): the theorems that only
THREAD the closing may be split in place; the old statement is kept as a
corollary and type-checked; the copies go.

For a threading theorem X of a built file (statement S, proof P) whose `_ran`
sibling is a COPY in Tools/ShippingKidFactsRan.lean or
Tools/ShippingMachineSeqLinkedRan.lean, one step

  * takes the sibling's text (statement and proof, as BUILT in the copy file)
    out of the copy file and puts it into the built file right before X;
  * replaces P by ONE application
        X_ran <explicit binders of the _ran form, in order>
          (Tools.ShippingMachineRan.machineRan_of_closes <run> entry <bnd> closes)
    and leaves S character for character as it is.

Every replacement is asserted to hit exactly one place. Before a block is
moved the script ASSERTS that the copy is the original with the run binders
removed, `closes` replaced by `ran` and every callee of the chain by its
`_ran` form (statement and proof, compared up to white space) — so what moves
is the built original's proof, in the built copy's line layout.

Usage (from the repository root; it never runs lean or lake):

  scripts/ran_threading_split.py list            the steps
  scripts/ran_threading_split.py apply N         step N (1-based): edits the built file and the copy file
  scripts/ran_threading_split.py stubs           the two copy files become import-only (after all steps)
  scripts/ran_threading_split.py verify          statements against BASE (hashes), no duplicate, no cycle
  scripts/ran_threading_split.py table           the statement table (markdown) for the record
  scripts/ran_threading_split.py statements      old / new statement texts (markdown) for the record
  scripts/ran_threading_split.py pintest         writes Tests/Compiler/RanThreadingStatementsTest.lean
  scripts/ran_threading_split.py record          writes docs/parallel/L-threading-split-statements.md
"""
import hashlib
import os
import re
import subprocess
import sys

BASE = "80745d94"
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
COPY_KIDS = "Tools/ShippingKidFactsRan.lean"
COPY_HEADS = "Tools/ShippingMachineSeqLinkedRan.lean"
RAN_IMPORT = "import Tools.ShippingMachineRanBase"
PIN_TEST = "Tests/Compiler/RanThreadingStatementsTest.lean"

# (built file, namespace, theorems in file order, copy file, kind, add the import line)
STEPS = [
    ("Tools/ShippingChecksCoreGate.lean", "Tools.ShippingChecksCoreGate",
     ["core_outsCheck_all_gate"], COPY_KIDS, "core", True),
    ("Tools/ShippingChecksWidths.lean", "Tools.ShippingChecksWidths",
     ["core_callPorts", "core_instOutWidthsOk", "core_hierGate"], COPY_KIDS, "core", False),
    ("Tools/ShippingChecksRaw.lean", "Tools.ShippingChecksRaw",
     ["core_raw_facts"], COPY_KIDS, "core", False),
    ("Tools/ShippingPortsMatchRaw.lean", "Tools.ShippingPortsMatchRaw",
     ["core_portsMatch_raw"], COPY_KIDS, "core", False),
    ("Tools/ShippingKidsSelf.lean", "Tools.ShippingKidsSelf",
     ["core_kidsPass_deep", "core_kidsMaskedN_top"], COPY_KIDS, "core", False),
    ("Tools/ShippingChecksRunFacts.lean", "Tools.ShippingChecksRunFacts",
     ["core_runFacts"], COPY_KIDS, "core", True),
    ("Tools/ShippingTextShipped.lean", "Tools.ShippingTextShipped",
     ["core_designCheck_run"], COPY_KIDS, "core", True),
    ("Tools/ShippingKidFacts.lean", "Tools.ShippingKidFacts",
     ["kids_runFacts", "kids_outsCheck", "kids_maskedN", "kids_designCheck"], COPY_KIDS, "core", True),
    ("Tools/ShippingMachineSeqLinkedR.lean", "Tools.ShippingMachineCausal",
     ["machine_traceL_of_loop_causalRA", "machine_traceL_of_comb_callsRA",
      "machine_traceL_of_data_causalRA"], COPY_HEADS, "head", True),
]

# every theorem of the chain that has a `_ran` form (base lemmas of round par/g-1 and the threading ones)
CHAIN = [
    "core_kids_facts", "core_kids_factsM", "core_raw_factsM", "core_hierGateM", "core_callPortsM",
    "core_closed_typedIn", "core_outsExtracted", "core_clk", "core_kids_self", "core_linkedWF",
    "core_instOuts_not_assigned", "core_callConns", "machine_trace_lets_of_streamBRA",
] + [t for s in STEPS for t in s[2]]

# the run binders of each kind: (binder texts to REMOVE, the closing binder, its replacement,
#   the identifiers to drop from a proof, the arguments of machineRan_of_closes)
KINDS = {
    "core": {
        "remove": [
            "{w w1 : Void IO.RealWorld}",
            "(hB : ChildBnd mref cref w)",
            "(hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)",
            "(entry : MachineDefines mctx mref cctx cref c d.shape)",
        ],
        "closes": "(closes : MachineClosesAt mctx mref cctx cref c d.shape)",
        "ran": "(ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)",
        "drop": ["hB", "hcore", "entry"],
        "producer": "(Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)",
    },
    "head": {
        "remove": [
            "{w w' : Void IO.RealWorld}",
            "(hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, design) w')",
            "(entry : MachineDefines mctx mref cctx cref declName d.shape)",
            "(hsyn : Tools.ShippingChildInv.ChildBnd mref cref w)",
        ],
        "closes": "(closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref declName d.shape)",
        "ran": "(ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref declName d.shape m design)",
        "drop": ["hr", "entry", "hsyn"],
        "producer": "(Tools.ShippingMachineRan.machineRan_of_closes hr entry hsyn closes)",
    },
}

STARTERS = ("set_option", "/--", "/-!", "theorem ", "end ", "namespace ", "def ", "structure ",
            "variable", "open ", "section", "private ", "instance", "abbrev ", "noncomputable ")


def die(msg):
    sys.exit("ran_threading_split: " + msg)


def read(path):
    with open(os.path.join(ROOT, path), encoding="utf-8") as f:
        return f.read()


def write(path, text):
    with open(os.path.join(ROOT, path), "w", encoding="utf-8") as f:
        f.write(text)


def base(path):
    return subprocess.run(["git", "-C", ROOT, "show", BASE + ":" + path], check=True,
                          capture_output=True).stdout.decode("utf-8")


def norm(text):
    """White space collapsed; no space after an opening or before a closing bracket."""
    t = re.sub(r"\s+", " ", text).strip()
    t = re.sub(r"([(\[{⟨]) ", r"\1", t)
    t = re.sub(r" ([)\]}⟩,])", r"\1", t)
    return t


def sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


class Block:
    """One theorem of a file: [set_option line] [doc comment] theorem NAME statement := proof."""

    def __init__(self, path, text, name):
        self.path, self.name = path, name
        lines = text.split("\n")
        hits = [i for i, l in enumerate(lines) if l.startswith("theorem " + name + " ")]
        if len(hits) != 1:
            die(f"{path}: {len(hits)} declarations of `theorem {name}` (expected exactly 1)")
        i = hits[0]
        j = i
        if lines[j - 1].rstrip().endswith("-/"):
            j -= 1
            while not lines[j].startswith("/--"):
                j -= 1
                if j < 0 or lines[j].startswith("theorem "):
                    die(f"{path}: {name}: the doc comment's start was not found")
        self.doc = lines[j:i]
        self.opt = []
        if lines[j - 1].startswith("set_option") and lines[j - 1].rstrip().endswith(" in"):
            j -= 1
            self.opt = [lines[j]]
        self.first = j
        k = i + 1
        while k < len(lines) and not (lines[k].startswith(STARTERS)):
            k += 1
        while lines[k - 1].strip() == "":
            k -= 1
        self.last = k  # exclusive
        s = i
        while s < k and not (lines[s].rstrip().endswith(" := by") or lines[s].rstrip().endswith(" :=")):
            s += 1
        if s == k:
            die(f"{path}: {name}: the end of the statement was not found")
        self.by = lines[s].rstrip().endswith(" := by")
        cut = len(" := by") if self.by else len(" :=")
        stmt = lines[i:s + 1]
        stmt[-1] = stmt[-1].rstrip()[:-cut]
        self.stmt = "\n".join(stmt)          # `theorem NAME … <conclusion>`, nothing after it
        self.proof = "\n".join(lines[s + 1:k])
        self.lines = lines

    def text(self):
        return "\n".join(self.lines[self.first:self.last])


def to_ran_stmt(stmt, name, kind):
    """The split's form of a statement (white space normalised)."""
    k = KINDS[kind]
    t = norm(stmt)
    for r in k["remove"]:
        if t.count(norm(r)) != 1:
            die(f"{name}: the binder `{r}` occurs {t.count(norm(r))} times in the statement")
        t = t.replace(norm(r), "")
    if t.count(norm(k["closes"])) != 1:
        die(f"{name}: the closing binder occurs {t.count(norm(k['closes']))} times")
    t = t.replace(norm(k["closes"]), norm(k["ran"]))
    head = "theorem " + name + " "
    if not t.startswith(head):
        die(f"{name}: unexpected statement head")
    return norm("theorem " + name + "_ran " + t[len(head):])


def to_ran_proof(proof, name, kind):
    """The split's form of a proof (white space normalised); also the number of renamed callees."""
    k = KINDS[kind]
    t = proof
    for ident in k["drop"]:
        t = re.sub(r"(?<![\w.'])" + re.escape(ident) + r"(?![\w'])", " ", t)
    n_closes = len(re.findall(r"(?<![\w.'])closes(?![\w'])", t))
    t = re.sub(r"(?<![\w.'])closes(?![\w'])", "ran", t)
    renamed = 0
    for callee in sorted(set(CHAIN), key=len, reverse=True):
        pat = r"(?<![\w'])" + re.escape(callee) + r"(?![\w'])"
        renamed += len(re.findall(pat, t))
        t = re.sub(pat, callee + "_ran", t)
    if renamed != n_closes:
        die(f"{name}: {n_closes} uses of the closing but {renamed} renamed callees")
    return norm(t), renamed


def strip_comments(text):
    return re.sub(r"--[^\n]*", "", text)


def split_binders(stmt, name):
    """(binder text, conclusion text) of `theorem NAME <binders> : <conclusion>`."""
    head = "theorem " + name + " "
    assert stmt.startswith(head)
    body = stmt[len(head):]
    depth, i = 0, 0
    while i < len(body):
        ch = body[i]
        if body.startswith("--", i):
            i = body.index("\n", i)
            continue
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and body[i + 1] != "=":
            return body[:i].rstrip(), body[i + 1:].lstrip("\n")
        i += 1
    die(f"{name}: no top-level colon in the statement")


def binder_groups(binders):
    """[(kind, [names], text)] of a binder text: kind e / i / c."""
    t = strip_comments(binders)
    out, i = [], 0
    close = {"(": ")", "{": "}", "[": "]"}
    kind = {"(": "e", "{": "i", "[": "c"}
    while i < len(t):
        ch = t[i]
        if ch in close:
            depth, j = 0, i
            while True:
                if t[j] in "([{⟨":
                    depth += 1
                elif t[j] in ")]}⟩":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            inner = t[i + 1:j]
            if ch == "[":
                names = ["inst"]
            else:
                names = inner.split(" : ", 1)[0].split()
            out.append((kind[ch], names, t[i:j + 1]))
            i = j + 1
        else:
            if not ch.isspace():
                die(f"unexpected text between binders: {t[i:i + 30]!r}")
            i += 1
    return out


def wrap(tokens, first_indent, indent, width=100):
    lines, cur = [], " " * first_indent
    for tok in tokens:
        if cur.strip() and len(cur) + 1 + len(tok) > width:
            lines.append(cur)
            cur = " " * indent + tok
        else:
            cur = cur + (" " if cur.strip() else "") + tok
    lines.append(cur)
    return lines


def corollary(name, ran_stmt, kind):
    """The old theorem's new proof: one application of the `_ran` form."""
    binders, _ = split_binders(ran_stmt, name + "_ran")
    toks = [name + "_ran"]
    seen_ran = False
    for k, names, _ in binder_groups(binders):
        if k != "e":
            continue
        for n in names:
            if n == "ran":
                toks.append(KINDS[kind]["producer"])
                seen_ran = True
            else:
                toks.append(n)
    if not seen_ran:
        die(f"{name}: the _ran form has no explicit binder `ran`")
    return wrap(toks, 2, 4)


def ran_doc(name):
    return [
        f"/-- `{name}` over `MachineRan`:",
        "the proof of the built theorem, MOVED here (split in place, branch",
        "`fix/ran-threading-split`) with the run, the reflection, the closing and the boundary",
        "replaced by `ran` and every callee of the chain by its `_ran` form. It takes of the run only",
        "that the machine synthesis this core run performed returned the result from an invariant",
        "world; the theorem below, its statement unchanged, is the instance at the all-worlds closing",
        "(`Tools.ShippingMachineRan.machineRan_of_closes`). -/",
    ]


def remove_block(text, blk):
    lines = text.split("\n")
    a, b = blk.first, blk.last
    if lines[a - 1].strip() == "":
        a -= 1
    return "\n".join(lines[:a] + lines[b:])


def apply(n):
    path, ns, names, copy_path, kind, add_import = STEPS[n - 1]
    built = read(path)
    copy = read(copy_path)
    for name in names:
        if re.search(r"^theorem " + re.escape(name) + r"_ran ", built, re.M):
            die(f"{path}: {name}_ran is already there (step applied?)")
        old = Block(path, built, name)
        cp = Block(copy_path, copy, name + "_ran")
        # what moves is the original, in the split's form
        want_stmt = to_ran_stmt(old.stmt, name, kind)
        if want_stmt != norm(cp.stmt):
            die(f"{name}: the copy's statement is not the original's in the split's form\n"
                f"want: {want_stmt}\ncopy: {norm(cp.stmt)}")
        want_proof, renamed = to_ran_proof(old.proof, name, kind)
        if want_proof != norm(cp.proof):
            die(f"{name}: the copy's proof is not the original's with the callees renamed\n"
                f"want: {want_proof}\ncopy: {norm(cp.proof)}")
        for ident in KINDS[kind]["drop"] + ["closes"]:
            if re.search(r"(?<![\w.'])" + re.escape(ident) + r"(?![\w'])", strip_comments(cp.proof)):
                die(f"{name}_ran: its proof mentions `{ident}`")
        if old.by != cp.by:
            die(f"{name}: `:= by` in one and `:=` in the other")
        new_ran = cp.opt + ran_doc(name) + [cp.stmt + (" := by" if cp.by else " :=")] + cp.proof.split("\n")
        new_old = old.opt + old.doc + [old.stmt + " :="] + corollary(name, cp.stmt, kind)
        old_text = old.text()
        if built.count(old_text) != 1:
            die(f"{path}: the block of {name} occurs {built.count(old_text)} times")
        built = built.replace(old_text, "\n".join(new_ran) + "\n\n" + "\n".join(new_old))
        # the statement did not move
        if Block(path, built, name).stmt != old.stmt:
            die(f"{name}: the old statement changed")
        copy = remove_block(copy, cp)
        print(f"step {n}: {ns}.{name}: proof moved to {name}_ran ({len(cp.proof.splitlines())} lines, "
              f"{renamed} callee(s) renamed); old statement sha256 {sha(old.stmt)[:16]} unchanged")
    if kind == "head":
        a = ("open Tools.ShippingMachineTraceX (MachineTraceLBX ServedReal machine_trace_lets_of_streamBR\n"
             "  machine_trace_lets_of_streamBRA)\n")
        b = ("open Tools.ShippingMachineTraceX (MachineTraceLBX ServedReal machine_trace_lets_of_streamBR\n"
             "  machine_trace_lets_of_streamBRA machine_trace_lets_of_streamBRA_ran)\n")
        if built.count(a) != 1:
            die(f"{path}: the `open Tools.ShippingMachineTraceX (…)` line occurs {built.count(a)} times")
        built = built.replace(a, b)
    if add_import:
        if RAN_IMPORT in built:
            die(f"{path}: already imports Tools.ShippingMachineRanBase")
        lines = built.split("\n")
        last = max(i for i, l in enumerate(lines) if l.startswith("import "))
        lines.insert(last + 1, RAN_IMPORT)
        built = "\n".join(lines)
    elif RAN_IMPORT not in built:
        die(f"{path}: expected to import Tools.ShippingMachineRanBase already")
    write(path, built)
    write(copy_path, copy)


STUB_KIDS = '''import Tools.ShippingKidFacts
import Tools.ShippingMachineRanBase

/-! # (emptied) The design-level chain of a parent with calls, over `MachineRan`

This file held the `_ran` SIBLINGS of fourteen threading theorems as COPIES of
their built originals (round par/g-1). By the ruling of 2026-10-14 (second
message, item 4) each original is now split IN PLACE: the proof is in
`<name>_ran` in the original's own file, under the SAME full name the copy
had here, and the original is its corollary at
`Tools.ShippingMachineRan.machineRan_of_closes`
(`docs/parallel/L-threading-split.md`, `scripts/ran_threading_split.py`):

| `_ran` form | now in |
|---|---|
| `Tools.ShippingChecksCoreGate.core_outsCheck_all_gate_ran` | `Tools/ShippingChecksCoreGate.lean` |
| `Tools.ShippingChecksWidths.core_hierGate_ran`, `core_callPorts_ran`, `core_instOutWidthsOk_ran` | `Tools/ShippingChecksWidths.lean` |
| `Tools.ShippingChecksRaw.core_raw_facts_ran` | `Tools/ShippingChecksRaw.lean` |
| `Tools.ShippingChecksRunFacts.core_runFacts_ran` | `Tools/ShippingChecksRunFacts.lean` |
| `Tools.ShippingPortsMatchRaw.core_portsMatch_raw_ran` | `Tools/ShippingPortsMatchRaw.lean` |
| `Tools.ShippingKidsSelf.core_kidsMaskedN_top_ran`, `core_kidsPass_deep_ran` | `Tools/ShippingKidsSelf.lean` |
| `Tools.ShippingTextShipped.core_designCheck_run_ran` | `Tools/ShippingTextShipped.lean` |
| `Tools.ShippingKidFacts.kids_runFacts_ran`, `kids_outsCheck_ran`, `kids_maskedN_ran`, `kids_designCheck_ran` | `Tools/ShippingKidFacts.lean` |

NOTHING is declared here any more. The file is kept, import-only, because
`lakefile.lean` names it as a library root and two files import it
(`Tools/ShippingOutermostCommand.lean`, `Tests/Compiler/RanSplitStatementsTest.lean`);
importing `Tools.ShippingKidFacts` gives every name above. It can be deleted
together with its `lean_lib` entry and those two import lines. -/
'''

STUB_HEADS = '''import Tools.ShippingMachineSeqLinkedR

/-! # (emptied) The three wired heads over `MachineRan`

This file held `machine_traceL_of_loop_causalRA_ran`, `_of_comb_callsRA_ran`
and `_of_data_causalRA_ran` (namespace `Tools.ShippingMachineCausal`) as
COPIES of the three built heads (round par/g-1). By the ruling of 2026-10-14
(second message, item 4) the heads are now split IN PLACE in
`Tools/ShippingMachineSeqLinkedR.lean`: the proofs are in the `_ran` forms
there, under the SAME full names, and each built head is the corollary at
`Tools.ShippingMachineRan.machineRan_of_closes`
(`docs/parallel/L-threading-split.md`, `scripts/ran_threading_split.py`).

NOTHING is declared here any more. The file is kept, import-only, because
`lakefile.lean` names it as a library root and two files import it
(`Tools/ShippingOutermostCommand.lean`, `Tests/Compiler/RanSplitStatementsTest.lean`).
It can be deleted together with its `lean_lib` entry and those two import
lines. -/
'''


def stubs():
    for path, stub in ((COPY_KIDS, STUB_KIDS), (COPY_HEADS, STUB_HEADS)):
        cur = read(path)
        left = re.findall(r"^(?:theorem|def|structure|abbrev|instance|lemma)\b.*", cur, re.M)
        if left:
            die(f"{path}: declarations left, not emptied: {left}")
        write(path, stub)
        print(f"{path}: import-only ({len(cur.splitlines())} -> {len(stub.splitlines())} lines)")


def imports_of(path):
    return re.findall(r"^import (\S+)", read(path), re.M)


def closure(mod, seen=None):
    seen = set() if seen is None else seen
    p = mod.replace(".", "/") + ".lean"
    if mod in seen or not os.path.exists(os.path.join(ROOT, p)):
        return seen
    seen.add(mod)
    for m in imports_of(p):
        closure(m, seen)
    return seen


def rows():
    """Per theorem: what the record's table shows. Asserts along the way."""
    out = []
    for path, ns, names, copy_path, kind, _ in STEPS:
        b_built, b_copy = base(path), base(copy_path)
        now = read(path)
        for name in names:
            old0 = Block(path, b_built, name)
            old1 = Block(path, now, name)
            cp0 = Block(copy_path, b_copy, name + "_ran")
            ran1 = Block(path, now, name + "_ran")
            if old0.stmt != old1.stmt:
                die(f"{ns}.{name}: its statement is NOT the base statement")
            if ran1.stmt != cp0.stmt or ran1.proof != cp0.proof:
                die(f"{ns}.{name}_ran: not the copy's text of the base commit")
            if to_ran_stmt(old0.stmt, name, kind) != norm(ran1.stmt):
                die(f"{ns}.{name}_ran: not the split's form of the old statement")
            if to_ran_proof(old0.proof, name, kind)[0] != norm(ran1.proof):
                die(f"{ns}.{name}_ran: not the old proof with the callees renamed")
            if ran1.first > old1.first:
                die(f"{ns}.{name}_ran: not before {name}")
            if name + "_ran" not in old1.proof or "machineRan_of_closes" not in old1.proof:
                die(f"{ns}.{name}: its proof is not the corollary")
            out.append(dict(path=path, ns=ns, name=name, kind=kind, old0=old0, old1=old1, ran=ran1,
                            copy_path=copy_path))
    return out


def verify():
    rs = rows()
    for r in rs:
        print(f"IDENTICAL {r['ns']}.{r['name']}: old statement sha256 {sha(r['old0'].stmt)} "
              f"(base {BASE}) = {sha(r['old1'].stmt)} (now); _ran statement and proof = the copy's at base")
    # no name is declared twice in the tree's Tools files
    decl = {}
    for dirpath, _, files in os.walk(os.path.join(ROOT, "Tools")):
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(dirpath, f)
                for m in re.finditer(r"^theorem (\S+_ran) ", open(p, encoding="utf-8").read(), re.M):
                    decl.setdefault(m.group(1), []).append(os.path.relpath(p, ROOT))
    for r in rs:
        where = decl.get(r["name"] + "_ran", [])
        if where != [r["path"]]:
            die(f"{r['name']}_ran is declared in {where} (expected only {r['path']})")
    # no cycle: the base file's import closure has none of the edited files
    cl = closure("Tools.ShippingMachineRanBase")
    for path, *_ in STEPS:
        mod = path[:-5].replace("/", ".")
        if mod in cl:
            die(f"import cycle: Tools.ShippingMachineRanBase reaches {mod}")
        if RAN_IMPORT not in read(path):
            die(f"{path}: does not import Tools.ShippingMachineRanBase")
    print(f"OK: {len(rs)} theorems; each _ran form declared once, in its original's file; "
          f"Tools.ShippingMachineRanBase's import closure ({len(cl)} modules) contains none of the "
          f"{len(STEPS)} edited files")


def table():
    rs = rows()
    print("| theorem | file | old statement: sha256 at base = now | binders (old → `_ran`) | proof lines moved | old proof now |")
    print("|---|---|---|---|---|---|")
    for r in rs:
        g0 = binder_groups(split_binders(r["old0"].stmt, r["name"])[0])
        g1 = binder_groups(split_binders(r["ran"].stmt, r["name"] + "_ran")[0])
        n0 = sum(len(g[1]) for g in g0)
        n1 = sum(len(g[1]) for g in g1)
        print(f"| `{r['ns']}.{r['name']}` | `{r['path']}` | `{sha(r['old0'].stmt)[:16]}` = "
              f"`{sha(r['old1'].stmt)[:16]}` IDENTICAL | {n0} → {n1} | "
              f"{len(r['old0'].proof.splitlines())} | {len(r['old1'].proof.splitlines())} lines |")


def statements():
    for r in rows():
        print(f"## `{r['ns']}.{r['name']}` (`{r['path']}`)\n")
        print(f"Old statement — at `{BASE}` and now, IDENTICAL (sha256 `{sha(r['old0'].stmt)}`):\n")
        print("```lean\n" + r["old0"].stmt + "\n```\n")
        print(f"`_ran` form (sha256 `{sha(r['ran'].stmt)}`; the text the copy file had at `{BASE}`):\n")
        print("```lean\n" + r["ran"].stmt + "\n```\n")
        print("Old theorem's proof now:\n")
        print("```lean\n" + r["old1"].proof + "\n```\n")


RECORD = "docs/parallel/L-threading-split-statements.md"
RECORD_HEAD = """# The threading theorems split in place: statement at `{base}`, statement now, and the `_ran` statement

Generated by `scripts/ran_threading_split.py record`, branch `fix/ran-threading-split`.
WRITTEN, NOT BUILT. For every theorem below the statement text (from `theorem <name>` to the `:=`,
exclusive) was extracted from `git show {base}:<file>` and from the working tree and compared
CHARACTER FOR CHARACTER (the script fails otherwise); the table gives the SHA-256 (first 16 hex
digits; the full digests are with each statement). The `_ran` statement and proof are, character
for character, the text the copy file had at `{base}`, and — up to white space — the old statement
and proof with the run binders removed, `closes` replaced by `ran` and every callee of the chain
replaced by its `_ran` form (both asserted by the script). Binder counts are of the statement text
(the four section variables of the first fourteen are not counted).

"""


def record():
    import contextlib
    import io
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        table()
        print()
        statements()
    write(RECORD, RECORD_HEAD.format(base=BASE) + buf.getvalue())
    print(f"{RECORD}: written")


VARS = ("{mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}\n"
        "    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}\n")
VAR_NAMES = [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i")]


def opens_before(text, blk):
    """The `open` lines in effect at a block: those after the governing `namespace` line."""
    lines = text.split("\n")
    ns = max(i for i in range(blk.first) if lines[i].startswith("namespace "))
    out, i = [], ns + 1
    while i < blk.first:
        if lines[i].startswith("open "):
            out.append(lines[i])
            while lines[i + 1].startswith("  ") and lines[i].count("(") > lines[i].count(")"):
                i += 1
                out.append(lines[i])
        i += 1
    has_var = any(l.startswith("variable {mctx") for l in lines[ns:blk.first])
    return lines[ns][len("namespace "):].strip(), out, has_var


def pintest():
    rs = rows()
    o = []
    o.append("import Tools.ShippingKidFacts")
    o.append("import Tools.ShippingMachineSeqLinkedR")
    o.append("import Tools.ShippingMachineRanBase")
    o.append("")
    o.append("/-! # The statements of the THREADING theorems split in place, PINNED (branch fix/ran-threading-split)")
    o.append("")
    o.append("WRITTEN, NOT BUILT. TARGET-ONLY; not in `Tests.AllTests`. ASSERTING: any drift")
    o.append("of a pinned statement is an elaboration error of this file. GENERATED by")
    o.append("`scripts/ran_threading_split.py pintest`; do not edit by hand.")
    o.append("")
    o.append("The ruling of 2026-10-14 (second message, item 4) lets the theorems that only")
    o.append("THREAD the closing be split in place: the proof moves into `<name>_ran` (over")
    o.append("`Tools.ShippingMachineRan.MachineRan`) in the theorem's own file and the old")
    o.append("theorem stays, statement unchanged, as the corollary at")
    o.append("`Tools.ShippingMachineRan.machineRan_of_closes`. This file states, for every")
    o.append(f"theorem split so, the statement AS IT WAS at the base commit `{BASE}` (copied")
    o.append("by the script from `git show`, the theorem's binders turned into a `∀`), and")
    o.append("checks:")
    o.append("")
    o.append("1. `example : <old statement> := @<name>` — the present constant has that")
    o.append("   type up to definitional equality (binder order and types; binder NAMES and")
    o.append("   implicitness are not seen by this check);")
    o.append("2. a `run_cmd` that reads the present constant's leading binders and compares")
    o.append("   their NAMES and KINDS (`e` explicit, `i` implicit, `c` instance) with the")
    o.append("   list parsed from the old text;")
    o.append("3. the old theorem is on the standard axioms and its proof term APPLIES its")
    o.append("   `_ran` form and `machineRan_of_closes` (direct constants of the value);")
    o.append("4. every `_ran` form exists, is on the standard axioms, is stated with")
    o.append("   `MachineRan` and with neither `MachineClosesAt` nor `MachineCloses`, and is")
    o.append("   declared in the SAME module as its old theorem (in place, not in a copy")
    o.append("   file).")
    o.append("")
    o.append("| theorem | file | binders |")
    o.append("|---|---|---|")
    exp = []
    for r in rs:
        binders, _ = split_binders(r["old0"].stmt, r["name"])
        ns, _, has_var = opens_before(base(r["path"]), r["old0"])
        names = (VAR_NAMES if has_var else []) + [(n, g[0]) for g in binder_groups(binders) for n in g[1]]
        exp.append((ns + "." + r["name"], names))
        o.append(f"| `{ns}.{r['name']}` | `{r['path']}` | {len(names)} |")
    o.append("")
    o.append("The `open` lists of each section are the original namespace's (statements")
    o.append("resolve as they do there); the namespace itself is opened, not entered.")
    o.append("`Tests/Compiler/RanSplitStatementsTest.lean` pins the base lemmas of the")
    o.append("first split (round par/g-1) and is not changed. -/")
    o.append("namespace Tests.Compiler.RanThreadingStatementsTest")
    o.append("")
    for idx, r in enumerate(rs):
        b = base(r["path"])
        ns, opens, has_var = opens_before(b, r["old0"])
        binders, concl = split_binders(r["old0"].stmt, r["name"])
        o.append(f"section Pin{idx}")
        o.append(f"open {ns}")
        o.extend(opens)
        o.append("")
        o.append(f"-- {ns}.{r['name']} ({r['path']}): split in place")
        o.append("example : ∀ " + (VARS if has_var else "") + binders + ",")
        o.append(concl + " :=")
        o.append(f"  @{ns}.{r['name']}")
        o.append("")
        o.append(f"end Pin{idx}")
        o.append("")
    o.append("/-- The leading binders of each pinned theorem, as parsed from the OLD text:")
    o.append("name and kind (`e` explicit, `i` implicit, `c` instance). For a theorem under")
    o.append("the section variables the first four are those, in their order. -/")
    o.append("def expected : List (Lean.Name × List (String × String)) := [")
    for i, (full, names) in enumerate(exp):
        pairs = ", ".join(f'("{n}", "{k}")' for n, k in names)
        o.append(f"  (`{full},")
        o.append(f"    [{pairs}])" + ("," if i + 1 < len(exp) else ""))
    o.append("]")
    o.append("")
    o.append(r'''/-- The kind letter of a binder. -/
def kindOf (b : Lean.BinderInfo) : String :=
  match b with
  | Lean.BinderInfo.default => "e"
  | Lean.BinderInfo.implicit => "i"
  | Lean.BinderInfo.strictImplicit => "s"
  | Lean.BinderInfo.instImplicit => "c"

/-- Standard axioms only, an error otherwise. -/
def stdAxioms (n : Lean.Name) : Lean.Meta.MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  let mut nOk : Nat := 0
  for (n, bs) in expected do
    let some ci := env.find? n | throwError "{n}: missing"
    let got ← Lean.Meta.forallBoundedTelescope ci.type (some bs.length) fun xs _ => do
      let mut out : List (String × String) := []
      for x in xs do
        let d ← x.fvarId!.getDecl
        out := out ++ [(d.userName.toString, kindOf d.binderInfo)]
      pure out
    unless got.length == bs.length do
      throwError "{n}: {got.length} leading binders, the old statement has {bs.length}"
    -- an instance binder has no name in the old text: its kind only
    let same := (got.zip bs).all fun (g, b) => g.2 == b.2 && (b.2 == "c" || g.1 == b.1)
    unless same do
      throwError "{n}: binder names / kinds changed.\nnow: {toString got}\nold: {toString bs}"
    stdAxioms n
    -- the old theorem is the corollary: its proof term applies the `_ran` form
    -- and the producer from the all-worlds closing
    let ran : Lean.Name := n.appendAfter "_ran"
    let used : Array Lean.Name :=
      match ci with
      | Lean.ConstantInfo.thmInfo ti => ti.value.getUsedConstants
      | _ => #[]
    unless used.contains ran do
      throwError "{n}: its proof term does not apply {ran}"
    unless used.contains ``Tools.ShippingMachineRan.machineRan_of_closes do
      throwError "{n}: its proof term does not apply machineRan_of_closes"
    -- the `_ran` form: present, standard axioms, stated over MachineRan only,
    -- declared in the module of its old theorem
    let some cr := env.find? ran | throwError "{ran}: missing"
    stdAxioms ran
    for c in [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingMachineEntry.MachineCloses] do
      if (cr.type.find? (·.isConstOf c)).isSome then
        throwError "{ran}: its statement mentions {c}"
    unless (cr.type.find? (·.isConstOf ``Tools.ShippingMachineRan.MachineRan)).isSome do
      throwError "{ran}: its statement does not mention MachineRan"
    unless (ci.type.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
      throwError "{n}: its statement does not mention MachineClosesAt (the old statement does)"
    let mOld := (env.getModuleIdxFor? n).map (·.toNat)
    let mRan := (env.getModuleIdxFor? ran).map (·.toNat)
    unless mOld == mRan do
      throwError "{ran}: not declared in the module of {n}"
    nOk := nOk + 1
  Lean.logInfo m!"RAN THREADING STATEMENTS: {nOk} threading theorems have their old statement (type by the examples above, leading binder names and kinds by this check), are on the standard axioms and are corollaries (their proof terms apply their _ran form and machineRan_of_closes); their {nOk} _ran forms are present, on the standard axioms, stated with MachineRan and without MachineClosesAt / MachineCloses, each in its old theorem's module"

end Tests.Compiler.RanThreadingStatementsTest''')
    write(PIN_TEST, "\n".join(o) + "\n")
    print(f"{PIN_TEST}: {len(rs)} statements pinned")


def main():
    a = sys.argv[1:]
    if a == ["list"]:
        for i, s in enumerate(STEPS, 1):
            print(f"{i}. {s[0]}: {', '.join(s[2])}  (copies in {s[3]})")
    elif len(a) == 2 and a[0] == "apply":
        apply(int(a[1]))
    elif a == ["stubs"]:
        stubs()
    elif a == ["verify"]:
        verify()
    elif a == ["table"]:
        table()
    elif a == ["statements"]:
        statements()
    elif a == ["pintest"]:
        pintest()
    elif a == ["record"]:
        record()
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
