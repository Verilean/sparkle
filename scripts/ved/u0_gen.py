#!/usr/bin/env python3
"""U0 measurement harness for `#verify_elab_deep`: case generator and classifier.

DISCOVERY / OBSERVATION MODE (reviewer change request 2026-11-08, P1-1).
U0 records what the current `#verify_elab_deep` produces for each required-IP
row.  It does NOT count anything as strictly verified: `strict_counted` is
`no` or `unknown`, never `yes`, because no probe that can be written without
changing Tools/DeepElab.lean establishes
  (i)  that the module the deep command verified is the module the original
       command returned in the same run (the deep command re-runs
       `synthesizeHierarchical` itself and returns nothing), and
  (ii) each output's expected FULL theorem type (only names, the theorem
       kind and the reachable axiom closure are checked here).
Design: docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md (sections 3 and 8).

The inventory is read ONLY with `git show <commit>:<path>` at a fixed commit
and its blob SHA is checked, so a moved branch can not change the denominator
(327 rows).  Every output goes outside the source tree.

Case construction (P1-2): a case is a COPY OF THE ORIGINAL SOURCE FILE in
which, right after the original command, a block is inserted:

    namespace VedU0Case_R<row>
    <decl probe>                 -- resolves the command's own identifier HERE
    set_option ... in            -- Elab.async false + the inventory `options`
    #verify_elab_deep <top>      -- the identifier exactly as the command wrote it
    #ved_audit_current_namespace
    <second-run probe>
    end VedU0Case_R<row>

so private declarations, the file's namespaces, `open`s, scoped options and
local attributes are those of the original command.  Rows whose invocation
can not be reproduced by `#verify_elab_deep <ident>` (parameter values,
`symbolicMode`, command arguments) are NOT run; they stay in the 327
denominator as `unsupported-invocation`.

Subcommands
  rows         list the inventory rows (row id = 1-based data line number)
  header       print the result TSV header
  gen          write one case directory: Case.lean, case.env, meta.json
  classify     read one case directory after the runner, print one TSV row
  error-row    print a harness-error row for (row, setting) that has no case
  smoke-split  split an existing deep test file into one-command variants
               (and a risk report); results are kept apart from the as-is run
"""
import argparse
import csv
import io
import json
import os
import re
import subprocess
import sys

INV_PATH = "scripts/gen5/fgc_baseline/inventory.tsv"
# fixed by the design doc: par/fgc-s0 tip read on 2026-11-08
INV_COMMIT = "f694355fcabee7c9915c9c83991e4a0b032fedf8"
INV_BLOB = "4a5b801f3a665ed95262b803109aa3f76005065d"
INV_ROWS = 327

# Every environment variable whose name starts with this prefix is CLEARED by
# the runner before a case's explicit settings are applied (P1-3 a).  The
# deep command reads SPARKLE_DEEP_{DEBUG,GOALS,NOFIRST,NOTHM,SHARE,SKIP,TRACE,
# TRACE_ONLY} and SPARKLE_SL_CHECK (Tools/DeepElab.lean, IO.getEnv); the
# compiler and Tools read further SPARKLE_* variables (SPARKLE_PROFILE,
# SPARKLE_NO_REGDEDUP, SPARKLE_NO_LOOPCACHE, ...).  Clearing the whole prefix
# covers them and any added later.
CLEARED_ENV_PREFIX = "SPARKLE_"

SETTINGS = {
    # name: (lean options for the inserted block, environment, route)
    "default": ([], {}, "default"),
    "shared": (["sparkle.deepShare true"], {}, "shared"),
    "profile": ([], {"SPARKLE_PROFILE": "1", "SPARKLE_DEEP_DEBUG": "1"}, "default"),
    # diagnostic modes: never counted as complete success
    "traceonly-shared": (["sparkle.deepShare true"], {"SPARKLE_DEEP_TRACE_ONLY": "1"}, "shared"),
    "defsonly-default": ([], {"SPARKLE_DEEP_NOTHM": "1"}, "default"),
}
TRACE_ONLY_SETTINGS = {"traceonly-shared", "defsonly-default"}

# Stages and, per route, the theorems each stage REQUIRES, per output port.
# `{b}` = last component of the resolved declaration, `{s}` = `_<port>` when
# the declaration returns a structure of ports, else "" (DeepElab.lean:3639).
# The default route produces no optimiser or SV theorem; the shared route is
# single-port.  SV is split three ways (P1-1): `text_parses` is ONLY the parse
# stage; `signal_runRT` is the round trip (Signal = runModule of the body the
# shipping parser reads back); `signal_svOpt` is the M4 emission semantics of
# the optimised body (an observation about `emitAssigns`, not about the
# printed text).  The existence of `text_parses` never makes sv_meaning yes.
STAGES = ["src", "ir", "opt", "sv_parse", "sv_roundtrip", "sv_meaning"]
REQUIRED = {
    "default": {"src": "{b}{s}_deep_trace", "ir": "{b}{s}_deep_signal_run"},
    "shared": {"src": "{b}_sdeep_trace", "ir": "{b}_sdeep_signal_run",
               "opt": "{b}_sdeep_signal_runOpt", "sv_parse": "{b}_sdeep_text_parses",
               "sv_roundtrip": "{b}_sdeep_signal_runRT", "sv_meaning": "{b}_sdeep_signal_svOpt"},
}
BODY_CONST = {"default": "_deep_body", "shared": "_sdeep_body"}

KEY_COLUMNS = ["inv_commit", "inv_blob", "row", "file", "line", "command", "ns", "top",
               "qualified", "params", "options", "args", "setting"]
RESULT_COLUMNS = KEY_COLUMNS + [
    # how the row was reproduced (P1-2)
    "invocation",               # deep-in-file | unsupported-invocation | unresolved-private | unresolved-name | harness-error | smoke-split
    "invocation_detail",
    "decl_resolved",            # the name the decl probe resolved in the command's own scope
    "decl_check",               # match | mismatch | absent | unknown  (resolved vs inventory `qualified`)
    # run identity (P1-3 b)
    "run_id", "attempt", "src_sha", "src_dirty_hash", "toolchain", "case_hash", "harness_hash",
    "effective_env", "lean_options", "cleared_env",
    "sv_group_approx",
    # run (P1-3 c)
    "ran", "rc", "term", "timeout", "wall_s", "peak_rss_kb", "peak_rss_source", "cgroup_peak_kb",
    "mem_evidence", "reaped", "time_limit_s", "rlimit_as_kb",
    # second-run probe (observational)
    "ret_kind", "second_run_modules", "outputs",
    # stages: expected / found / closure verdict / axioms of the required theorems
    *[f"{st}_{k}" for st in STAGES for k in ("expected", "found", "closure", "axioms")],
    "missing_theorems",
    "observed_against_second_run",   # match | mismatch | unknown  (never "reordered")
    "skipped", "trace_only", "refusal", "errors_outside_block",
    "n_theorems", "n_extra", "extra_rejected", "raw_axioms",
    "strict_counted",           # no | unknown   (never yes in U0, see the module docstring)
    "strict_blockers",
    "harness_error",
    "deep_run_record",          # measured | not-run | none (none = unconfirmed, NOT failure)
    "stdout_ref", "stderr_ref",
]


def die(msg):
    sys.stderr.write(msg + "\n")
    sys.exit(2)


def git_show_inventory(repo, commit, blob):
    got = subprocess.run(["git", "rev-parse", f"{commit}:{INV_PATH}"], cwd=repo,
                         capture_output=True, text=True, check=True).stdout.strip()
    if got != blob:
        die(f"inventory blob mismatch at {commit}: {got} != {blob}")
    text = subprocess.run(["git", "show", f"{commit}:{INV_PATH}"], cwd=repo,
                          capture_output=True, text=True, check=True).stdout
    rows = list(csv.DictReader(io.StringIO(text), delimiter="\t"))
    if len(rows) != INV_ROWS:
        die(f"inventory has {len(rows)} rows, expected {INV_ROWS}")
    for i, r in enumerate(rows, 1):
        r["row"] = str(i)
    return rows


def module_of(path):
    if not path.endswith(".lean"):
        die(f"not a .lean file: {path}")
    return path[:-5].replace("/", ".")


# ---------------------------------------------------------------- source scan

def blank_comments(text):
    """Replace comment characters by spaces (newlines kept), so line numbers
    are unchanged.  Handles nested block comments and string literals."""
    out, i, n, depth, in_str = [], 0, len(text), 0, False
    while i < n:
        c, nx = text[i], text[i + 1] if i + 1 < n else ""
        if depth:
            if c == "/" and nx == "-":
                depth += 1; out.append("  "); i += 2; continue
            if c == "-" and nx == "/":
                depth -= 1; out.append("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if in_str:
            if c == "\\" and nx:
                out.append(c + nx); i += 2; continue
            if c == '"':
                in_str = False
            out.append(c); i += 1; continue
        if c == "/" and nx == "-":
            depth = 1; out.append("  "); i += 2; continue
        if c == "-" and nx == "-":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if c == '"':
            in_str = True
        out.append(c); i += 1
    return "".join(out)


DECL_KW = r"(?:def|abbrev|theorem|opaque|instance|structure)"
MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"


def scan_source(text, line, command, top):
    """Locate the command and read what the original scope carries.
    `uncertain` lists reasons the scan can not vouch for the insertion."""
    code = blank_comments(text)
    lines = code.splitlines()
    res = {"cmd_index": None, "end_index": None, "uncertain": [], "private": False,
           "decl_seen": False, "imports_end": 0, "ns_stack": []}
    pat = re.compile(r"^\s*(?:set_option\s+\S+\s+\S+\s+in\s+|#guard_msgs\s+in\s+)*"
                     + re.escape(command) + r"\s+" + re.escape(top) + r"(\s|$)")
    want = line - 1
    if 0 <= want < len(lines) and pat.match(lines[want]):
        idx = want
    else:
        hits = [i for i, ln in enumerate(lines) if pat.match(ln)]
        if len(hits) != 1:
            res["uncertain"].append(f"command-not-located({len(hits)} matches)")
            return res
        idx = hits[0]
        res["uncertain_note"] = f"line-moved {line}->{idx + 1}"
    res["cmd_index"] = idx
    # the command's extent: following indented continuation lines
    j = idx + 1
    while j < len(lines) and lines[j].strip() and lines[j][:1] in " \t":
        j += 1
    res["end_index"] = j  # insert before this index
    # imports (Lean requires them first)
    last_imp = -1
    for i, ln in enumerate(lines):
        if re.match(r"^\s*(public\s+)?import\s+\S", ln):
            last_imp = i
        elif ln.strip() and not re.match(r"^\s*(module|prelude)\s*$", ln):
            break
    res["imports_end"] = last_imp + 1
    if any(re.match(r"^\s*module\s*$", ln) for ln in lines[:res["imports_end"] + 1]):
        res["uncertain"].append("module-system-header")
    # scope stack up to the command (namespace/section/mutual ... end)
    stack = []
    for ln in lines[:idx]:
        m = re.match(r"^\s*namespace\s+(\S+)", ln)
        if m:
            stack.append(("namespace", m.group(1))); continue
        m = re.match(r"^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$", ln)
        if m:
            stack.append(("section", m.group(1) or "")); continue
        if re.match(r"^\s*mutual\s*$", ln):
            stack.append(("mutual", "")); continue
        m = re.match(r"^\s*end(?:\s+(\S+))?\s*$", ln)
        if m:
            if not stack:
                res["uncertain"].append("unbalanced-end")
            else:
                stack.pop()
    if any(k == "mutual" for k, _ in stack):
        res["uncertain"].append("command-inside-mutual")
    res["ns_stack"] = [n for k, n in stack if k == "namespace"]
    # private / declaration of `top` (exact or as a dotted suffix)
    last = top.split(".")[-1]
    for m in re.finditer(r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(" + MODIFIERS + r")" + DECL_KW + r"\s+(\S+)", code):
        name = m.group(2)
        if name == top or (name.split(".")[-1] == last
                           and (top.endswith("." + name) or name.endswith("." + top) or name == last)):
            res["decl_seen"] = True
            if "private" in m.group(1):
                res["private"] = True
    return res


def import_closure(repo, roots):
    seen, st = set(), list(roots)
    while st:
        mod = st.pop()
        if mod in seen:
            continue
        seen.add(mod)
        p = os.path.join(repo, mod.replace(".", "/") + ".lean")
        if not os.path.exists(p):
            continue
        for ln in blank_comments(open(p, errors="replace").read()).splitlines():
            m = re.match(r"^\s*(?:public\s+)?import\s+(.+)", ln)
            if m:
                st.extend(m.group(1).split())
            elif ln.strip() and not re.match(r"^\s*(module|prelude)\s*$", ln):
                break
    return seen


def invocation_of(r, scan, closure):
    """(invocation, detail, run?) for an inventory row."""
    reasons = []
    if r["params"].strip():
        reasons.append(f"params `{r['params']}` (#verify_elab_deep takes an identifier only; "
                       f"{r['command']} binds them)")
    opts = [o.strip() for o in r["options"].split(",") if o.strip()]
    if any(o.split("=")[0] == "symbolicMode" for o in opts):
        reasons.append("symbolicMode (an option of the parameterised entry, no deep equivalent)")
    if r["args"].strip():
        reasons.append(f"command arguments `{r['args'][:80]}` (not passable to #verify_elab_deep)")
    if reasons:
        return "unsupported-invocation", "; ".join(reasons), False
    if module_of(r["file"]) in closure:
        return ("harness-error", "source module is in the import closure of "
                "Tools.DeepElab/Tools.VedStrictAudit (a copy would redeclare it)", False)
    if scan["uncertain"]:
        return "unsupported-invocation", "source scan: " + ";".join(scan["uncertain"]), False
    detail = "copy of the original file, deep block inserted after the original command"
    if scan["private"]:
        detail += "; declaration is private (resolved in its own file)"
    if scan.get("uncertain_note"):
        detail += "; " + scan["uncertain_note"]
    return "deep-in-file", detail, True


def lean_option_lines(opts_col, setting):
    out = []
    for kv in filter(None, (o.strip() for o in opts_col.split(","))):
        k, _, v = kv.partition("=")
        if k == "symbolicMode":
            continue
        out.append(f"{k} {v}")
    out += SETTINGS[setting][0]
    return out


def inserted_block(r, setting, base, ns):
    opts = lean_option_lines(r["options"], setting)
    prefix = "".join(f"set_option {o} in\n" for o in ["Elab.async false"] + opts)
    top = r["top"]
    q = r["qualified"] or ""
    body_c = base + BODY_CONST[SETTINGS[setting][2]]
    return f"""
-- ===== VED U0 BEGIN row {r['row']} setting {setting} (inventory {INV_COMMIT[:8]}) =====
namespace {ns}
open Lean Elab Command in
run_cmd do
  logInfo m!"VED NS {{← getCurrNamespace}}"
  try
    let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent "{top}".toName)
    let u := (privateToUserName? n).getD n
    logInfo m!"VED DECL resolved={{n}} user={{u}} inventory={q} {{if u == "{q}".toName then "match" else "mismatch"}}"
  catch e => logInfo m!"VED DECL absent: {{← e.toMessageData.toString}}"
{prefix}#verify_elab_deep {top}
#ved_audit_current_namespace
open Lean Elab Command Meta in
run_cmd do
  try
    let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent "{top}".toName)
    let ci ← getConstInfo n
    let head ← liftTermElabM <| forallTelescope ci.type fun _ b => pure b.getAppFn
    if head.isConstOf ``Sparkle.Core.Signal.Signal then logInfo m!"VED RET signal"
    else match head with
      | .const s _ => logInfo m!"VED RET struct {{s}}"
      | _ => logInfo m!"VED RET other"
    -- OBSERVATION ONLY: a SECOND synthesis, not the module the deep command used
    let design ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical n)
    logInfo m!"VED SECONDRUN modules={{design.modules.length}}"
    match design.modules with
    | [m] =>
      for p in m.outputs do logInfo m!"VED OUTPUT {{p.name}}"
      let c := (← getCurrNamespace) ++ "{body_c}".toName
      match (← getEnv).find? c with
      | none => logInfo m!"VED BODY absent"
      | some bi =>
        let v := (bi.value? (allowOpaque := true)).getD default
        logInfo m!"VED BODY {{if v == toExpr m.body then "match" else "mismatch"}}"
    | _ => pure ()
  catch e => logInfo m!"VED PROBE failed: {{← e.toMessageData.toString}}"
end {ns}
-- ===== VED U0 END =====
"""


def case_text(src_text, scan, r, setting):
    base = r["top"].split(".")[-1]
    ns = f"VedU0Case_R{r['row']}"
    lines = src_text.splitlines()
    ie, ei = scan["imports_end"], scan["end_index"]
    out = lines[:ie] + ["import Tools.DeepElab", "import Tools.VedStrictAudit"] + lines[ie:ei]
    block = inserted_block(r, setting, base, ns).splitlines()
    begin = len(out) + 1  # 1-based first line of the block
    out += block
    end = len(out)
    out += lines[ei:]
    return "\n".join(out) + "\n", begin, end


def cmd_rows(a):
    for r in git_show_inventory(a.repo, a.commit, a.blob):
        print("\t".join([r["row"], r["file"], r["line"], r["command"], r["qualified"] or r["top"]]))


def cmd_gen(a):
    rows = git_show_inventory(a.repo, a.commit, a.blob)
    i = int(a.row)
    if not 1 <= i <= len(rows):
        die(f"row {a.row} out of range 1..{len(rows)}")
    r = rows[i - 1]
    if a.setting not in SETTINGS:
        die(f"unknown setting {a.setting}; one of {sorted(SETTINGS)}")
    d = a.dir
    os.makedirs(d, exist_ok=True)
    src_path = os.path.join(a.repo, r["file"])
    if not os.path.exists(src_path):
        die(f"source file missing at the measured SHA: {r['file']}")
    src_text = open(src_path, errors="replace").read()
    scan = scan_source(src_text, int(r["line"]), r["command"], r["top"])
    closure = import_closure(a.repo, ["Tools.DeepElab", "Tools.VedStrictAudit"])
    inv, detail, run = invocation_of(r, scan, closure)
    meta = {k: r.get(k, "") for k in KEY_COLUMNS if k != "setting"}
    meta.update(inv_commit=a.commit, inv_blob=a.blob, setting=a.setting, invocation=inv,
                invocation_detail=detail, run=run, route=SETTINGS[a.setting][2],
                module=module_of(r["file"]), base=r["top"].split(".")[-1],
                ns_suffix=f"VedU0Case_R{r['row']}", lean_options=lean_option_lines(r["options"], a.setting),
                scan_private=scan["private"], scan_decl_seen=scan["decl_seen"], kind="row")
    if run:
        text, b, e = case_text(src_text, scan, r, a.setting)
        with open(os.path.join(d, "Case.lean"), "w") as f:
            f.write(text)
        meta.update(block_begin=b, block_end=e)
    env = SETTINGS[a.setting][1]
    with open(os.path.join(d, "case.env"), "w") as f:
        for k, v in sorted(env.items()):
            f.write(f"{k}={v}\n")
    with open(os.path.join(d, "meta.json"), "w") as f:
        json.dump(meta, f, indent=1, sort_keys=True)
    print(d)


# ------------------------------------------------------------- smoke split

def cmd_smoke_split(a):
    """One variant per line-initial `#verify_elab_deep` of an existing test
    file: the other deep commands are commented out, the kept one runs inside
    a fresh namespace followed by `#ved_audit_current_namespace`.  Every
    variant also gets a RISK REPORT (split_report.txt): later lines that name
    generated `_deep_`/`_sdeep_` constants (they break when their command is
    commented out or when the kept one's names move into the namespace).  An
    error the classifier finds OUTSIDE the inserted lines is a split-harness
    failure, recorded apart from the deep command's result."""
    src = open(a.file, errors="replace").read().splitlines()
    code = blank_comments("\n".join(src)).splitlines()
    cmds = [i for i, ln in enumerate(code) if re.match(r"#verify_elab_deep\s+\S+", ln)]

    def prefixes(i):
        out = []
        j = i - 1
        while j >= 0 and re.match(r"\s*(set_option\s+\S+\s+\S+|#guard_msgs)\s+in\s*$", code[j]):
            out.append(j); j -= 1
        return out
    stem = os.path.splitext(os.path.basename(a.file))[0]
    gen_ref = re.compile(r"\b(\w+_s?deep_\w+|\w+_s?deep)\b")
    for k, keep in enumerate(cmds):
        decl = code[keep].split()[1]
        others = {j for c in cmds if c != keep for j in [c] + prefixes(c)}
        first = min([keep] + prefixes(keep))
        out, begin, end = [], None, None
        ns = f"VedU0Smoke{k:02d}"
        for i, ln in enumerate(src):
            if i in others:
                out.append("-- U0 split: " + ln)
                continue
            if i == first:
                out.append(f"namespace {ns}")
                begin = len(out)          # 1-based line of `namespace`
            out.append(ln)
            if i == keep:
                out.append("#ved_audit_current_namespace")
                out.append(f"end {ns}")
                end = len(out)            # 1-based line of `end`
        imp = max([i for i, ln in enumerate(out) if re.match(r"\s*import\s", ln)], default=-1)
        out.insert(imp + 1, "import Tools.VedStrictAudit")
        begin += 1; end += 1
        risks = []
        for i in range(keep + 1, len(code)):
            if i in others:
                continue
            for m in gen_ref.finditer(code[i]):
                risks.append(f"line {i + 1}: references {m.group(1)}")
        d = os.path.join(a.out, f"S_{stem}_{k:02d}")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "Case.lean"), "w") as f:
            f.write("\n".join(out) + "\n")
        open(os.path.join(d, "case.env"), "w").close()
        meta = {"inv_commit": "-", "inv_blob": "-", "row": f"smoke:{stem}:{k}",
                "file": os.path.relpath(os.path.realpath(a.file), os.path.realpath(a.repo)),
                "line": str(keep + 1), "command": "#verify_elab_deep", "ns": "", "top": decl,
                "qualified": "", "params": "", "options": "", "args": "", "setting": "as-in-file",
                "invocation": "smoke-split",
                "invocation_detail": f"kept line {keep + 1}; commented {len(others)} lines",
                "run": True, "base": decl.split(".")[-1], "ns_suffix": ns,
                "route": "shared" if any(re.search(r"sparkle\.deepShare\s+true", code[j])
                                         for j in prefixes(keep)) else "default",
                "lean_options": [], "block_begin": begin, "block_end": end, "kind": "smoke-split"}
        with open(os.path.join(d, "meta.json"), "w") as f:
            json.dump(meta, f, indent=1, sort_keys=True)
        with open(os.path.join(d, "split_report.txt"), "w") as f:
            f.write(f"file {a.file} variant {k} keeps line {keep + 1}: {src[keep].strip()}\n")
            f.write(f"commented lines: {sorted(x + 1 for x in others)}\n")
            f.write(f"namespace {ns} lines {begin}..{end} of Case.lean\n")
            f.write(f"later references to generated names ({len(risks)}):\n")
            for x in risks:
                f.write("  " + x + "\n")
        print(d)


# ---------------------------------------------------------------- classify

def read(path):
    try:
        with open(path, errors="replace") as f:
            return f.read()
    except FileNotFoundError:
        return None


def kv_file(path):
    t = read(path)
    if t is None:
        return None
    out = {}
    for ln in t.splitlines():
        k, _, v = ln.partition("=")
        if k:
            out[k] = v
    return out


def yn(b):
    return "yes" if b else "no"


def blank_row(meta):
    row = {c: "" for c in RESULT_COLUMNS}
    for k in KEY_COLUMNS + ["invocation", "invocation_detail"]:
        row[k] = str(meta.get(k, ""))
    row["lean_options"] = ";".join(meta.get("lean_options", []))
    return row


def stage_table(route, base, ret_kind, outputs, thms):
    """Per stage: expected names (per OUTPUT), found names, closure verdict
    over exactly those theorems, their axioms.  `thms` maps simple name ->
    (verdict, axioms).  Theorems outside the required sets do not enter a
    stage's verdict (an extra observational theorem with a non-standard axiom
    does not fail the IR stage)."""
    res = {}
    req = REQUIRED.get(route)
    for st in STAGES:
        if req is None or ret_kind not in ("signal", "struct") or not outputs:
            res[st] = {"expected": None, "found": [], "closure": "unknown", "axioms": [], "missing": []}
            continue
        pat = req.get(st)
        if pat is None:
            res[st] = {"expected": [], "found": [], "closure": "not-in-route", "axioms": [], "missing": []}
            continue
        if "{s}" in pat:
            names = [pat.format(b=base, s=(f"_{o}" if ret_kind == "struct" else "")) for o in outputs]
        else:
            names = [pat.format(b=base)]
        found = [n for n in names if n in thms]
        missing = [n for n in names if n not in thms]
        axs = sorted({x for n in found for x in thms[n][1]})
        if missing:
            verdict = "missing"
        elif all(thms[n][0] == "OK" for n in found):
            verdict = "ok"
        else:
            verdict = "rejected"
        res[st] = {"expected": names, "found": found, "closure": verdict, "axioms": axs, "missing": missing}
    return res


def error_lines(text, case_name):
    """(line, message) of every Lean error reported against the case file."""
    out = []
    for m in re.finditer(r"(?m)^(\S*?)" + re.escape(case_name) + r":(\d+):(\d+): error: (.*)$", text):
        out.append((int(m.group(2)), m.group(4)))
    return out


def classify_dir(d, sv_group=""):
    meta = json.loads(read(os.path.join(d, "meta.json")) or "null")
    if meta is None:
        raise RuntimeError(f"{d}: meta.json missing or empty")
    row = blank_row(meta)
    row["sv_group_approx"] = sv_group
    ident = json.loads(read(os.path.join(d, "identity.json")) or "{}")
    for k in ["run_id", "attempt", "src_sha", "src_dirty_hash", "toolchain", "case_hash", "harness_hash"]:
        row[k] = str(ident.get(k, ""))
    row["effective_env"] = ";".join(ident.get("effective_env", []))
    row["cleared_env"] = ";".join(ident.get("cleared_env", []))
    row["stdout_ref"] = os.path.join(d, "stdout.txt")
    row["stderr_ref"] = os.path.join(d, "stderr.txt")
    if not meta.get("run"):
        row.update(ran="no", deep_run_record="not-run", strict_counted="no",
                   strict_blockers=meta["invocation"])
        return row
    run = kv_file(os.path.join(d, "run.txt"))
    if run is None:
        row.update(ran="unknown", invocation="harness-error", harness_error="run.txt missing",
                   deep_run_record="none", strict_counted="no", strict_blockers="harness-error")
        return row
    row["ran"] = "yes"
    for k in ["rc", "term", "timeout", "wall_s", "peak_rss_kb", "peak_rss_source", "cgroup_peak_kb",
              "mem_evidence", "reaped", "time_limit_s", "rlimit_as_kb"]:
        row[k] = run.get(k, "")
    row["deep_run_record"] = "measured"
    if run.get("harness_error"):
        row["harness_error"] = run["harness_error"]
        row["invocation"] = "harness-error"
    out = read(os.path.join(d, "stdout.txt")) or ""
    err = read(os.path.join(d, "stderr.txt")) or ""
    text = out + "\n" + err
    # namespace the block ran in (generated names land there)
    m = re.search(r"VED NS (\S+)", text)
    ns = m.group(1) if m else ""
    audits = re.findall(r"VED AUDIT (\S+) strict=(OK|REJECTED) axioms=\[([^\]]*)\]", text)
    thms = {}
    for n, v, ax in audits:
        simple = n[len(ns) + 1:] if ns and n.startswith(ns + ".") else n
        thms[simple] = (v, [x.strip() for x in ax.split(",") if x.strip()])
    # decl check (P1-2): resolved in the command's own scope, compared to `qualified`
    m = re.search(r"VED DECL resolved=(\S+) user=(\S+) inventory=(\S*) (match|mismatch)", text)
    if m:
        row["decl_resolved"], row["decl_check"] = m.group(1), m.group(4)
    elif "VED DECL absent" in text:
        row["decl_check"] = "absent"
        row["invocation"] = "unresolved-private" if meta.get("scan_private") else "unresolved-name"
    else:
        row["decl_check"] = "unknown"
    m = re.search(r"VED RET (signal|struct|other)", text)
    ret_kind = m.group(1) if m else ""
    m = re.search(r"VED SECONDRUN modules=(\d+)", text)
    row["second_run_modules"] = m.group(1) if m else ""
    outputs = re.findall(r"VED OUTPUT (\S+)", text)
    row["ret_kind"], row["outputs"] = ret_kind, ";".join(outputs)
    st = stage_table(meta.get("route", "unknown"), meta["base"], ret_kind, outputs, thms)
    required = set()
    for s in STAGES:
        e = st[s]["expected"]
        row[f"{s}_expected"] = "?" if e is None else str(len(e))
        row[f"{s}_found"] = str(len(st[s]["found"]))
        row[f"{s}_closure"] = st[s]["closure"]
        row[f"{s}_axioms"] = ";".join(st[s]["axioms"])
        required |= set(st[s]["found"])
    row["missing_theorems"] = ";".join(n for s in STAGES for n in st[s]["missing"])
    m = re.search(r"VED BODY (match|mismatch|absent)", text)
    row["observed_against_second_run"] = {"match": "match", "mismatch": "mismatch"}.get(
        m.group(1) if m else "", "unknown")
    skipped = sorted(set(re.findall(
        r"(IR replay skipped|\w+ bridge SKIPPED|SV-semantics theorem SKIPPED|text bridge SKIPPED)", text)))
    row["skipped"] = ";".join(skipped)
    trace_only = (meta["setting"] in TRACE_ONLY_SETTINGS
                  or "SPARKLE_DEEP_TRACE_ONLY" in text or "SPARKLE_DEEP_NOTHM" in text)
    row["trace_only"] = yn(trace_only)
    # errors inside the inserted block = the deep command's refusal;
    # outside = the file itself or the split harness
    errs = error_lines(text, "Case.lean")
    b, e = int(meta.get("block_begin", 0)), int(meta.get("block_end", 0))
    inside = [msg for ln, msg in errs if b <= ln <= e]
    outside = [f"{ln}:{msg[:80]}" for ln, msg in errs if not b <= ln <= e]
    row["refusal"] = (inside[0][:200] if inside else "").replace("\t", " ")
    row["errors_outside_block"] = str(len(outside))
    if outside and meta.get("kind") == "smoke-split":
        row["harness_error"] = ((row["harness_error"] + ";") if row["harness_error"] else "") + \
            "split-harness: errors outside the kept command: " + " | ".join(outside[:3])
    extra = {n: v for n, v in thms.items() if n not in required}
    row["n_theorems"] = str(len(thms))
    row["n_extra"] = str(len(extra))
    row["extra_rejected"] = str(sum(1 for v in extra.values() if v[0] == "REJECTED"))
    row["raw_axioms"] = ";".join(sorted({x for v in thms.values() for x in v[1]}))
    # strict_counted: never yes in U0 (module docstring)
    blockers = []
    if run.get("rc") != "0":
        blockers.append(f"rc={run.get('rc')}")
    if run.get("timeout") == "yes":
        blockers.append("timeout")
    if trace_only:
        blockers.append("trace-only")
    if row["refusal"]:
        blockers.append("refusal")
    if meta.get("kind") == "row" and row["invocation"] != "deep-in-file":
        blockers.append(row["invocation"])
    if row["harness_error"]:
        blockers.append("harness-error")
    for s in ("src", "ir"):
        if row[f"{s}_closure"] != "ok":
            blockers.append(f"{s}:{row[f'{s}_closure']}")
    if skipped:
        blockers.append("skipped")
    definite = bool(blockers)
    if row["observed_against_second_run"] != "match":
        blockers.append(f"body-vs-second-run:{row['observed_against_second_run']}")
    blockers += ["artifact-identity-not-probed", "theorem-types-not-checked"]
    row["strict_counted"] = "no" if definite else "unknown"
    row["strict_blockers"] = ";".join(blockers)
    return row


def emit(row):
    print("\t".join(str(row.get(c, "")).replace("\t", " ").replace("\n", " ") for c in RESULT_COLUMNS))


def cmd_classify(a):
    emit(classify_dir(a.case_dir, a.sv_group))


def cmd_error_row(a):
    meta = {"row": a.row, "setting": a.setting, "invocation": "harness-error"}
    try:
        rows = git_show_inventory(a.repo, a.commit, a.blob)
        r = rows[int(a.row) - 1]
        meta.update({k: r.get(k, "") for k in KEY_COLUMNS if k != "setting"})
        meta.update(inv_commit=a.commit, inv_blob=a.blob)
    except (Exception, SystemExit):
        pass
    row = blank_row(meta)
    row.update(invocation="harness-error", harness_error=a.reason, ran="no", deep_run_record="none",
               strict_counted="no", strict_blockers="harness-error", attempt=a.attempt,
               run_id=a.run_id)
    emit(row)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--repo", default=".")
    p.add_argument("--commit", default=INV_COMMIT)
    p.add_argument("--blob", default=INV_BLOB)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("rows")
    sub.add_parser("header")
    g = sub.add_parser("gen")
    g.add_argument("--row", required=True)
    g.add_argument("--setting", required=True)
    g.add_argument("--dir", required=True)
    c = sub.add_parser("classify")
    c.add_argument("case_dir")
    c.add_argument("--sv-group", default="", help="approximate S/C/H/M/D/P group from the SV baseline (kept separate)")
    e = sub.add_parser("error-row")
    e.add_argument("--row", required=True)
    e.add_argument("--setting", required=True)
    e.add_argument("--reason", required=True)
    e.add_argument("--attempt", default="")
    e.add_argument("--run-id", default="")
    sp = sub.add_parser("smoke-split")
    sp.add_argument("file")
    sp.add_argument("--out", required=True)
    a = p.parse_args()
    if a.cmd in ("gen", "smoke-split"):
        repo = os.path.realpath(a.repo)
        out = os.path.realpath(a.dir if a.cmd == "gen" else a.out)
        if out == repo or out.startswith(repo + os.sep):
            die("output must be outside the source tree")
    {"rows": cmd_rows, "gen": cmd_gen, "classify": cmd_classify, "smoke-split": cmd_smoke_split,
     "error-row": cmd_error_row, "header": lambda _: print("\t".join(RESULT_COLUMNS))}[a.cmd](a)


if __name__ == "__main__":
    main()
