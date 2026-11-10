#!/usr/bin/env python3
"""U1 MEASUREMENT harness: case generator and classifier for `#ved_u1` and
`#ved_u1_deep` (Tools/VedU1Entry.lean, Tools/VedU1Deep.lean).  MEASUREMENT
ONLY, never for main.  Derived from u0_gen.py (imported: inventory loading by
`git show` at a fixed commit with blob check, source scan, import closure,
option lines are reused unchanged).

Routes (the `setting` column; one record per row and route, 327 each):
  u1        in the inserted block:  set_option Elab.async false in #ved_u1 <ident>
  u1_deep   first the PREPARATION  `set_option Elab.async false in #verify_elab_deep <ident>`
            (default route; its time and failure have their own columns), then
            `set_option Elab.async false in #ved_u1_deep <ident>`.  If the
            preparation fails the U1 step is "not reached (prep failed)": the
            file still runs the U1 command (one Lean file cannot skip it), but
            its outcome is ignored.  Nothing from another declaration or a
            previous run is reused: every case is a fresh process.

Case construction is U0's: a COPY OF THE ORIGINAL SOURCE FILE with a block
inserted right after the original command (private decls, namespaces, opens,
scoped options are those of the original), the U1 tools' imports added.
Rows whose invocation can not be reproduced by an identifier (parameter
values, symbolicMode, command args) stay in the 327 as unsupported-invocation.

STRICT COUNTING ("returned-IR strict: U1, reset=0, order-free").  `strict_counted=yes`
only if every item holds, each established by the independent PROBE command
that runs after the entry command (`VED U1P ...` lines), never by `VED U1 OK`
alone:
  1 `<decl>.ved_u1` exists and is a theorem                      (probe THM)
  2 its stored type is exactly `U1Stmt <decl>.ved_contract <decl>.ved_mod @<decl>`
    (the expected Expr is rebuilt in the probe, as checkU1 does), no mvars
    / fvars, no universe params                                  (probe TYPE)
  3 `<decl>.ved_mod` exists, is a closed Module term, and the contract's last
    argument is that constant.  That it is the module RETURNED in the same run
    is the entry's own check (checkU1: `di.value == toExpr m`, evaluated back
    to m); the probe can only check existence/closedness, as the brief allows.
  4 kernel accepted synchronously: the case's U1 command carries
    `Elab.async false` and the theorem is in the environment afterwards
  5 `collectAxioms` closure of the theorem ⊆ {propext, Classical.choice, Quot.sound}
  6 exactly ONE output projection of the declaration's type      (probe OUTS);
    multi-output is refused by the entry, never partly counted
plus: the run was not killed/timed out, the decl resolved in the original scope
equals the inventory `qualified`, no `ved_u1`/`ved_mod` existed before the
entry, the `VED U1 OK` name matches `<resolved>.ved_u1`, and (u1_deep) the
preparation succeeded.  NOT counted: source-only facts, a subset of outputs, an
observed match with a separately synthesized artifact.  opt / SV are the
separate column `opt_sv` = "not connected"; U1 success is not release completion.

Subcommands: rows | header | gen | classify | error-row   (as u0_gen.py)
"""
import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)  # `python3 -I` does not add the script directory
import u0_gen  # noqa: E402
from u0_gen import (INV_BLOB, INV_COMMIT, INV_PATH, INV_ROWS, die, git_show_inventory,  # noqa: E402,F401
                    import_closure, invocation_of, kv_file, lean_option_lines, module_of, read,
                    scan_source)

# u1_deep_ns: as u1_deep, but the preparation and `#ved_u1_deep` are elaborated
# inside the DECLARATION's namespace (Lean's withNamespace, added to the original
# scope; opens / private names / options are kept).  `#verify_elab_deep` names
# its facts in the current namespace while `#ved_u1_deep` reads them under the
# declaration's prefix, so a command written outside that namespace (e.g.
# CircuitDoTest's `section SynthesisChecks`) never meets in u1_deep.  Reported
# as its own route; the scope difference is recorded, never hidden.
ROUTES = ("u1", "u1_deep", "u1_deep_ns")
DEEP_ROUTES = ("u1_deep", "u1_deep_ns")
ENTRY_CMD = {"u1": "#ved_u1", "u1_deep": "#ved_u1_deep", "u1_deep_ns": "#ved_u1_deep"}
IMPORTS = {"u1": ["Tools.VedU1Entry", "Tools.VedStrictAudit"],
           "u1_deep": ["Tools.VedU1Deep", "Tools.VedStrictAudit"],
           "u1_deep_ns": ["Tools.VedU1Deep", "Tools.VedStrictAudit"]}
STD3 = {"propext", "Classical.choice", "Quot.sound"}
# pipeline order inside the entry, for "later stages not reached"
PIPELINE = ["table", "multi-output", "synthesis", "artifact", "order", "type", "proof", "kernel", "audit"]
REFUSAL_STAGES = set(PIPELINE) | {"checker"}

KEY_COLUMNS = ["inv_commit", "inv_blob", "row", "file", "line", "command", "ns", "top",
               "qualified", "params", "options", "args", "setting"]
RESULT_COLUMNS = KEY_COLUMNS + [
    "invocation",            # u1-in-file | unsupported-invocation | unresolved-private | unresolved-name | harness-error
    "invocation_detail", "decl_resolved", "decl_check",
    "run_id", "attempt", "src_sha", "src_dirty_hash", "toolchain", "case_hash", "harness_hash",
    "effective_env", "lean_options", "cleared_env",
    "ran", "rc", "term", "timeout", "wall_s", "peak_rss_kb", "peak_rss_source", "cgroup_peak_kb",
    "mem_evidence", "reaped", "time_limit_s", "rlimit_as_kb",
    # preparation (u1_deep only)
    "prep_status", "prep_error",
    # the U1 step
    "u1_status",             # ok | refused | error | not-reached(prep failed) | not-reached(unsupported) | not-reached(run aborted) | unresolved
    "first_cause",           # see FIRST_CAUSES in the docstring of classify
    "refusal_stage", "refusal_msg", "later_stages_not_reached",
    "u1_ok_line", "u1_ok_thm",
    # independent probe
    "probe_present", "probe_thm", "probe_type", "probe_mvars", "probe_levels", "probe_mod",
    "probe_contract", "probe_outputs", "probe_axioms", "probe_axioms_std3", "probe_preexisting",
    "kernel_sync",
    # timing (ms from in-file monotonic markers; "combined" where not separable)
    "t_synthesis", "t_deep_prep", "t_u1_proof", "t_elab_kernel", "t_audit", "t_u1_combined",
    "t_probe", "t_total_wall_s",
    "errors_outside_block", "errors_outside_first",
    "strict_counted", "strict_label", "strict_blockers",
    "opt_sv", "harness_error", "stdout_ref", "stderr_ref",
]

# ------------------------------------------------------------------ case text

TIMER = '''open Lean Elab Command in
elab "#vedu1_t " s:str : command => do
  logInfo m!"VED U1T {s.getString} {← IO.monoMsNow}"'''

# u1_deep_ns only: elaborate one command inside the declaration's namespace
IN_DECLNS = '''open Lean Elab Command in
elab "#vedu1_in_declns " id:ident c:command : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  logInfo m!"VED U1N scope={n.getPrefix}"
  withNamespace n.getPrefix (elabCommand c)'''

PRE_PROBE = '''open Lean Elab Command in
run_cmd do
  logInfo m!"VED U1P NS {← getCurrNamespace}"
  try
    let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent "@TOP@".toName)
    let u := (privateToUserName? n).getD n
    logInfo m!"VED U1P DECL resolved={n} user={u} inventory=@Q@ {if u == "@Q@".toName then "match" else "mismatch"}"
    let env ← getEnv
    logInfo m!"VED U1P PRE thm={env.contains (n ++ `ved_u1)} mod={env.contains (n ++ `ved_mod)} contract={env.contains (n ++ `ved_contract)}"
  catch e => logInfo m!"VED U1P DECL absent: {← e.toMessageData.toString}"'''

# One independent probe after the entry command.  It never trusts `VED U1 OK`.
PROBE = '''open Lean Elab Command Meta in
run_cmd do
  try
    let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent "@TOP@".toName)
    let env ← getEnv
    let thm := n ++ `ved_u1
    let md := n ++ `ved_mod
    let ct := n ++ `ved_contract
    match env.find? thm with
    | none => logInfo m!"VED U1P THM absent"
    | some (.thmInfo _) => logInfo m!"VED U1P THM theorem"
    | some _ => logInfo m!"VED U1P THM not-a-theorem"
    if let some (.thmInfo ti) := env.find? thm then
      let expected := mkAppN (mkConst ``Tools.VedU1Contract.U1Stmt) #[mkConst ct, mkConst md, mkConst n]
      logInfo m!"VED U1P TYPE {if ti.type == expected then "exact" else "differs"}"
      logInfo m!"VED U1P MVARS type={ti.type.hasMVar} value={ti.value.hasMVar} fvars={ti.type.hasFVar || ti.value.hasFVar}"
      logInfo m!"VED U1P LEVELS {ti.levelParams.length}"
      let ax ← liftCoreM <| collectAxioms thm
      logInfo m!"VED U1P AXIOMS {Tools.VedStrictAudit.showNames (Tools.VedStrictAudit.sortNames ax)}"
    match env.find? md with
    | none => logInfo m!"VED U1P MOD absent"
    | some (.defnInfo di) =>
      let closed := !di.value.hasMVar && !di.value.hasFVar && !di.value.hasLooseBVars
      logInfo m!"VED U1P MOD closed={closed} type={di.type == mkConst ``Sparkle.IR.AST.Module}"
    | some _ => logInfo m!"VED U1P MOD not-a-def"
    match env.find? ct with
    | none => logInfo m!"VED U1P CONTRACT absent"
    | some (.defnInfo di) =>
      let ok := di.value.getAppFn.isConstOf ``Tools.VedU1Contract.contractOf &&
        di.value.getAppArgs.back? == some (mkConst md)
      logInfo m!"VED U1P CONTRACT {if ok then "bound-to-mod" else "other"}"
    | some _ => logInfo m!"VED U1P CONTRACT not-a-def"
    let tbl ← liftTermElabM (Tools.VedU1Contract.readTable n)
    logInfo m!"VED U1P OUTS {tbl.out.flat.length}"
  catch e => logInfo m!"VED U1P PROBE failed: {← e.toMessageData.toString}"'''


def block_pieces(r, route, ns):
    """[(segment, text)] in order; segment is None for plumbing."""
    opts = lean_option_lines(r["options"], "default")
    prefix = "".join(f"set_option {o} in\n" for o in ["Elab.async false"] + opts)
    top, q = r["top"], r["qualified"] or ""
    sub = lambda s: s.replace("@TOP@", top).replace("@Q@", q)
    p = [(None, f"-- ===== VED U1 BEGIN row {r['row']} route {route} (inventory {INV_COMMIT[:8]}) ====="),
         (None, f"namespace {ns}"), (None, TIMER), ("pre", sub(PRE_PROBE))]
    if route == "u1_deep_ns":
        wrap = lambda cmd: f"#vedu1_in_declns {top}\n" + prefix + cmd
        p += [(None, IN_DECLNS), (None, f"end {ns}"),
              ("prep", '#vedu1_t "p_begin"'), ("prep", wrap(f"#verify_elab_deep {top}")),
              ("prep", '#vedu1_t "p_end"'),
              ("u1", '#vedu1_t "u_begin"'), ("u1", wrap(f"{ENTRY_CMD[route]} {top}")),
              ("u1", '#vedu1_t "u_end"'), (None, f"namespace {ns}")]
    elif route == "u1_deep":
        # `#verify_elab_deep` names its facts in the CURRENT namespace, and
        # `#ved_u1_deep` looks them up under the declaration's own prefix, so
        # both run in the original command's scope, outside the case namespace
        # (inside it the facts land under VedU1Case_R<row> and are not found).
        p += [(None, f"end {ns}"),
              ("prep", '#vedu1_t "p_begin"'), ("prep", prefix + f"#verify_elab_deep {top}"),
              ("prep", '#vedu1_t "p_end"'),
              ("u1", '#vedu1_t "u_begin"'), ("u1", prefix + f"{ENTRY_CMD[route]} {top}"),
              ("u1", '#vedu1_t "u_end"'), (None, f"namespace {ns}")]
    else:
        p += [("u1", '#vedu1_t "u_begin"'), ("u1", prefix + f"{ENTRY_CMD[route]} {top}"),
              ("u1", '#vedu1_t "u_end"')]
    p += [("probe", sub(PROBE)), ("probe", '#vedu1_t "probe_end"'),
          (None, f"end {ns}"), (None, "-- ===== VED U1 END =====")]
    return p


def case_text(src_text, scan, r, route):
    ns = f"VedU1Case_R{r['row']}"
    lines = src_text.splitlines()
    ie, ei = scan["imports_end"], scan["end_index"]
    out = lines[:ie] + [f"import {m}" for m in IMPORTS[route]] + lines[ie:ei]
    out.append("")
    block_begin = len(out) + 1
    segs = {}
    for seg, text in block_pieces(r, route, ns):
        first = len(out) + 1
        out += text.splitlines()
        if seg:
            lo, hi = segs.get(seg, (first, 0))
            segs[seg] = (lo, len(out))
    block_end = len(out)
    out += lines[ei:]
    return "\n".join(out) + "\n", block_begin, block_end, segs


def cmd_rows(a):
    for r in git_show_inventory(a.repo, a.commit, a.blob):
        print("\t".join([r["row"], r["file"], r["line"], r["command"], r["qualified"] or r["top"]]))


def cmd_gen(a):
    rows = git_show_inventory(a.repo, a.commit, a.blob)
    i = int(a.row)
    if not 1 <= i <= len(rows):
        die(f"row {a.row} out of range 1..{len(rows)}")
    r = rows[i - 1]
    route = a.setting
    if route not in ROUTES:
        die(f"unknown route {route}; one of {list(ROUTES)}")
    d = a.dir
    os.makedirs(d, exist_ok=True)
    src_path = os.path.join(a.repo, r["file"])
    if not os.path.exists(src_path):
        # a fact about the measured tree, not a harness failure: the row stays in the 327, not run
        meta = {k: r.get(k, "") for k in KEY_COLUMNS if k != "setting"}
        meta.update(inv_commit=a.commit, inv_blob=a.blob, setting=route, route=route,
                    invocation="source-missing",
                    invocation_detail=f"{r['file']} does not exist in the measured tree", run=False,
                    kind="row", lean_options=[])
        open(os.path.join(d, "case.env"), "w").close()
        with open(os.path.join(d, "meta.json"), "w") as f:
            json.dump(meta, f, indent=1, sort_keys=True)
        print(d)
        return
    src_text = open(src_path, errors="replace").read()
    scan = scan_source(src_text, int(r["line"]), r["command"], r["top"])
    closure = import_closure(a.repo, IMPORTS[route])
    inv, detail, run = invocation_of(r, scan, closure)
    if inv == "deep-in-file":
        inv = "u1-in-file"
        detail = detail.replace("deep block", f"{route} block")
    meta = {k: r.get(k, "") for k in KEY_COLUMNS if k != "setting"}
    meta.update(inv_commit=a.commit, inv_blob=a.blob, setting=route, route=route, invocation=inv,
                invocation_detail=detail, run=run, module=module_of(r["file"]),
                base=r["top"].split(".")[-1], ns_suffix=f"VedU1Case_R{r['row']}",
                lean_options=lean_option_lines(r["options"], "default"),
                scan_private=scan["private"], scan_decl_seen=scan["decl_seen"], kind="row",
                async_false=True)
    if run:
        text, b, e, segs = case_text(src_text, scan, r, route)
        with open(os.path.join(d, "Case.lean"), "w") as f:
            f.write(text)
        meta.update(block_begin=b, block_end=e, segs=segs)
    open(os.path.join(d, "case.env"), "w").close()   # no extra SPARKLE_* settings
    with open(os.path.join(d, "meta.json"), "w") as f:
        json.dump(meta, f, indent=1, sort_keys=True)
    print(d)


# ---------------------------------------------------------------- classify

MSG_RE = re.compile(r"^(?:\S*?)Case\.lean:(\d+):(\d+): (?:(error|warning|info)(?:\([^)\s]*\))?: )?(.*)$")


# Lean's command-line driver prints errors and warnings with a
# `Case.lean:L:C:` prefix but INFO messages (logInfo: `VED U1 OK`, the probe's
# `VED U1P ...`, the timers) as bare text with no position.  A bare line that
# starts with "VED " is therefore its own message, placed by the timer markers
# around it (elaboration order): before p_begin/u_begin -> pre, p_begin..p_end
# -> prep, u_begin..u_end -> u1, u_end..probe_end -> probe.
MARK_SEG = {"p_begin": "prep", "p_end": None, "u_begin": "u1", "u_end": "probe", "probe_end": None}


def messages(text, segs=None):
    """[(line, severity, full text)] of the messages Lean printed for the case file
    (continuation lines are appended to the message they follow).  Bare `VED `
    info lines get the first line of the segment the markers put them in."""
    out, cur = [], "pre"
    for ln in text.splitlines():
        m = MSG_RE.match(ln)
        if m:
            out.append([int(m.group(1)), m.group(3) or "info", m.group(4)])
            continue
        if ln.startswith("VED "):
            t = re.match(r"VED U1T (\w+) ", ln)
            seg_here = cur
            if t and t.group(1) in MARK_SEG:
                cur = MARK_SEG[t.group(1)]
                seg_here = "probe" if t.group(1) == "probe_end" else (cur or seg_here)
            line = (segs or {}).get(seg_here, (0, 0))[0] if seg_here else 0
            out.append([line, "info", ln])
        elif out:
            out[-1][2] += "\n" + ln
    return [tuple(x) for x in out]


def seg_of(line, segs):
    for name, (lo, hi) in segs.items():
        if lo <= line <= hi:
            return name
    return None


def blank_row(meta):
    row = {c: "" for c in RESULT_COLUMNS}
    for k in KEY_COLUMNS + ["invocation", "invocation_detail"]:
        row[k] = str(meta.get(k, ""))
    row["lean_options"] = ";".join(meta.get("lean_options", []))
    row["opt_sv"] = "not connected"
    return row


def first_line(s, n=200):
    return s.split("\n", 1)[0][:n].replace("\t", " ")


def later_stages(stage):
    if stage in PIPELINE:
        return ";".join(PIPELINE[PIPELINE.index(stage) + 1:])
    return ""


def parse_probe(text):
    """The `VED U1P` lines of the probe segment -> dict (None-valued when absent)."""
    p = {}
    pats = [("thm", r"VED U1P THM (\S+)"), ("type", r"VED U1P TYPE (\S+)"),
            ("mvars", r"VED U1P MVARS type=(\w+) value=(\w+) fvars=(\w+)"),
            ("levels", r"VED U1P LEVELS (\d+)"), ("mod", r"VED U1P MOD (.*)"),
            ("contract", r"VED U1P CONTRACT (\S+)"), ("outs", r"VED U1P OUTS (\d+)"),
            ("axioms", r"VED U1P AXIOMS \[([^\]]*)\]"), ("failed", r"VED U1P PROBE failed: (.*)")]
    for k, pat in pats:
        m = re.search(pat, text)
        p[k] = m.groups() if m else None
    return p


def classify_dir(d, sv_group=""):
    meta = json.loads(read(os.path.join(d, "meta.json")) or "null")
    if meta is None:
        raise RuntimeError(f"{d}: meta.json missing or empty")
    row = blank_row(meta)
    route = meta.get("route", "")
    ident = json.loads(read(os.path.join(d, "identity.json")) or "{}")
    for k in ["run_id", "attempt", "src_sha", "src_dirty_hash", "toolchain", "case_hash", "harness_hash"]:
        row[k] = str(ident.get(k, ""))
    row["effective_env"] = ";".join(ident.get("effective_env", []))
    row["cleared_env"] = ";".join(ident.get("cleared_env", []))
    row["stdout_ref"] = os.path.join(d, "stdout.txt")
    row["stderr_ref"] = os.path.join(d, "stderr.txt")
    row["prep_status"] = "n/a" if route == "u1" else "not-run"
    if not meta.get("run"):
        row.update(ran="no", strict_counted="no", strict_blockers=meta["invocation"],
                   first_cause=meta["invocation"], u1_status="not-reached(unsupported)",
                   strict_label="no")
        return row
    run = kv_file(os.path.join(d, "run.txt"))
    if run is None:
        row.update(ran="unknown", invocation="harness-error", harness_error="run.txt missing",
                   strict_counted="no", strict_blockers="harness-error", first_cause="harness-error",
                   u1_status="not-reached(run aborted)", strict_label="no")
        return row
    row["ran"] = "yes"
    for k in ["rc", "term", "timeout", "peak_rss_kb", "peak_rss_source", "cgroup_peak_kb",
              "mem_evidence", "reaped", "time_limit_s", "rlimit_as_kb"]:
        row[k] = run.get(k, "")
    row["t_total_wall_s"] = run.get("wall_s", "")
    if run.get("harness_error"):
        row["harness_error"] = run["harness_error"]
        row["invocation"] = "harness-error"
    out = read(os.path.join(d, "stdout.txt")) or ""
    err = read(os.path.join(d, "stderr.txt")) or ""
    text = out + "\n" + err
    segs = {k: tuple(v) for k, v in meta.get("segs", {}).items()}
    msgs = messages(text, segs)
    in_seg = lambda name: [(ln, sev, t) for ln, sev, t in msgs if seg_of(ln, segs) == name]
    outside = [(ln, t) for ln, sev, t in msgs if sev == "error" and seg_of(ln, segs) is None]
    row["errors_outside_block"] = str(len(outside))
    row["errors_outside_first"] = (f"{outside[0][0]}:{first_line(outside[0][1], 120)}" if outside else "")

    # decl resolved in the command's own scope (pre-probe)
    m = re.search(r"VED U1P DECL resolved=(\S+) user=(\S+) inventory=(\S*) (match|mismatch)", text)
    resolved = ""
    if m:
        resolved = m.group(1)
        row["decl_resolved"], row["decl_check"] = resolved, m.group(4)
        # the inventory gives a scope-relative name when its `ns` is empty (245
        # rows, also for files inside a namespace): the identifier resolved in
        # the original command's own scope, so a suffix match is that name
        q, user = meta.get("qualified", "") or "", m.group(2)
        if (m.group(4) == "mismatch" and not (meta.get("ns") or "") and q
                and user.endswith("." + q)):
            row["decl_check"] = "match-scoped"
    elif "VED U1P DECL absent" in text:
        row["decl_check"] = "absent"
        row["invocation"] = "unresolved-private" if meta.get("scan_private") else "unresolved-name"
    else:
        row["decl_check"] = "unknown"
    m = re.search(r"VED U1P PRE thm=(\w+) mod=(\w+) contract=(\w+)", text)
    pre_exist = bool(m and "true" in m.groups())
    row["probe_preexisting"] = "unknown" if not m else ("yes" if pre_exist else "no")

    # timing markers (monotonic ms inside the Lean process)
    marks = {k: int(v) for k, v in re.findall(r"VED U1T (\w+) (\d+)", text)}
    dt = lambda a, b: str(marks[b] - marks[a]) if a in marks and b in marks else ""
    row["t_deep_prep"] = dt("p_begin", "p_end") if route in DEEP_ROUTES else "n/a"
    row["t_u1_combined"] = dt("u_begin", "u_end")
    row["t_probe"] = dt("u_end", "probe_end")
    sep = "combined" if row["t_u1_combined"] else ""
    for c in ("t_synthesis", "t_u1_proof", "t_elab_kernel", "t_audit"):
        row[c] = sep        # not separable without changing the U1 tools

    # preparation (u1_deep)
    prep_ok = True
    if route in DEEP_ROUTES:
        perr = [t for ln, sev, t in in_seg("prep") if sev == "error"]
        if perr:
            row["prep_status"], row["prep_error"] = "failed", first_line(perr[0])
            prep_ok = False
        elif "p_end" in marks:
            row["prep_status"] = "ok"
        else:
            row["prep_status"], prep_ok = "incomplete", False

    # the U1 step
    u1 = in_seg("u1")
    u1_errs = [t for ln, sev, t in u1 if sev == "error"]
    okm = next((re.match(r"VED U1 OK (\S+):", t) for ln, sev, t in u1 if t.startswith("VED U1 OK ")), None)
    row["u1_ok_line"] = "yes" if okm else "no"
    row["u1_ok_thm"] = okm.group(1) if okm else ""
    refusal = None
    for t in u1_errs:
        m = re.match(r"VED U1 REFUSED (\S+) \[([\w-]+)\]: ?(.*)", t, re.S)
        if m:
            refusal = (m.group(2), m.group(3))
            break
    u1_done = "u_end" in marks
    # --- external / run-level causes (first)
    term, ev = run.get("term", ""), run.get("mem_evidence", "")
    rcv = run.get("rc", "")
    abnormal = term.startswith("signal_") or "signal_unknown" in term
    oom = ("cgroup_oom_kill" in ev) or ("allocator_text" in ev and abnormal)
    if run.get("timeout") == "yes":
        cause = "external-timeout"
    elif oom:
        cause = "oom"
    elif abnormal:
        cause = "signal"
    elif run.get("harness_error"):
        cause = "harness-error"
    elif row["decl_check"] == "absent":
        cause = "unresolved"
    elif not msgs and not marks:
        cause = "harness-error"
        row["harness_error"] = (row["harness_error"] + ";" if row["harness_error"] else "") + \
            f"no Lean messages and no markers (rc={rcv}; import failure?)"
    elif route in DEEP_ROUTES and not prep_ok and "p_end" in marks:
        cause = "prep"
    else:
        cause = ""
    if cause:
        # run-level cause: the U1 step is not meaningful beyond what was observed
        if cause == "prep":
            row["u1_status"] = "not-reached(prep failed)"
        elif cause == "unresolved":
            row["u1_status"] = "unresolved"
        else:
            row["u1_status"] = "not-reached(run aborted)" if not u1_done else "ok-observed-then-aborted"
        row["first_cause"] = cause
        if cause == "prep":
            row["later_stages_not_reached"] = "u1:" + ";".join(PIPELINE)
    elif refusal:
        stage, msg = refusal
        row.update(refusal_stage=stage, refusal_msg=first_line(msg))
        cause = stage
        # the text heuristics only refine stages whose message is a raw error
        # from elsewhere; a [proof]/[type]/... refusal stays at its stage (its
        # goal text may mention runCircuitH without being that failure)
        if stage in ("synthesis", "checker"):
            if "Missing cases" in msg:
                cause = "missing-cases"
            elif "runCircuitH" in msg:
                cause = "runCircuitH-location"
        row.update(u1_status="refused", first_cause=cause, later_stages_not_reached=later_stages(stage))
    elif u1_errs:
        e0 = u1_errs[0]
        if "Missing cases" in e0:
            cause = "missing-cases"
        elif "runCircuitH" in e0:
            cause = "runCircuitH-location"
        elif re.search(r"unexpected token|parse error|unknown command", e0):
            cause = "syntax"
        elif re.search(r"maxHeartbeats|deterministic.*timeout", e0):
            cause = "uncaught-heartbeat"
        elif re.search(r"maximum recursion", e0):
            cause = "uncaught-recursion"
        else:
            cause = "uncaught-error"
        row.update(u1_status="error", first_cause=cause, refusal_msg=first_line(e0))
    elif not okm:
        row.update(u1_status="error", first_cause="no-u1-result",
                   refusal_msg="neither `VED U1 OK` nor an error in the U1 segment")

    # --- the independent probe and the strict verdict
    pm = [t for ln, sev, t in in_seg("probe")]
    p = parse_probe("\n".join(pm))
    row["probe_present"] = "yes" if "probe_end" in marks and not p["failed"] else "no"
    if p["thm"]:
        row["probe_thm"] = p["thm"][0]
    if p["type"]:
        row["probe_type"] = p["type"][0]
    if p["mvars"]:
        row["probe_mvars"] = "no" if p["mvars"] == ("false", "false", "false") else "yes"
    if p["levels"]:
        row["probe_levels"] = p["levels"][0]
    if p["mod"]:
        row["probe_mod"] = p["mod"][0]
    if p["contract"]:
        row["probe_contract"] = p["contract"][0]
    if p["outs"]:
        row["probe_outputs"] = p["outs"][0]
    axs = []
    if p["axioms"]:
        axs = [x.strip() for x in p["axioms"][0].split(",") if x.strip()]
        row["probe_axioms"] = ";".join(axs)
        row["probe_axioms_std3"] = "yes" if set(axs) <= STD3 else "no"
    row["kernel_sync"] = ("yes" if meta.get("async_false") and p["thm"] and p["thm"][0] == "theorem"
                          else "no")

    bl = []
    if cause:
        bl.append(f"cause:{cause}")
    if meta.get("invocation") != "u1-in-file":
        bl.append(meta.get("invocation", "?"))
    if row["harness_error"]:
        bl.append("harness-error")
    if route in DEEP_ROUTES and not prep_ok:
        bl.append(f"prep:{row['prep_status']}")
    if not okm:
        bl.append("no-VED-U1-OK-line")
    if u1_errs:
        bl.append("u1-segment-error")
    if row["probe_present"] != "yes":
        bl.append("probe-missing" + (f"({first_line(p['failed'][0], 80)})" if p["failed"] else ""))
    if row["probe_thm"] != "theorem":
        bl.append(f"thm:{row['probe_thm'] or 'unknown'}")
    if row["probe_type"] != "exact":
        bl.append(f"type:{row['probe_type'] or 'unknown'}")
    if row["probe_mvars"] != "no":
        bl.append(f"mvars:{row['probe_mvars'] or 'unknown'}")
    if row["probe_levels"] not in ("0",):
        bl.append(f"levels:{row['probe_levels'] or 'unknown'}")
    if not row["probe_mod"].startswith("closed=true type=true"):
        bl.append(f"mod:{row['probe_mod'] or 'unknown'}")
    if row["probe_contract"] != "bound-to-mod":
        bl.append(f"contract:{row['probe_contract'] or 'unknown'}")
    if row["probe_outputs"] != "1":
        bl.append(f"outputs:{row['probe_outputs'] or 'unknown'}")
    if row["probe_axioms_std3"] != "yes":
        extra = sorted(set(axs) - STD3)
        bl.append("axioms:" + (",".join(extra) if extra else "unknown"))
    if row["kernel_sync"] != "yes":
        bl.append("kernel-not-sync")
    if row["decl_check"] not in ("match", "match-scoped"):
        bl.append(f"decl:{row['decl_check']}")
    if pre_exist or row["probe_preexisting"] != "no":
        bl.append(f"preexisting:{row['probe_preexisting']}")
    if resolved and row["u1_ok_thm"] != f"{resolved}.ved_u1":
        bl.append(f"ok-thm-name:{row['u1_ok_thm'] or 'none'}")
    if row["ran"] != "yes" or "probe_end" not in marks:
        bl.append("run-incomplete")
    strict = not bl
    row["strict_counted"] = "yes" if strict else "no"
    row["strict_label"] = "returned-IR strict: U1, reset=0, order-free" if strict else "no"
    row["strict_blockers"] = ";".join(bl)
    if strict:
        row.update(u1_status="ok", first_cause="none")
    elif row["u1_ok_line"] == "yes" and not cause and not refusal and not u1_errs:
        # `VED U1 OK` printed, but the independent probe disagrees: never counted
        row.update(u1_status="ok-line-not-confirmed", first_cause="probe-rejected")
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
    row.update(invocation="harness-error", harness_error=a.reason, ran="no", strict_counted="no",
               strict_blockers="harness-error", first_cause="harness-error", attempt=a.attempt,
               run_id=a.run_id, u1_status="not-reached(run aborted)", strict_label="no")
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
    g.add_argument("--setting", required=True, help="route: u1 | u1_deep | u1_deep_ns")
    g.add_argument("--dir", required=True)
    c = sub.add_parser("classify")
    c.add_argument("case_dir")
    c.add_argument("--sv-group", default="", help="ignored (kept for the runner's CLI)")
    e = sub.add_parser("error-row")
    e.add_argument("--row", required=True)
    e.add_argument("--setting", required=True)
    e.add_argument("--reason", required=True)
    e.add_argument("--attempt", default="")
    e.add_argument("--run-id", default="")
    a = p.parse_args()
    if a.cmd == "gen":
        repo, out = os.path.realpath(a.repo), os.path.realpath(a.dir)
        if out == repo or out.startswith(repo + os.sep):
            die("output must be outside the source tree")
    {"rows": cmd_rows, "gen": cmd_gen, "classify": cmd_classify, "error-row": cmd_error_row,
     "header": lambda _: print("\t".join(RESULT_COLUMNS))}[a.cmd](a)


if __name__ == "__main__":
    main()
