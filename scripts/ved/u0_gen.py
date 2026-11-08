#!/usr/bin/env python3
"""U0 measurement harness for `#verify_elab_deep` (generator and classifier).

WRITTEN, NOT RUN (2026-11-08).  Design: docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md.

The inventory is read ONLY with `git show <commit>:<path>` at a fixed commit,
and its blob SHA is checked, so a moved branch can not change the
denominator (327 rows).  Every output goes under --out, which must be outside
the source tree (the Job's report directory).

Subcommands
  rows      list the inventory rows (row id = 1-based data line number)
  gen       write one case directory for (row, setting): Case.lean, case.env, meta.tsv
  classify  read one case directory after u0_case.sh ran it, print one TSV row
  smoke-split  split an existing deep test file into one-command variants
  header    print the result TSV header

The classifier only reads text the case produced.  It never turns a
PROVEN string into success: a row is strict-counted only when the case's own
Lean-side probes (VED AUDIT / VED BODY / VED REQ lines) say so.
"""
import argparse
import csv
import io
import os
import re
import subprocess
import sys

INV_PATH = "scripts/gen5/fgc_baseline/inventory.tsv"
# fixed by the design doc: par/fgc-s0 tip read on 2026-11-08
INV_COMMIT = "f694355fcabee7c9915c9c83991e4a0b032fedf8"
INV_BLOB = "4a5b801f3a665ed95262b803109aa3f76005065d"

SETTINGS = {
    # name: (lean options inserted in the case file, environment variables)
    "default": ([], {}),
    "shared": (["set_option sparkle.deepShare true"], {}),
    "profile": ([], {"SPARKLE_PROFILE": "1", "SPARKLE_DEEP_DEBUG": "1"}),
    # diagnostic modes: never counted as complete success
    "traceonly-shared": (["set_option sparkle.deepShare true"], {"SPARKLE_DEEP_TRACE_ONLY": "1"}),
    "defsonly-default": ([], {"SPARKLE_DEEP_NOTHM": "1"}),
}
TRACE_ONLY_SETTINGS = {"traceonly-shared", "defsonly-default"}

RESULT_COLUMNS = [
    # keys
    "inv_commit", "inv_blob", "row", "file", "line", "command", "ns", "top", "decl",
    "params", "options", "args", "setting", "sparkle_sha", "sv_group_approx",
    # run
    "rc", "timeout", "oom_or_limit", "wall_s", "peak_rss_kb", "time_limit_s", "mem_limit_kb",
    # classification (separate columns, never merged)
    "source_deep_theorem",      # yes: {base}_deep_trace / _sdeep_trace exists and is a theorem
    "real_body_replay",         # yes: a replay theorem over the module's own m.body (VED BODY real)
    "reordered_body_replay",    # yes: replay exists but over deepOrderBody m.body (VED BODY reordered)
    "opt_bridged",              # yes: _sdeep_signal_runOpt exists (optimizeModule, NOT checkedOptimize)
    "sv_bridged",               # yes: _sdeep_signal_svOpt or _sdeep_text_parses exists
    "skipped",                  # replay or bridge SKIPPED messages (list)
    "nonstd_axioms",            # yes: some produced theorem REJECTED by the strict audit
    "trace_only",               # yes: a diagnostic setting, or a TRACE_ONLY / defs-only message
    "refusal",                  # first #verify_elab_deep error text (refusal reason), else empty
    "strict_counted",           # yes only under the rule in the design doc §3.4
    "n_theorems", "n_strict_ok", "n_rejected",
    "raw_axioms",               # union of raw closures, ';'-separated
    "deep_run_record",          # 'measured' here; 'none' = unconfirmed, NOT failure
    "stdout_ref", "stderr_ref", "audit_ref",
]


def git_show_inventory(repo, commit, blob):
    got = subprocess.run(["git", "rev-parse", f"{commit}:{INV_PATH}"], cwd=repo,
                         capture_output=True, text=True, check=True).stdout.strip()
    if got != blob:
        sys.exit(f"inventory blob mismatch at {commit}: {got} != {blob}")
    text = subprocess.run(["git", "show", f"{commit}:{INV_PATH}"], cwd=repo,
                          capture_output=True, text=True, check=True).stdout
    rows = list(csv.DictReader(io.StringIO(text), delimiter="\t"))
    if len(rows) != 327:
        sys.exit(f"inventory has {len(rows)} rows, expected 327")
    for i, r in enumerate(rows, 1):
        r["row"] = str(i)
    return rows


def module_of(path):
    if not path.endswith(".lean"):
        sys.exit(f"not a .lean file: {path}")
    return path[:-5].replace("/", ".")


def decl_of(r):
    # `qualified` is the extractor's reference value (open is not resolved);
    # a name that does not resolve is recorded as refusal 'unresolved-name'
    return r["qualified"] or r["top"]


def lean_options(opts):
    out = []
    for kv in filter(None, (o.strip() for o in opts.split(","))):
        k, _, v = kv.partition("=")
        if k == "symbolicMode":
            continue  # #synthesizeParameterizedVerilog only; recorded in the options column
        out.append(f"set_option {k} {v}")
    return out


def case_text(r, setting):
    rid = r["row"]
    decl = decl_of(r)
    base = decl.split(".")[-1]
    ns = f"VedU0.R{rid}"
    opts, _ = SETTINGS[setting]
    lines = [
        "import Tools.DeepElab",
        "import Tools.VedStrictAudit",
        f"import {module_of(r['file'])}",
        "",
        f"-- U0 case: inventory {INV_COMMIT[:8]} row {rid} {r['file']}:{r['line']} {r['command']} {r['top']}",
        f"-- params: {r['params'] or '-'}  options: {r['options'] or '-'}  args: {r['args'] or '-'}  setting: {setting}",
        "set_option Elab.async false",  # synchronous kernel registration
    ]
    lines += lean_options(r["options"]) + opts
    lines += [
        "",
        f"namespace {ns}",
        (f"open {r['ns']}" if r["ns"] else ""),
        "",
        f"#verify_elab_deep {decl}",
        "",
        "-- every theorem the command registered under this namespace: strict verdict + raw closure",
        f"#ved_audit_generated {ns}",
        "",
        "-- which body the replay is about (real m.body or deepOrderBody m.body)",
        "open Lean Elab Command in",
        "run_cmd do",
        f"  let decl ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent `{decl})",
        "  let design ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical decl)",
        "  match design.modules with",
        "  | [m] =>",
        f"    for tag in [\"_deep_body\", \"_sdeep_body\"] do",
        f"      match (← getEnv).find? (Name.mkStr `{ns} (\"{base}\" ++ tag)) with",
        "      | none => logInfo m!\"VED BODY {tag} absent\"",
        "      | some ci =>",
        "        let v := (ci.value? (allowOpaque := true)).getD default",
        "        if v == toExpr m.body then logInfo m!\"VED BODY {tag} real\"",
        "        else logInfo m!\"VED BODY {tag} reordered\"",
        "  | ms => logInfo m!\"VED BODY n/a ({ms.length} modules)\"",
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def cmd_rows(a):
    for r in git_show_inventory(a.repo, a.commit, a.blob):
        print("\t".join([r["row"], r["file"], r["line"], r["command"], decl_of(r)]))


def cmd_gen(a):
    rows = git_show_inventory(a.repo, a.commit, a.blob)
    r = rows[int(a.row) - 1]
    if a.setting not in SETTINGS:
        sys.exit(f"unknown setting {a.setting}; one of {sorted(SETTINGS)}")
    d = os.path.join(a.out, f"R{int(a.row):03d}_{a.setting}")
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "Case.lean"), "w") as f:
        f.write(case_text(r, a.setting))
    _, env = SETTINGS[a.setting]
    with open(os.path.join(d, "case.env"), "w") as f:
        for k, v in env.items():
            f.write(f"{k}={v}\n")
    with open(os.path.join(d, "meta.tsv"), "w") as f:
        keys = ["inv_commit", "inv_blob", "row", "file", "line", "command", "ns", "top", "decl",
                "params", "options", "args", "setting", "module"]
        vals = [a.commit, a.blob, r["row"], r["file"], r["line"], r["command"], r["ns"], r["top"],
                decl_of(r), r["params"], r["options"], r["args"], a.setting, module_of(r["file"])]
        f.write("\t".join(keys) + "\n" + "\t".join(v.replace("\t", " ") for v in vals) + "\n")
    print(d)


def cmd_smoke_split(a):
    """One variant per `#verify_elab_deep` of an existing test file: the other
    commands are commented out, the kept one runs inside a fresh namespace and
    is followed by `#ved_audit_generated`.  The as-is file is still run once
    (u0_case.sh --smoke-file) for the comparison with the September counts."""
    src = open(a.file).read().splitlines()
    cmds = [i for i, ln in enumerate(src) if re.match(r"#verify_elab_deep\s+\S+", ln)]
    def prefix_line(i):
        return i - 1 if i > 0 and re.match(r"set_option\s+\S+\s+\S+\s+in\s*$", src[i - 1]) else None
    stem = os.path.splitext(os.path.basename(a.file))[0]
    for k, keep in enumerate(cmds):
        out, stack = [], []
        for i, ln in enumerate(src):
            m = re.match(r"namespace\s+(\S+)", ln)
            if m:
                stack.append(m.group(1))
            elif re.match(r"end\s+\S+", ln) and stack:
                stack.pop()
            others = {j for c in cmds if c != keep for j in (c, prefix_line(c)) if j is not None}
            if i in others:
                out.append("-- U0 split: " + ln)
            elif i == (prefix_line(keep) if prefix_line(keep) is not None else keep):
                out.append("namespace VedU0Smoke")
                out.append(ln)
            elif i == keep:
                out.append(ln)
            else:
                out.append(ln)
            if i == keep:
                ns = ".".join(stack + ["VedU0Smoke"])
                out.append("end VedU0Smoke")
                out.append(f"#ved_audit_generated {ns}")
        if not any(ln.startswith("import Tools.VedStrictAudit") for ln in out):
            first = next(i for i, ln in enumerate(out) if ln.startswith("import "))
            out.insert(first, "import Tools.VedStrictAudit")
        d = os.path.join(a.out, f"S_{stem}_{k:02d}")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "Case.lean"), "w") as f:
            f.write("\n".join(out) + "\n")
        open(os.path.join(d, "case.env"), "w").close()
        decl = src[keep].split()[1]
        with open(os.path.join(d, "meta.tsv"), "w") as f:
            f.write("\t".join(["inv_commit", "inv_blob", "row", "file", "line", "command", "ns", "top",
                               "decl", "params", "options", "args", "setting", "module"]) + "\n")
            f.write("\t".join(["-", "-", f"smoke:{stem}:{k}", a.file, str(keep + 1), "#verify_elab_deep",
                               "", decl, decl, "", "", "", "as-in-file", "-"]) + "\n")
        print(d)


def read(path):
    try:
        with open(path, errors="replace") as f:
            return f.read()
    except FileNotFoundError:
        return ""


def kv_file(path):
    out = {}
    for ln in read(path).splitlines():
        k, _, v = ln.partition("=")
        if k:
            out[k] = v
    return out


def cmd_classify(a):
    d = a.case_dir
    meta_lines = read(os.path.join(d, "meta.tsv")).splitlines()
    meta = dict(zip(meta_lines[0].split("\t"), meta_lines[1].split("\t")))
    run = kv_file(os.path.join(d, "run.txt"))           # written by u0_case.sh
    out = read(os.path.join(d, "stdout.txt"))
    err = read(os.path.join(d, "stderr.txt"))
    text = out + "\n" + err
    base = meta["decl"].split(".")[-1]
    audits = re.findall(r"VED AUDIT (\S+) strict=(OK|REJECTED) axioms=\[([^\]]*)\]", text)
    thms = {n: (v, ax) for n, v, ax in audits}
    last = {n.split(".")[-1] for n in thms}

    def has(suffix_re):
        return any(re.fullmatch(re.escape(base) + suffix_re, x) for x in last)

    src = has(r"(_[^.]*)?_deep_trace") or has(r"_sdeep_trace")
    replay = has(r"(_[^.]*)?_deep_signal_run") or has(r"_sdeep_signal_run")
    body = set(re.findall(r"VED BODY _s?deep_body (real|reordered)", text))
    real = replay and "real" in body and "reordered" not in body
    reord = replay and "reordered" in body
    opt = has(r"_sdeep_signal_runOpt")
    sv = has(r"_sdeep_signal_svOpt") or has(r"_sdeep_text_parses")
    skipped = sorted(set(re.findall(r"(IR replay skipped|\w+ bridge SKIPPED|SV-semantics theorem SKIPPED|text bridge SKIPPED)", text)))
    rejected = [n for n, (v, _) in thms.items() if v == "REJECTED"]
    trace_only = (meta["setting"] in TRACE_ONLY_SETTINGS
                  or "SPARKLE_DEEP_TRACE_ONLY" in text or "defs only (SPARKLE_DEEP_NOTHM)" in text)
    m = re.search(r"error: (#verify_elab_deep[^\n]*)", text) or re.search(r"error: ([^\n]*)", text)
    refusal = m.group(1)[:200] if m else ""
    if "unknown identifier" in refusal or "unknown constant" in refusal:
        refusal = "unresolved-name: " + refusal
    rc = run.get("rc", "")
    timeout = run.get("timeout", "")
    # strict-counted (design doc §3.4): the replay over the module's OWN body
    # exists, every produced theorem passed the strict audit, the run ended
    # normally, nothing was skipped, and no diagnostic mode was used.
    strict = (rc == "0" and timeout == "no" and src and real and not rejected
              and not skipped and not trace_only and not refusal)
    axs = sorted({x.strip() for _, (_, ax) in thms.items() for x in ax.split(",") if x.strip()})
    yn = lambda b: "yes" if b else "no"
    row = {
        **{k: meta.get(k, "") for k in ["inv_commit", "inv_blob", "row", "file", "line", "command",
                                         "ns", "top", "decl", "params", "options", "args", "setting"]},
        "sparkle_sha": run.get("sparkle_sha", ""),
        "sv_group_approx": a.sv_group or "",
        "rc": rc, "timeout": timeout, "oom_or_limit": run.get("limit", ""),
        "wall_s": run.get("wall_s", ""), "peak_rss_kb": run.get("peak_rss_kb", ""),
        "time_limit_s": run.get("time_limit_s", ""), "mem_limit_kb": run.get("mem_limit_kb", ""),
        "source_deep_theorem": yn(src), "real_body_replay": yn(real),
        "reordered_body_replay": yn(reord), "opt_bridged": yn(opt), "sv_bridged": yn(sv),
        "skipped": ";".join(skipped), "nonstd_axioms": yn(bool(rejected)),
        "trace_only": yn(trace_only), "refusal": refusal.replace("\t", " "),
        "strict_counted": yn(strict),
        "n_theorems": str(len(thms)), "n_strict_ok": str(len(thms) - len(rejected)),
        "n_rejected": str(len(rejected)), "raw_axioms": ";".join(axs),
        "deep_run_record": "measured" if rc != "" else "none",
        "stdout_ref": os.path.join(d, "stdout.txt"), "stderr_ref": os.path.join(d, "stderr.txt"),
        "audit_ref": os.path.join(d, "stdout.txt") + "#VED",
    }
    print("\t".join(row[c] for c in RESULT_COLUMNS))


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
    g.add_argument("--out", required=True)
    c = sub.add_parser("classify")
    c.add_argument("case_dir")
    c.add_argument("--sv-group", default="", help="approximate S/C/H/M/D/P group from the SV baseline (kept separate)")
    sp = sub.add_parser("smoke-split")
    sp.add_argument("file")
    sp.add_argument("--out", required=True)
    a = p.parse_args()
    if a.cmd in ("gen", "smoke-split"):
        repo = os.path.realpath(a.repo)
        out = os.path.realpath(a.out)
        if out == repo or out.startswith(repo + os.sep):
            sys.exit("--out must be outside the source tree")
    {"rows": cmd_rows, "gen": cmd_gen, "classify": cmd_classify, "smoke-split": cmd_smoke_split,
     "header": lambda _: print("\t".join(RESULT_COLUMNS))}[a.cmd](a)


if __name__ == "__main__":
    main()
