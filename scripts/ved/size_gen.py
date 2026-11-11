#!/usr/bin/env python3
"""VED circuit-SIZE measurement: case generator and classifier.  MEASUREMENT
ONLY, never for main.  Derived from u1_gen.py / u0_gen.py (imported: inventory
loading by `git show` at a fixed commit with a blob check, source scan, import
closure, option lines are reused unchanged; the inventory logic is not forked).

One record per inventory row (327), setting `size`.  The case is a COPY OF THE
ORIGINAL SOURCE FILE with a block inserted right after the original command (the
original scope: private decls, namespaces, opens, scoped options).  The block
calls the SAME compiler functions the row's command calls, once, and writes
files next to Case.lean (no compiler change):

  command kind "module"  (#synthesizeVerilog)
      (m, d) := Sparkle.Compiler.Elab.synthesizeCombinational decl
      HASHED TEXT sv      = toVerilog (optimizeModule m)         -- a RE-SYNTHESIS with the same
                            functions the command's elaborator calls; the TOP module only, OPTIMISED.
                            It is not the command's own output: see sv_origin_check below.
      children text       = toVerilogDesign {modules := d.modules without m}  -- NOT part of what
                            the command prints; emitted too (each child optimised, joined by "\\n")
                            so yosys sees the whole hierarchy, hashed separately.
  command kind "design"  (#writeDesign, #writeVerilogDesign, #synthesizeVerilogDesign)
      design := Sparkle.Compiler.Elab.synthesizeHierarchical decl
      HASHED TEXT sv      = toVerilogDesign design  -- a re-synthesis with the functions those commands
                            call: EVERY module of the hierarchy, each one optimised (toVerilogDesign applies
                            optimizeModule per module), joined by "\\n".  Per-module texts are
                            hashed too.  (#writeDesign's path / wire-name arguments only name
                            output files and the JIT wires: they cannot change the SV, so the
                            size harness waives them -- the U1 harness refuses them.)
  Not reproduced: the DRC the commands run first (warnings/errors, no effect on the text),
  C/CSim output, the `#synthesizeParameterizedVerilog` rows (parameters, symbolicMode: they stay
  unsupported-invocation as in the U1 harness).

sv_origin_check: the ORIGINAL command stays in the case and runs first; what it emitted is captured INSIDE the
case, attempt-specifically, and compared in FULL with the re-synthesised SV: `same` | `differ` | `not-checked`
(reason in sv_origin_reason).  Only `same` on a side lets that side's row enter the formal comparison (size_run.py
compare); `differ` / `not-checked` / missing make the row not-comparable / incomplete (exit 2).  The comparison of
two re-synthesised artifacts of rows whose origin is not `same` is only an observation (obs_* columns).
  stdout commands (#synthesizeVerilog, #synthesizeVerilogDesign): a `run_cmd` before the command draws an
    attempt token (monotonic ns, pid, random; written to size_token.txt) and prints `VED SIZE CAP BEGIN <token>`; a
    `run_cmd` right after it prints `VED SIZE CAP END <token>`.  stdout must hold each marker exactly once, BEGIN
    before END.  The captured range (between the BEGIN line and the END marker) must be
        <SV> "\n" "\n" <tail line> "\n" <compiler messages, if any>
    where the command did `IO.println verilog` then `IO.println "\n<tail line>"`; <tail line> is
    `-- Verilog successfully generated!` / `-- Hierarchical Verilog successfully generated!`.  The ONLY text
    removed is that tail println (its leading "\n", the line and its newline) and what follows it (messages the
    command logged: warnings; never SV); <SV> (everything before it, the whole range otherwise) must equal the
    re-synthesised text byte for byte.  A range without the tail line is `not-checked`.
  write commands (#writeDesign, #writeVerilogDesign): the command's path argument (first string literal of the
    row's args) is MOVED ASIDE before the command (`<path>.size-bak-<token>`), the command runs, and right after it
    (before any later command) the file is copied to size_orig_write.bin and the backup is dropped (or, when the
    command wrote nothing, moved back).  `written` in size_wpost.txt with the attempt token is the proof that THIS
    attempt's command wrote the file; a path that is absent afterwards (only a pre-existing file, or no write) is
    `not-checked`.  Later commands that overwrite the path cannot change the capture.
Not covered by the origin check: the children SV of a #synthesizeVerilog row (not printed by the command), the DRC
and C/CSim outputs.
Entry guard (AUXILIARY, NOT evidence of output identity): at gen time Sparkle/Compiler/Elab.lean of the measured tree
is read with Lean comments and string literals removed and the command's elaborator is checked for the identifiers the
block re-uses (synthesizeCombinational / optimizeModule / synthesizeHierarchical / toVerilogDesign ...), matched at
identifier boundaries; a miss is `entry-mismatch` (not run).  It only avoids running the block through an obviously
different entry function; identity of the output is shown by the origin check alone.

size_status is `ok` only when the whole case succeeded (rc 0, no signal, no timeout, no Lean error, files
complete, sv_join_check=yes).  Artifacts seen in a case that did not succeed are kept as an observation
(`failed-observed`, size_observed=yes, numbers filled) and are never a successful measurement.

The record's sv_sha256 is the sha256 of the hashed sv text; `sv_identity` is the sha256 of
sv text + NUL + children text.  IR counts are taken from the returned Module/Design
(`ir_*` = returned, before optimisation; `opt_*` = after optimizeModule) over every
module of the emitted scope (sv text + children); `irtop_*` = the top module only.

yosys (pinned nixpkgs; every option is recorded in the record): the SV files are read by
  (a) generic: read_verilog -sv F..; hierarchy -top T; synth -top T; stat
  (b) fpga:    read_verilog -sv F..; hierarchy -top T; synth_gowin -top T; stat
with T the SV name of the IR top module (`sanitizeName m.name`, as the emitter writes it; both names are recorded).  A timeout, an error, a missing top or an unreadable stat is
a status, never a 0.  Numbers are blank unless the status is `ok`.

Subcommands: rows | header | gen | classify | error-row
"""
import argparse
import hashlib
import json
import os
import re
import shlex
import signal
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import u0_gen  # noqa: E402
import u1_gen  # noqa: E402
from u0_gen import (INV_BLOB, INV_COMMIT, INV_PATH, INV_ROWS, die, git_show_inventory,  # noqa: E402,F401
                    import_closure, invocation_of, kv_file, lean_option_lines, module_of, read,
                    scan_source)

SETTING = "size"
KEY_COLUMNS = u1_gen.KEY_COLUMNS
DESIGN_CMDS = ("#writeDesign", "#writeVerilogDesign", "#synthesizeVerilogDesign")
MODULE_CMDS = ("#synthesizeVerilog",)
ORIGIN_TAIL = {"#synthesizeVerilog": "-- Verilog successfully generated!",
               "#synthesizeVerilogDesign": "-- Hierarchical Verilog successfully generated!"}
# the SV never depends on these arguments (output paths, JIT observable wires)
ARGS_WAIVED = DESIGN_CMDS

NIXPKGS_REV = "4fe25e12eb9f4c744966dd3de5a05246cf098601"
DEFAULT_YOSYS = f"nix shell github:NixOS/nixpkgs/{NIXPKGS_REV}#yosys -c yosys"
DEFAULT_YOSYS_TMO = 600

IR_FIELDS = ["modules", "regs", "mems", "insts", "stmts", "wires", "regbits", "regbits_unknown", "membits"]
RESULT_COLUMNS = KEY_COLUMNS + [
    "invocation", "invocation_detail", "args_waived", "cmd_kind",
    "run_id", "attempt", "src_sha", "src_dirty_hash", "toolchain", "case_hash", "harness_hash",
    "ran", "rc", "term", "timeout", "wall_s", "peak_rss_kb",
    "size_status", "size_error", "size_observed", "sv_origin_check", "sv_origin_reason",
    "top", "sv_top", "synth_ms", "sv_modules", "children_modules",
    "sv_sha256", "sv_bytes", "children_sha256", "sv_identity", "sv_module_sha256", "sv_join_check",
] + [f"ir_{f}" for f in IR_FIELDS] + [f"opt_{f}" for f in IR_FIELDS] + [
    f"irtop_{f}" for f in ("regs", "mems", "insts", "stmts", "wires", "regbits", "membits")
] + [
    "ys_version", "ys_cmd", "ys_files", "ys_timeout_s",
    "g_status", "g_error", "g_script", "g_cells", "g_dff", "g_unresolved", "g_types", "g_wall_s",
    "f_status", "f_error", "f_script", "f_cells", "f_lut", "f_ff", "f_bram", "f_lutram", "f_types", "f_wall_s",
    "harness_error", "stdout_ref", "stderr_ref",
]

# ------------------------------------------------------------------ case text

HEAD = '''open Lean Elab Command Meta in
run_cmd do
  let dir := (System.FilePath.mk (← read).fileName).parent.getD "."
  try
    let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent "@TOP@".toName)
    IO.println "VED SIZE MARK row @ROW@"
    let t0 ← IO.monoMsNow
'''

BODY_MODULE = '''    let (m, d) ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeCombinational n)
    let kids := d.modules.filter (·.name != m.name)
    let scope : List Sparkle.IR.AST.Module := [m]
    let top := m.name
    let sv := Sparkle.Backend.Verilog.toVerilog (Sparkle.IR.Optimize.optimizeModule m)
    let kidsSv := if kids.isEmpty then "" else
      Sparkle.Backend.Verilog.toVerilogDesign { topModule := m.name, modules := kids }
    let kind := "module"
'''

BODY_DESIGN = '''    let design ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical n)
    let kids : List Sparkle.IR.AST.Module := []
    let scope := design.modules
    let top := design.topModule
    let sv := Sparkle.Backend.Verilog.toVerilogDesign design
    let kidsSv := ""
    let kind := "design"
'''

TAIL = '''    let t1 ← IO.monoMsNow
    let isReg := fun (s : Sparkle.IR.AST.Stmt) => match s with | .register .. => true | _ => false
    let isMem := fun (s : Sparkle.IR.AST.Stmt) => match s with | .memory .. => true | _ => false
    let isInst := fun (s : Sparkle.IR.AST.Stmt) => match s with | .inst .. => true | _ => false
    let wOf := fun (m : Sparkle.IR.AST.Module) (nm : String) =>
      ((m.wires ++ m.inputs ++ m.outputs).find? (·.name == nm)).map (·.ty.bitWidth)
    let regBits := fun (m : Sparkle.IR.AST.Module) => m.body.foldl (fun a s => match s with
      | .register o .. => a + ((wOf m o).getD 0) | _ => a) 0
    let regUnk := fun (m : Sparkle.IR.AST.Module) => m.body.foldl (fun a s => match s with
      | .register o .. => if (wOf m o).isSome then a else a + 1 | _ => a) 0
    let memBits := fun (m : Sparkle.IR.AST.Module) => m.body.foldl (fun a s => match s with
      | .memory _ aw dw .. => a + (2 ^ aw) * dw | _ => a) 0
    let line := fun (tag : String) (role : String) (i : Nat) (m : Sparkle.IR.AST.Module) =>
      s!"mod {tag} {role} {i} {m.name} regs={(m.body.filter isReg).length} mems={(m.body.filter isMem).length} insts={(m.body.filter isInst).length} stmts={m.body.length} wires={m.wires.length} regbits={regBits m} regbits_unknown={regUnk m} membits={memBits m}"
    let mut lines : Array String := #[s!"kind={kind}", s!"top={top}", s!"sv_top={Sparkle.Backend.Verilog.sanitizeName top}", s!"synth_ms={t1 - t0}",
      s!"sv_modules={scope.length}", s!"children_modules={kids.length}"]
    let mut i := 0
    for m in scope do
      lines := lines.push (line "raw" "sv" i m)
      lines := lines.push (line "opt" "sv" i (Sparkle.IR.Optimize.optimizeModule m))
      IO.FS.writeFile (dir / s!"size_mod_{i}.sv") (Sparkle.Backend.Verilog.toVerilog (Sparkle.IR.Optimize.optimizeModule m))
      i := i + 1
    for m in kids do
      lines := lines.push (line "raw" "child" i m)
      lines := lines.push (line "opt" "child" i (Sparkle.IR.Optimize.optimizeModule m))
      i := i + 1
    IO.FS.writeFile (dir / "size_sv.sv") sv
    if !kidsSv.isEmpty then IO.FS.writeFile (dir / "size_children.sv") kidsSv
    IO.FS.writeFile (dir / "size_ir.txt") ("\\n".intercalate lines.toList ++ "\\nEND\\n")
    logInfo m!"VED SIZE OK kind={kind} top={top} modules={scope.length}+{kids.length}"
  catch e =>
    let msg ← e.toMessageData.toString
    IO.FS.writeFile (dir / "size_err.txt") msg
    logInfo m!"VED SIZE ERROR {msg}"'''


CAP_HEAD = '''open Lean Elab Command in
run_cmd do
  let dir := (System.FilePath.mk (← read).fileName).parent.getD "."
'''
CAP_PRE_STDOUT = CAP_HEAD + '''  let t0 ← IO.monoNanosNow
  let pid ← IO.Process.getPID
  let rnd ← IO.rand 0 1000000000
  let tok := s!"{t0}-{pid}-{rnd}"
  IO.FS.writeFile (dir / "size_token.txt") tok
  IO.println s!"VED SIZE CAP BEGIN {tok}"'''
CAP_POST_STDOUT = CAP_HEAD + '''  let tok ← IO.FS.readFile (dir / "size_token.txt")
  IO.println s!"VED SIZE CAP END {tok}"'''
CAP_PRE_WRITE = CAP_HEAD + '''  let t0 ← IO.monoNanosNow
  let pid ← IO.Process.getPID
  let rnd ← IO.rand 0 1000000000
  let tok := s!"{t0}-{pid}-{rnd}"
  IO.FS.writeFile (dir / "size_token.txt") tok
  let p : System.FilePath := "@PATH@"
  let bak : System.FilePath := p.toString ++ ".size-bak-" ++ tok
  let had ← p.pathExists
  if had then IO.FS.rename p bak
  IO.FS.writeFile (dir / "size_wpre.txt") s!"{tok}\\nhad={had}\\n"'''
CAP_POST_WRITE = CAP_HEAD + '''  let tok ← IO.FS.readFile (dir / "size_token.txt")
  let p : System.FilePath := "@PATH@"
  let bak : System.FilePath := p.toString ++ ".size-bak-" ++ tok
  let st ← if (← p.pathExists) then do
      IO.FS.writeBinFile (dir / "size_orig_write.bin") (← IO.FS.readBinFile p)
      if (← bak.pathExists) then IO.FS.removeFile bak
      pure "written"
    else do
      if (← bak.pathExists) then IO.FS.rename bak p
      pure "absent"
  IO.FS.writeFile (dir / "size_wpost.txt") s!"{tok}\\n{st}\\n"'''
CAP_OPTS = "set_option Elab.async false in\n"


def capture_blocks(r, code=""):
    """-> (pre text, post text) wrapped around the ORIGINAL command; ("", "") when there is nothing to capture
    (a write command without a path argument)."""
    cmd = r["command"]
    if cmd in ORIGIN_TAIL:
        return CAP_OPTS + CAP_PRE_STDOUT, CAP_OPTS + CAP_POST_STDOUT
    if cmd in ("#writeDesign", "#writeVerilogDesign"):
        path = origin_arg(r, code)
        if not path:
            return "", ""
        return (CAP_OPTS + CAP_PRE_WRITE.replace("@PATH@", path), CAP_OPTS + CAP_POST_WRITE.replace("@PATH@", path))
    return "", ""


def block_text(r):
    kind = "design" if r["command"] in DESIGN_CMDS else "module"
    opts = lean_option_lines(r["options"], "default")
    prefix = "".join(f"set_option {o} in\n" for o in ["Elab.async false"] + opts)
    body = BODY_DESIGN if kind == "design" else BODY_MODULE
    text = prefix + HEAD + body + TAIL
    return kind, text.replace("@TOP@", r["top"]).replace("@ROW@", r["row"])


def case_text(src_text, scan, r):
    lines = src_text.splitlines()
    ie, ci, ei = scan["imports_end"], scan["cmd_index"], scan["end_index"]
    code = "\n".join(u0_gen.blank_comments(src_text).splitlines()[ci:ei])
    pre, post = capture_blocks(r, code)
    out = lines[:ie] + lines[ie:ci]
    if pre:
        out.append("-- ===== VED SIZE CAPTURE PRE (before the original command) =====")
        out += pre.splitlines()
        out.append("-- ===== VED SIZE CAPTURE PRE END =====")
    out += lines[ci:ei]
    if post:
        out.append("-- ===== VED SIZE CAPTURE POST (right after the original command) =====")
        out += post.splitlines()
        out.append("-- ===== VED SIZE CAPTURE POST END =====")
    out.append("")
    begin = len(out) + 1
    out.append(f"-- ===== VED SIZE BEGIN row {r['row']} (inventory {INV_COMMIT[:8]}) =====")
    kind, text = block_text(r)
    out += text.splitlines()
    out.append("-- ===== VED SIZE END =====")
    end = len(out)
    out += lines[ei:]
    return "\n".join(out) + "\n", begin, end, kind


ENTRY_FILE = "Sparkle/Compiler/Elab.lean"
# what the command's elaborator must call for the block's re-synthesis to be the same pipeline
ENTRY_REQUIRED = {
    "#synthesizeVerilog": ["synthesizeCombinational", "optimizeModule", "toVerilog"],
    "#synthesizeVerilogDesign": ["synthesizeHierarchical", "toVerilogDesign"],
    "#writeVerilogDesign": ["synthesizeHierarchical", "toVerilogDesign"],
    "#writeDesign": ["writeDesignCore"],              # + the private def below
}
ENTRY_FORBIDDEN = {"#synthesizeVerilog": ["synthesizeHierarchical"]}
CORE_REQUIRED = ["synthesizeHierarchical", "toVerilogDesign"]


CHAR_LIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
IDENT_TOKEN = re.compile(r"[\w'.!?]+")


def strip_lean(src, strings=False):
    """`src` with Lean comments blanked (`--` to end of line; `/- ... -/` including `/--` docs, nested), and, when
    `strings`, the contents of string literals too (the quotes stay).  Blanked characters become spaces, newlines are
    kept, so line structure is unchanged.  `--` or `/-` inside a string literal is not a comment; a char literal
    (`'"'`) is not a string start."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        elif src.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif c == '"':
            out.append('"')
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\" and i + 1 < n:
                    seg = src[i:i + 2]
                    out.append("  " if strings and seg[1] != "\n" else seg)
                    i += 2
                else:
                    out.append(" " if strings and src[i] != "\n" else src[i])
                    i += 1
            if i < n:
                out.append('"')
                i += 1
        elif c == "'" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'")) and CHAR_LIT.match(src, i):
            m = CHAR_LIT.match(src, i)
            out.append(m.group(0))
            i = m.end()
        else:
            out.append(c)
            i += 1
    return "".join(out)


def decl_blocks(src, head):
    """Texts of the top-level declarations whose first line starts with `head` (the body is the indented
    lines that follow; the next column-0 line ends it).  `src` is expected comment-stripped (strip_lean)."""
    out, cur = [], None
    for ln in src.splitlines():
        if ln.startswith(head):
            if cur is not None:
                out.append("\n".join(cur))
            cur = [ln]
        elif cur is not None:
            if ln and ln[0] not in " \t":
                out.append("\n".join(cur))
                cur = None
            else:
                cur.append(ln)
    if cur is not None:
        out.append("\n".join(cur))
    return out


def calls(text, name):
    """True when the identifier `name` occurs in `text` (comments and strings already removed) as a whole identifier
    or as the last component of a qualified one (`A.B.name`): identifier characters are letters, digits, `_`, `'`,
    `.`, `!`, `?`, so `nameV2`, `name'` and `pre_name` are other identifiers."""
    return any(t == name or t.endswith("." + name) for t in IDENT_TOKEN.findall(text))


def entry_check(repo, command):
    """-> "" when the measured tree's elaborator for `command` calls the functions the size block re-uses,
    otherwise the reason.  AUXILIARY: it is no evidence that the output is the same (the origin check is)."""
    path = os.path.join(repo, ENTRY_FILE)
    src = read(path)
    if src is None:
        return f"{ENTRY_FILE} not readable in the measured tree"
    code = strip_lean(src)                      # comments gone, strings kept (the `elab "#cmd"` head)
    blocks = decl_blocks(code, f'elab "{command}"')
    if not blocks:
        return f"no `elab \"{command}\"` in {ENTRY_FILE}"
    text = strip_lean("\n".join(blocks), strings=True)
    miss = [t for t in ENTRY_REQUIRED[command] if not calls(text, t)]
    bad = [t for t in ENTRY_FORBIDDEN.get(command, []) if calls(text, t)]
    if command == "#writeDesign":
        core = strip_lean("\n".join(decl_blocks(code, "private def writeDesignCore")), strings=True)
        miss += [t for t in CORE_REQUIRED if not calls(core, t)] if core.strip() else ["private def writeDesignCore"]
    if miss or bad:
        return (f"elaborator of {command} in the measured tree " + (f"does not call {','.join(miss)}" if miss else "")
                + (" and " if miss and bad else "") + (f"calls {','.join(bad)}" if bad else "")
                + "; the size block would measure through another function")
    return ""


def origin_arg(r, code=""):
    """The first string literal argument of the original write command (#writeDesign / #writeVerilogDesign): the
    file it wrote, as written in the source (escapes unchanged); "" for the other commands.  The inventory `args`
    column is used when it has a literal, otherwise the command text of the source (`code`, comments blanked:
    the command line and its indented continuation lines, after the command name)."""
    if r["command"] not in ("#writeDesign", "#writeVerilogDesign"):
        return ""
    m = re.search(r'"((?:[^"\\]|\\.)*)"', r["args"])
    if not m and code:
        at = code.find(r["command"])
        m = re.search(r'"((?:[^"\\]|\\.)*)"', code[at:]) if at >= 0 else None
    return m.group(1) if m else ""


def cmd_rows(a):
    for r in git_show_inventory(a.repo, a.commit, a.blob):
        print("\t".join([r["row"], r["file"], r["line"], r["command"], r["qualified"] or r["top"]]))


def cmd_gen(a):
    rows = git_show_inventory(a.repo, a.commit, a.blob)
    i = int(a.row)
    if not 1 <= i <= len(rows):
        die(f"row {a.row} out of range 1..{len(rows)}")
    r = rows[i - 1]
    if a.setting != SETTING:
        die(f"unknown setting {a.setting}; only `{SETTING}`")
    d = a.dir
    os.makedirs(d, exist_ok=True)
    meta = {k: r.get(k, "") for k in KEY_COLUMNS if k != "setting"}
    meta.update(inv_commit=a.commit, inv_blob=a.blob, setting=SETTING, kind="row", lean_options=[],
                cmd_kind="design" if r["command"] in DESIGN_CMDS else "module", args_waived="no")
    src_path = os.path.join(a.repo, r["file"])
    open(os.path.join(d, "case.env"), "w").close()
    if not os.path.exists(src_path):
        meta.update(invocation="source-missing", run=False,
                    invocation_detail=f"{r['file']} does not exist in the measured tree")
    else:
        src_text = open(src_path, errors="replace").read()
        scan = scan_source(src_text, int(r["line"]), r["command"], r["top"])
        r2 = dict(r)
        waived = bool(r["args"].strip()) and r["command"] in ARGS_WAIVED
        if waived:
            r2["args"] = ""
        closure = import_closure(a.repo, [])
        inv, detail, run = invocation_of(r2, scan, closure)
        if run and scan["cmd_index"]:
            prev = [ln for ln in u0_gen.blank_comments(src_text).splitlines()[:scan["cmd_index"]] if ln.strip()]
            if prev and re.search(r"\bin\s*$", prev[-1]):
                inv, detail, run = ("unsupported-invocation",
                                    "the command line follows a `... in` modifier line (the capture block cannot be inserted before it)", False)
        if run and r["command"] in ENTRY_REQUIRED:
            why = entry_check(a.repo, r["command"])
            if why:
                inv, detail, run = "entry-mismatch", why, False
        if inv == "deep-in-file":
            inv = "size-in-file"
            detail = detail.replace("deep block", "size block")
        if inv == "unsupported-invocation" and r["command"] not in MODULE_CMDS + DESIGN_CMDS:
            detail += f"; command {r['command']} has no size block"
        meta.update(invocation=inv, invocation_detail=detail, run=run, args_waived="yes" if waived else "no",
                    command=r["command"], origin_arg=origin_arg(r, "\n".join(
                        u0_gen.blank_comments(src_text).splitlines()[scan["cmd_index"]:scan["end_index"]]) if scan["cmd_index"] is not None else ""), repo=os.path.realpath(a.repo),
                    module=module_of(r["file"]), scan_private=scan["private"], scan_decl_seen=scan["decl_seen"])
        if run:
            text, b, e, kind = case_text(src_text, scan, r)
            with open(os.path.join(d, "Case.lean"), "w") as f:
                f.write(text)
            meta.update(block_begin=b, block_end=e, cmd_kind=kind,
                        lean_options=lean_option_lines(r["options"], "default"))
    with open(os.path.join(d, "meta.json"), "w") as f:
        json.dump(meta, f, indent=1, sort_keys=True)
    print(d)


# ---------------------------------------------------------------- yosys

SECTION_RE = re.compile(r"^=== (.+?) ===\s*$")
COUNT_RE = re.compile(r"^\s+(\d+)\s+(\S.*?)\s*$")
VERSION_RE = re.compile(r"^\s*(Yosys \d\S*.*)$", re.M)


def parse_stat(text, top):
    """Parse yosys `stat` text.  With a `design hierarchy` section the totals that
    include submodules are used (the LAST `Count including submodules` block);
    otherwise the section of `top`.  Returns {"cells": int, "types": {type: n}} or None.
    `cells` is the `N cells` line (0 when the design has none and the line is absent
    only if the module section exists and lists no cells)."""
    lines = text.splitlines()
    start = None
    for i, ln in enumerate(lines):
        m = SECTION_RE.match(ln)
        if m and m.group(1) == "design hierarchy":
            start = i
    sect = None
    if start is not None:
        sect = lines[start + 1:]
        # the block with the totals: after the last "Count including submodules"
        idx = [i for i, ln in enumerate(sect) if "Count including submodules" in ln]
        if idx:
            sect = sect[idx[-1] + 1:]
    else:
        for i, ln in enumerate(lines):
            m = SECTION_RE.match(ln)
            if m and m.group(1) == top:
                sect = lines[i + 1:]
                break
        if sect is None:
            return None
        end = next((j for j, ln in enumerate(sect) if SECTION_RE.match(ln)), len(sect))
        sect = sect[:end]
    cells, types, in_cells, saw_wires = None, {}, False, False
    for ln in sect:
        if SECTION_RE.match(ln):
            break
        m = COUNT_RE.match(ln)
        if not m:
            if not ln.strip():
                in_cells = False
            continue
        n, name = int(m.group(1)), m.group(2)
        if name == "cells":
            cells, in_cells = n, True
        elif name == "submodules":
            in_cells = False
        elif name == "wires":
            saw_wires = True
        elif in_cells:
            types[name] = n
    if cells is None:
        # a section that lists wires but no cells line is an empty design
        if not saw_wires:
            return None
        cells = 0
    return {"cells": cells, "types": types}


DFF_GENERIC = re.compile(r"^\$_S?DFF|^\$_DLATCH|^\$_ALDFF|^\$_DFFSR|^\$_SDFF|^\$_DFFE|^\$dff|^\$adff|^\$sdff|^\$dlatch")
GOWIN_LUT = re.compile(r"^LUT[1-4]$")
GOWIN_FF = re.compile(r"^DFF[A-Z]*$|^DLATCH[A-Z]*$|^DLL[A-Z]*$")   # DFF, DFFE, DFFS, DFFR, DFFP, DFFC, DFFN*...
GOWIN_BRAM = re.compile(r"^(SP|SPX9|DP|DPX9|DPB|DPX9B|SDP|SDPX9|SDPB|SDPX9B|pROM|pROMX9|ROM16)$")
GOWIN_LUTRAM = re.compile(r"^RAM16SDP\d$")


def generic_numbers(st):
    t = st["types"]
    dff = sum(n for k, n in t.items() if DFF_GENERIC.match(k))
    unresolved = sum(n for k, n in t.items() if not k.startswith("$"))
    return {"cells": st["cells"], "dff": dff, "unresolved": unresolved}


def fpga_numbers(st):
    t = st["types"]
    return {"cells": st["cells"],
            "lut": sum(n for k, n in t.items() if GOWIN_LUT.match(k)),
            "ff": sum(n for k, n in t.items() if GOWIN_FF.match(k)),
            "bram": sum(n for k, n in t.items() if GOWIN_BRAM.match(k)),
            "lutram": sum(n for k, n in t.items() if GOWIN_LUTRAM.match(k))}


def run_yosys(cmd, tmo, script, d, tag, top):
    """Run one yosys flow.  -> dict(status, error, version, stat(dict|None), wall)."""
    spath, lpath, stpath = (os.path.join(d, f"yosys_{tag}{ext}") for ext in (".ys", ".log", ".stat"))
    with open(spath, "w") as f:
        f.write("\n".join(script + [f"tee -q -o {stpath} stat"]) + "\n")
    if os.path.exists(stpath):
        os.remove(stpath)
    full = cmd + ["-q", "-s", spath, "-l", lpath]
    t0 = time.monotonic()
    out = {"status": "", "error": "", "version": "", "stat": None}
    try:
        p = subprocess.Popen(full, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                             start_new_session=True, text=True, errors="replace")
    except OSError as e:
        out.update(status="error", error=f"cannot start yosys: {e}")
        out["wall"] = f"{time.monotonic() - t0:.1f}"
        return out
    try:
        console, _ = p.communicate(timeout=tmo)
        rc = p.returncode
    except subprocess.TimeoutExpired:
        for sig in (signal.SIGTERM, signal.SIGKILL):
            try:
                os.killpg(p.pid, sig)
            except ProcessLookupError:
                pass
            try:
                p.communicate(timeout=10)
                break
            except subprocess.TimeoutExpired:
                continue
        out.update(status="timeout", error=f"timeout after {tmo}s")
        out["wall"] = f"{time.monotonic() - t0:.1f}"
        return out
    out["wall"] = f"{time.monotonic() - t0:.1f}"
    log = read(lpath) or ""
    m = VERSION_RE.search(log) or VERSION_RE.search(console or "")
    out["version"] = m.group(1).strip() if m else ""
    text = (console or "") + "\n" + log
    errs = [ln for ln in text.splitlines() if ln.startswith("ERROR")]
    if rc != 0 or errs:
        first = (errs[0] if errs else f"exit {rc}")[:200]
        miss = bool(errs) and "not found" in errs[0] and top in errs[0]
        out.update(status="top-missing" if miss else "error", error=first)
        return out
    stat_text = read(stpath)
    if stat_text is None:
        out.update(status="no-stat", error="yosys exited 0 but wrote no stat output")
        return out
    st = parse_stat(stat_text, top)
    if st is None:
        out.update(status="no-stat", error="stat output not parsable")
        return out
    out.update(status="ok", stat=st)
    return out


def yosys_cmd():
    return shlex.split(os.environ.get("SIZE_YOSYS", DEFAULT_YOSYS))


def yosys_tmo():
    return int(os.environ.get("SIZE_YOSYS_TMO", str(DEFAULT_YOSYS_TMO)))


# ---------------------------------------------------------------- classify

def sha(b):
    return hashlib.sha256(b).hexdigest()


def blank_row(meta):
    row = {c: "" for c in RESULT_COLUMNS}
    for k in KEY_COLUMNS + ["invocation", "invocation_detail", "args_waived", "cmd_kind"]:
        row[k] = str(meta.get(k, ""))
    return row


def read_ir(path):
    """-> (header dict, [(tag, role, idx, name, {field: int})]) or None when the file is absent/incomplete."""
    t = read(path)
    if t is None or not t.rstrip().endswith("END"):
        return None
    hdr, mods = {}, []
    for ln in t.splitlines():
        if ln.startswith("mod "):
            p = ln.split()
            kv = dict(x.split("=", 1) for x in p[5:])
            mods.append((p[1], p[2], int(p[3]), p[4], {k: int(v) for k, v in kv.items()}))
        elif "=" in ln:
            k, _, v = ln.partition("=")
            hdr[k] = v
    return hdr, mods


def ir_columns(row, hdr, mods):
    for tag in ("raw", "opt"):
        sel = [m for m in mods if m[0] == tag]
        pre = "ir_" if tag == "raw" else "opt_"
        row[pre + "modules"] = str(len(sel))
        for f in ("regs", "mems", "insts", "stmts", "wires", "regbits", "regbits_unknown", "membits"):
            row[pre + f] = str(sum(m[4][f] for m in sel))
    top = hdr.get("top", "")
    tops = [m for m in mods if m[0] == "raw" and m[3] == top]
    if tops:
        for f in ("regs", "mems", "insts", "stmts", "wires", "regbits", "membits"):
            row["irtop_" + f] = str(tops[0][4][f])


def command_warnings(text, case_dir):
    """Strip the original command's own one-line warnings from the start of `text`.  A line counts only when it
    is `<…/Case.lean>:<L>:<c>: warning: …` with L the original command's line in this case's Case.lean (the
    line after the PRE END marker).  -> (number stripped, rest).  Errors and other positions are never
    stripped, so they still make the row `differ`."""
    lines = (read(os.path.join(case_dir, "Case.lean")) or "").split("\n")
    pre = "-- ===== VED SIZE CAPTURE PRE END ====="
    if pre not in lines:
        return 0, text
    cmd_line = lines.index(pre) + 2
    warn = re.compile(r"(?:[^\n:]*/)?Case\.lean" + rf":{cmd_line}:\d+: warning: [^\n]*\n")
    n = 0
    while True:
        m = warn.match(text)
        if not m:
            return n, text
        text, n = text[m.end():], n + 1


MARK_RE = re.compile(r"VED SIZE MARK row \d+")


def origin_check(meta, stdout, sv_text, case_dir):
    """Compare what the ORIGINAL command emitted IN THIS ATTEMPT with the re-synthesised SV.  The full rules are in
    the module docstring.  -> (same|differ|not-checked, reason)."""
    cmd = meta.get("command", "")
    tok = (read(os.path.join(case_dir, "size_token.txt")) or "").strip()
    if cmd not in ORIGIN_TAIL and cmd not in ("#writeDesign", "#writeVerilogDesign"):
        return "not-checked", f"no capture defined for {cmd or 'unknown command'}"
    if not tok:
        return "not-checked", "no attempt token (the capture block before the original command did not run)"
    if cmd in ORIGIN_TAIL:
        if stdout is None:
            return "not-checked", "no stdout captured"
        begin, end = f"VED SIZE CAP BEGIN {tok}\n", f"VED SIZE CAP END {tok}"
        if stdout.count(begin) != 1 or stdout.count(end) != 1:
            return "not-checked", (f"capture markers of this attempt not found exactly once in stdout "
                                   f"(begin={stdout.count(begin)} end={stdout.count(end)})")
        bi, ei = stdout.index(begin) + len(begin), stdout.index(end)
        if ei < bi:
            return "not-checked", "capture END marker before BEGIN marker"
        rng = stdout[bi:ei]
        tail = ORIGIN_TAIL[cmd]
        sep = "\n\n" + tail + "\n"
        at = rng.find(sep)
        if at < 0:
            return "not-checked", f"original command's `{tail}` line not found inside the capture range"
        if rng[:at] == sv_text:
            return "same", "the whole captured range of the original command (minus its tail line) equals the re-synthesised SV"
        # Lean prints the original command's own warnings (e.g. `[DRC] …`) before its IO output: one-line
        # warnings positioned AT the original command's line, at the very start of the range, are not SV
        lead, body = command_warnings(rng[:at], case_dir)
        if lead and body == sv_text:
            return "same", (f"the captured range of the original command equals the re-synthesised SV after "
                            f"{lead} leading one-line warning(s) of that command were removed")
        return "differ", "the captured output of the original command differs from the re-synthesised SV"
    # write commands: the capture file of THIS attempt
    pre = (read(os.path.join(case_dir, "size_wpre.txt")) or "").split("\n")
    post = (read(os.path.join(case_dir, "size_wpost.txt")) or "").split("\n")
    if pre[0] != tok:
        return "not-checked", "the pre-command step of this attempt did not run (token mismatch)"
    if post[0] != tok:
        return "not-checked", "the capture right after the original command did not run in this attempt"
    if len(post) < 2 or post[1] != "written":
        return "not-checked", "the original command did not write its path in this attempt" + (
            " (a file that was there before is not used)" if len(pre) > 1 and pre[1] == "had=true" else "")
    try:
        cap = open(os.path.join(case_dir, "size_orig_write.bin"), "rb").read()
    except OSError:
        return "not-checked", "capture file of the written output missing"
    if cap == sv_text.encode():
        return "same", "file written by the original command in this attempt (captured right after it) equals the re-synthesised SV"
    return "differ", "file written by the original command in this attempt differs from the re-synthesised SV"


def classify_dir(d, sv_group=""):
    meta = json.load(open(os.path.join(d, "meta.json"))) if os.path.exists(os.path.join(d, "meta.json")) else {}
    row = blank_row(meta)
    idn = {}
    try:
        idn = json.load(open(os.path.join(d, "identity.json")))
    except (OSError, ValueError):
        pass
    for k in ("run_id", "attempt", "src_sha", "src_dirty_hash", "toolchain", "case_hash", "harness_hash"):
        row[k] = str(idn.get(k, ""))
    row["stdout_ref"], row["stderr_ref"] = os.path.join(d, "stdout.txt"), os.path.join(d, "stderr.txt")
    row["ys_cmd"], row["ys_timeout_s"] = " ".join(yosys_cmd()), str(yosys_tmo())
    run = kv_file(os.path.join(d, "run.txt"))
    inv = meta.get("invocation", "")
    if not meta.get("run"):
        row["ran"] = "no"
        row["size_status"] = "not-run"
        row["size_error"] = inv
        for t in ("g", "f"):
            row[t + "_status"] = "not-run"
        return row
    row["ran"] = "yes"
    if run is None:
        row["harness_error"] = "run.txt missing"
        row["size_status"] = "harness-error"
        return row
    for k in ("rc", "term", "timeout", "wall_s", "peak_rss_kb"):
        row[k] = run.get(k, "")
    if run.get("harness_error"):
        row["harness_error"] = run["harness_error"]
        row["size_status"] = "harness-error"
        return row
    out = (read(row["stdout_ref"]) or "") + (read(row["stderr_ref"]) or "")
    err = read(os.path.join(d, "size_err.txt"))
    parsed = read_ir(os.path.join(d, "size_ir.txt"))
    if err is not None:
        row["size_status"] = "synthesis-error"
        row["size_error"] = err.strip().split("\n", 1)[0][:200]
    elif run.get("timeout") == "yes":
        row["size_status"] = "lean-timeout"
        row["size_error"] = run.get("term", "")
    elif parsed is None or not os.path.exists(os.path.join(d, "size_sv.sv")):
        errl = [ln for ln in out.splitlines() if ": error" in ln]
        row["size_status"] = "no-output"
        row["size_error"] = (errl[0] if errl else f"no size files written (term={run.get('term', '')})")[:200]
    else:
        # the artifacts exist; whole-case success is a separate question
        fail = []
        if run.get("term") != "exit_0" or run.get("rc") != "0":
            fail.append(f"case did not exit 0 (rc={run.get('rc', '')} term={run.get('term', '')})")
        errl = [ln for ln in out.splitlines() if ": error" in ln]
        if errl:
            fail.append("Lean error: " + errl[0].strip())
        row["size_status"] = "failed-observed" if fail else "ok"
        row["size_error"] = "; ".join(fail)[:200]
    if row["size_status"] not in ("ok", "failed-observed"):
        for t in ("g", "f"):
            row[t + "_status"] = "not-run"
        return row
    hdr, mods = parsed
    row["top"], row["sv_top"], row["synth_ms"] = hdr.get("top", ""), hdr.get("sv_top", ""), hdr.get("synth_ms", "")
    row["sv_modules"], row["children_modules"] = hdr.get("sv_modules", ""), hdr.get("children_modules", "")
    row["cmd_kind"] = hdr.get("kind", row["cmd_kind"])
    ir_columns(row, hdr, mods)
    sv = open(os.path.join(d, "size_sv.sv"), "rb").read()
    kp = os.path.join(d, "size_children.sv")
    kids = open(kp, "rb").read() if os.path.exists(kp) else b""
    row["sv_sha256"], row["sv_bytes"] = sha(sv), str(len(sv))
    row["children_sha256"] = sha(kids) if kids else ""
    row["sv_identity"] = sha(sv + b"\0" + kids)
    n_sv = int(hdr.get("sv_modules", "0") or 0)
    mod_texts = []
    for i in range(n_sv):
        p = os.path.join(d, f"size_mod_{i}.sv")
        mod_texts.append(open(p, "rb").read() if os.path.exists(p) else None)
    names = [m[3] for m in mods if m[0] == "raw" and m[1] == "sv"]
    row["sv_module_sha256"] = ";".join(f"{n}:{sha(t)[:16]}" if t is not None else f"{n}:missing"
                                       for n, t in zip(names, mod_texts))
    row["sv_join_check"] = "yes" if None not in mod_texts and b"\n".join(mod_texts) == sv else "no"
    if row["sv_join_check"] == "no" and row["size_status"] == "ok":
        row["size_status"] = "failed-observed"
        row["size_error"] = "sv_join_check=no (per-module SV does not join to the SV)"
    row["size_observed"] = "yes" if row["size_status"] == "failed-observed" else ""
    row["sv_origin_check"], row["sv_origin_reason"] = origin_check(meta, read(row["stdout_ref"]), sv.decode(errors="replace"), d)
    # yosys
    files = [os.path.join(d, "size_sv.sv")] + ([kp] if kids else [])
    row["ys_files"] = ";".join(os.path.basename(f) for f in files)
    top, cmd, tmo = row["sv_top"] or row["top"], yosys_cmd(), yosys_tmo()   # yosys sees the EMITTED (sanitised) name
    rd = "read_verilog -sv " + " ".join(files)
    rd_rec = "read_verilog -sv " + " ".join(os.path.basename(f) for f in files)   # recorded: no run-dir paths
    flows = (("g", "generic", "synth"), ("f", "fpga", "synth_gowin"))
    for pre, tag, synth in flows:
        script = [rd, f"hierarchy -top {top}", f"{synth} -top {top}"]
        res = run_yosys(cmd, tmo, script, d, tag, top)
        row[pre + "_status"], row[pre + "_error"] = res["status"], res["error"].replace("\t", " ")
        row[pre + "_script"] = "; ".join([rd_rec] + script[1:] + ["stat"])
        row[pre + "_wall_s"] = res.get("wall", "")
        if res["version"] and not row["ys_version"]:
            row["ys_version"] = res["version"]
        st = res["stat"]
        if st:
            row[pre + "_types"] = json.dumps(st["types"], sort_keys=True, separators=(",", ":"))
            if pre == "g":
                n = generic_numbers(st)
                row.update(g_cells=str(n["cells"]), g_dff=str(n["dff"]), g_unresolved=str(n["unresolved"]))
            else:
                n = fpga_numbers(st)
                row.update(f_cells=str(n["cells"]), f_lut=str(n["lut"]), f_ff=str(n["ff"]),
                           f_bram=str(n["bram"]), f_lutram=str(n["lutram"]))
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
    row.update(invocation="harness-error", harness_error=a.reason, ran="no", size_status="harness-error",
               attempt=a.attempt, run_id=a.run_id, g_status="not-run", f_status="not-run")
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
    g.add_argument("--setting", required=True, help="size")
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
