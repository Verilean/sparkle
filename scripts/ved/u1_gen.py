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

  u1_packed in the inserted block:  set_option Elab.async false in #ved_u1_packed <ident>
            (result `Signal d (A x B)` in ONE port `out`; Tools/VedU1PackedEntry.lean).
            Strict only through its own probe (PACKED_PROBE_DEF): the statement
            `PackedStmt <decl>.ved_contract <decl>.ved_mod <stmt>` is rebuilt and compared
            exactly, the slice map the probe computes from the declaration's TYPE (leaf
            widths, first leaf highest) must equal the stored one, the module has the one
            output `out` of the summed width.  Own route; its own union "standard + packed".

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
#
# u1_hier: the hierarchical entry `#ved_u1_hier` (Tools/VedU1HierEntry.lean; not a
# deep route: no preparation, the block runs in the ORIGINAL scope like `u1`).
# Strict only through the hier probe (PROBE_HIER below), which rebuilds the
# statement `U1HStmt <decl>.ved_contract <decl>.ved_mod <decl>.ved_design <stmt>`
# and reads the closed module and design values itself.
# u2_hier: the stateful hierarchical entry `#ved_u2_hier` (Tools/VedU2HierEntry.lean, H2a: depth 1,
# register-free parent, single-output leaf children, child input ports straight from parent inputs;
# H2b: the parent may also have registers, statement `U2HRStmt`).
# Same shape as u1_hier (original scope, no preparation).  Strict only through PROBE_HIER_U2, which
# rebuilds `U2HStmt` (or `U2HRStmt` when the registered module has a register) `<decl>.ved_contract <decl>.ved_mod <decl>.ved_design <stmt>` itself.  Its own
# route column and its own union "standard + u2_hier"; never in the default ROUTES of u1_full.sh.
# u1_packed: `#ved_u1_packed <ident>` (Tools/VedU1PackedEntry.lean) in the original
# scope, for a result `Signal d (A x B)` packed into ONE port `out`.  Not a deep
# route.  Its own probe (PACKED_PROBE_DEF) rebuilds `PackedStmt <ved_contract>
# <ved_mod> <stmt>` and checks the slice map against the packing rule computed
# from the declaration's TYPE.  Reported as its own route: the standard union
# stays u1 + u1_deep, and "standard + packed" is a separate union.
ROUTES = ("u1", "u1_deep", "u1_deep_ns", "u1_hier", "u1_packed", "u2_hier")
HIER_ROUTES = ("u1_hier", "u2_hier")
DEEP_ROUTES = ("u1_deep", "u1_deep_ns")
ENTRY_CMD = {"u1": "#ved_u1", "u1_deep": "#ved_u1_deep", "u1_deep_ns": "#ved_u1_deep",
             "u1_hier": "#ved_u1_hier", "u1_packed": "#ved_u1_packed",
             "u2_hier": "#ved_u2_hier"}
IMPORTS = {"u1_packed": ["Tools.VedU1PackedEntry", "Tools.VedStrictAudit"],
           "u1": ["Tools.VedU1Entry", "Tools.VedStrictAudit"],
           "u1_deep": ["Tools.VedU1Deep", "Tools.VedStrictAudit"],
           "u1_deep_ns": ["Tools.VedU1Deep", "Tools.VedStrictAudit"],
           "u1_hier": ["Tools.VedU1HierEntry", "Tools.VedStrictAudit"],
           "u2_hier": ["Tools.VedU2HierRegEntry", "Tools.VedStrictAudit"]}
STD3 = {"propext", "Classical.choice", "Quot.sound"}
# pipeline order inside the entry, for "later stages not reached"
PIPELINE = ["table", "multi-output", "synthesis", "artifact", "order", "type", "proof", "kernel", "audit"]
HIER_PIPELINE = ["table", "multi-output", "synthesis", "artifact", "hier-shape", "order", "child", "type",
                 "proof", "kernel", "audit"]
PIPELINE_PACKED = ["table", "packed", "synthesis", "artifact", "order", "type", "proof", "kernel", "audit"]
# u2_hier (Tools/VedU2HierEntry.lean): stages in the order of the checker
U2_HIER_PIPELINE = ["table", "multi-output", "synthesis", "artifact", "hier-shape", "clkrst", "order", "scope",
                    "conns", "child", "open", "type", "proof", "kernel", "audit"]
REFUSAL_STAGES = (set(PIPELINE) | set(HIER_PIPELINE) | set(PIPELINE_PACKED) | set(U2_HIER_PIPELINE)
                  | {"checker"})

KEY_COLUMNS = ["inv_commit", "inv_blob", "row", "file", "line", "command", "ns", "top",
               "qualified", "params", "options", "args", "setting"]
RESULT_COLUMNS = KEY_COLUMNS + [
    "invocation",            # u1-in-file | unsupported-invocation | unresolved-private | unresolved-name | harness-error
    "invocation_detail", "decl_resolved", "decl_check",
    # u1_deep_ns only (n/a elsewhere): the namespace the wrapper opened, and
    # whether the bare identifier named the SAME constant inside it, for the
    # preparation and for the U1 command (both wraps must say `same`)
    "ns_scope", "ns_check", "ns_detail", "ns_mode", "prep_command", "u1_command",
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
    "u1_ok_line", "u1_ok_thm", "u1_ok_specialised", "probe_domains",
    # independent probe
    "probe_present", "probe_thm", "probe_type", "probe_mvars", "probe_levels", "probe_mod",
    "probe_contract", "probe_outputs", "probe_slices", "probe_port", "probe_axioms", "probe_axioms_std3", "probe_preexisting",
    # u1_hier probe (n/a elsewhere): closed design, top/children/instances, child leaf theorems, ports
    "probe_design", "probe_hier_top", "probe_hier_modules", "probe_hier_insts", "probe_hier_children",
    "probe_hier_child_thms", "probe_ports", "probe_expected_stmt", "tool_reported",
    "kernel_sync",
    # timing (ms from in-file monotonic markers; "combined" where not separable)
    "t_synthesis", "t_deep_prep", "t_u1_proof", "t_elab_kernel", "t_audit", "t_u1_combined",
    "t_probe", "t_total_wall_s",
    "errors_outside_block", "errors_outside_first",
    "case_ok", "strict_counted", "strict_label", "strict_blockers",
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
  -- a private constant's namespace is that of its user-facing name
  let scope := ((privateToUserName? n).getD n).getPrefix
  if scope.isAnonymous then
    -- a root-level declaration: no namespace to open, so the command is
    -- elaborated as is in the original scope (the u1_deep command)
    logInfo m!"VED U1N scope=_root_ outer={n} inner={n} same mode=root"
    elabCommand c
  else
    let r : Option String ← try
        withNamespace scope do
          -- withNamespace also changes how the bare identifier resolves: run
          -- the command only if it still names the SAME constant inside
          let n' ← liftCoreM <| realizeGlobalConstNoOverload id
          logInfo m!"VED U1N scope={scope} outer={n} inner={n'} {if n == n' then "same" else "differs"} mode=ns"
          if n == n' then elabCommand c
          else logError m!"VED U1N REFUSED {id}: resolves to {n'} inside {scope}, not {n}"
        pure none
      catch e => pure (some (← e.toMessageData.toString))
    if let some msg := r then
      logError m!"VED U1N HARNESS-FAIL {id} scope={scope}: {msg}"'''

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
    -- the statement term, rebuilt here independently of the entry: the
    -- original constant, applied to `defaultDomain` once per LEADING implicit
    -- binder whose type is exactly `DomainConfig` (reviewer 2026-11-10)
    let k ← liftTermElabM do
      let ci ← getConstInfo n
      forallTelescope ci.type fun xs _ => do
        let mut k := 0
        for x in xs do
          let ld ← x.fvarId!.getDecl
          if !ld.binderInfo.isExplicit && ld.type.isConstOf `Sparkle.Core.Domain.DomainConfig then k := k + 1
          else break
        pure k
    logInfo m!"VED U1P STMT domains={k}"
    let stmt := mkAppN (mkConst n) (List.replicate k (mkConst `Sparkle.Core.Domain.defaultDomain)).toArray
    if let some (.thmInfo ti) := env.find? thm then
      let expected := mkAppN (mkConst ``Tools.VedU1Contract.U1Stmt) #[mkConst ct, mkConst md, stmt]
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
    -- the outputs of the STATEMENT term's type (`@decl defaultDomain` when
    -- specialised; readTable on the bare constant refuses its implicit binder)
    let tbl ← liftTermElabM do
      Tools.VedU1Contract.readTableOfType n (← Lean.Meta.inferType stmt)
    logInfo m!"VED U1P OUTS {tbl.out.flat.length}"
  catch e => logInfo m!"VED U1P PROBE failed: {← e.toMessageData.toString}"'''

# u1_packed probe, written independently of the tool: the statement is rebuilt
# here (`PackedStmt <ved_contract> <ved_mod> <stmt>`), the packing rule is computed
# from the declaration's TYPE by this walker (leaf widths, first leaf in the HIGH
# bits: offset_i = sum of the widths after leaf i), and the stored slice map, the
# contract's port and the module's output port are READ from the registered
# constants by whnf (never by the tool's `OTy.slices`).
PACKED_PROBE_DEF = '''open Lean Meta in
partial def vedu1pLeaves (ty : Expr) : MetaM (List Nat) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``Prod, #[a, b]) => return (← vedu1pLeaves a) ++ (← vedu1pLeaves b)
  | (``Bool, #[]) => return [1]
  | (``BitVec, #[w]) =>
    match ← evalNat (← whnf (← instantiateMVars w)) with
    | some n => return [n]
    | none => throwError "non-literal BitVec width {w}"
  | _ => throwError "unsupported leaf type {ty}"

open Lean Meta in
partial def vedu1pPairs (e : Expr) : MetaM (List (Nat × Nat)) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, h, t]) =>
    let h ← whnf h
    match h.getAppFnArgs with
    | (``Prod.mk, #[_, _, a, b]) =>
      let some a ← evalNat (← whnf a) | throwError "non-literal offset {a}"
      let some b ← evalNat (← whnf b) | throwError "non-literal width {b}"
      return (a, b) :: (← vedu1pPairs t)
    | _ => throwError "not a pair {h}"
  | _ => throwError "not a list {e}"

open Lean Meta in
partial def vedu1pPorts (e : Expr) : MetaM (List (String × Nat)) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, h, t]) =>
    let h ← whnf h
    match h.getAppFnArgs with
    | (``Sparkle.IR.AST.Port.mk, #[nm, ty]) =>
      let .lit (.strVal s) ← whnf nm | throwError "non-literal port name {nm}"
      let ty ← whnf ty
      match ty.getAppFnArgs with
      | (``Sparkle.IR.Type.HWType.bitVector, #[w]) =>
        let some w ← evalNat (← whnf w) | throwError "non-literal port width {w}"
        return (s, w) :: (← vedu1pPorts t)
      | _ => return (s, 0) :: (← vedu1pPorts t)
    | _ => throwError "not a port {h}"
  | _ => throwError "not a list {e}"

open Lean Elab Command Meta in
elab "#vedu1_packed_probe " id:ident : command => do
  try
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let env ← getEnv
    let thm := n ++ `ved_u1
    let md := n ++ `ved_mod
    let ct := n ++ `ved_contract
    match env.find? thm with
    | none => logInfo m!"VED U1P THM absent"
    | some (.thmInfo _) => logInfo m!"VED U1P THM theorem"
    | some _ => logInfo m!"VED U1P THM not-a-theorem"
    -- the statement term, rebuilt here: the original constant applied to
    -- `defaultDomain` once per LEADING implicit binder of type exactly `DomainConfig`
    let k ← liftTermElabM do
      let ci ← getConstInfo n
      forallTelescope ci.type fun xs _ => do
        let mut k := 0
        for x in xs do
          let ld ← x.fvarId!.getDecl
          if !ld.binderInfo.isExplicit && ld.type.isConstOf `Sparkle.Core.Domain.DomainConfig then k := k + 1
          else break
        pure k
    logInfo m!"VED U1P STMT domains={k}"
    let stmt := mkAppN (mkConst n) (List.replicate k (mkConst `Sparkle.Core.Domain.defaultDomain)).toArray
    if let some (.thmInfo ti) := env.find? thm then
      let expected := mkAppN (mkConst ``Tools.VedU1Packed.PackedStmt) #[mkConst ct, mkConst md, stmt]
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
    -- the packing rule, from the declaration's TYPE (`Signal d (A x B)`)
    let ws ← liftTermElabM do
      forallTelescopeReducing (← inferType stmt) fun _ res => do
        let res ← whnfR (← instantiateMVars res)
        match res.getAppFnArgs with
        | (``Sparkle.Core.Signal.Signal, #[_, a]) => vedu1pLeaves a
        | _ => throwError "result {res} is not a Signal"
    let total := ws.foldl (· + ·) 0
    let offs := (List.range ws.length).map fun i => (ws.drop (i + 1)).foldl (· + ·) 0
    let expSl := offs.zip ws
    let showSl (l : List (Nat × Nat)) := "[" ++ ",".intercalate (l.map fun (o, w) => s!"({o},{w})") ++ "]"
    logInfo m!"VED U1P LEAVES {ws.length} widths={ws} total={total}"
    -- the stored contract (`PContract`): slice map, port name, module name, wires
    match env.find? ct with
    | none => logInfo m!"VED U1P CONTRACT absent"
    | some (.defnInfo _) =>
      let c := mkConst ct
      let sl ← liftTermElabM <| vedu1pPairs (mkApp (mkConst ``Tools.VedU1Packed.PContract.slices) c)
      logInfo m!"VED U1P SLICES expected={showSl expSl} stored={showSl sl} {if sl == expSl then "equal" else "differs"}"
      let (cport, cmod, wiresEq, mname) ← liftTermElabM do
        let cport ← whnf (mkApp (mkConst ``Tools.VedU1Packed.PContract.port) c)
        let cmod ← whnf (mkApp (mkConst ``Tools.VedU1Packed.PContract.modName) c)
        let mname ← whnf (mkApp (mkConst ``Sparkle.IR.AST.Module.name) (mkConst md))
        let weq ← isDefEq (mkApp (mkConst ``Tools.VedU1Packed.PContract.wires) c)
          (mkApp (mkConst ``Sparkle.IR.AST.Module.wires) (mkConst md))
        pure (cport, cmod, weq, mname)
      let bound := cport == mkStrLit "out" && cmod == mname && wiresEq
      logInfo m!"VED U1P CONTRACT {if bound then "bound-to-mod" else "other"}"
    | some _ => logInfo m!"VED U1P CONTRACT not-a-def"
    -- the module's output ports: exactly one, named `out`, of the packed width
    if env.contains md then
      let ps ← liftTermElabM <| vedu1pPorts (mkApp (mkConst ``Sparkle.IR.AST.Module.outputs) (mkConst md))
      logInfo m!"VED U1P PORT module={ps} expect=[(out, {total})] {if ps == [("out", total)] then "match" else "differs"}"
    -- the output count of the STATEMENT term's type
    let tbl ← liftTermElabM do
      Tools.VedU1Contract.readTableOfType n (← Lean.Meta.inferType stmt)
    logInfo m!"VED U1P OUTS {tbl.out.flat.length}"
  catch e => logInfo m!"VED U1P PROBE failed: {← e.toMessageData.toString}"'''

PACKED_PROBE = '#vedu1_packed_probe @TOP@'


# The probe of the hierarchical route.  Independent of the tool: it never calls
# the tool's checker or HierShape; it rebuilds the statement and reads the CLOSED
# module / design / contract values itself (Meta.evalExpr on the stored value).
PRE_PROBE_HIER = '''open Lean Elab Command in
run_cmd do
  logInfo m!"VED U1P NS {← getCurrNamespace}"
  try
    let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent "@TOP@".toName)
    let u := (privateToUserName? n).getD n
    logInfo m!"VED U1P DECL resolved={n} user={u} inventory=@Q@ {if u == "@Q@".toName then "match" else "mismatch"}"
    let env ← getEnv
    let kids := env.constants.fold (fun a k _ => a || (n ++ `ved_child).isPrefixOf k) false
    logInfo m!"VED U1P PRE thm={env.contains (n ++ `ved_u1)} mod={env.contains (n ++ `ved_mod)} contract={env.contains (n ++ `ved_contract)} design={env.contains (n ++ `ved_design)} child={kids}"
  catch e => logInfo m!"VED U1P DECL absent: {← e.toMessageData.toString}"'''

EVAL_HELP = '''open Lean Meta in
unsafe def vedu1hEvalImpl {a : Type} (ty e : Lean.Expr) : MetaM a := Meta.evalExpr a ty e
open Lean Meta in
@[implemented_by vedu1hEvalImpl] opaque vedu1hEval {a : Type} (ty e : Lean.Expr) : MetaM a'''

PROBE_HIER = '''open Lean Elab Command Meta Sparkle.IR.AST in
run_cmd do
  try
    let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent "@TOP@".toName)
    let env ← getEnv
    let thm := n ++ `ved_u1
    let md := n ++ `ved_mod
    let dn := n ++ `ved_design
    let ct := n ++ `ved_contract
    match env.find? thm with
    | none => logInfo m!"VED U1P THM absent"
    | some (.thmInfo _) => logInfo m!"VED U1P THM theorem"
    | some _ => logInfo m!"VED U1P THM not-a-theorem"
    -- the statement term, rebuilt here: the original constant applied to
    -- `defaultDomain` once per LEADING implicit `DomainConfig` binder
    let k ← liftTermElabM do
      let ci ← getConstInfo n
      forallTelescope ci.type fun xs _ => do
        let mut k := 0
        for x in xs do
          let ld ← x.fvarId!.getDecl
          if !ld.binderInfo.isExplicit && ld.type.isConstOf `Sparkle.Core.Domain.DomainConfig then k := k + 1
          else break
        pure k
    logInfo m!"VED U1P STMT domains={k}"
    let stmt := mkAppN (mkConst n) (List.replicate k (mkConst `Sparkle.Core.Domain.defaultDomain)).toArray
    if let some (.thmInfo ti) := env.find? thm then
      let expected := mkAppN (mkConst ``Tools.VedU1Hier.U1HStmt) #[mkConst ct, mkConst md, mkConst dn, stmt]
      logInfo m!"VED U1P TYPE {if ti.type == expected then "exact" else "differs"}"
      logInfo m!"VED U1P MVARS type={ti.type.hasMVar} value={ti.value.hasMVar} fvars={ti.type.hasFVar || ti.value.hasFVar}"
      logInfo m!"VED U1P LEVELS {ti.levelParams.length}"
      let ax ← liftCoreM <| collectAxioms thm
      logInfo m!"VED U1P AXIOMS {Tools.VedStrictAudit.showNames (Tools.VedStrictAudit.sortNames ax)}"
    let closedOf (v : Lean.Expr) := !v.hasMVar && !v.hasFVar && !v.hasLooseBVars
    -- the closed module value
    let mut modV : Option Sparkle.IR.AST.Module := none
    match env.find? md with
    | none => logInfo m!"VED U1P MOD absent"
    | some (.defnInfo di) =>
      logInfo m!"VED U1P MOD closed={closedOf di.value} type={di.type == mkConst ``Sparkle.IR.AST.Module}"
      if closedOf di.value then
        modV := some (← liftTermElabM (vedu1hEval (a := Sparkle.IR.AST.Module) (mkConst ``Sparkle.IR.AST.Module) di.value))
    | some _ => logInfo m!"VED U1P MOD not-a-def"
    -- the closed design value
    let mut desV : Option Sparkle.IR.AST.Design := none
    match env.find? dn with
    | none => logInfo m!"VED U1P DESIGN absent"
    | some (.defnInfo di) =>
      logInfo m!"VED U1P DESIGN closed={closedOf di.value} type={di.type == mkConst ``Sparkle.IR.AST.Design}"
      if closedOf di.value then
        desV := some (← liftTermElabM (vedu1hEval (a := Sparkle.IR.AST.Design) (mkConst ``Sparkle.IR.AST.Design) di.value))
    | some _ => logInfo m!"VED U1P DESIGN not-a-def"
    -- the contract: bound to `ved_mod`, ports equal the module's
    let tbl ← liftTermElabM do
      Tools.VedU1Contract.readTableOfType n (← Lean.Meta.inferType stmt)
    match env.find? ct with
    | none => logInfo m!"VED U1P CONTRACT absent"
    | some (.defnInfo di) =>
      let ok := di.value.getAppFn.isConstOf ``Tools.VedU1Contract.contractOf &&
        di.value.getAppArgs.back? == some (mkConst md)
      logInfo m!"VED U1P CONTRACT {if ok then "bound-to-mod" else "other"}"
      -- ports: the contract's arguments (table, output names, clock/reset) and the
      -- module's ports against the table rebuilt from the statement's type
      -- (the contract value itself is read as an expression, not evaluated)
      if let some m := modV then
        let args := di.value.getAppArgs
        let okp := args.size == 4 && args[0]! == toExpr tbl &&
          args[1]! == toExpr (m.outputs.map (·.name)) &&
          args[2]! == toExpr (none : Option (String × String)) &&
          m.inputs.length == tbl.ins.length && m.outputs.length == tbl.out.flat.length &&
          (m.inputs.map (·.name)) == tbl.binders.map ("_gen_" ++ ·) &&
          (m.inputs.map (·.ty)) == tbl.ins.map (·.hw) && (m.outputs.map (·.ty)) == tbl.out.flat.map (·.hw)
        logInfo m!"VED U1P PORTS {if okp then "ok" else "differs"} inputs={m.inputs.length} outputs={m.outputs.length}"
      else logInfo m!"VED U1P PORTS no-module"
    | some _ => logInfo m!"VED U1P CONTRACT not-a-def"
    logInfo m!"VED U1P OUTS {tbl.out.flat.length}"
    -- the hierarchy
    if let (some m, some d) := (modV, desV) then
      logInfo m!"VED U1P HIERTOP {if d.topModule == m.name then "ok" else "differs"} design={d.topModule} mod={m.name}"
      let insts := m.body.filterMap fun s => match s with | .inst mn _ _ => some mn | _ => none
      let names := d.modules.map (·.name)
      let missing := insts.filter fun mn => !(names.contains mn)
      logInfo m!"VED U1P HIERMODS n={names.length} nonempty={!names.isEmpty} top-not-child={!(names.contains m.name)}"
      logInfo m!"VED U1P HIERINST {if missing.isEmpty && !insts.isEmpty then "ok" else "bad"} n={insts.length} missing={missing}"
      let mut allThm := true
      for cm in d.modules do
        let cthm := n ++ `ved_child ++ cm.name.toName ++ `ved_u1
        let st := match env.find? cthm with
          | none => "absent"
          | some (.thmInfo ti) =>
            if ti.type.getAppFn.isConstOf ``Tools.VedU1Contract.U1Stmt then "theorem" else "theorem-other-stmt"
          | some _ => "not-a-theorem"
        if st != "theorem" then allThm := false
        logInfo m!"VED U1P HIERCHILD {cm.name} thm={st}"
      logInfo m!"VED U1P HIERCHILDREN {names} all-theorems={allThm}"
  catch e => logInfo m!"VED U1P PROBE failed: {← e.toMessageData.toString}"'''


_P1 = """        let okp := args.size == 4 && args[0]! == toExpr tbl &&
          args[1]! == toExpr (m.outputs.map (·.name)) &&
          args[2]! == toExpr (none : Option (String × String)) &&
          m.inputs.length == tbl.ins.length && m.outputs.length == tbl.out.flat.length &&
          (m.inputs.map (·.name)) == tbl.binders.map ("_gen_" ++ ·) &&
          (m.inputs.map (·.ty)) == tbl.ins.map (·.hw) && (m.outputs.map (·.ty)) == tbl.out.flat.map (·.hw)"""
_P2 = """        -- H2a/H2b: the parent's inputs are the data inputs, then none or exactly clock and reset
        let kr : Option (Option (String × String)) := match m.inputs.drop tbl.ins.length with
          | [] => some none
          | [k, r] => some (some (k.name, r.name))
          | _ => none
        let nd := tbl.ins.length
        let okp := kr.isSome && args.size == 4 && args[0]! == toExpr tbl &&
          args[1]! == toExpr (m.outputs.map (·.name)) && m.outputs.map (·.name) == ["out"] &&
          args[2]! == toExpr kr.get! &&
          m.outputs.length == tbl.out.flat.length &&
          ((m.inputs.take nd).map (·.name)) == tbl.binders.map ("_gen_" ++ ·) &&
          ((m.inputs.take nd).map (·.ty)) == tbl.ins.map (·.hw) && (m.outputs.map (·.ty)) == tbl.out.flat.map (·.hw)"""
# H2b: the expected statement is chosen from the registered module ITSELF (its closed value, evaluated
# here): `U2HRStmt` when its body has a register, else `U2HStmt`; compared with `==` (exact).
_E1 = "      let expected := mkAppN (mkConst ``Tools.VedU1Hier.U1HStmt) #[mkConst ct, mkConst md, mkConst dn, stmt]"
_E2 = """      let hasReg : Option Bool ← match env.find? md with
        | some (.defnInfo di) =>
          if !di.value.hasMVar && !di.value.hasFVar && !di.value.hasLooseBVars then
            let mv ← liftTermElabM (vedu1hEval (a := Sparkle.IR.AST.Module) (mkConst ``Sparkle.IR.AST.Module) di.value)
            pure (some (mv.body.any fun s => match s with | .register .. => true | _ => false))
          else pure none
        | _ => pure none
      let stmtC := if hasReg == some true then ``Tools.VedU2Hier.U2HRStmt else ``Tools.VedU2Hier.U2HStmt
      logInfo m!"VED U1P EXPSTMT {if hasReg == some true then "U2HRStmt" else "U2HStmt"} registers={match hasReg with | some b => toString b | none => "unknown"}"
      let expected := mkAppN (mkConst stmtC) #[mkConst ct, mkConst md, mkConst dn, stmt]"""
assert _E1 in PROBE_HIER
PROBE_HIER_U2 = (PROBE_HIER.replace(_E1, _E2).replace(_P1, _P2))
assert "U2HRStmt" in PROBE_HIER_U2 and _P2 in PROBE_HIER_U2 and _E2 in PROBE_HIER_U2

# u2_hier: nothing named `<decl>.ved_*` (theorem, module, design, contract, outs, body, child.*,
# open, open_eq, ...) may exist before the entry runs
PRE_PROBE_U2 = PRE_PROBE_HIER.replace(
    "let kids := env.constants.fold (fun a k _ => a || (n ++ `ved_child).isPrefixOf k) false",
    "let kids := env.constants.fold (fun a k _ => a || (n.isPrefixOf k && k != n && ((k.components[n.components.length]?).any fun c => c.toString.startsWith \"ved_\"))) false")
assert PRE_PROBE_U2 != PRE_PROBE_HIER


def block_pieces(r, route, ns):
    """[(segment, text)] in order; segment is None for plumbing."""
    opts = lean_option_lines(r["options"], "default")
    prefix = "".join(f"set_option {o} in\n" for o in ["Elab.async false"] + opts)
    top, q = r["top"], r["qualified"] or ""
    sub = lambda s: s.replace("@TOP@", top).replace("@Q@", q)
    hier = route in HIER_ROUTES
    p = [(None, f"-- ===== VED U1 BEGIN row {r['row']} route {route} (inventory {INV_COMMIT[:8]}) ====="),
         (None, f"namespace {ns}"), (None, TIMER), ("pre", sub(PRE_PROBE_U2 if route == "u2_hier" else PRE_PROBE_HIER if hier else PRE_PROBE))]
    if hier:
        p.append((None, EVAL_HELP))
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
    if route == "u1_packed":
        probe = [("probe", PACKED_PROBE_DEF), ("probe", sub(PACKED_PROBE))]
    else:
        probe = [("probe", sub(PROBE_HIER_U2 if route == "u2_hier" else PROBE_HIER if hier else PROBE))]
    p += probe + [("probe", '#vedu1_t "probe_end"'),
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


def later_stages(stage, route=""):
    pipe = U2_HIER_PIPELINE if route == "u2_hier" else HIER_PIPELINE if route == "u1_hier" else PIPELINE_PACKED if route == "u1_packed" else PIPELINE
    if stage in pipe:
        return ";".join(pipe[pipe.index(stage) + 1:])
    return ""


def parse_probe(text):
    """The `VED U1P` lines of the probe segment -> dict (None-valued when absent)."""
    p = {}
    pats = [("thm", r"VED U1P THM (\S+)"), ("type", r"VED U1P TYPE (\S+)"),
            ("mvars", r"VED U1P MVARS type=(\w+) value=(\w+) fvars=(\w+)"),
            ("levels", r"VED U1P LEVELS (\d+)"), ("mod", r"VED U1P MOD (.*)"),
            ("contract", r"VED U1P CONTRACT (\S+)"), ("outs", r"VED U1P OUTS (\d+)"),
            ("leaves", r"VED U1P LEAVES (\d+) widths=\[([^\]]*)\] total=(\d+)"),
            ("slices", r"VED U1P SLICES expected=(\S+) stored=(\S+) (equal|differs)"),
            ("port", r"(?m)VED U1P PORT module=(\S.*?) expect=(\S.*?) (match|differs)\s*$"),
            ("axioms", r"VED U1P AXIOMS \[([^\]]*)\]"), ("failed", r"VED U1P PROBE failed: (.*)")]
    for k, pat in pats:
        m = re.search(pat, text)
        p[k] = m.groups() if m else None
    return p


def hier_probe(row, ptext, okm, u1, route=""):
    """The u1_hier part of the probe: fills the probe_hier_* columns, returns the blockers.
    Every item must be established by a `VED U1P` line of the probe itself."""
    bl = []
    g = lambda pat: re.search(pat, ptext)
    m = g(r"VED U1P DESIGN (.*)")
    row["probe_design"] = m.group(1).strip() if m else ""
    if not (m and m.group(1).startswith("closed=true type=true")):
        bl.append(f"design:{row['probe_design'] or 'unknown'}")
    m = g(r"VED U1P HIERTOP (\w+) design=(\S*) mod=(\S*)")
    row["probe_hier_top"] = m.group(1) if m else ""
    if not (m and m.group(1) == "ok"):
        bl.append("topModule:" + (f"differs(design={m.group(2)},mod={m.group(3)})" if m else "unknown"))
    m = g(r"VED U1P HIERMODS n=(\d+) nonempty=(\w+) top-not-child=(\w+)")
    row["probe_hier_modules"] = m.group(1) if m else ""
    if not (m and m.group(2) == "true" and int(m.group(1)) > 0):
        bl.append("modules:" + ("empty" if m else "unknown"))
    elif m.group(3) != "true":
        bl.append("modules:top-is-child")
    m = g(r"VED U1P HIERINST (\w+) n=(\d+) missing=(\[[^\]]*\])")
    row["probe_hier_insts"] = f"{m.group(1)} n={m.group(2)} missing={m.group(3)}" if m else ""
    if not (m and m.group(1) == "ok"):
        bl.append("instances:" + (f"n={m.group(2)},missing={m.group(3)}" if m else "unknown"))
    kids = re.findall(r"VED U1P HIERCHILD (\S+) thm=(\S+)", ptext)
    m = g(r"VED U1P HIERCHILDREN \[([^\]]*)\] all-theorems=(\w+)")
    row["probe_hier_children"] = ";".join(x.strip().strip('"') for x in m.group(1).split(",") if x.strip()) if m else ""
    row["probe_hier_child_thms"] = ";".join(f"{n.strip(chr(34))}={t}" for n, t in kids)
    if not m:
        bl.append("children:unknown")
    else:
        names = [x.strip().strip('"') for x in m.group(1).split(",") if x.strip()]
        bad = [f"{n.strip(chr(34))}={t}" for n, t in kids if t != "theorem"]
        if m.group(2) != "true" or bad or len(kids) != len(names) or not names:
            bl.append("child-thm:" + (",".join(bad) or "inconsistent"))
    m = g(r"VED U1P PORTS (\w[\w-]*)")
    row["probe_ports"] = m.group(1) if m else ""
    if row["probe_ports"] != "ok":
        bl.append(f"ports:{row['probe_ports'] or 'unknown'}")
    if route == "u2_hier":
        m = g(r"VED U1P EXPSTMT (U2HR?Stmt) registers=(\w+)")
        row["probe_expected_stmt"] = f"{m.group(1)} registers={m.group(2)}" if m else ""
        if not m or m.group(2) not in ("true", "false"):
            bl.append("expected-stmt:" + (row["probe_expected_stmt"] or "unknown"))
    if okm:
        full = next((t for ln, sev, t in u1 if t.startswith(("VED U1 HIER OK ", "VED U2 HIER OK "))), "")
        mt = re.search(r"synthesis (\d+) ms, children (\d+) ms, parent proof (\d+) ms, peak (\d+) kB", full)
        if mt:
            row["tool_reported"] = "synth_ms=%s;children_ms=%s;parent_ms=%s;peak_kb=%s" % mt.groups()
    return bl


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
    row["prep_status"] = "n/a" if route in ("u1", "u1_hier", "u1_packed", "u2_hier") else "not-run"
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
    # namespace wrapper (u1_deep_ns): one `VED U1N` line per wrap (prep, U1)
    if route == "u1_deep_ns":
        wraps = re.findall(r"VED U1N scope=(\S+) outer=(\S+) inner=(\S+) (same|differs)", text)
        row["ns_scope"] = ",".join(sorted({w[0] for w in wraps}))
        row["ns_detail"] = ";".join(f"outer={w[1]} inner={w[2]}" for w in wraps)
        modes = sorted(set(re.findall(r"VED U1N scope=\S+ outer=\S+ inner=\S+ (?:same|differs) mode=(\w+)", text)))
        row["ns_mode"] = ",".join(modes) if modes else "unrecorded"
        if len(wraps) == 2 and all(w[3] == "same" and w[1] == resolved for w in wraps):
            row["ns_check"] = "same"
        elif any(w[3] == "differs" for w in wraps):
            row["ns_check"] = "differs"
        elif wraps and resolved and any(w[1] != resolved for w in wraps):
            row["ns_check"] = "outer-differs-from-original"
        else:
            row["ns_check"] = f"absent({len(wraps)} wraps)"
    else:
        row["ns_scope"] = row["ns_check"] = row["ns_detail"] = row["ns_mode"] = "n/a"
    row["prep_command"] = ("n/a" if route in ("u1", "u1_hier", "u1_packed", "u2_hier") else
                           ("#vedu1_in_declns " if route == "u1_deep_ns" else "") + f"#verify_elab_deep {meta.get('top', '')}")
    row["u1_command"] = ("#vedu1_in_declns " if route == "u1_deep_ns" else "") + f"{ENTRY_CMD[route]} {meta.get('top', '')}"
    m = re.search(r"VED U1P PRE thm=(\w+) mod=(\w+) contract=(\w+)(?: design=(\w+) child=(\w+))?", text)
    pre_exist = bool(m and "true" in m.groups())
    if route in HIER_ROUTES and m and m.group(4) is None:
        pre_exist = True      # a PRE line without design/child cannot show they were absent
    row["probe_preexisting"] = "unknown" if not m else ("yes" if pre_exist else "no")
    if route in HIER_ROUTES and m and m.group(4) is None:
        row["probe_preexisting"] = "unknown"

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

    # namespace wrapper failure (u1_deep_ns): its own HARNESS-FAIL line, or
    # Lean's `invalid scope` from withNamespace in older harness versions
    ns_fail = ""
    if route == "u1_deep_ns":
        for ln, sev, t in msgs:
            if sev == "error" and (t.startswith("VED U1N HARNESS-FAIL") or t.strip() == "invalid scope"):
                ns_fail = t
                break

    # the U1 step
    u1 = in_seg("u1")
    u1_errs = [t for ln, sev, t in u1 if sev == "error"]
    # u1_packed: the tool's own `VED U1 PACKED OK` line; a plain `VED U1 OK` is not accepted there
    ok_prefix = ("VED U2 HIER OK " if route == "u2_hier" else "VED U1 HIER OK " if route == "u1_hier" else
                 "VED U1 PACKED OK " if route == "u1_packed" else "VED U1 OK ")
    okm = next((re.match(re.escape(ok_prefix) + r"(\S+)( \(specialised at defaultDomain\))?:", t)
                for ln, sev, t in u1 if t.startswith(ok_prefix)), None)
    row["u1_ok_line"] = "yes" if okm else "no"
    row["u1_ok_thm"] = okm.group(1) if okm else ""
    row["u1_ok_specialised"] = ("yes" if okm.group(2) else "no") if okm else ""
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
    elif route == "u1_deep_ns" and ns_fail:
        # the namespace wrapper itself failed (e.g. `invalid scope` from
        # withNamespace at the root or on a private name before 2026-11-10):
        # the row's command never ran, so this is undetermined, not a refusal
        cause = "harness-error(ns-wrapper)"
        row["harness_error"] = (row["harness_error"] + ";" if row["harness_error"] else "") + \
            f"namespace wrapper failed: {first_line(ns_fail, 160)}"
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
        row.update(u1_status="refused", first_cause=cause, later_stages_not_reached=later_stages(stage, route))
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
    if route == "u1_packed":
        if p["slices"]:
            row["probe_slices"] = f"{p['slices'][2]} expected={p['slices'][0]} stored={p['slices'][1]}"
        if p["port"]:
            row["probe_port"] = f"{p['port'][2]} module={p['port'][0]} expect={p['port'][1]}"
    axs = []
    if p["axioms"]:
        axs = [x.strip() for x in p["axioms"][0].split(",") if x.strip()]
        row["probe_axioms"] = ";".join(axs)
        row["probe_axioms_std3"] = "yes" if set(axs) <= STD3 else "no"
    hier_bl = []
    if route in HIER_ROUTES:
        hier_bl = hier_probe(row, "\n".join(pm), okm, u1, route)
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
        bl.append("no-VED-U1-PACKED-OK-line" if route == "u1_packed" else "no-VED-U1-OK-line")
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
    if route == "u1_packed":
        # the packed contract: at least two leaves inside one Signal, the packing rule
        # (computed by the probe from the declaration's TYPE) equals the stored slice
        # map, the widths add up to the width of the module's single output `out`
        lv = p["leaves"]
        widths = [int(x) for x in lv[1].split(",") if x.strip()] if lv else []
        if not lv:
            bl.append("leaves:unknown")
        elif len(widths) < 2 or str(len(widths)) != row["probe_outputs"]:
            bl.append(f"leaves:{len(widths)} outputs={row['probe_outputs'] or 'unknown'}")
        elif sum(widths) != int(lv[2]):
            bl.append("leaves:width-sum")
        if not p["slices"] or p["slices"][2] != "equal":
            bl.append(f"slices:{p['slices'][2] if p['slices'] else 'unknown'}")
        if not p["port"] or p["port"][2] != "match":
            bl.append(f"port:{p['port'][2] if p['port'] else 'unknown'}")
    elif row["probe_outputs"] != "1":
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
    m_dom = re.search(r"VED U1P STMT domains=(\d+)", "\n".join(pm))
    row["probe_domains"] = m_dom.group(1) if m_dom else ""
    if not m_dom:
        bl.append("stmt-domains:unknown")
    elif okm and (row["probe_domains"] != "0") != (row["u1_ok_specialised"] == "yes"):
        # the OK line's "specialised" claim must match the statement the probe rebuilt
        bl.append(f"specialised-mismatch:ok={row['u1_ok_specialised']},domains={row['probe_domains']}")
    if resolved and row["u1_ok_thm"] != f"{resolved}.ved_u1":
        bl.append(f"ok-thm-name:{row['u1_ok_thm'] or 'none'}")
    if row["ran"] != "yes" or "probe_end" not in marks:
        bl.append("run-incomplete")
    if route == "u1_deep_ns" and row["ns_check"] != "same":
        bl.append(f"ns:{row['ns_check'] or 'unknown'}")
    # the case itself must succeed: Lean's exit status 0 and no error outside
    # the inserted block (an error after the probe or in the original file
    # would otherwise leave strict=yes)
    row["case_ok"] = "yes" if rcv == "0" and row["errors_outside_block"] == "0" else "no"
    if rcv != "0":
        bl.append(f"rc:{rcv or 'unknown'}")
    if row["errors_outside_block"] != "0":
        bl.append(f"outside-errors:{row['errors_outside_block']}")
    bl += hier_bl
    strict = not bl
    case_only = bool(bl) and all(b.startswith(("rc:", "outside-errors:")) for b in bl)
    row["strict_counted"] = "yes" if strict else "no"
    row["strict_label"] = "returned-IR strict: U1, reset=0, order-free" if strict else "no"
    row["strict_blockers"] = ";".join(bl)
    if strict:
        row.update(u1_status="ok", first_cause="none")
    elif case_only and row["u1_ok_line"] == "yes" and not cause and not refusal and not u1_errs:
        # theorem confirmed by the probe, but the case itself failed (non-zero
        # exit or an error outside the block): not counted
        row.update(u1_status="ok-but-case-failed", first_cause="case-error")
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
    g.add_argument("--setting", required=True, help="route: u1 | u1_deep | u1_deep_ns | u1_hier | u1_packed | u2_hier")
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
