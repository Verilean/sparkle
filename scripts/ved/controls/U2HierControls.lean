/-
U2 measurement controls for the stateful hierarchical route `u2_hier` probe (MEASUREMENT ONLY, never for
main).  TEMPLATE: the two markers below are filled from scripts/ved/u1_gen.py (EVAL_HELP and
PROBE_HIER_U2) so the probe tested here is the probe the harness runs; scripts/ved/controls/
gen_u2hier_controls.py writes the .lean file, and the Python tests check that it has not drifted.

Run (after `kjob lake build Tools.VedU2HierRegEntry Tools.VedStrictAudit`):
  python3 -I scripts/ved/controls/gen_u2hier_controls.py OUT.lean
  kjob lake env lean OUT.lean
The file elaborates without error iff every control holds; each prints `VED U2HCTL <id> PASS`.

The probe chooses the expected statement from the registered module itself: `U2HRStmt` when the
module's body has a register, else `U2HStmt`, compared with `==`.  Strict (TYPE exact, and every other
probe item) is expected ONLY where marked YES.

  P0  H2a positive: register-free parent `parA` (two register-free children), `#ved_u2_hier` accepts;
      EXPSTMT U2HStmt registers=false, TYPE exact, PORTS ok, all-theorems=true, std3.      strict YES
  P1  H2b positive: parent WITH a register `parR` (one register child `accMod`);
      EXPSTMT U2HRStmt registers=true, TYPE exact, PORTS ok, all-theorems=true, std3.      strict YES
  M1  another declaration's theorem: `parR2` carries `parR`'s artifacts and `parR.ved_u1`.   TYPE differs
  M2  U2HStmt stored for a register parent (hand-written theorem under `ved_u1`):
      EXPSTMT U2HRStmt, TYPE differs.                                                      not strict
  M3  U2HRStmt stored for a register-free parent: EXPSTMT U2HStmt, TYPE differs.             not strict
  M4  register presence swapped: the register parent's module under a theorem that states the
      register-free statement (M2's mirror at the module level: module of `parR`, statement
      `U2HStmt` of the register-free `parA`'s artifacts) and the register-free module under
      `U2HRStmt` of the register parent's artifacts: TYPE differs both ways.                not strict
  M5  the same-statement theorem is accepted for a CLONE of the register parent (sanity of the
      cloner: sorry proof of the right statement shows TYPE exact, and only the std3 line differs).
-/
import Tools.VedU2HierRegEntry
import Tools.VedStrictAudit
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

open Lean Elab Command Meta
open Sparkle.IR.AST Sparkle.Core.Domain Sparkle.Core.Signal

namespace VedH2Ctl
@[hardware_module] def hcA (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x - y
@[hardware_module] def hcB (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (x ^^^ y) - y
@[hardware_module] def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r
#verify_elab_deep accMod

-- H2a: register-free parent
def parA (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := hcA a b + hcB a b
def parA2 (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := hcA a b + hcB a b
def parA3 (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := hcA a b + hcB a b
-- H2b: a parent with a register and one instance
@[hardware_module] def parR (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod a
    p <~ u - p
    return (p : Signal defaultDomain (BitVec 8))
@[hardware_module] def parR2 (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod a
    p <~ u - p
    return (p : Signal defaultDomain (BitVec 8))
@[hardware_module] def parR3 (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod a
    p <~ u - p
    return (p : Signal defaultDomain (BitVec 8))
@[hardware_module] def parR4 (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod a
    p <~ u - p
    return (p : Signal defaultDomain (BitVec 8))
@[hardware_module] def parR5 (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod a
    p <~ u - p
    return (p : Signal defaultDomain (BitVec 8))
end VedH2Ctl

-- the probe's evaluator and the probe, verbatim from u1_gen.py
open Lean Meta in
unsafe def vedu1hEvalImpl {a : Type} (ty e : Lean.Expr) : MetaM a := Meta.evalExpr a ty e
open Lean Meta in
@[implemented_by vedu1hEvalImpl] opaque vedu1hEval {a : Type} (ty e : Lean.Expr) : MetaM a

open Lean Elab Command Meta Sparkle.IR.AST in
elab "#vedu2h_probe " id:ident : command => do
  try
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
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
      let hasReg : Option Bool ← match env.find? md with
        | some (.defnInfo di) =>
          if !di.value.hasMVar && !di.value.hasFVar && !di.value.hasLooseBVars then
            let mv ← liftTermElabM (vedu1hEval (a := Sparkle.IR.AST.Module) (mkConst ``Sparkle.IR.AST.Module) di.value)
            pure (some (mv.body.any fun s => match s with | .register .. => true | _ => false))
          else pure none
        | _ => pure none
      let stmtC := if hasReg == some true then ``Tools.VedU2Hier.U2HRStmt else ``Tools.VedU2Hier.U2HStmt
      logInfo m!"VED U1P EXPSTMT {if hasReg == some true then "U2HRStmt" else "U2HStmt"} registers={match hasReg with | some b => toString b | none => "unknown"}"
      let expected := mkAppN (mkConst stmtC) #[mkConst ct, mkConst md, mkConst dn, stmt]
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
        -- H2a/H2b: the parent's inputs are the data inputs, then none or exactly clock and reset
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
          ((m.inputs.take nd).map (·.ty)) == tbl.ins.map (·.hw) && (m.outputs.map (·.ty)) == tbl.out.flat.map (·.hw)
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
  catch e => logInfo m!"VED U1P PROBE failed: {← e.toMessageData.toString}"

/-! ## Control plumbing -/

/-- Run `c`, capture its messages and drop them; every `has` must be a substring of some message, no
`lacks` may be, and no message may be an error. -/
elab "#vedu2h_expect " id:str "[" hs:str,* "]" "[" ls:str,* "]" c:command : command => do
  let saved := (← get).messages
  modify fun s => { s with messages := MessageLog.empty }
  elabCommand c
  let msgs ← (← get).messages.toList.mapM fun m => do pure (m.severity, ← m.data.toString)
  modify fun s => { s with messages := saved }
  let has (p : String) := msgs.any fun (_, t) => (t.splitOn p).length > 1
  let errs := msgs.filter (·.1 == .error)
  unless errs.isEmpty do throwError m!"VED U2HCTL {id.getString} FAIL: errors {errs.map (·.2)}"
  for h in hs.getElems do
    unless has h.getString do
      throwError m!"VED U2HCTL {id.getString} FAIL: expected line `{h.getString}` not found in {msgs.map (·.2)}"
  for l in ls.getElems do
    if has l.getString then
      throwError m!"VED U2HCTL {id.getString} FAIL: unexpected `{l.getString}` in {msgs.map (·.2)}"
  logInfo m!"VED U2HCTL {id.getString} PASS"

/-- The harness's two steps on one declaration: the tool, then the probe. -/
elab "#vedu2h_both " id:ident : command => do
  elabCommand (← `(set_option Elab.async false in #ved_u2_hier $id))
  elabCommand (← `(#vedu2h_probe $id))

/-- Clone the artifacts of `src` under `dst` (the module value of `modFrom`) and store, under
`dst.ved_u1`, a hand-written theorem: `stmt` (`U2HStmt` / `U2HRStmt`) of the clone's contract, module,
design and declaration, proved by `sorryAx`; or, with `own`, `src`'s own theorem. -/
def cloneH (src dst modFrom : Name) (stmt : Option Name) (kids : List Name) : CommandElabM Unit := liftTermElabM do
  let env ← getEnv
  let some (.defnInfo dm) := env.find? (src ++ `ved_mod) | throwError "no {src}.ved_mod"
  let some (.defnInfo dd) := env.find? (src ++ `ved_design) | throwError "no {src}.ved_design"
  let some (.defnInfo dc) := env.find? (src ++ `ved_contract) | throwError "no {src}.ved_contract"
  let some (.thmInfo dt) := env.find? (src ++ `ved_u1) | throwError "no {src}.ved_u1"
  let mkD (n : Name) (ty v : Lean.Expr) : MetaM Unit :=
    addDecl (.defnDecl (mkDefinitionValEx n [] ty v .abbrev .safe []))
  let some (.defnInfo dm2) := env.find? (modFrom ++ `ved_mod) | throwError "no {modFrom}.ved_mod"
  mkD (dst ++ `ved_mod) dm.type dm2.value
  mkD (dst ++ `ved_design) dd.type dd.value
  mkD (dst ++ `ved_contract) dc.type
    (mkAppN dc.value.getAppFn (dc.value.getAppArgs.pop.push (mkConst (dst ++ `ved_mod))))
  match stmt with
  | some sn =>
    let expected := mkAppN (mkConst sn)
      #[mkConst (dst ++ `ved_contract), mkConst (dst ++ `ved_mod), mkConst (dst ++ `ved_design), mkConst dst]
    addDecl (.thmDecl { name := dst ++ `ved_u1, levelParams := [], type := expected,
                        value := mkApp2 (mkConst ``sorryAx [Level.zero]) expected (mkConst ``Bool.false) })
  | none =>
    addDecl (.thmDecl { name := dst ++ `ved_u1, levelParams := [], type := dt.type, value := mkConst dt.name })
  for k in kids do
    let some (.thmInfo kt) := env.find? (src ++ `ved_child ++ k ++ `ved_u1) | throwError "no leaf theorem of {k}"
    addDecl (.thmDecl { name := dst ++ `ved_child ++ k ++ `ved_u1, levelParams := [], type := kt.type,
                        value := mkConst kt.name })

elab "#vedu2h_clone " src:ident dst:ident "mod" mf:ident "stmt" s:ident "kids" "[" ks:ident,* "]" : command => do
  cloneH src.getId dst.getId (if mf.getId == `own then src.getId else mf.getId) (if s.getId == `own then none else some s.getId) (ks.getElems.toList.map (·.getId))

/-! ## P0: H2a, the register-free parent, `U2HStmt` -/
#vedu2h_expect "P0" [
    "VED U2 HIER OK VedH2Ctl.parA.ved_u1",
    "VED U1P THM theorem", "VED U1P EXPSTMT U2HStmt registers=false", "VED U1P TYPE exact",
    "VED U1P MVARS type=false value=false fvars=false", "VED U1P LEVELS 0",
    "VED U1P MOD closed=true type=true", "VED U1P DESIGN closed=true type=true",
    "VED U1P CONTRACT bound-to-mod", "VED U1P PORTS ok", "VED U1P OUTS 1",
    "VED U1P HIERTOP ok", "VED U1P HIERINST ok n=2 missing=[]", "all-theorems=true", "VED U1P AXIOMS"]
  ["sorryAx", "differs", "absent", "U2HRStmt", "ofReduceBool", "trustCompiler"]
  #vedu2h_both VedH2Ctl.parA

/-! ## P1: H2b, the parent with a register, `U2HRStmt` -/
#vedu2h_expect "P1" [
    "VED U2 HIER OK VedH2Ctl.parR.ved_u1",
    "VED U1P THM theorem", "VED U1P EXPSTMT U2HRStmt registers=true", "VED U1P TYPE exact",
    "VED U1P MVARS type=false value=false fvars=false", "VED U1P LEVELS 0",
    "VED U1P MOD closed=true type=true", "VED U1P DESIGN closed=true type=true",
    "VED U1P CONTRACT bound-to-mod", "VED U1P PORTS ok", "VED U1P OUTS 1",
    "VED U1P HIERTOP ok", "VED U1P HIERINST ok n=1 missing=[]", "all-theorems=true", "VED U1P AXIOMS"]
  ["sorryAx", "differs", "absent", "U2HStmt registers", "ofReduceBool", "trustCompiler"]
  #vedu2h_both VedH2Ctl.parR

/-! ## M1: another declaration's theorem (`parR`'s own `ved_u1` under the carrier `parR2`) -/
#vedu2h_clone VedH2Ctl.parR VedH2Ctl.parR2 mod own stmt own kids [VedH2Ctl.accMod]
#vedu2h_expect "M1" ["VED U1P THM theorem", "VED U1P EXPSTMT U2HRStmt registers=true", "VED U1P TYPE differs"]
  ["VED U1P TYPE exact"]
  #vedu2h_probe VedH2Ctl.parR2

/-! ## M2: `U2HStmt` stored for a register parent -/
#vedu2h_clone VedH2Ctl.parR VedH2Ctl.parR3 mod own stmt Tools.VedU2Hier.U2HStmt kids [VedH2Ctl.accMod]
#vedu2h_expect "M2" ["VED U1P THM theorem", "VED U1P EXPSTMT U2HRStmt registers=true", "VED U1P TYPE differs"]
  ["VED U1P TYPE exact"]
  #vedu2h_probe VedH2Ctl.parR3

/-! ## M3: `U2HRStmt` stored for a register-free parent -/
#vedu2h_clone VedH2Ctl.parA VedH2Ctl.parA2 mod own stmt Tools.VedU2Hier.U2HRStmt kids [VedH2Ctl.hcA, VedH2Ctl.hcB]
#vedu2h_expect "M3" ["VED U1P THM theorem", "VED U1P EXPSTMT U2HStmt registers=false", "VED U1P TYPE differs"]
  ["VED U1P TYPE exact"]
  #vedu2h_probe VedH2Ctl.parA2

/-! ## M4: register presence swapped at the module level (`mod` = the other declaration's module value):
the register parent's module under the statement a register-free parent carries (`U2HStmt`), and the
register-free module under `U2HRStmt`.  The probe takes the register presence from the module that IS
registered, so each is `differs`. -/
#vedu2h_clone VedH2Ctl.parA VedH2Ctl.parA3 mod VedH2Ctl.parR stmt Tools.VedU2Hier.U2HStmt kids [VedH2Ctl.hcA, VedH2Ctl.hcB]
#vedu2h_expect "M4a" ["VED U1P THM theorem", "VED U1P EXPSTMT U2HRStmt registers=true", "VED U1P TYPE differs"]
  ["VED U1P TYPE exact"]
  #vedu2h_probe VedH2Ctl.parA3

#vedu2h_clone VedH2Ctl.parR VedH2Ctl.parR4 mod VedH2Ctl.parA stmt Tools.VedU2Hier.U2HRStmt kids [VedH2Ctl.accMod]
#vedu2h_expect "M4b" ["VED U1P THM theorem", "VED U1P EXPSTMT U2HStmt registers=false", "VED U1P TYPE differs"]
  ["VED U1P TYPE exact"]
  #vedu2h_probe VedH2Ctl.parR4

/-! ## M5: cloner sanity: the right statement (`U2HRStmt`) stored for a register parent's clone is
`TYPE exact` (the proof is `sorryAx`, so only the audit line shows it) -/
#vedu2h_clone VedH2Ctl.parR VedH2Ctl.parR5 mod own stmt Tools.VedU2Hier.U2HRStmt kids [VedH2Ctl.accMod]
#vedu2h_expect "M5" ["VED U1P THM theorem", "VED U1P EXPSTMT U2HRStmt registers=true", "VED U1P TYPE exact",
    "VED U1P PORTS ok", "sorryAx"] ["VED U1P TYPE differs"]
  #vedu2h_probe VedH2Ctl.parR5
