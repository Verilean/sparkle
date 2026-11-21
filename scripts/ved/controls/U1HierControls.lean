/-
U1 measurement controls for the HIERARCHICAL route `u1_hier` probe
(MEASUREMENT ONLY, never for main).  TEMPLATE: the two markers below are filled
from scripts/ved/u1_gen.py (EVAL_HELP and PROBE_HIER) so the probe tested here is
the probe the harness runs; scripts/ved/controls/gen_u1hier_controls.py writes
the .lean file, and the Python tests check that the probe region has not drifted.

Run (after `kjob lake build Tools.VedU1HierEntry Tools.VedStrictAudit`):
  python3 -I scripts/ved/controls/gen_u1hier_controls.py OUT.lean
  kjob lake env lean OUT.lean
The file elaborates without error iff every control holds; each prints
`VED U1HCTL <id> PASS`.

  C0  a hand-made 2-child parent (`VedHCtl.par`, children hcA and hcB, two
      instances): `#ved_u1_hier` accepts and the probe confirms every item
      (theorem, exact U1HStmt type, std3, closed module and design, contract
      bound, ports, topModule, both children's leaf theorems);
  C1  another declaration's theorem: `par2` carries `par`'s artifacts and
      `par.ved_u1` itself; the exact-type check REJECTS it (TYPE differs);
  C2  a design whose topModule differs: the probe reports HIERTOP differs;
  C3  a missing child theorem: the leaf theorem of hcB is absent, the probe
      reports it (hcA present) and all-theorems=false;
  C4  a design with no child module: the probe reports nonempty=false;
  C5  a PRIVATE parent: accepted, the constants live under the private name and
      the probe resolves the children under it.
C2-C4 are built by cloning `par`'s checked artifacts under another declaration
(theorem value `sorryAx`: only the structural lines of the probe are asserted
there; the std3 line is expected to show the sorry).
-/
import Tools.VedU1HierEntry
import Tools.VedStrictAudit

open Lean Elab Command Meta
open Sparkle.IR.AST Sparkle.Core.Domain Sparkle.Core.Signal

namespace VedHCtl
@[hardware_module] def hcA (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x - y
@[hardware_module] def hcB (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (x ^^^ y) - y
def par (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := hcB (hcA a b) b
def par2 (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := hcB (hcA a b) b
def par3 (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := hcB (hcA a b) b
def par4 (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := hcB (hcA a b) b
def par5 (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := hcB (hcA a b) b
private def ppar (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := hcB (hcA a b) b
end VedHCtl

-- the probe's evaluator and the probe, verbatim from u1_gen.py
open Lean Meta in
unsafe def vedu1hEvalImpl {a : Type} (ty e : Lean.Expr) : MetaM a := Meta.evalExpr a ty e
open Lean Meta in
@[implemented_by vedu1hEvalImpl] opaque vedu1hEval {a : Type} (ty e : Lean.Expr) : MetaM a

open Lean Elab Command Meta Sparkle.IR.AST in
elab "#vedu1h_probe " id:ident : command => do
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
  catch e => logInfo m!"VED U1P PROBE failed: {← e.toMessageData.toString}"

/-! ## Control plumbing -/

/-- Run `c`, capture its messages and drop them; every `has` must be a substring
of some message, no `lacks` may be, and no message may be an error. -/
elab "#vedu1h_expect " id:str "[" hs:str,* "]" "[" ls:str,* "]" c:command : command => do
  let saved := (← get).messages
  modify fun s => { s with messages := MessageLog.empty }
  elabCommand c
  let msgs ← (← get).messages.toList.mapM fun m => do pure (m.severity, ← m.data.toString)
  modify fun s => { s with messages := saved }
  let has (p : String) := msgs.any fun (_, t) => (t.splitOn p).length > 1
  let errs := msgs.filter (·.1 == .error)
  unless errs.isEmpty do throwError m!"VED U1HCTL {id.getString} FAIL: errors {errs.map (·.2)}"
  for h in hs.getElems do
    unless has h.getString do
      throwError m!"VED U1HCTL {id.getString} FAIL: expected line `{h.getString}` not found in {msgs.map (·.2)}"
  for l in ls.getElems do
    if has l.getString then
      throwError m!"VED U1HCTL {id.getString} FAIL: unexpected `{l.getString}` in {msgs.map (·.2)}"
  logInfo m!"VED U1HCTL {id.getString} PASS"

/-- The harness's two steps on one declaration: the tool, then the probe. -/
elab "#vedu1h_both " id:ident : command => do
  elabCommand (← `(set_option Elab.async false in #ved_u1_hier $id))
  elabCommand (← `(#vedu1h_probe $id))

/-- Clone the artifacts of `src` under `dst`: module, contract (bound to the clone's module),
design (top module renamed, or its module list emptied) and the theorem (`sorryAx` of the clone's
exact statement, or `src`'s own theorem), plus the leaf theorems of `kids`. -/
def cloneHier (src dst : Name) (topMod : Option String) (noKids : Bool) (kids : List Name)
    (sorryProof : Bool) : CommandElabM Unit := liftTermElabM do
  let env ← getEnv
  let some (.defnInfo dm) := env.find? (src ++ `ved_mod) | throwError "no {src}.ved_mod"
  let some (.defnInfo dd) := env.find? (src ++ `ved_design) | throwError "no {src}.ved_design"
  let some (.defnInfo dc) := env.find? (src ++ `ved_contract) | throwError "no {src}.ved_contract"
  let some (.thmInfo dt) := env.find? (src ++ `ved_u1) | throwError "no {src}.ved_u1"
  let mkD (n : Name) (ty v : Lean.Expr) : MetaM Unit :=
    addDecl (.defnDecl (mkDefinitionValEx n [] ty v .abbrev .safe []))
  mkD (dst ++ `ved_mod) dm.type dm.value
  let dv ← match topMod, noKids with
    | none, false => pure dd.value
    | _, _ => do
        let d : Sparkle.IR.AST.Design ← vedu1hEval (a := Sparkle.IR.AST.Design) (mkConst ``Sparkle.IR.AST.Design) dd.value
        let d := match topMod with | some t => { d with topModule := t } | none => d
        let d := if noKids then { d with modules := [] } else d
        pure (toExpr d)
  mkD (dst ++ `ved_design) dd.type dv
  mkD (dst ++ `ved_contract) dc.type
    (mkAppN dc.value.getAppFn (dc.value.getAppArgs.pop.push (mkConst (dst ++ `ved_mod))))
  let expected := mkAppN (mkConst ``Tools.VedU1Hier.U1HStmt)
    #[mkConst (dst ++ `ved_contract), mkConst (dst ++ `ved_mod), mkConst (dst ++ `ved_design), mkConst dst]
  if sorryProof then
    addDecl (.thmDecl { name := dst ++ `ved_u1, levelParams := [], type := expected,
                        value := mkApp2 (mkConst ``sorryAx [Level.zero]) expected (mkConst ``Bool.false) })
  else
    addDecl (.thmDecl { name := dst ++ `ved_u1, levelParams := [], type := dt.type, value := mkConst dt.name })
  for k in kids do
    let some (.thmInfo kt) := env.find? (src ++ `ved_child ++ k ++ `ved_u1) | throwError "no leaf theorem of {k}"
    addDecl (.thmDecl { name := dst ++ `ved_child ++ k ++ `ved_u1, levelParams := [], type := kt.type,
                        value := mkConst kt.name })

elab "#vedu1h_clone " src:ident dst:ident "top" t:str "nokids" nk:ident "kids" "[" ks:ident,* "]" "sorry" sp:ident : command => do
  let top := if t.getString == "" then none else some t.getString
  cloneHier src.getId dst.getId top (nk.getId == `true) (ks.getElems.toList.map (·.getId)) (sp.getId == `true)

/-! ## C0: the hand-made 2-child parent is accepted -/
#vedu1h_expect "C0" [
    "VED U1 HIER OK VedHCtl.par.ved_u1",
    "VED U1P THM theorem", "VED U1P TYPE exact",
    "VED U1P MVARS type=false value=false fvars=false", "VED U1P LEVELS 0",
    "VED U1P MOD closed=true type=true", "VED U1P DESIGN closed=true type=true",
    "VED U1P CONTRACT bound-to-mod", "VED U1P PORTS ok", "VED U1P OUTS 1",
    "VED U1P HIERTOP ok", "VED U1P HIERMODS n=2 nonempty=true top-not-child=true",
    "VED U1P HIERINST ok n=2 missing=[]",
    "VED U1P HIERCHILD VedHCtl.hcA thm=theorem", "VED U1P HIERCHILD VedHCtl.hcB thm=theorem",
    "all-theorems=true"]
  ["sorryAx", "differs", "absent"]
  #vedu1h_both VedHCtl.par
#vedu1h_expect "C0-probe" ["VED U1P THM theorem", "VED U1P TYPE exact", "all-theorems=true"] ["sorryAx", "differs"]
  #vedu1h_probe VedHCtl.par
-- the axioms of the accepted theorem are std3 (no sorryAx / reduceBool / trustCompiler)
#vedu1h_expect "C0-axioms" ["VED U1P AXIOMS"] ["sorryAx", "ofReduceBool", "trustCompiler"]
  #vedu1h_probe VedHCtl.par

/-! C1: another declaration's theorem (`par`'s own `ved_u1`, renamed carrier `par2`) -/
#vedu1h_clone VedHCtl.par VedHCtl.par2 top "" nokids false kids [VedHCtl.hcA, VedHCtl.hcB] sorry false
#vedu1h_expect "C1" ["VED U1P THM theorem", "VED U1P TYPE differs"] ["VED U1P TYPE exact"]
  #vedu1h_probe VedHCtl.par2

/-! C2: a design whose topModule differs -/
#vedu1h_clone VedHCtl.par VedHCtl.par3 top "Elsewhere" nokids false kids [VedHCtl.hcA, VedHCtl.hcB] sorry true
#vedu1h_expect "C2" ["VED U1P THM theorem", "VED U1P TYPE exact", "VED U1P HIERTOP differs design=Elsewhere mod=VedHCtl.par"]
  ["VED U1P HIERTOP ok"]
  #vedu1h_probe VedHCtl.par3

/-! C3: a missing child theorem (hcB's leaf theorem is not there) -/
#vedu1h_clone VedHCtl.par VedHCtl.par4 top "" nokids false kids [VedHCtl.hcA] sorry true
#vedu1h_expect "C3" ["VED U1P TYPE exact", "VED U1P HIERTOP ok", "VED U1P HIERCHILD VedHCtl.hcA thm=theorem",
    "VED U1P HIERCHILD VedHCtl.hcB thm=absent", "all-theorems=false"]
  ["all-theorems=true"]
  #vedu1h_probe VedHCtl.par4

/-! C4: a design with no child module -/
#vedu1h_clone VedHCtl.par VedHCtl.par5 top "" nokids true kids [] sorry true
#vedu1h_expect "C4" ["VED U1P TYPE exact", "VED U1P HIERMODS n=0 nonempty=false"] ["nonempty=true"]
  #vedu1h_probe VedHCtl.par5

/-! C5: a private parent -/
#vedu1h_expect "C5" ["VED U1P THM theorem", "VED U1P TYPE exact", "VED U1P HIERTOP ok",
    "VED U1P HIERINST ok n=2 missing=[]", "all-theorems=true"]
  ["differs", "absent", "sorryAx"]
  #vedu1h_both VedHCtl.ppar
