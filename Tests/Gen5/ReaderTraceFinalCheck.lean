import Tools.ShippingGen5ReaderTraceFinal
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod: `kjob lake build Tests.Gen5.ReaderTraceFinalCheck` exit 0 on the tree of 36825acade0973d83a4e7e544f78a81ad453edcf (TYPE 1 / MUTANT 3 signature-defeq rejections / BINDERS 21 / CLOSURE 13096 / AXIOMS standard 3; this line comment-only). Clean build is the coder's.

/-! # RT final theorem checks (`scripts/gen5/RT_FINAL_FREEZE.md` §5): `readerTrace_final`

The Expected statements are written here from the freeze §1 table and §2 (own spelling, binder by binder), not copied from the implementation.
TYPE: `readerTrace_final` against `ExpFinal` by `checkExpected` (binder names, binder infos, types; `isDefEq` fallback is logged).
MUTANT: three well-typed single changes (a hypothesis dropped, a conjunct dropped, `nDeclOfCi E` replaced by `0`) are rejected by
signature / defeq. These are NOT semantic counterexamples.
BINDERS: the Prop binders are matched by fully qualified `Lean.Name` (ordered, and as sets both directions); `PassPh` / `ZeroLitAgrees0` do not occur;
a same-tail decoy in another namespace is rejected (negative control).
CLOSURE: no `sorryAx` / `Lean.ofReduceBool` / `Lean.trustCompiler` is reachable; negative controls are built in memory.
AXIOMS: `propext, Classical.choice, Quot.sound` only.
Nothing here shows that any hypothesis holds. -/

namespace Tests.Gen5.ReaderTraceFinalCheck
open Lean Meta Elab
open Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel
open Tools.ShippingGen5GDCover1 Tools.ShippingMachineAuto Tools.ShippingGen5Sem Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6

section Expected

def ExpFinal : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge)
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    (∀ n : Nat, TraceGood (structEnv env) (nDeclOfCi E) (readF (structEnv env) n)) ∧
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧
      FReachC (nDeclOfCi E) ({} : MachRead) st0 ∧ FReachC (nDeclOfCi E) st0 st1 ∧ FReachC (nDeclOfCi E) st1 st ∧
      TrInv (structEnv env) (nDeclOfCi E) st ∧
      ShapeAgree d st ∧ FullInv (kDOf d) st ∧ LetsNoLoose st

-- mutants (single changes; rejected by signature / defeq, NOT semantic counterexamples)
def MutDropHyp : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge)
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    (∀ n : Nat, TraceGood (structEnv env) (nDeclOfCi E) (readF (structEnv env) n)) ∧
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧
      FReachC (nDeclOfCi E) ({} : MachRead) st0 ∧ FReachC (nDeclOfCi E) st0 st1 ∧ FReachC (nDeclOfCi E) st1 st ∧
      TrInv (structEnv env) (nDeclOfCi E) st ∧
      ShapeAgree d st ∧ FullInv (kDOf d) st ∧ LetsNoLoose st
def MutDropConjunct : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge)
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    (∀ n : Nat, TraceGood (structEnv env) (nDeclOfCi E) (readF (structEnv env) n)) ∧
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧
      FReachC (nDeclOfCi E) ({} : MachRead) st0 ∧ FReachC (nDeclOfCi E) st0 st1 ∧ FReachC (nDeclOfCi E) st1 st ∧
      TrInv (structEnv env) (nDeclOfCi E) st ∧
      ShapeAgree d st ∧ FullInv (kDOf d) st
def MutNDecl : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge)
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    (∀ n : Nat, TraceGood (structEnv env) 0 (readF (structEnv env) n)) ∧
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧
      FReachC (nDeclOfCi E) ({} : MachRead) st0 ∧ FReachC (nDeclOfCi E) st0 st1 ∧ FReachC (nDeclOfCi E) st1 st ∧
      TrInv (structEnv env) (nDeclOfCi E) st ∧
      ShapeAgree d st ∧ FullInv (kDOf d) st ∧ LetsNoLoose st

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``Tools.ShippingGen5ReaderTraceFinal.readerTrace_final ``ExpFinal
  logInfo m!"GEN5 FINALCHECK TYPE 1 declaration compared by checkExpected (any isDefEq acceptance is logged above as GEN3 DEFEQ)"
  checkMutant ``Tools.ShippingGen5ReaderTraceFinal.readerTrace_final ``MutDropHyp
  checkMutant ``Tools.ShippingGen5ReaderTraceFinal.readerTrace_final ``MutDropConjunct
  checkMutant ``Tools.ShippingGen5ReaderTraceFinal.readerTrace_final ``MutNDecl
  logInfo m!"GEN5 FINALCHECK MUTANT 3 statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

/-! ## Binder set: full `Lean.Name` matching -/

/-- Head constants of the Prop binders of `readerTrace_final`, in binder order (16 hypotheses of freeze §1, then `CiDirect`, `Or`, `Eq`, `Eq`, `Eq`). -/
def allowedBinders : List Name :=
  [``Tools.Assume.ExprEqv.EqvAtom, ``Tools.ShippingLetsReaderInv.LiftAgrees, ``Tools.ShippingLetsReaderInv.Inst1Agrees,
   ``Tools.Assume.AbbrevExtern.ReplaceAgrees, ``Tools.Assume.AbbrevExtern.HeadBetaAgreesL,
   ``Tools.PassPh.BetaNonTargetAgrees, ``Tools.Assume.ExprEqvGL.ExprEqvLaws,
   ``Tools.ShippingLetsReaderInv.EnvTypesFVarFree,
   ``Tools.Assume.EnvSigTy.SigTyClosed, ``Tools.Assume.EnvInstS.InstSFieldsDet,
   ``Tools.Assume.EnvDeclValue.DeclValuePh, ``Tools.Assume.PackTupleBridge.PackTupleInputsBridge,
   ``Tools.Assume.NormNodePh.RawNodePh, ``Tools.Assume.NormNodePh.NormNodePh,
   ``Tools.PassPh.RecRulePhU, ``Tools.ShippingGen5ReaderTraceU2.FuelBridge,
   ``Tools.ShippingGen5ReaderTrace.CiDirect, ``Or, ``Eq, ``Eq, ``Eq]

def propBinderHeads (thm : Name) : MetaM (List Name) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut out : List Name := []
    for x in xs do
      let t ← inferType (← inferType x)
      if t.isProp then
        let ty ← instantiateMVars (← inferType x)
        if let some c := ty.getAppFn.constName? then out := out ++ [c]
        else throwError "GEN5 FINALCHECK BINDERS FAILED: Prop binder with non-constant head {ty}"
    pure out

def bindersMatch (heads allowed : List Name) : Bool :=
  heads == allowed && allowed.all heads.contains && heads.all allowed.contains

namespace Decoy
def RawNodePh (_ : StructEnv) : Prop := True
def FuelBridge : Prop := True
theorem useDecoy (s : StructEnv) (_ : RawNodePh s) (_ : FuelBridge) : True := trivial
end Decoy

run_cmd Lean.Elab.Command.liftTermElabM do
  let heads ← propBinderHeads ``Tools.ShippingGen5ReaderTraceFinal.readerTrace_final
  unless bindersMatch heads allowedBinders do
    throwError "GEN5 FINALCHECK BINDERS FAILED: heads {heads}\nexpected {allowedBinders}"
  for n in [`Tools.PassPh.PassPh, `Tools.Assume.N3Extern.ZeroLitAgrees0, `Tools.Assume.AbbrevExtern.HeadBetaAgrees0] do
    if heads.contains n then throwError "GEN5 FINALCHECK BINDERS FAILED: {n} is a binder"
  -- negative control: decoy binders (same tail, other namespace)
  let dh ← propBinderHeads ``Decoy.useDecoy
  unless dh == [``Decoy.RawNodePh, ``Decoy.FuelBridge] do throwError "GEN5 FINALCHECK BINDERS CONTROL FAILED: decoy heads {dh}"
  let swapped := allowedBinders.map fun n =>
    if n == ``Tools.Assume.NormNodePh.RawNodePh then ``Decoy.RawNodePh
    else if n == ``Tools.ShippingGen5ReaderTraceU2.FuelBridge then ``Decoy.FuelBridge else n
  if bindersMatch swapped allowedBinders then throwError "GEN5 FINALCHECK BINDERS CONTROL FAILED: decoy binders accepted"
  logInfo m!"GEN5 FINALCHECK BINDERS OK: {heads.length} Prop binders (16 hypotheses of freeze §1 + CiDirect + Or + 3 Eq) match by full name; PassPh / ZeroLitAgrees0 / HeadBetaAgrees0 absent; decoy rejected"

/-! ## Closure audit -/

def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def closureOf (env : Environment) (root : Name) : StateT (NameSet × NameSet) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.insert root)
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()
    match ci with
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

def closureHits (env : Environment) (roots : List Name) : MetaM (NameSet × NameSet × List Name) := do
  let (_, (seen, unk)) ← (roots.forM (closureOf env)).run ({}, {})
  pure (seen, unk, forbiddenConsts.filter seen.contains)

def closureRoots : List Name := [``Tools.ShippingGen5ReaderTraceFinal.readerTrace_final]

-- Negative controls (built in memory, no `sorry` token in this file)
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) tru (mkConst ``Bool.false)
    let ok := mkConst ``True.intro
    addDecl (.thmDecl { name := `FinalCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `FinalCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.thmDecl { name := `FinalCheck.clean1, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    for n in [`FinalCheck.direct, `FinalCheck.viaHelper] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 FINALCHECK CLOSURE CONTROL FAILED: {n} not detected"
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 FINALCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    let (_, _, hits) ← closureHits env [`FinalCheck.clean1]
    unless hits.isEmpty do throwError "GEN5 FINALCHECK CLOSURE CONTROL FAILED: clean control flagged {hits}"
    logInfo m!"GEN5 FINALCHECK CLOSURE CONTROLS OK: 2 negative controls detected, 3 forbidden roots hit themselves, 1 clean control clean"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless hits.isEmpty do throwError "GEN5 FINALCHECK CLOSURE FAILED: forbidden constants {hits}"
  unless unk.isEmpty do throwError "GEN5 FINALCHECK CLOSURE FAILED: unknown constants {unk.toList}"
  -- HeadBetaAgrees0 is reached through definitions (as in the U2 Check), so only the binder check covers it; PassPh must not be reached
  if seen.contains `Tools.PassPh.PassPh then throwError "GEN5 FINALCHECK CLOSURE FAILED: PassPh reached"
  logInfo m!"GEN5 FINALCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} root; no forbidden constant"

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in closureRoots do checkAxioms n
  logInfo m!"GEN5 FINALCHECK AXIOMS OK: {closureRoots.length} root, standard axioms only (propext, Classical.choice, Quot.sound)"

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo m!"GEN5 FINALCHECK COUNTS: TYPE 1 / MUTANT 3 / BINDERS {allowedBinders.length} (16 hypotheses) / CLOSURE 1 root / AXIOMS 1 / decoy 1"

end Tests.Gen5.ReaderTraceFinalCheck
