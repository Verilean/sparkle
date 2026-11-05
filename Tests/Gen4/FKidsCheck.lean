import Tools.ShippingGen4FKids
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- FKIDS CHECK: audit of the three frozen theorems `fKids_memoHit`, `fKids_statePF`, `fKids` (FKIDS_FREEZE.md §2), each verified separately.

/-! # Audit of `fKids_memoHit`

1. TYPE: the theorem's type equals `Expected.memoHit` (the frozen text, written separately), STRUCTURALLY (`Expr.eqv`) and by `isDefEq`.
2. MUTANT: signature rejections only (NOT semantic counterexamples), by `Expr.eqv` AND `isDefEq`; and a negative control for the structural comparison.
3. AXIOMS: only propext / Classical.choice / Quot.sound.
4. CLOSURE: no `Laws` / `T1Hyp` / `T1HypND` in the closure (positive controls: the detector flags `T1Hyp`, `T1HypND`).
5. HYPOTHESES: in the theorem TYPE the only named assumptions are `MemoFamily` and `MsgMvK`. -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Sparkle.Compiler.Elab
open Tools.ShippingGen4FKids Tools.ShippingGen4FKidsDepth

namespace Tests.Gen4.FKidsCheck

namespace Expected

def memoHit : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (D : Nat), D ≠ 0 → ∀ (c : Name),
    Triple mctx mref cctx cref (WorldPF O D) (synthesizeChild c)
      (fun r w => WorldPF O D w ∧ PairPF r) (fun e w => WorldPF O D w ∧ OkExc e)

def statePF : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ true true)
      mctx mref cctx cref w (M0, D0) w' →
    Tools.ShippingGen4FKids.DesignPF D0

def fKids : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = []

end Expected

namespace Mutant

/-- M1: no `MsgMvK`. -/
def M1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (D : Nat), D ≠ 0 → ∀ (c : Name),
    Triple mctx mref cctx cref (WorldPF O D) (synthesizeChild c)
      (fun r w => WorldPF O D w ∧ PairPF r) (fun e w => WorldPF O D w ∧ OkExc e)

/-- M2: depth 0 allowed. -/
def M2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (D : Nat) (c : Name),
    Triple mctx mref cctx cref (WorldPF O D) (synthesizeChild c)
      (fun r w => WorldPF O D w ∧ PairPF r) (fun e w => WorldPF O D w ∧ OkExc e)

/-- M3: the result is not claimed `PairPF`. -/
def M3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (D : Nat), D ≠ 0 → ∀ (c : Name),
    Triple mctx mref cctx cref (WorldPF O D) (synthesizeChild c)
      (fun _ w => WorldPF O D w) (fun e w => WorldPF O D w ∧ OkExc e)

/-- M4: the world is not given back as `WorldPF` (K only). -/
def M4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (D : Nat), D ≠ 0 → ∀ (c : Name),
    Triple mctx mref cctx cref (WorldPF O D) (synthesizeChild c)
      (fun r w => Tools.ShippingGen4KWalkDepth.KWD O Tools.ShippingGen4KWalk.MemoKeysInChild D w ∧ PairPF r) (fun e w => WorldPF O D w ∧ OkExc e)

/-- M5: the failure side without `OkExc`. -/
def M5 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (D : Nat), D ≠ 0 → ∀ (c : Name),
    Triple mctx mref cctx cref (WorldPF O D) (synthesizeChild c)
      (fun r w => WorldPF O D w ∧ PairPF r) (fun _ w => WorldPF O D w)

/-- S1: no `MsgMvK`. -/
def S1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ true true)
      mctx mref cctx cref w (M0, D0) w' →
    Tools.ShippingGen4FKids.DesignPF D0

/-- S2: the top module is claimed parameter free too. -/
def S2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ true true)
      mctx mref cctx cref w (M0, D0) w' →
    Tools.ShippingGen4FKids.DesignPF D0 ∧ Tools.ShippingGen4FKids.ParamFree M0

/-- S3: no start-world hypothesis. -/
def S3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ true true)
      mctx mref cctx cref w (M0, D0) w' →
    Tools.ShippingGen4FKids.DesignPF D0

/-- S4: the non-symbolic entry. -/
def S4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ false true)
      mctx mref cctx cref w (M0, D0) w' →
    Tools.ShippingGen4FKids.DesignPF D0

/-- F1: no `MsgMvK`. -/
def F1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = []

/-- F2: the guard is dropped (the top module is claimed parameter free too). -/
def F2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.parameters = []

/-- F3: no start-world hypothesis. -/
def F3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = []

/-- F4: the guard is `=` instead of `≠`. -/
def F4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.name = M'.name → x.parameters = []

end Mutant

private partial def closure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | none => closure env rest seen
    | some ci =>
      let body : List Name := match ci with
        | .thmInfo v => v.value.getUsedConstants.toList
        | .defnInfo v => v.value.getUsedConstants.toList
        | _ => []
      closure env (ci.type.getUsedConstants.toList ++ body ++ rest) seen

private def forbidden : List Name :=
  [`Tools.ShippingGen2.Laws, `Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]

private def closureBad (n : Name) : CoreM (List Name) := do
  let seen := closure (← getEnv) [n] {}
  return seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m

private def checkOne (t : Name) (expName : Name) (muts : List Name) : TermElabM String := do
  let pre := `Tests.Gen4.FKidsCheck
  let ti ← getConstInfo t
  let expC ← getConstInfo (pre ++ `Expected ++ expName)
  let some expV := expC.value? | throwError "Expected.{expName} has no value"
  let structural := Expr.eqv ti.type expV
  unless structural do throwError "TYPE mismatch (structural) for {t}"
  unless ← isDefEq ti.type (mkConst (pre ++ `Expected ++ expName)) do throwError "TYPE mismatch (isDefEq) for {t}"
  let mut rej : Nat := 0
  let mut structRej : Nat := 0
  for m in muts do
    let mc ← getConstInfo (pre ++ `Mutant ++ m)
    if ← isDefEq ti.type (mkConst (pre ++ `Mutant ++ m)) then throwError "mutant {m} NOT rejected"
    rej := rej + 1
    let some mv := mc.value? | throwError "{m} has no value"
    if Expr.eqv ti.type mv then throwError "mutant {m} NOT rejected structurally"
    structRej := structRej + 1
  let axs ← collectAxioms t
  let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
  unless bad.isEmpty do throwError "{t}: axioms {bad}"
  let badC ← closureBad t
  unless badC.isEmpty do throwError "{t}: forbidden constants {badC}"
  let hypNames : List Name :=
    [`Tools.ShippingGen4KWalkEntry.LogMvK, `Tools.ShippingGen4FKidsEntry.LogMvKS, `Tools.ShippingGen4FKidsFallback.LegacyImplKS,
     `Tools.ShippingGen4FKidsHelpers.PpMvKS, `Tools.ShippingGen4KWalkDiag.MsgMvK, `Tools.ShippingGen4FKidsFallback.LegacyCachedKS,
     `Tools.ShippingGen4FKidsFallback.ChildEntryKS, `Tools.Assume.MemoFamily.MemoFamily,
     `Tools.ShippingLegacySemTelescopeN.LamTelescopeN]
  let inType := hypNames.filter ti.type.getUsedConstants.contains
  unless inType == [`Tools.ShippingGen4KWalkDiag.MsgMvK, `Tools.Assume.MemoFamily.MemoFamily] ||
      inType == [`Tools.Assume.MemoFamily.MemoFamily, `Tools.ShippingGen4KWalkDiag.MsgMvK] do
    throwError "hypotheses in type {inType}, expected exactly MsgMvK and MemoFamily"
  return s!"{t}: TYPE isDefEq ok / structural(Expr.eqv) {structural} / MUTANT {rej}/{muts.length} isDefEq-rejected, {structRej}/{muts.length} structurally rejected (signature rejections, not semantic counterexamples) / AXIOMS standard-only / CLOSURE clean / HYPOTHESES in type {inType}"

elab "#fkids_check" : command => liftTermElabM do
  let r1 ← checkOne `Tools.ShippingGen4FKids.fKids_memoHit `memoHit [`M1, `M2, `M3, `M4, `M5]
  let r2 ← checkOne `Tools.ShippingGen4FKids.fKids_statePF `statePF [`S1, `S2, `S3, `S4]
  let r3 ← checkOne `Tools.ShippingGen4FKids.fKids `fKids [`F1, `F2, `F3, `F4]
  for c in [`Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND] do
    let b ← closureBad c
    if b.isEmpty then throwError "closure detector MISSED {c}"
  logInfo m!"FKIDS CHECK (3 theorems, verified separately; closure detector positive controls ok):\n{r1}\n{r2}\n{r3}"

#fkids_check

end Tests.Gen4.FKidsCheck
