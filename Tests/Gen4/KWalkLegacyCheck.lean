import Tests.Gen4.KWalkDepthCheck
import Tools.ShippingGen4KWalkLegacyInduct
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- NOT BUILT (rt173 wip). KWALKLEGACY CHECK: audit of Tools/ShippingGen4KWalkLegacyArm.lean and Tools/ShippingGen4KWalkLegacyInduct.lean.

/-! # Audit of the legacy arm (`hleg`) and of the induction / outermost entry without it

1. TYPE: each audited theorem's type is `isDefEq` to `Expected.*` below, written separately (reusing the spelled-out `KDof` / `KDXof` / `tripleD` of the depth Check).
2. MUTANT: signature/defeq REJECTIONS only. NOT semantic counterexamples.
3. AXIOMS: only propext / Classical.choice / Quot.sound.
4. CLOSURE: no `Laws` / `T1Hyp` / `T1HypND` constant in the transitive closure (positive controls: the detector flags `T1Hyp`, `T1HypND`).
   Hypothesis-like definitions (`LogMvK`, `LegacyImplK`, `LegacyArmD`, `PpMvK`, `MsgMvK`) are reported twice: those appearing in the THEOREM TYPE (asked, not provided)
   and those appearing anywhere in its closure (proof terms included: a definition that only appears in the closure was derived from the family, not asked). -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Sparkle.Compiler.Elab
open Tests.Gen4.KWalkDepthCheck.Expected

namespace Tests.Gen4.KWalkLegacyCheck

namespace Expected

/-- The translator premise of the induction: `RecK`, spelled out. -/
def recK {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (D : Nat) (translate : TranslateFn) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCP mctx mref cctx cref (KDof O D) (translate e hint top named)

def legacyArm : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → logMv O → ∀ (D : Nat)
    (translate : TranslateFn) (b : Bool) (declName : Name) (ci : ConstantInfo)
    (isInst : Lean.Expr → Bool), recK O D translate →
    tripleD (KDof O D) (KDXof O declName D) (fun e w => KDof O D w ∧ OkExc e) mctx mref cctx cref
      (synthesizeFromConst translate (profLogIO b) declName [] false false ci isInst)

def childDepth : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → logMv O →
    (∀ D : Nat, D ≠ 0 → Tools.ShippingGen4KWalkFallback.LegacyImplK O (KDof O D)) →
    ∀ (D : Nat), D ≠ 0 → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ n : Name,
      tripleD (KDof O D) (KDof O D) (fun e w => KDof O D w ∧ OkExc e) mctx mref cctx cref (synthesizeChild n)

def topEntry : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → logMv O →
    (∀ D : Nat, D ≠ 0 → Tools.ShippingGen4KWalkFallback.LegacyImplK O (KDof O D)) → AdmCtx O.quiet mctx cctx →
    ∀ declName : Name,
    tripleD (KD0of O) (KDXof O declName 0) (fun e w => KQof O w ∧ OkExc e) mctx mref cctx cref
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)

/-- `LogMvK` is no longer asked: only the family and `LegacyImplK`. -/
def topEntryFam : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O →
    (∀ D : Nat, D ≠ 0 → Tools.ShippingGen4KWalkFallback.LegacyImplK O (KDof O D)) → AdmCtx O.quiet mctx cctx →
    ∀ declName : Name,
    tripleD (KD0of O) (KDXof O declName 0) (fun e w => KQof O w ∧ OkExc e) mctx mref cctx cref
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)

end Expected

namespace Mutant

/-- L1: the legacy arm claims the full `K` (not `K_n`) on success. -/
def L1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → logMv O → ∀ (D : Nat)
    (translate : TranslateFn) (b : Bool) (declName : Name) (ci : ConstantInfo)
    (isInst : Lean.Expr → Bool), Expected.recK O D translate →
    tripleD (KDof O D) (KDof O D) (fun e w => KDof O D w ∧ OkExc e) mctx mref cctx cref
      (synthesizeFromConst translate (profLogIO b) declName [] false false ci isInst)

/-- L2: the legacy arm's failure side without `OkExc`. -/
def L2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → logMv O → ∀ (D : Nat)
    (translate : TranslateFn) (b : Bool) (declName : Name) (ci : ConstantInfo)
    (isInst : Lean.Expr → Bool), Expected.recK O D translate →
    tripleD (KDof O D) (KDXof O declName D) (fun _ w => KDof O D w) mctx mref cctx cref
      (synthesizeFromConst translate (profLogIO b) declName [] false false ci isInst)

/-- L3: the legacy arm without the translator premise. -/
def L3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → logMv O → ∀ (D : Nat)
    (translate : TranslateFn) (b : Bool) (declName : Name) (ci : ConstantInfo)
    (isInst : Lean.Expr → Bool),
    tripleD (KDof O D) (KDXof O declName D) (fun e w => KDof O D w ∧ OkExc e) mctx mref cctx cref
      (synthesizeFromConst translate (profLogIO b) declName [] false false ci isInst)

/-- L4: the legacy arm with the certified front end ON (a different run). -/
def L4 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → logMv O → ∀ (D : Nat)
    (translate : TranslateFn) (b : Bool) (declName : Name) (ci : ConstantInfo)
    (isInst : Lean.Expr → Bool), Expected.recK O D translate →
    tripleD (KDof O D) (KDXof O declName D) (fun e w => KDof O D w ∧ OkExc e) mctx mref cctx cref
      (synthesizeFromConst translate (profLogIO b) declName [] false true ci isInst)

/-- L5: the depth result still asks the legacy arm as a hypothesis (the old shape). -/
def L5 : Prop := Tests.Gen4.KWalkDepthCheck.Expected.headline

/-- L6: the family-only top entry claims the full `K` on failure. -/
def L6 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O →
    (∀ D : Nat, D ≠ 0 → Tools.ShippingGen4KWalkFallback.LegacyImplK O (KDof O D)) → AdmCtx O.quiet mctx cctx →
    ∀ declName : Name,
    tripleD (KD0of O) (KDXof O declName 0) (fun e w => KDof O 0 w ∧ OkExc e) mctx mref cctx cref
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)

end Mutant

/-! ## The checker -/

private partial def closure (env : Environment) (todo : List Name) (seen : NameSet) (opq : NameSet) :
    NameSet × NameSet :=
  match todo with
  | [] => (seen, opq)
  | n :: rest =>
    if seen.contains n then closure env rest seen opq else
    let seen := seen.insert n
    match env.find? n with
    | none => closure env rest seen opq
    | some ci =>
      let (body, opq) : List Name × NameSet := match ci with
        | .thmInfo v => (v.value.getUsedConstants.toList, opq)
        | .defnInfo v => (v.value.getUsedConstants.toList, opq)
        | .opaqueInfo _ => ([], opq.insert n)
        | _ => ([], opq)
      closure env (ci.type.getUsedConstants.toList ++ body ++ rest) seen opq

private def forbidden : List Name :=
  [`Tools.ShippingGen2.Laws, `Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]

private def closureBad (n : Name) : CoreM (List Name × Nat) := do
  let (seen, _) := closure (← getEnv) [n] {} {}
  return (seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m, seen.size)

elab "#kwalklegacy_check" : command => liftTermElabM do
  let la := `Tools.ShippingGen4KWalkLegacyArm
  let li := `Tools.ShippingGen4KWalkLegacyInduct
  let pre := `Tests.Gen4.KWalkLegacyCheck
  let typeCases : List (Name × Name) :=
    [(la ++ `legacy_windowD, pre ++ `Expected ++ `legacyArm),
     (li ++ `synthesizeChild_depthKL, pre ++ `Expected ++ `childDepth),
     (li ++ `topEntry_KL, pre ++ `Expected ++ `topEntry),
     (li ++ `topEntry_K_of_family, pre ++ `Expected ++ `topEntryFam)]
  let mutCases : List (String × Name × Name) :=
    [("L1", la ++ `legacy_windowD, `L1), ("L2", la ++ `legacy_windowD, `L2), ("L3", la ++ `legacy_windowD, `L3),
     ("L4", la ++ `legacy_windowD, `L4), ("L5", li ++ `synthesizeChild_depthKL, `L5),
     ("L6", li ++ `topEntry_K_of_family, `L6)]
  let mut ok : Nat := 0
  for (t, e) in typeCases do
    let ti ← getConstInfo t
    unless ← isDefEq ti.type (mkConst e) do throwError "TYPE mismatch for {t}"
    ok := ok + 1
  let mut rej : Nat := 0
  for (lbl, t, m) in mutCases do
    let ti ← getConstInfo t
    if ← isDefEq ti.type (mkConst (pre ++ `Mutant ++ m)) then throwError "mutant {lbl} NOT rejected for {t}"
    rej := rej + 1
  let audited : List Name := typeCases.map (·.1) ++
    [la ++ `kwdX_of_kwd, la ++ `tripleK_memoGetD, li ++ `child_stepL, li ++ `child_budgetL]
  let mut axOk : Nat := 0
  let mut clOk : Nat := 0
  for n in audited do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    unless bad.isEmpty do throwError "{n}: axioms {bad}"
    axOk := axOk + 1
    let (bad, _) ← closureBad n
    unless bad.isEmpty do throwError "{n}: forbidden constants {bad}"
    clOk := clOk + 1
  for c in [`Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND] do
    let (bad, _) ← closureBad c
    if bad.isEmpty then throwError "closure detector MISSED {c}"
  -- the hypotheses: in the TYPE (asked) and in the closure (asked or derived)
  let hypNames : List Name :=
    [`Tools.ShippingGen4KWalkEntry.LogMvK, `Tools.ShippingGen4KWalkFallback.LegacyImplK,
     `Tools.ShippingGen4KWalkDepthInduct.LegacyArmD, `Tools.ShippingGen4KWalkHelpers.PpMvK,
     `Tools.ShippingGen4KWalkDiag.MsgMvK, `Tools.ShippingGen4KWalkFallback.LegacyCachedK,
     `Tools.ShippingGen4KWalkFallback.ChildEntryK]
  let mut report : List String := []
  for t in [li ++ `topEntry_K_of_family, li ++ `topEntry_KL, li ++ `synthesizeChild_depthKL, la ++ `legacy_windowD] do
    let (seen, _) := closure (← getEnv) [t] {} {}
    let ty := (← getConstInfo t).type.getUsedConstants
    let inType := hypNames.filter fun h => ty.contains h
    let inClosure := hypNames.filter seen.contains
    report := report ++ [s!"{t}: in type {inType} / in closure {inClosure}"]
    if t == li ++ `topEntry_K_of_family then
      unless inType == [`Tools.ShippingGen4KWalkFallback.LegacyImplK] do
        throwError "topEntry_K_of_family: hypotheses in type {inType}, expected exactly [LegacyImplK]"
      if seen.contains `Tools.ShippingGen4KWalkDepthInduct.LegacyArmD then throwError "LegacyArmD is in the closure"
  logInfo m!"KWALKLEGACY CHECK: TYPE {ok}/{typeCases.length} / MUTANT {rej}/{mutCases.length} (signature/defeq rejections, not semantic counterexamples) / AXIOMS {axOk}/{audited.length} standard-only / CLOSURE {clOk}/{audited.length} clean (+2 positive controls) / HYPOTHESES {report}"

#kwalklegacy_check

end Tests.Gen4.KWalkLegacyCheck
