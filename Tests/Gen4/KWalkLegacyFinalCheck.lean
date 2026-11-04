import Tests.Gen4.KWalkLegacyCheck
import Tools.ShippingGen4KWalkLegacyFinal
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- BUILT (rt180): kjob lake build Tests.Gen4.KWalkLegacyFinalCheck exit 0 (787 jobs): TYPE 2/2 / MUTANT 5/5 / AXIOMS 2/2 / CLOSURE 2/2 (+2 controls); type hypothesis of topEntry_K_of_family3 = MsgMvK only; clean build is the coder's. KWALKLEGACYFINAL CHECK: audit of Tools/ShippingGen4KWalkLegacyFinal.lean (`LegacyImplK` discharged; the only hypothesis in the type of the top entry is `MsgMvK`).

/-! # Audit of `legacyImplK_of_entry` and `topEntry_K_of_family3`

1. TYPE: each audited theorem's type is `isDefEq` to `Expected.*` below, written separately.
2. MUTANT: signature/defeq REJECTIONS only. NOT semantic counterexamples.
3. AXIOMS: only propext / Classical.choice / Quot.sound.
4. CLOSURE: no `Laws` / `T1Hyp` / `T1HypND` constant in the transitive closure (positive controls: the detector flags `T1Hyp`, `T1HypND`).
   Hypothesis-like definitions are reported twice: in the THEOREM TYPE (asked) and anywhere in its closure (a definition that only appears in the closure was derived from the family). -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Sparkle.Compiler.Elab
open Tests.Gen4.KWalkDepthCheck.Expected

namespace Tests.Gen4.KWalkLegacyFinalCheck

namespace Expected

/-- `LegacyImplK` spelled out. -/
def legacyImpl {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ rec : TranslateFn,
    (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named)) →
    ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ e hint top named, KeepsCP mctx mref cctx cref I
        (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)

def implOfEntry : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {I : Void IO.RealWorld → Prop}, Tools.ShippingGen4KWalkPrims.StableK O.quiet I →
    (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c)) →
    legacyImpl O I

def topEntryFinal : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {mctx : Meta.Context} {cctx : Core.Context} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → Tools.ShippingGen4KWalkDiag.MsgMvK O → AdmCtx O.quiet mctx cctx →
    ∀ declName : Name,
    tripleD (KD0of O) (KDXof O declName 0) (fun e w => KQof O w ∧ OkExc e) mctx mref cctx cref
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)

end Expected

namespace Mutant

/-- F1: the old shape (`LegacyImplK` still asked, `MsgMvK` not). -/
def F1 : Prop := Tests.Gen4.KWalkLegacyCheck.Expected.topEntryFam

/-- F2: no `MsgMvK` asked. -/
def F2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {mctx : Meta.Context} {cctx : Core.Context} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ declName : Name,
    tripleD (KD0of O) (KDXof O declName 0) (fun e w => KQof O w ∧ OkExc e) mctx mref cctx cref
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)

/-- F3: the success side without `OkExc`. -/
def F3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {mctx : Meta.Context} {cctx : Core.Context} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → Tools.ShippingGen4KWalkDiag.MsgMvK O → AdmCtx O.quiet mctx cctx →
    ∀ declName : Name,
    tripleD (KD0of O) (KDXof O declName 0) (fun _ w => KQof O w) mctx mref cctx cref
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)

/-- F4: the failure side claims the full `K` (depth 0). -/
def F4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {mctx : Meta.Context} {cctx : Core.Context} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → Tools.ShippingGen4KWalkDiag.MsgMvK O → AdmCtx O.quiet mctx cctx →
    ∀ declName : Name,
    tripleD (KD0of O) (KDof O 0) (fun e w => KQof O w ∧ OkExc e) mctx mref cctx cref
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)

/-- F5: `implOfEntry` without the child entry. -/
def F5 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {I : Void IO.RealWorld → Prop}, Tools.ShippingGen4KWalkPrims.StableK O.quiet I →
    Expected.legacyImpl O I

end Mutant

/-! ## The checker -/

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

elab "#kwalklegacyfinal_check" : command => liftTermElabM do
  let fi := `Tools.ShippingGen4KWalkLegacyFinal
  let pre := `Tests.Gen4.KWalkLegacyFinalCheck
  let typeCases : List (Name × Name) :=
    [(fi ++ `legacyImplK_of_entry, pre ++ `Expected ++ `implOfEntry),
     (fi ++ `topEntry_K_of_family3, pre ++ `Expected ++ `topEntryFinal)]
  let mutCases : List (String × Name × Name) :=
    [("F1", fi ++ `topEntry_K_of_family3, `F1), ("F2", fi ++ `topEntry_K_of_family3, `F2),
     ("F3", fi ++ `topEntry_K_of_family3, `F3), ("F4", fi ++ `topEntry_K_of_family3, `F4),
     ("F5", fi ++ `legacyImplK_of_entry, `F5)]
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
  let audited : List Name := typeCases.map (·.1)
  let mut axOk : Nat := 0
  let mut clOk : Nat := 0
  for n in audited do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    unless bad.isEmpty do throwError "{n}: axioms {bad}"
    axOk := axOk + 1
    let bad ← closureBad n
    unless bad.isEmpty do throwError "{n}: forbidden constants {bad}"
    clOk := clOk + 1
  for c in [`Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND] do
    let bad ← closureBad c
    if bad.isEmpty then throwError "closure detector MISSED {c}"
  let hypNames : List Name :=
    [`Tools.ShippingGen4KWalkEntry.LogMvK, `Tools.ShippingGen4KWalkFallback.LegacyImplK,
     `Tools.ShippingGen4KWalkDepthInduct.LegacyArmD, `Tools.ShippingGen4KWalkHelpers.PpMvK,
     `Tools.ShippingGen4KWalkDiag.MsgMvK, `Tools.ShippingGen4KWalkFallback.LegacyCachedK,
     `Tools.ShippingGen4KWalkFallback.ChildEntryK]
  let mut report : List String := []
  for t in [fi ++ `topEntry_K_of_family3, fi ++ `legacyImplK_of_entry] do
    let seen := closure (← getEnv) [t] {}
    let ty := (← getConstInfo t).type.getUsedConstants
    let inType := hypNames.filter fun h => ty.contains h
    let inClosure := hypNames.filter seen.contains
    report := report ++ [s!"{t}: in type {inType} / in closure {inClosure}"]
    if t == fi ++ `topEntry_K_of_family3 then
      unless inType == [`Tools.ShippingGen4KWalkDiag.MsgMvK] do
        throwError "topEntry_K_of_family3: hypotheses in type {inType}, expected exactly [MsgMvK]"
      if seen.contains `Tools.ShippingGen4KWalkDepthInduct.LegacyArmD then throwError "LegacyArmD is in the closure"
  logInfo m!"KWALKLEGACYFINAL CHECK: TYPE {ok}/{typeCases.length} / MUTANT {rej}/{mutCases.length} (signature/defeq rejections, not semantic counterexamples) / AXIOMS {axOk}/{audited.length} standard-only / CLOSURE {clOk}/{audited.length} clean (+2 positive controls) / HYPOTHESES {report}"

#kwalklegacyfinal_check

end Tests.Gen4.KWalkLegacyFinalCheck
