import Tools.ShippingGen4KWalkEntryArms
import Tools.ShippingGen2Defs
-- BUILT: kjob lake build Tests.Gen4.KWalkEntryCheck exit 0 (rt169, source as of 894ffd2f); KWALKENTRY CHECK: TYPE 4/4 / MUTANT 2/2 (signature/defeq rejections, not semantic counterexamples) / AXIOMS 12/12 standard-only / CLOSURE 12/12 clean (+2 positive controls). Clean build is the coder's. Audit of Tools/ShippingGen4KWalkEntry{,Arms}.lean (S4 of scripts/gen4/KWALK_PLAN.md).
set_option autoImplicit false
-- NOT BUILT (rt169). KWALKENTRY CHECK: audit of Tools/ShippingGen4KWalkEntry.lean and Tools/ShippingGen4KWalkEntryArms.lean (S4 of scripts/gen4/KWALK_PLAN.md).

/-! # Audit of the S4 files

1. TYPE: each audited theorem's type is `isDefEq` to `Expected.*` below, written separately (`KWalk`/`KWalkX` spelled with `readOf`;
   `Triple` unfolded to its `match`; `LogMvK` spelled with `readOf`).
2. MUTANT: signature/defeq REJECTIONS only. NOT semantic counterexamples.
3. AXIOMS: only propext / Classical.choice / Quot.sound.
4. CLOSURE: no `Laws` / `T1Hyp` / `T1HypND` constant in the transitive closure (positive controls: the detector flags `T1Hyp`, `T1HypND`).
   `MemoFamily` is allowed (it is the hypothesis `M`); `LogMvK` is the DIAG-PENDING hypothesis (a def, not a family statement). -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Sparkle.Compiler.Elab

namespace Tests.Gen4.KWalkEntryCheck

namespace Expected

def KWalkOf {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (w : Void IO.RealWorld) : Prop :=
  O.quiet w ∧ readOf sparkleChildSynth w = some synthesizeChild ∧
    ∀ k, (readOf sparkleSubModuleCache w).contains k = true → (readOf sparkleChildCache w).contains k = true

def KWalkXOf {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (n : Name) (w : Void IO.RealWorld) : Prop :=
  O.quiet w ∧ readOf sparkleChildSynth w = some synthesizeChild ∧
    ∀ k, (readOf sparkleSubModuleCache w).contains k = true →
      (readOf sparkleChildCache w).contains k = true ∨ (n == k) = true

def logMv {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ b msg w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) =
      readOf sparkleSubModuleCache w

def windowTriple {α : Type} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (O : RefLawsAOps MkRefd mref cref) (n : Name) (p : MetaM α) : Prop :=
  ∀ w, KWalkOf O w → match p mctx mref cctx cref w with
    | .ok _ w' => KWalkXOf O n w'
    | .error e w' => KWalkOf O w' ∧ OkExc e

def memoInsert : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → ∀ (n : Name) (r : Res),
    windowTriple mctx mref cctx cref O n (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit)

def profLog : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, Tools.ShippingGen4KWalkPrims.StableK O.quiet I → logMv O →
    ∀ (b : Bool) (msg : String), Keeps mctx mref cctx cref I (liftM (profLogIO b msg) : MetaM Unit)

def certifiedArm : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → logMv O →
    ∀ (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
      (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)} {body : Lean.Expr},
    certifiedShape? false [] constInfo = some (bs, body) →
    (∀ e hint top named, KeepsC mctx mref cctx cref (KWalkOf O) (translate e hint top named)) →
    windowTriple mctx mref cctx cref O declName
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)

def frontends : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → logMv O →
    ∀ (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
      (isInst : Lean.Expr → Bool),
    (∀ e hint top named, KeepsC mctx mref cctx cref (KWalkOf O) (translate e hint top named)) →
    (∀ c, Keeps mctx mref cctx cref (KWalkOf O) (synthesizeChild c)) →
    (certifiedShape? false [] constInfo = none → mixedCertifiedShape? false [] constInfo isInst = none →
      windowTriple mctx mref cctx cref O declName
        (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)) →
    windowTriple mctx mref cctx cref O declName
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)

end Expected

namespace Mutant

/-- M1: the memo write returning in K (the window not opened). -/
def M1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → ∀ (n : Name) (r : Res),
    ∀ w, Expected.KWalkOf O w → match (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit) mctx mref cctx cref w with
      | .ok _ w' => Expected.KWalkOf O w'
      | .error e w' => Expected.KWalkOf O w' ∧ OkExc e

/-- M2: the front-ends theorem without the logger hypothesis. -/
def M2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
      (isInst : Lean.Expr → Bool),
    (∀ e hint top named, KeepsC mctx mref cctx cref (Expected.KWalkOf O) (translate e hint top named)) →
    (∀ c, Keeps mctx mref cctx cref (Expected.KWalkOf O) (synthesizeChild c)) →
    (certifiedShape? false [] constInfo = none → mixedCertifiedShape? false [] constInfo isInst = none →
      Expected.windowTriple mctx mref cctx cref O declName
        (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)) →
    Expected.windowTriple mctx mref cctx cref O declName
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst)

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

elab "#kwalkentry_check" : command => liftTermElabM do
  let en := `Tools.ShippingGen4KWalkEntry
  let ar := `Tools.ShippingGen4KWalkEntryArms
  let pre := `Tests.Gen4.KWalkEntryCheck
  let typeCases : List (Name × Name) :=
    [(en ++ `triple_memoInsert, pre ++ `Expected ++ `memoInsert),
     (en ++ `keepsK_profLog, pre ++ `Expected ++ `profLog),
     (ar ++ `fromConst_certified_windowK, pre ++ `Expected ++ `certifiedArm),
     (ar ++ `fromConst_frontends_windowK, pre ++ `Expected ++ `frontends)]
  let mutCases : List (String × Name × Name) :=
    [("M1", en ++ `triple_memoInsert, `M1), ("M2", ar ++ `fromConst_frontends_windowK, `M2)]
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
    [en ++ `emitLeavesK, en ++ `certified_keepsK, en ++ `mixed_keepsK, en ++ `machineCert_keepsK,
     en ++ `closeInstsM_keepsK, en ++ `closeInstsGM_keepsK,
     ar ++ `fromConst_mixed_windowK, ar ++ `fromConst_machine_windowK]
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
  -- LogMvK is in the closure of the arms (it is their hypothesis): count that it IS reachable
  let (seen, _) := closure (← getEnv) [ar ++ `fromConst_frontends_windowK] {} {}
  let logIn := seen.contains (en ++ `LogMvK)
  logInfo m!"KWALKENTRY CHECK: TYPE {ok}/4 / MUTANT {rej}/2 (signature/defeq rejections, not semantic counterexamples) / AXIOMS {axOk}/{audited.length} standard-only / CLOSURE {clOk}/{audited.length} clean (+2 positive controls) / LogMvK hypothesis in closure of frontends: {logIn}"

#kwalkentry_check

end Tests.Gen4.KWalkEntryCheck
