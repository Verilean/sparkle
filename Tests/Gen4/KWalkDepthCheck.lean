import Tools.ShippingGen4KWalkDepthInduct
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
-- NOT BUILT. KWALKDEPTH CHECK: audit of Tools/ShippingGen4KWalk{Depth,DepthArms,DepthEntry,DepthInduct}.lean (S6 of scripts/gen4/KWALK_PLAN.md, scripts/gen4/KWALK_S6_FREEZE.md).
set_option autoImplicit false

/-! # Audit of the S6 depth induction

1. TYPE: each audited theorem's type is `isDefEq` to `Expected.*` below, written separately (`KW`-with-depth spelled with `readOf`; `Triple` unfolded to its `match`).
2. MUTANT: signature/defeq REJECTIONS only. NOT semantic counterexamples.
3. AXIOMS: only propext / Classical.choice / Quot.sound.
4. CLOSURE: no `Laws` / `T1Hyp` / `T1HypND` constant in the transitive closure (positive controls: the detector flags `T1Hyp`, `T1HypND`). `MemoFamily` is allowed (the hypothesis `M`).
   The REMAINING hypotheses of the induction (`LogMvK`, `LegacyImplK`, `LegacyArmD`) must be IN the closure of the headline theorem (they are hypotheses, not provided), and `PpMvK` is reported. -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Sparkle.Compiler.Elab

namespace Tests.Gen4.KWalkDepthCheck

namespace Expected

/-- `KWD O K D`, spelled out: quiet, the synthesis ref pinned, the key relation `K`, the depth `D`. -/
def KDof {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (D : Nat) (w : Void IO.RealWorld) : Prop :=
  (O.quiet w ∧ readOf sparkleChildSynth w = some synthesizeChild ∧
    ∀ k, (readOf sparkleSubModuleCache w).contains k = true → (readOf sparkleChildCache w).contains k = true) ∧
  readOf sparkleSynthDepth w = D

def KDXof {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (n : Name) (D : Nat) (w : Void IO.RealWorld) : Prop :=
  (O.quiet w ∧ readOf sparkleChildSynth w = some synthesizeChild ∧
    ∀ k, (readOf sparkleSubModuleCache w).contains k = true →
      (readOf sparkleChildCache w).contains k = true ∨ (n == k) = true) ∧
  readOf sparkleSynthDepth w = D

def logMv {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ b msg w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) =
      readOf sparkleSubModuleCache w

def tripleD {α : Type} (Pre : Void IO.RealWorld → Prop) (Qok : Void IO.RealWorld → Prop)
    (Rf : Exception → Void IO.RealWorld → Prop) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (p : MetaM α) : Prop :=
  ∀ w, Pre w → match p mctx mref cctx cref w with
    | .ok _ w' => Qok w'
    | .error e w' => Rf e w'

def memoInsertD : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → ∀ (D : Nat) (n : Name) (r : Res)
    {R : Exception → Void IO.RealWorld → Prop},
    tripleD (KDof O D) (KDXof O n D) R mctx mref cctx cref (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit)

def childInsertD : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → ∀ (D : Nat) (n : Name) (r : Res)
    {R : Exception → Void IO.RealWorld → Prop},
    tripleD (KDXof O n D) (KDof O D) R mctx mref cctx cref (sparkleChildCache.modify (·.insert n r) : MetaM Unit)

def entryNestedD : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → logMv O →
    ∀ (translate : Lean.Environment → TranslateFn) (declName : Name) (D : Nat), D ≠ 0 →
    (D < sparkleSynthDepthLimit → ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      tripleD (KDof O (D + 1)) (KDXof O declName (D + 1)) (fun e w => KDof O (D + 1) w ∧ OkExc e) mctx mref cctx cref
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)) →
    tripleD (KDof O D) (KDXof O declName D) (fun e w => KDof O D w ∧ OkExc e) mctx mref cctx cref
      (synthesizeCombinationalCoreWith translate declName [] false true)

def childWindowD : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → ∀ (D : Nat),
    (∀ n : Name, tripleD (KDof O D) (KDXof O n D) (fun e w => KDof O D w ∧ OkExc e) mctx mref cctx cref
      (synthesizeCombinational n)) →
    ∀ n : Name, tripleD (KDof O D) (KDof O D) (fun e w => KDof O D w ∧ OkExc e) mctx mref cctx cref
      (synthesizeChild n)

/-- The headline: hypotheses `LogMvK`, `LegacyImplK` (at every nonzero depth), the legacy arm (at every nonzero depth). -/
def headline : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → logMv O →
    (∀ D : Nat, D ≠ 0 → Tools.ShippingGen4KWalkFallback.LegacyImplK O (KDof O D)) →
    (∀ D : Nat, D ≠ 0 → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ (b : Bool) (env : Lean.Environment) (declName : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
        certifiedShape? false [] ci = none → mixedCertifiedShape? false [] ci isInst = none →
        tripleD (KDof O D) (KDXof O declName D) (fun e w => KDof O D w ∧ OkExc e) mctx mref cctx cref
          (synthesizeFromConst (fun e h t n => translateExprToWire env e h t n) (profLogIO b) declName [] false false ci isInst)) →
    ∀ (D : Nat), D ≠ 0 → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ n : Name,
      tripleD (KDof O D) (KDof O D) (fun e w => KDof O D w ∧ OkExc e) mctx mref cctx cref (synthesizeChild n)

end Expected

namespace Mutant

/-- M1: the memo write returning at K (the window not opened) with the depth kept. -/
def M1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → ∀ (D : Nat) (n : Name) (r : Res)
    {R : Exception → Void IO.RealWorld → Prop},
    Expected.tripleD (Expected.KDof O D) (Expected.KDof O D) R mctx mref cctx cref
      (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit)

/-- M2: the nested entry whose depth is NOT given back (the post-world depth `D + 1`). -/
def M2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → Expected.logMv O →
    ∀ (translate : Lean.Environment → TranslateFn) (declName : Name) (D : Nat), D ≠ 0 →
    (D < sparkleSynthDepthLimit → ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Expected.tripleD (Expected.KDof O (D + 1)) (Expected.KDXof O declName (D + 1))
        (fun e w => Expected.KDof O (D + 1) w ∧ OkExc e) mctx mref cctx cref
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)) →
    Expected.tripleD (Expected.KDof O D) (Expected.KDXof O declName (D + 1)) (fun e w => Expected.KDof O D w ∧ OkExc e)
      mctx mref cctx cref (synthesizeCombinationalCoreWith translate declName [] false true)

/-- M3: the nested entry without the budget guard `D < sparkleSynthDepthLimit` (the body asked at every depth, which is not provable). -/
def M3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx → Expected.logMv O →
    ∀ (translate : Lean.Environment → TranslateFn) (declName : Name) (D : Nat), D ≠ 0 →
    (∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Expected.tripleD (Expected.KDof O (D + 1)) (Expected.KDXof O declName (D + 1))
        (fun e w => Expected.KDof O (D + 1) w ∧ OkExc e) mctx mref cctx cref
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)) →
    Expected.tripleD (Expected.KDof O D) (Expected.KDXof O declName D) (fun e w => Expected.KDof O D w ∧ OkExc e)
      mctx mref cctx cref (synthesizeCombinationalCoreWith translate declName [] false true)

/-- M4: the headline without the logger hypothesis. -/
def M4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O →
    (∀ D : Nat, D ≠ 0 → Tools.ShippingGen4KWalkFallback.LegacyImplK O (Expected.KDof O D)) →
    (∀ D : Nat, D ≠ 0 → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ (b : Bool) (env : Lean.Environment) (declName : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
        certifiedShape? false [] ci = none → mixedCertifiedShape? false [] ci isInst = none →
        Expected.tripleD (Expected.KDof O D) (Expected.KDXof O declName D) (fun e w => Expected.KDof O D w ∧ OkExc e)
          mctx mref cctx cref
          (synthesizeFromConst (fun e h t n => translateExprToWire env e h t n) (profLogIO b) declName [] false false ci isInst)) →
    ∀ (D : Nat), D ≠ 0 → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ n : Name,
      Expected.tripleD (Expected.KDof O D) (Expected.KDof O D) (fun e w => Expected.KDof O D w ∧ OkExc e) mctx mref cctx cref
        (synthesizeChild n)

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

elab "#kwalkdepth_check" : command => liftTermElabM do
  let dp := `Tools.ShippingGen4KWalkDepth
  let da := `Tools.ShippingGen4KWalkDepthArms
  let de := `Tools.ShippingGen4KWalkDepthEntry
  let di := `Tools.ShippingGen4KWalkDepthInduct
  let pre := `Tests.Gen4.KWalkDepthCheck
  let typeCases : List (Name × Name) :=
    [(dp ++ `triple_memoInsertD, pre ++ `Expected ++ `memoInsertD),
     (dp ++ `triple_childInsertD, pre ++ `Expected ++ `childInsertD),
     (de ++ `entryNested_windowD, pre ++ `Expected ++ `entryNestedD),
     (de ++ `synthesizeChild_windowD, pre ++ `Expected ++ `childWindowD),
     (di ++ `synthesizeChild_depthK, pre ++ `Expected ++ `headline)]
  let mutCases : List (String × Name × Name) :=
    [("M1", dp ++ `triple_memoInsertD, `M1), ("M2", de ++ `entryNested_windowD, `M2),
     ("M3", de ++ `entryNested_windowD, `M3), ("M4", di ++ `synthesizeChild_depthK, `M4)]
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
    [dp ++ `tryFinallySplit2, dp ++ `triple_framedNM_totalD, dp ++ `triple_depthSetD, dp ++ `triple_depthModifyD,
     dp ++ `tripleK_depthGetD, dp ++ `fin_totalD,
     da ++ `fromConst_certified_windowD, da ++ `fromConst_mixed_windowD, da ++ `fromConst_machine_windowD,
     da ++ `fromConst_frontends_windowD, de ++ `combWith_nestedD,
     di ++ `child_step, di ++ `child_budget, di ++ `memo_miss_of_child_miss, di ++ `memo_miss_of_child_miss_KWD,
     di ++ `tripleK_cacheGetD, di ++ `childMiss_memoMiss]
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
  -- the remaining hypotheses are in the closure of the headline (they are asked, not provided)
  let (seen, _) := closure (← getEnv) [di ++ `synthesizeChild_depthK] {} {}
  let logIn := seen.contains `Tools.ShippingGen4KWalkEntry.LogMvK
  let implIn := seen.contains `Tools.ShippingGen4KWalkFallback.LegacyImplK
  let legIn := seen.contains (di ++ `LegacyArmD)
  let ppIn := seen.contains `Tools.ShippingGen4KWalkHelpers.PpMvK
  unless logIn && implIn && legIn do throwError "a remaining hypothesis is NOT in the closure"
  logInfo m!"KWALKDEPTH CHECK: TYPE {ok}/{typeCases.length} / MUTANT {rej}/{mutCases.length} (signature/defeq rejections, not semantic counterexamples) / AXIOMS {axOk}/{audited.length} standard-only / CLOSURE {clOk}/{audited.length} clean (+2 positive controls) / hypotheses in closure of the headline: LogMvK {logIn}, LegacyImplK {implIn}, LegacyArmD {legIn}; PpMvK {ppIn}"

#kwalkdepth_check

end Tests.Gen4.KWalkDepthCheck
