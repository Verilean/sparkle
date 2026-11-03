import Tools.Assume.MemoFamily
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- BUILT: kjob lake build Tests.Gen4.MemoFamilyCheck exit 0 (742 jobs, rt163, base 496afcef): MEMOFAMILY CHECK: TYPE 12/12 / MUTANT 8/8 variants of 7 labels / AXIOMS 8 standard-only / CLOSURE 8 clean (+2 positive controls) / MODEL 1. Clean build is the coder's.

/-! # Audit of Tools/Assume/MemoFamily.lean (scripts/gen4/MEMO_FAMILY_FREEZE.md rev2, f23b4bc7)

`MemoFamily` is a TRUSTED hypothesis structure (a hypothesis about the runtime behaviour of the memo / child-cache /
depth cells). This file audits its TYPE only.

1. TYPE: each of the 12 statements (8 fields of `MemoFamily` + 4 of `MemoTele`) is `isDefEq` to `Expected.*` below,
   which was written separately from the freeze section 2 text (not copied from the implementation file;
   `mv` is spelled `readOf sparkleSubModuleCache`, `cv/sv/dv` as `readOf` of their refs).
2. MUTANT (M1-M7; M6 has two variants): signature/defeq REJECTIONS only. A mutant is rejected because its type is not
   defeq to the field's type. This is NOT a semantic counterexample and says nothing about whether the mutated
   statement is true or false at runtime.
3. AXIOMS: only propext / Classical.choice / Quot.sound (no sorryAx, no ofReduceBool).
4. CLOSURE: transitive constant closure (types, thm/def bodies; opaque bodies are not tracked) contains no
   `Laws` / `T1Hyp` / `T1HypND` constant. The detector is run on `T1Hyp` and `T1HypND` as positive controls.
5. MODEL: `vacuous_model` (quiet = False) shows the TYPE is satisfiable. This is a satisfiability check of the type,
   not evidence about the runtime. -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Sparkle.Compiler.Elab

namespace Tests.Gen4.MemoFamilyCheck

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## Expected (from the freeze text) -/
namespace Expected

def frame (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {α : Type} (p : MetaM α), Tools.Assume.MemoFamily.FramedNM MkRefd p → ∀ w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref p w) = readOf sparkleSubModuleCache w
def frameCacheSet (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
def frameDepthSet (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
def memoGet (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ m w w',
    RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w m w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
def memoSet (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = v
def memoModify (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = f (readOf sparkleSubModuleCache w)
def frameCacheModify (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
def frameDepthModify (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Nat → Nat) w u w',
    RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w

/-- The invariant-preservation premise shared by the four tele statements. -/
def TeleI (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ w w', readOf sparkleChildCache w' = readOf sparkleChildCache w →
    readOf sparkleChildSynth w' = readOf sparkleChildSynth w →
    readOf sparkleSynthDepth w' = readOf sparkleSynthDepth w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w → (O.quiet w → O.quiet w') →
    I w → I w'
def telescope (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    TeleI O I →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)
def lamTelescope (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    TeleI O I →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup)
def localDecl (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    TeleI O I →
    ∀ (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k)
def letDecl (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    TeleI O I →
    ∀ (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k)
end Expected

/-! ## Mutants: each changes one thing; rejected by signature/defeq (not semantic counterexamples) -/
namespace Mutant

/-- M1: memoSet conclusion `= v` replaced by `= mv w`. -/
def M1 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
/-- M2: memoSet without `O.quiet w →`. -/
def M2 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' →
    readOf sparkleSubModuleCache w' = v
/-- M3: memoSet without `AdmCtx O.quiet mctx cctx →`. -/
def M3 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = v
/-- M4: frame over `FramedA` (which contains the memo cell's own get/set/modify) instead of `FramedNM`. -/
def M4 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {α : Type} (p : MetaM α), FramedA MkRefd p → ∀ w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref p w) = readOf sparkleSubModuleCache w
/-- M5: memoModify conclusion `= f (mv w)` replaced by `= mv w`. -/
def M5 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w' →
    O.quiet w → readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
/-- M6a: frameCacheModify without `O.quiet w →`. -/
def M6a (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
/-- M6b: frameDepthModify without `O.quiet w →`. -/
def M6b (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Nat → Nat) w u w',
    RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w' →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
/-- M7: frameDepthModify with `RunsTo (set …)` in place of `RunsTo (modify …)` (the function argument becomes a value). -/
def M7 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (v : Nat) w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
end Mutant

/-! ## Vacuous model (satisfiability of the type only) -/
def vacO : RefLawsAOps MkRefd mref cref := RefLawsAOps.quietFalse MkRefd mref cref
theorem vacuous_model : Tools.Assume.MemoFamily.MemoFamily (mref := mref) (cref := cref) vacO where
  frame := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  frameCacheSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameDepthSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  memoGet := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  memoSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  memoModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameCacheModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameDepthModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  tele :=
    { telescope := by intro _ _ _ I _ hIq _ _ _ _ w hw; exact False.elim (hIq w hw)
      lamTelescope := by intro _ _ _ I _ hIq _ _ _ _ _ w hw; exact False.elim (hIq w hw)
      localDecl := by intro _ _ _ I _ hIq _ _ _ _ _ w hw; exact False.elim (hIq w hw)
      letDecl := by intro _ _ _ I _ hIq _ _ _ _ _ _ w hw; exact False.elim (hIq w hw) }

/-! ## The checker -/

/-- Transitive constant closure; `thmInfo`/`defnInfo` bodies and all types are traversed; `opaqueInfo` bodies are not
(reached opaque constants are returned so the log can say so). -/
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

/-- The projection `S.field : ∀ {mref cref} {O}, S O → T`; return `T` with `mref cref O` as given. -/
private def fieldDefEq (field : Name) (E : Name) : MetaM Bool := do
  let info ← getConstInfo field
  forallBoundedTelescope info.type (some 4) fun xs body => do
    let some mrefF := xs[0]? | throwError "{field}: no mref"
    let some crefF := xs[1]? | throwError "{field}: no cref"
    let some oF := xs[2]? | throwError "{field}: no O"
    let lvls := (← getConstInfo E).levelParams.map fun _ => levelZero
    let exp := mkConst E lvls
    let expApplied := mkApp3 exp mrefF crefF oF
    isDefEq body expApplied

elab "#memo_family_check" : command => liftTermElabM do
  let fam := `Tools.Assume.MemoFamily.MemoFamily
  let tele := `Tools.Assume.MemoFamily.MemoTele
  let pre := `Tests.Gen4.MemoFamilyCheck
  let typeCases : List (Name × Name) :=
    [(fam ++ `frame, pre ++ `Expected ++ `frame), (fam ++ `frameCacheSet, pre ++ `Expected ++ `frameCacheSet),
     (fam ++ `frameDepthSet, pre ++ `Expected ++ `frameDepthSet), (fam ++ `memoGet, pre ++ `Expected ++ `memoGet),
     (fam ++ `memoSet, pre ++ `Expected ++ `memoSet), (fam ++ `memoModify, pre ++ `Expected ++ `memoModify),
     (fam ++ `frameCacheModify, pre ++ `Expected ++ `frameCacheModify),
     (fam ++ `frameDepthModify, pre ++ `Expected ++ `frameDepthModify),
     (tele ++ `telescope, pre ++ `Expected ++ `telescope), (tele ++ `lamTelescope, pre ++ `Expected ++ `lamTelescope),
     (tele ++ `localDecl, pre ++ `Expected ++ `localDecl), (tele ++ `letDecl, pre ++ `Expected ++ `letDecl)]
  let mutCases : List (String × Name × Name) :=
    [("M1", fam ++ `memoSet, `M1), ("M2", fam ++ `memoSet, `M2), ("M3", fam ++ `memoSet, `M3),
     ("M4", fam ++ `frame, `M4), ("M5", fam ++ `memoModify, `M5), ("M6a", fam ++ `frameCacheModify, `M6a),
     ("M6b", fam ++ `frameDepthModify, `M6b), ("M7", fam ++ `frameDepthModify, `M7)]
  -- TYPE
  let mut ok : Nat := 0
  for (f, e) in typeCases do
    unless ← fieldDefEq f e do throwError "TYPE mismatch for {f}"
    ok := ok + 1
  unless ok == 12 do throwError "TYPE count {ok} ≠ 12"
  -- MUTANT (control: the same mutant machinery accepts the unmutated Expected as defeq)
  let mut rej : Nat := 0
  for (lbl, f, m) in mutCases do
    if ← fieldDefEq f (pre ++ `Mutant ++ m) then throwError "mutant {lbl} NOT rejected for {f}"
    rej := rej + 1
  let labels := (mutCases.map (·.1)).map (·.take 2) |>.eraseDups
  unless labels.length == 7 do throwError "mutant labels {labels} ≠ M1..M7"
  -- AXIOMS
  let audited : List Name :=
    [fam, tele, fam ++ `mk, tele ++ `mk, pre ++ `vacuous_model, `Tools.Assume.MemoFamily.FramedNM,
     `Tools.Assume.MemoFamily.SideRefNM, `Tools.Assume.MemoFamily.mv]
  let mut axOk : Nat := 0
  for n in audited do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    unless bad.isEmpty do throwError "{n}: axioms {bad}"
    axOk := axOk + 1
  -- CLOSURE
  let mut clOk : Nat := 0
  let mut sizes : Nat := 0
  for n in audited do
    let (bad, sz) ← closureBad n
    unless bad.isEmpty do throwError "{n}: forbidden constants {bad}"
    clOk := clOk + 1
    sizes := sizes + sz
  -- positive controls: the same detector flags T1Hyp / T1HypND / Laws-dependent constants
  for c in [`Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND] do
    let (bad, _) ← closureBad c
    if bad.isEmpty then throwError "closure detector MISSED {c}"
  -- MODEL
  let mi ← getConstInfo (pre ++ `vacuous_model)
  let mut modelOk : Nat := 0
  if mi.type.getUsedConstants.contains fam then modelOk := 1
  unless modelOk == 1 do throwError "vacuous_model does not state MemoFamily"
  logInfo m!"MEMOFAMILY CHECK: TYPE {ok}/12 / MUTANT {rej}/8 variants of 7 labels (signature/defeq rejections, not semantic counterexamples) / AXIOMS {axOk} standard-only / CLOSURE {clOk} clean (+2 positive controls) / MODEL {modelOk} (vacuous quiet=False; type satisfiability only)"

#memo_family_check

end Tests.Gen4.MemoFamilyCheck
