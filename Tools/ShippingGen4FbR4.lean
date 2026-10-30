import Tools.ShippingMachineOutcomeA4
set_option autoImplicit false
-- NOT BUILT (unit FB-2): R4Run / A4MachineSideA / a4_machine_or_R4Run. Not a supply result.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §9.2.2 (rev5).

namespace Tools.ShippingGen4FbR4
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Sparkle.IR.Builder
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingMachineOutcomeA Tools.ShippingMachineOutcomeA3 Tools.ShippingMachineOutcomeA4

/-- (b) side of `core_machine_outcomeA'''`: prefix items 1-9 with `r = none`, the `legacyTail` run `w₆ → w₅`, and the
harness/closing data. `t'` is inside the second `closeLets` disjunct. -/
def R4Run {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ none w₆ ∧
    JQC O (D + 1) w₄ ∧ JQC O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC O D w' ∧
    RunsTo (legacyTail
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName [] false
      (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
        (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
      JQC O (D + 1) w₇ ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆) ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆))))

/-- (a) side of `core_machine_outcomeA'''` (NOT `Gen2.MachineTaken`): the same prefix 1-9 with `r = some (m, d)`,
and the profile-log and memo-insert runs `w₆ → wl → w₅`. -/
def A4MachineSideA {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ (some (m, d)) w₆ ∧
    JQC O (D + 1) w₄ ∧ JQC O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC O D w' ∧
    ∃ wl : Void IO.RealWorld,
      RunsTo (show MetaM Unit from profLogIO pb
        s!"[profile] synthesizeCombinational {declName} machine certified front end")
        mctx mref cctx cref w₆ () wl ∧
      RunsTo (sparkleSubModuleCache.modify (·.insert declName (m, d)) : MetaM Unit)
        mctx mref cctx cref wl () w₅

/-- The none-side extraction: `core_machine_outcomeA'''` with its item-10 disjunction split. No new law/premise. -/
theorem a4_machine_or_R4Run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) :
    A4MachineSideA O mctx cctx D declName shape m d w w' ∨ R4Run O mctx cctx D declName shape m d w w' := by
  obtain ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, r, h1, h2, h3, h4, h5, h6, h7a, h7b, h8, h9, h10⟩ :=
    core_machine_outcomeA''' O hA T hr entry hw hc
  rcases h10 with ⟨res, rfl, rfl, wl, hl, hm⟩ | ⟨rfl, htail, t, d₀, w₇, hh, hj, hcase⟩
  · exact Or.inl ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h1, h2, h3, h4, h5, h6, h7a, h7b, h8, h9, wl, hl, hm⟩
  · exact Or.inr ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h1, h2, h3, h4, h5, h6, h7a, h7b, h8, h9,
      htail, t, d₀, w₇, hh, hj, hcase⟩

end Tools.ShippingGen4FbR4
