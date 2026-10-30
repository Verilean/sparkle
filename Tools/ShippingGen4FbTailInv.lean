import Tools.ShippingGen4FbInv
import Tools.ShippingChildLegacyTailA
set_option autoImplicit false
-- NOT BUILT (unit FB-4): text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §12.2/§12.3 (rev7, scoped approval at 6b41b373).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Theorems and one definition only.

/-! # FB-4: the `legacyTail` run keeps `InvAt (D+1)`; the packaged `R4RunInvT`

K-TAIL `legacyTail_keepsInv` (Route 2 of §12.2: the proof of `legacyTail_core` replayed on the named program
`legacyTail`), `R4RunInvT` (the `R4RunInv` body of f07f4bf2 with ONE more leading conjunct `InvAt (D+1) w₅`), and
`a4_inv_tail_machine_or_R4RunInvT` (re-packs FB-3's single witness package; no second existential for `w₅`).

Preservation only (P). `InvAt` at the tail end `w₅` is NOT the semantic guarantee of the legacy route or of the memo
hit (T-LEG / T-MEMO / T-PP / T-FIN / K4 are not supplied here). -/

namespace Tools.ShippingGen4FbTailInv
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
open Tools.ShippingChildLegacyTailA Tools.ShippingChildLegacyHelpersA Tools.ShippingChildWalkA
open Tools.ShippingChildProjFieldA Tools.ShippingChildPathA Tools.ShippingChildTranslatePathA
open Tools.ShippingGen2 Tools.ShippingGen4FbR4 Tools.ShippingGen4FbInv

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000

/-- The replay of `legacyTail_core` on the named program `legacyTail`, generic in the invariant (Route 2 of §12.2). -/
theorem legacyTail_keeps_generic {mctx : Meta.Context} {cctx : Core.Context}
    (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (TLam : LamTelescopeLawA O.quiet mref cref) (TF : ForallTelescopeLawA O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (translate : TranslateFn) (htr : RecA O I translate)
    (b : Bool) (declName : Name) (ci : ConstantInfo) :
    Keeps mctx mref cctx cref I (legacyTail translate (profLogIO b) declName [] false ci) := by
  unfold legacyTail
  simp only [Bool.not_false, ↓reduceIte]
  refine Keeps.bind (by vca) fun memo => ?_
  split
  · vca
  · refine Keeps.bind (by vca) fun _ => ?_
    split
    · refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine keepsA_lambdaTelescope O hA hS TLam _ _ _ (fun m c xs b' hA' => ?_)
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (splitReturnLeaves_keeps O hS TLam TF hA' _ _) fun leaves => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      refine Keeps.bind (by vca) fun _ => ?_
      rw [keeps_iff]
      refine Triple.bindQ (φ := MkRefd _) (tripleA_mkExprCache O hA' hS _) ?_
      intro cacheRef hr
      refine Triple.bind
        (keeps_iff.mp (bindInputsLegacy_keepsCP O hS TLam TF hA' _ _ _ _
          (emitLeavesAP O hA' hS _ b cacheRef hr (htr m c hA') _ _ _) 0 _ _
          (ctxOk_entry false hr))) ?_
      rintro ⟨_, fs⟩
      refine Triple.bind (finishSynthA declName fs) ?_
      intro result
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA' hS (FramedA.sideModify _ .subModule))) ?_
      intro _
      exact Triple.pure fun _ hw => hw
    · vca

/-- K-TAIL: the named program `legacyTail` (parameters `[]`, `symbolicMode := false`) keeps `InvAt (D+1)`. -/
theorem legacyTail_keepsInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat)
    (hC : ChildKeepsInv L P Reach (D + 1))
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    (tenv : Lean.Environment) (pb : Bool) (declName : Name) (ci : ConstantInfo) :
    Keeps mctx mref cctx cref (InvAt L P Reach (D + 1))
      (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName [] false ci) :=
  legacyTail_keeps_generic L.O (stableA_invAt L P Reach (D + 1))
    (RefLawsATele.lamTelescopeLaw L.T) (RefLawsATele.forallTelescopeLaw L.T) hA _
    (translate_keepsInv_of_tele L P Reach (D + 1) hC tenv) pb declName ci

/-- `R4RunInv` (f07f4bf2, `Tools/ShippingGen4FbInv.lean`) with ONE more leading conjunct `InvAt (D+1) w₅`, `w₅` the END
world of the `legacyTail` run (the world `coreFinally` starts from). Preservation only; the meaning of the legacy
tail, of the memo hit and of the post-processing is NOT stated here (unsupplied). -/
def R4RunInvT (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧ InvAt L P Reach (D + 1) w₅ ∧
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC L.O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ none w₆ ∧
    JQC L.O (D + 1) w₄ ∧ JQC L.O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC L.O D w' ∧
    RunsTo (legacyTail
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName [] false
      (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
        (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
      JQC L.O (D + 1) w₇ ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆) ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆))))


/-- K-RUNT: the extraction. `InvAt` at `w₅` is obtained from the tail run of FB-3's ONE witness package; no second
existential for `w₅`. -/
theorem a4_inv_tail_machine_or_R4RunInvT (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
      R4RunInvT L P Reach mctx cctx D declName shape m d w w' := by
  rcases a4_inv_machine_or_R4RunInv L P Reach hA hI hC hr entry with h | h
  · exact Or.inl h
  · obtain ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h4, h6, rest⟩ := h
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, htail, g11⟩ := rest
    have h5 : InvAt L P Reach (D + 1) w₅ :=
      triple_runs (keeps_iff.mp (legacyTail_keepsInv L P Reach D hC hA tenv pb declName _)) h6 htail
    exact Or.inr ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h4, h6, h5, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
      htail, g11⟩

end Tools.ShippingGen4FbTailInv
