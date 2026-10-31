import Tools.ShippingGen4FbFin0
set_option autoImplicit false
-- NOT BUILT (unit FB-13): written against scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §21.4 (rev12, scoped approved at a02dc304).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. One definition and three theorems only.

/-! # FB-13: T-MACH-INV, `InvAt` on the `A4MachineSideA` side

`A4MachineSideInv` is `A4MachineSideA` (Tools/ShippingGen4FbR4.lean:71 at a02dc304) with three leading conjuncts
`InvAt (D+1)` at `w₄` (machine start), `w₆` (machine end) and `w₅` (memo-insert end), the same witnesses as the run data.
`a4_inv_side_or_tail`: the proof of `a4_inv_machine_or_R4RunInv` up to `hI6` is repeated and BOTH branches are packed
from that one witness package (the `R4RunInvT` branch applies `legacyTail_keepsInv` to the same `R4RunInv` data).
`tFin0_of_a4MachineSideInv`, `a4_inv_tail_fin0_both`: depth 0.
Preservation only (P): no meaning of the machine route, T-LEG, T-MEMO, K4 or T-PP is stated. -/

namespace Tools.ShippingGen4FbMachInv
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Sparkle.IR.Builder
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildBndCore
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingMachineOutcomeA Tools.ShippingMachineOutcomeA3 Tools.ShippingMachineOutcomeA4
open Tools.ShippingGen2 Tools.ShippingGen4FbR4 Tools.ShippingGen4FbInv Tools.ShippingGen4FbTailInv
open Tools.ShippingGen4FbFin0

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

def A4MachineSideInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
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
      declName shape) mctx mref cctx cref w₄ (some (m, d)) w₆ ∧
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
    ∃ wl : Void IO.RealWorld,
      RunsTo (show MetaM Unit from profLogIO pb
        s!"[profile] synthesizeCombinational {declName} machine certified front end")
        mctx mref cctx cref w₆ () wl ∧
      RunsTo (sparkleSubModuleCache.modify (·.insert declName (m, d)) : MetaM Unit)
        mctx mref cctx cref wl () w₅

theorem a4_inv_side_or_tail (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideInv L P Reach mctx cctx D declName shape m d w w' ∨
      R4RunInvT L P Reach mctx cctx D declName shape m d w w' := by
  obtain ⟨b, envR, ci, w1, w2, w3, w4, get, henv, run, hw3, hI3, sf, sw, sl, sp, sc, ss, sg, hfin, hz, hst⟩ :=
    core_reads_link4Inv L P Reach hA hI hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  have htrD := htr_of_tele L.O hA L.T D envR
  obtain ⟨envR', wA, henv', hwA, hsplit⟩ :=
    synthesizeFromConst_machine_split2A L.O hA htrD
      (fun c => childKeepsC_all_of_tele L.O L.T (D + 1) (by omega) mctx cctx hA c) old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w6, hrun, hw6, hout⟩ := hsplit shape hshape
  have hIA : InvAt L P Reach (D + 1) wA :=
    triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (D + 1)) FramedA.env)) hI3 henv'
  have hI6 : InvAt L P Reach (D + 1) w6 :=
    triple_runs (keeps_iff.mp (machineAttempt_keepsInv L P Reach D hC hA envR b declName shape)) hIA hrun
  have hJw' : JQC L.O D w' := by
    by_cases h0 : D = 0
    · subst h0
      exact triple_runs (Tools.ShippingChildComposeC.core_tripleAC_of_tele L.O hA L.T declName) hI.1.1 hr
    · exact triple_runs (Tools.ShippingChildCoreC.core_tripleAC L.O hA D declName
        (Tools.ShippingChildDepthC.hbodyC_of_step L.O (Tools.ShippingChildComposeC.bodyStepC_of_tele L.O L.T)
          hA D declName)) hI.1 hr
  have hfin' := coreFinally_split hfin
  rcases hout with ⟨res, rfl, rfl, wl, hl, hm⟩ | ⟨rfl, htail⟩
  · have hIl : InvAt L P Reach (D + 1) wl :=
      triple_runs (keeps_iff.mp (keepsA_diag L.O hA (stableA_invAt L P Reach (D + 1))
        (Diag.profLog b _))) hI6 hl
    have hI5 : InvAt L P Reach (D + 1) w4 :=
      triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (D + 1))
        (FramedA.sideModify _ .subModule))) hIl hm
    exact Or.inl ⟨envR, b, ci, envR', w1, w2, w3, wA, w4, w6, hIA, hI6, hI5, get, henv, hw3, henv', hshape, hrun,
      hwA, hw6, ⟨sf, sw, sl, sp, sc, ss, sg, hfin, hfin', hz, hst⟩, hJw', wl, hl, hm⟩
  · obtain ⟨t, d₀, wh, hh, hwh, hcase⟩ := synthesizeMachineCertified_noneSplitA L.O hA htrD hwA hrun
    have hI5 : InvAt L P Reach (D + 1) w4 :=
      triple_runs (keeps_iff.mp (legacyTail_keepsInv L P Reach D hC hA envR b declName _)) hI6 htail
    exact Or.inr ⟨envR, b, ci, envR', w1, w2, w3, wA, w4, w6, hIA, hI6, hI5, get, henv, hw3, henv', hshape, hrun,
      hwA, hw6, ⟨sf, sw, sl, sp, sc, ss, sg, hfin, hfin', hz, hst⟩, hJw', htail, t, d₀, wh, hh, hwh, hcase⟩

theorem tFin0_of_a4MachineSideInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : A4MachineSideInv L P Reach mctx cctx 0 declName shape m d w w') :
    InvAt L P Reach 0 w' := by
  obtain ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h4, h6, h5, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
    hl⟩ := h
  obtain ⟨sf, sw, sl, sp, sc, ss, sg, _, hfr, _, _⟩ := g9
  obtain ⟨y0, hmod, h0, -⟩ := hfr
  have hw' : w' = y0 := h0 rfl
  obtain ⟨hcv, -, -⟩ := L.O.depthModify' hA (· - 1) h5.1.1.1 hmod
  exact ⟨g10, by rw [hw', hcv]; exact h5.2⟩

theorem a4_inv_tail_fin0_both (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    (A4MachineSideInv L P Reach mctx cctx 0 declName shape m d w w' ∨
      R4RunInvT L P Reach mctx cctx 0 declName shape m d w w') ∧ InvAt L P Reach 0 w' := by
  rcases a4_inv_side_or_tail L P Reach hA hI hC hr entry with h | h
  · exact ⟨Or.inl h, tFin0_of_a4MachineSideInv L P Reach hA h⟩
  · exact ⟨Or.inr h, tFin0_of_r4RunInvT L P Reach hA h⟩

end Tools.ShippingGen4FbMachInv
