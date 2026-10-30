import Tools.ShippingGen4FbR4
import Tools.ShippingGen2Keep
set_option autoImplicit false
-- NOT BUILT (unit FB-3): text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §10 (rev6, approved at b18d3a5e).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Theorems and one definition only.

/-! # FB-3: `InvAt` kept along the core prefix and the machine attempt; the packaged `R4RunInv`

What this file states (types frozen in FALLBACK_SUPPLY_FREEZE.md §10): `invAt_cacheClear`, `invAt_depthSet`,
`core_reads_link4Inv` (the prefix of `core_reads_link4A` with `InvAt (D+1) w3` added), `machineAttempt_keepsInv`,
`R4RunInv` (the built `R4Run` body of e7181279 with `O := L.O` and the two leading conjuncts `InvAt (D+1) w₄`,
`InvAt (D+1) w₆`), and `a4_inv_machine_or_R4RunInv` (one extraction, ONE prefix witness: the `InvAt` facts are about
the same `w₃ w₄ w₆` as the run data, not about separately obtained existentials).

What it does NOT give: `InvAt` at the END `w₅` of the `legacyTail`. Only the preservation of `InvAt` up to the tail's
START world `w₆` is stated. That preservation is a different thing from the semantic guarantee of the legacy route
and from the one of the memo hit: those semantic guarantees are NOT supplied by this file (unsupplied obligations
T-LEG / T-MEMO). The tail's own run (`legacyTail … w₆ (m, d) w₅`) is only carried as a run witness, as in `R4Run`. -/

namespace Tools.ShippingGen4FbInv
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

open Tools.ShippingGen2 Tools.ShippingGen4FbR4

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- K-CLEAR: the depth-0 cache clear, at `InvAt`. -/
theorem invAt_cacheClear (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ L.O.quiet D)
      (sparkleChildCache.set {} : MetaM Unit) (fun _ => InvAt L P Reach D) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := L.O.cacheSet hA _ _ _ _ h hw.1
    refine ⟨⟨⟨L.O.cacheSetQ hA _ _ _ _ h hw.1, hk.2.1.trans hw.2.1, hk.2.2.trans hw.2.2⟩, ?_⟩, ?_⟩
    · rw [hk.1]; exact cacheInvA_empty L.O
    · intro c r _ hget
      rw [hk.1] at hget
      simp at hget

/-- K-DEPTH: the depth set `D → v`, at `InvAt`. -/
theorem invAt_depthSet (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx) (D v : Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (InvAt L P Reach D)
      (ST.Ref.set sparkleSynthDepth v : MetaM Unit) (fun _ => InvAt L P Reach v) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := L.O.depthSet hA _ _ _ _ h hw.1.1.1
    refine ⟨⟨⟨L.O.depthSetQ hA _ _ _ _ h hw.1.1.1, hk.2.1.trans hw.1.1.2.1, hk.2.2⟩, ?_⟩, ?_⟩
    · rw [hk.1]; exact hw.1.2
    · rw [hk.1]; exact hw.2

/-- K-MACH: the machine attempt keeps `InvAt (D+1)` (an instance of `machineCert_keepsAP`). -/
theorem machineAttempt_keepsInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat)
    (hC : ChildKeepsInv L P Reach (D + 1))
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    (tenv : Lean.Environment) (pb : Bool) (declName : Name) (shape : MachineShape) :
    Keeps mctx mref cctx cref (InvAt L P Reach (D + 1))
      (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb) declName shape) :=
  machineCert_keepsAP L.O hA (stableA_invAt L P Reach (D + 1))
    (fun e hint top named => translateExprToWire tenv e hint top named) pb declName
    (fun e hint top named => translate_keepsInv_of_tele L P Reach (D + 1) hC tenv mctx cctx hA e hint top named)
    (hC mctx cctx hA) (invAt_sv L P Reach (D + 1)) shape

/-- K-LINK: `core_reads_link4A` with `InvAt` threaded through the prefix (one added conjunct `InvAt (D+1) w3`). -/
theorem core_reads_link4Inv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {D : Nat} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module}
    {Dg : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w)
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, Dg) w') :
    ∃ (b : Bool) (envR : Environment) (ci : ConstantInfo) (w1 w2 w3 w4 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO b)
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, Dg) w4 ∧ JQC L.O (D + 1) w3 ∧
      InvAt L P Reach (D + 1) w3 ∧
      ∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
        (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
        (sg : Std.HashMap String String),
        RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w4 () w' ∧
        (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
        (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
          declName b D w sf sw sl sp sc ss sg) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases h0 : D = 0
  · subst h0
    have hw := hI
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach 0) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag L.O hA (stableA_invAt L P Reach 0)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet L.O hA (stableA_invAt L P Reach 0)) hw s3
    have hdD : d = 0 := hd.2.trans hd.1.1.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    simp only [↓reduceIte, beq_self_eq_true] at h
    peelP h; peelP h; peelP h; peelP h; peelP h; peelP h; peelP h
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (invAt_cacheClear L P Reach hA 0 (R := fun _ _ => False)) hw.1.1 step
    clear step
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    peelF L.O hA (stableA_invAt L P Reach 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (invAt_depthSet L P Reach hA 0 (0 + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨_, u, h, hfin⟩ := RunsTo.try_finally' h
    cases u
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (0 + 1))
      (FramedA.constInfo _))) hw hget
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (0 + 1))
      FramedA.env)) hw henv
    exact ⟨prof.isSome, env, ci, _, w2, _, _, hget, henv, h, hw.1, hw, _, _, _, _, _, _, _, hfin,
      fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun h0 => absurd rfl h0⟩
  · have hw := hI
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach D) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag L.O hA (stableA_invAt L P Reach D)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet L.O hA (stableA_invAt L P Reach D)) hw s3
    have hdD : d = D := hd.2.trans hd.1.1.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    have h0' : ¬ ((d == 0) = true) := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at h
    peelK L.O hA (stableA_invAt L P Reach d) h hw sf x1 g1
    peelK L.O hA (stableA_invAt L P Reach d) h hw sw x2 g2
    peelK L.O hA (stableA_invAt L P Reach d) h hw sl x3 g3
    peelK L.O hA (stableA_invAt L P Reach d) h hw sp x4 g4
    peelK L.O hA (stableA_invAt L P Reach d) h hw sc x5 g5
    peelK L.O hA (stableA_invAt L P Reach d) h hw ss x6 g6
    peelK L.O hA (stableA_invAt L P Reach d) h hw sg x7 g7
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (invAt_depthSet L P Reach hA d (d + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨_, u, h, hfin⟩ := RunsTo.try_finally' h
    cases u
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (d + 1))
      (FramedA.constInfo _))) hw hget
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (d + 1))
      FramedA.env)) hw henv
    exact ⟨prof.isSome, env, ci, _, w2, _, _, hget, henv, h, hw.1, hw, _, _, _, _, _, _, _, hfin,
      fun h0' => absurd h0' h0,
      fun _ => ⟨prof, wa, wb, wc, x1, x2, x3, x4, x5, x6, x7, rfl, s1, s2, s3, g1,
        runsTo_get_readOf _ g1, g2, runsTo_get_readOf _ g2, g3, runsTo_get_readOf _ g3, g4,
        runsTo_get_readOf _ g4, g5, runsTo_get_readOf _ g5, g6, runsTo_get_readOf _ g6, g7,
        runsTo_get_readOf _ g7⟩⟩

/-- `R4Run` (e7181279, `Tools/ShippingGen4FbR4.lean`) with `O := L.O` and the two leading conjuncts
`InvAt (D+1) w₄`, `InvAt (D+1) w₆`. The body after those two conjuncts is the `R4Run` body unchanged. Preserving the
tail's START world `w₆` is stated; the meaning of the legacy tail and of the memo is NOT (unsupplied). -/
def R4RunInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧
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

/-- K-RUN: the extraction. The `InvAt` facts and the run data share ONE set of witnesses (`w₃ w₄ w₆` come from the same
prefix peel, the same `getEnv` and the same machine run); nothing is re-obtained by a separate existential. -/
theorem a4_inv_machine_or_R4RunInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
      R4RunInv L P Reach mctx cctx D declName shape m d w w' := by
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
  · exact Or.inl ⟨envR, b, ci, envR', w1, w2, w3, wA, w4, w6, get, henv, hw3, henv', hshape, hrun,
      hwA, hw6, ⟨sf, sw, sl, sp, sc, ss, sg, hfin, hfin', hz, hst⟩, hJw', wl, hl, hm⟩
  · obtain ⟨t, d₀, wh, hh, hwh, hcase⟩ := synthesizeMachineCertified_noneSplitA L.O hA htrD hwA hrun
    exact Or.inr ⟨envR, b, ci, envR', w1, w2, w3, wA, w4, w6, hIA, hI6, get, henv, hw3, henv', hshape, hrun,
      hwA, hw6, ⟨sf, sw, sl, sp, sc, ss, sg, hfin, hfin', hz, hst⟩, hJw', htail, t, d₀, wh, hh, hwh, hcase⟩

end Tools.ShippingGen4FbInv
