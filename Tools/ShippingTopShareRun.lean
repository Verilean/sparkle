import Tools.ShippingSharedLeafNL
-- BUILT (unit SR9): t1 exit 0; see REPORT-SR9.md for the final-SHA rebuild.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # The parent's own run connected to its closing (unit SR9, L8ao)

* `core_run_tracked0`: the OUTERMOST entry (`D = 0`) of a machine: the clear `set {}` then the body starts in a
  `JQC O 1` world whose cache VALUE is `{}`; the `finally` is cache-neutral.
* `machineSynth_closing_split`: the machine synthesis of a machine with calls, any callees: the harness keeps the
  cache value, and the rest of the run is a run of `closeInstsGM` from a `JQC O D'` world with the same cache value.
* `topshare_entry_run`: ONE theorem from the parent's `synthesizeCombinational` run at `D = 0` to the conclusion of
  `topshare_closing` (the start world `JQC`/`CacheClosed`/`KeyTop`/absence is DERIVED: the cache is `{}`).
Not done here: instantiation at the declarations (`TopShareInstTest`); the data premises stay premises. -/

namespace Tools.ShippingTopShareRun
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildVCA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPinC
open Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit
open Tools.ShippingSharedLeafExt Tools.ShippingLeafKeepCache Tools.ShippingLeafBodyCi Tools.ShippingLeafTermKeeps
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses Tools.ShippingSeqChildIface Tools.ShippingSeqChildIfaceA
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMixedEntrySoundness
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingChildRunAKids Tools.ShippingMachineOutcomeA3 Tools.ShippingChildCoreC Tools.ShippingChildVertA
open Tools.ShippingClosedKinds Tools.ShippingSharedLeafNL

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A returning run of the OUTERMOST core entry (`D = 0`) of a machine, with the cache tracked.** The machine
synthesis starts in a `JQC O 1` world whose cache VALUE is `{}` (the clear `set {}`; the sets after it keep the
cache), and the entry's end world has the SAME cache value as the machine synthesis's end (the `finally` is
cache-neutral) and is `JQC O 0` once the machine synthesis ends in `JQC O 1`. -/
theorem core_run_tracked0 (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {c : Name} {shape : MachineShape}
    (entry : MachineDefines mctx mref cctx cref c shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c shape)
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {Dg : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hr : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, Dg) w1) :
    ∃ (tenv : Lean.Environment) (b : Bool) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
        mctx mref cctx cref w9 (some (M, Dg)) w10 ∧
      JQC O 1 w9 ∧ cv w9 = {} ∧ (JQC O 1 w10 → JQC O 0 w1 ∧ cv w1 = cv w10) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at hr
  simp only [Bool.false_eq_true, ↓reduceIte] at hr
  obtain ⟨prof, wa, s1, hr⟩ := RunsTo.bind hr
  have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O 0) (FramedA.ioEnv _))) hw s1
  obtain ⟨_, wb, s2, hr⟩ := RunsTo.bind hr
  have hw := triple_runs (keeps_iff.mp (keepsA_diag O hA (stableA_JQC O 0)
    (Diag.profLog prof.isSome _))) hw s2
  obtain ⟨d, wc, s3, hr⟩ := RunsTo.bind hr
  have hd := triple_runs (tripleA_depthGet O hA (stableA_JQC O 0)) hw s3
  have hdD : d = 0 := hd.2.trans hd.1.1.2.2
  have hw := hd.1
  subst hdD
  rcases RunsTo.ite hr with hr | hr
  · obtain ⟨_, _, ht, _⟩ := RunsTo.bind hr
    exact (throwError_not_runs _ ht).elim
  simp only [↓reduceIte, beq_self_eq_true] at hr
  peelP hr; peelP hr; peelP hr; peelP hr; peelP hr; peelP hr; peelP hr
  peelF O hA (stableA_JQC O 0) hr hw; peelF O hA (stableA_JQC O 0) hr hw
  peelF O hA (stableA_JQC O 0) hr hw; peelF O hA (stableA_JQC O 0) hr hw
  obtain ⟨_, _, step, hr⟩ := RunsTo.bind hr
  have hw := triple_runs (Triple.conseq (tripleK_clear O hA 0 (R := fun _ _ => False))
    (fun _ h => h.1) (fun _ _ h => h) (fun _ _ h => h)) hw step
  clear step
  peelF O hA (stableK O 0 {}) hr hw; peelF O hA (stableK O 0 {}) hr hw
  peelF O hA (stableK O 0 {}) hr hw; peelF O hA (stableK O 0 {}) hr hw
  peelF O hA (stableK O 0 {}) hr hw; peelF O hA (stableK O 0 {}) hr hw
  peelF O hA (stableK O 0 {}) hr hw
  obtain ⟨_, _, step, hr⟩ := RunsTo.bind hr
  have hw := triple_runs (tripleK_depthSet O hA 0 (0 + 1) {} (R := fun _ _ => False)) hw step
  clear step
  obtain ⟨w4, u, hbody, hfin⟩ := RunsTo.try_finally' hr
  obtain ⟨ci, w2, hget, hbody⟩ := RunsTo.bind hbody
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableK O (0 + 1) {})
    (FramedA.constInfo _))) hw hget
  obtain ⟨env, w2b, henv, hbody⟩ := RunsTo.bind hbody
  have hw2b := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableK O (0 + 1) {})
    FramedA.env)) hw2 henv
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ hget henv henv
  unfold synthesizeFromConst at hbody
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hbody
  obtain ⟨envR, w5, henv', hbody⟩ := RunsTo.bind hbody
  have hw5 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableK O (0 + 1) {})
    FramedA.env)) hw2b henv'
  obtain ⟨mach, w6, hp, hbody⟩ := RunsTo.bind hbody
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ hget henv henv'
  rw [hshape] at hbody
  dsimp only at hbody
  obtain ⟨r, w8, hmach, hbody⟩ := RunsTo.bind hbody
  have hne := closes (tenv := env) prof.isSome (0 + 1) _ r w8 hw5.1
    (Nat.succ_le_succ (Nat.zero_le 0)) hmach
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    dsimp only at hbody
    obtain ⟨_, wl, s1', hbody⟩ := RunsTo.bind hbody
    obtain ⟨_, wm, s2', hbody⟩ := RunsTo.bind hbody
    obtain ⟨hres, rfl⟩ := RunsTo.pure_world hbody
    cases hres
    refine ⟨env, prof.isSome, w6, w8, hmach, hw5.1, hw5.2, ?_⟩
    intro hJ8
    have h1 := triple_runs (keeps_iff.mp (keepsA_diag O hA (stableK O (0 + 1) (cv w8))
      (Diag.profLog prof.isSome _))) ⟨hJ8, rfl⟩ s1'
    have h2 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableK O (0 + 1) (cv w8))
      (FramedA.sideModify _ .subModule))) h1 s2'
    have h3 := triple_runs (finK O hA 0 (cv w8) _ _ _ _ _ _ _) h2 hfin
    exact ⟨h3.1, h3.2⟩

/-- **The machine synthesis of a machine with calls (any callees), split at its closing.** From a `JQC O D'`
world, a returning run of `synthesizeMachineCertified` of `d.shape` to `some (M, Dg)` is: the mixed synthesis
(the harness keeps the cache VALUE: the translator on the quoted body, `leafTranslatorKeeps_of_machineData` at
`JK`), the pure `closeLets`, then a returning run of `closeInstsGM` from a `JQC O D'` world with the same cache
value as the start. -/
theorem machineSynth_closing_split (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D' : Nat} {tenv : Lean.Environment} {b : Bool} {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hins : d.shape.insts ≠ []) (hfne : d.shape.instFields ≠ [])
    {w9 w10 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {Dg : Sparkle.IR.AST.Design}
    (hw : JQC O D' w9)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c d.shape)
      mctx mref cctx cref w9 (some (M, Dg)) w10) :
    ∃ (t t' d₀ : _) (w1 : Void IO.RealWorld), MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c
        d.shape.binders d.shape.body) (t, d₀) ∧
      closeLets d.shape.layout.lets t = some t' ∧ JQC O D' w1 ∧ cv w1 = cv w9 ∧
      RunsTo (closeInstsGM d.shape t (closeMachine d.shape.layout t') d₀) mctx mref cctx cref w1
        (some (M, Dg)) w10 := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (mixed_keepsLeaf O hA (stableK O D' (cv w9))
    (fun e hint top named => translateExprToWire tenv e hint top named) b c
    d.shape.binders d.shape.body
    (leafTranslatorKeeps_of_machineData O hA (stableK O D' (cv w9)) d ok hbody tenv))) ⟨hw, rfl⟩ run
  dsimp only at hr
  split at hr
  · rename_i t' hcl'
    split at hr
    · rename_i hi
      exact absurd hi hins
    · rename_i hi
      split at hr
      · rename_i hf
        exact absurd (List.isEmpty_iff.mp hf) hfne
      · rename_i hf
        exact ⟨t, t', d', w1, run.mreturns, hcl', hw1.1, hw1.2, hr⟩
  · have := RunsTo.pure_eq hr
    cases this

/-- **ONE theorem from the parent's own entry run (`D = 0`) to the closing's conclusion.** A returning run of
`synthesizeCombinational c` of a parent whose machine has the calls `[(c₁, o₁), (c₂, o₂)]` (non-memory origins),
started in a `JQC O 0` world: the entry's clear and the harness's cache-keeping give the closing's start world
(`JQC O 1`, cache `{}`: `CacheClosed`, `KeyTop`, both callees absent are DERIVED, not premises), and
`topshare_closing` applies. Conclusion: the machine synthesis's result is the pure `closeInstsG` of `[y₁, y₂]`,
the end cache is `CacheCoh` with `y₁`, `y₂` at `c₁`, `c₂`, the `hcross` shape holds, the shared leaf's entry is in
both designs, and the entry's end world is `JQC O 0` with the cache of the closing's end. Premises (named): the
parent's data (`dp`: `ok`, `hbody`, `hins`, `hfne`), `entryP`, `closesP`, and for each callee exactly those of
`topshare_closing`. -/
theorem topshare_entry_run (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {c c₁ c₂ : Name} (hc12 : c₁ ≠ c₂) {o₁ o₂ : InstOrigin}
    (ho₁ : o₁.child? = none) (ho₂ : o₂.child? = none)
    (dp : MachineData) (okp : dp.ok = true)
    (hbodyp : dp.shape.body = quote dp.dom
      (fun j => inputExpr dp.shape.binders.length (dp.bpos j))
      (fun j => inputExpr dp.shape.binders.length (dp.vpos j)) dp.packed)
    (hinsp : dp.shape.insts ≠ []) (hfnep : dp.shape.instFields ≠ [])
    (hP : dp.shape.instTagged = [(c₁, o₁), (c₂, o₂)])
    (entryP : MachineDefines mctx mref cctx cref c dp.shape)
    (closesP : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c dp.shape)
    (d₁ d₂ : MachineData) (ok₁ : d₁.ok = true) (ok₂ : d₂.ok = true)
    (hbody₁ : d₁.shape.body = quote d₁.dom
      (fun j => inputExpr d₁.shape.binders.length (d₁.bpos j))
      (fun j => inputExpr d₁.shape.binders.length (d₁.vpos j)) d₁.packed)
    (hbody₂ : d₂.shape.body = quote d₂.dom
      (fun j => inputExpr d₂.shape.binders.length (d₂.bpos j))
      (fun j => inputExpr d₂.shape.binders.length (d₂.vpos j)) d₂.packed)
    {n₁ n₂ : Nat} (hC₁ : d₁.callsOk n₁ = true) (hC₂ : d₂.callsOk n₂ = true)
    (hslots₁ : d₁.ss.length = d₁.shape.layout.slots.length)
    (hslots₂ : d₂.ss.length = d₂.shape.layout.slots.length)
    (hdomB₁ : ∀ b ∈ d₁.shape.binders.drop n₁, b.2 ≠ .domain)
    (hdomB₂ : ∀ b ∈ d₂.shape.binders.drop n₂, b.2 ≠ .domain)
    (hins₁ : d₁.shape.insts ≠ []) (hins₂ : d₂.shape.insts ≠ [])
    (hfne₁ : d₁.shape.instFields ≠ []) (hfne₂ : d₂.shape.instFields ≠ [])
    (hleaf₁ : ∀ x ∈ d₁.shape.instTagged, x.2.child? = none ∧ LeafOK mctx mref cctx cref x.1)
    (hleaf₂ : ∀ x ∈ d₂.shape.instTagged, x.2.child? = none ∧ LeafOK mctx mref cctx cref x.1)
    (hcne₁ : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₁)
    (hcne₂ : ∀ k (hk : k < d₂.shape.insts.length), (d₂.shape.insts[k]).1 ≠ c₂)
    (hc2not : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₂)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (closes₁ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c₁ d₁.shape)
    (closes₂ : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c₂ d₂.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 : Void IO.RealWorld),
      closeLets dp.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dp.shape) dp.shape.insts.length
        dp.shape.layout.slots.length (t.inputs.map (·.name)) (dp.shape.insts.map (·.2.1))
        dp.shape.instFields [y₁, y₂] (closeMachine dp.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? c₁ = some y₁ ∧ (cv w10).get? c₂ = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      ∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules := by
  obtain ⟨M, Dg, wc, hcore, htail, -⟩ := full_run_tracked O hA (D := 0) h
  obtain ⟨tenv, b, w9, w10, hmach, hw9, hc9, htl⟩ := core_run_tracked0 O hA entryP closesP hw hcore
  obtain ⟨t, t', d₀, w1, -, hlets, hj1, hcv1, hclose⟩ :=
    machineSynth_closing_split O hA (D' := 1) dp okp hbodyp hinsp hfnep hw9 hmach
  have hcvw1 : cv w1 = {} := hcv1.trans hc9
  obtain ⟨y₁, y₂, hrr, hj, hc, hk, hcoh, hg1, hg2, hcross, hshared⟩ :=
    topshare_closing O hA (D := 1) Nat.one_ne_zero hc12 ho₁ ho₂ hP d₁ d₂ ok₁ ok₂ hbody₁ hbody₂ hC₁ hC₂
      hslots₁ hslots₂ hdomB₁ hdomB₂ hins₁ hins₂ hfne₁ hfne₂ hleaf₁ hleaf₂ hcne₁ hcne₂ hc2not
      entry₁ entry₂ closes₁ closes₂ hj1
      (by rw [hcvw1]; exact cacheClosed_empty) (by rw [hcvw1]; exact keyTop_empty)
      (by rw [hcvw1]; simp) (by rw [hcvw1]; simp) hclose
  obtain ⟨hjc, hcvc⟩ := htl hj
  obtain ⟨hj2, hcv2⟩ := htail hjc
  exact ⟨y₁, y₂, t, t', d₀, M, Dg, w10, hlets, hrr, hj2, hcv2.trans hcvc, hc, hk, hcoh, hg1, hg2,
    hcross, hshared⟩

end Tools.ShippingTopShareRun

#print axioms Tools.ShippingTopShareRun.core_run_tracked0
#print axioms Tools.ShippingTopShareRun.machineSynth_closing_split
#print axioms Tools.ShippingTopShareRun.topshare_entry_run
