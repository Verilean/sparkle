import Tools.ShippingSharedLeafNL
import Tools.ShippingMemClosesKidsT
import Tools.ShippingMachineClosesData
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
open Tools.ShippingMemCloses Tools.ShippingMachineClosesData
open Tools.ShippingInstTagged (originAt)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The machine synthesis does not fall back at the START world of the outermost entry** (`JQC O 1`, cache value
`{}`): the weaker, start-world-only form of `MachineClosesAtA`, which is all that the outermost entry uses. -/
def MachineClosesAtStart0 (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context)
    (cctx : Core.Context) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) w r w', JQC O 1 w → cv w = {} →
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w' → r ≠ none

/-- **A returning run of the OUTERMOST core entry (`D = 0`) of a machine, with the cache tracked.** The machine
synthesis starts in a `JQC O 1` world whose cache VALUE is `{}` (the clear `set {}`; the sets after it keep the
cache), and the entry's end world has the SAME cache value as the machine synthesis's end (the `finally` is
cache-neutral) and is `JQC O 0` once the machine synthesis ends in `JQC O 1`. -/
theorem core_run_tracked0' (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {c : Name} {shape : MachineShape}
    (entry : MachineDefines mctx mref cctx cref c shape)
    (closes : MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx c shape)
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
  have hne := closes (tenv := env) prof.isSome _ r w8 hw5.1 hw5.2 hmach
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

/-- `core_run_tracked0'` with the full `MachineClosesAtA` (the start-world form follows). -/
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
      JQC O 1 w9 ∧ cv w9 = {} ∧ (JQC O 1 w10 → JQC O 0 w1 ∧ cv w1 = cv w10) :=
  core_run_tracked0' O hA entry
    (fun b _ r _ hj _ hr' => closes b 1 _ r _ hj (Nat.le_refl 1) hr') hw hr

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

/-! ## The real `topshare` shape: FOUR call entries `[c₁, c₁, c₂, c₂]` (each call reads two fields) -/

/-- The data premises of ONE non-leaf callee `c` whose calls are leaves (the premises of
`synthesizeChild_nonleaf_miss` about the callee, bundled): `d.ok`, `hbody`, `hC`/`hdomB` (`∃ nDecl`), `hslots`,
`hins`, `hfne`, every call a non-memory leaf with `LeafOK`, no call is `c` itself, `entry`, `closes`. -/
def CalleeOK (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    (c : Name) (d : MachineData) : Prop :=
  d.ok = true ∧
  d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
  (∃ nDecl : Nat, d.callsOk nDecl = true ∧ ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain) ∧
  d.ss.length = d.shape.layout.slots.length ∧
  d.shape.insts ≠ [] ∧ d.shape.instFields ≠ [] ∧
  (∀ x ∈ d.shape.instTagged, x.2.child? = none ∧ LeafOK mctx mref cctx cref x.1) ∧
  (∀ k (hk : k < d.shape.insts.length), (d.shape.insts[k]).1 ≠ c) ∧
  MachineDefines mctx mref cctx cref c d.shape ∧
  MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c d.shape

/-- **Four calls `[c₁, c₁, c₂, c₂]` (wrap, wrap, wrap3, wrap3): the second call of each callee is a cache HIT.**
Four returning `synthesizeChild` runs in sequence from a `JQC O D` world with `CacheClosed`/`KeyTop` and both
callees absent: the end cache is `CacheCoh` with `y₁`, `y₂` at `c₁`, `c₂`, the repeated calls return the same
`y₁`, `y₂` (hits), the `hcross` shape holds, and the shared leaf's entry is inside both designs. -/
theorem topshare_quad (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {c₁ c₂ : Name} (hc12 : c₁ ≠ c₂)
    (d₁ d₂ : MachineData) (K₁ : CalleeOK O mctx cctx c₁ d₁) (K₂ : CalleeOK O mctx cctx c₂ d₂)
    (hc2not : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₂)
    {w w₁ w₁' w₂ w₂' : Void IO.RealWorld} {y₁ y₁' y₂ y₂' : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w))
    (hm₁ : (cv w).get? c₁ = none) (hm₂ : (cv w).get? c₂ = none)
    (h₁ : RunsTo (synthesizeChild c₁) mctx mref cctx cref w y₁ w₁)
    (h₁' : RunsTo (synthesizeChild c₁) mctx mref cctx cref w₁ y₁' w₁')
    (h₂ : RunsTo (synthesizeChild c₂) mctx mref cctx cref w₁' y₂ w₂)
    (h₂' : RunsTo (synthesizeChild c₂) mctx mref cctx cref w₂ y₂' w₂') :
    y₁' = y₁ ∧ y₂' = y₂ ∧
    JQC O D w₂' ∧ CacheClosed (cv w₂') ∧ KeyTop (cv w₂') ∧ CacheCoh (cv w₂') ∧
      (cv w₂').get? c₁ = some y₁ ∧ (cv w₂').get? c₂ = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      ∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w₂').get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules := by
  obtain ⟨ok₁, hbody₁, ⟨n₁, hC₁, hdomB₁⟩, hslots₁, hins₁, hfne₁, hleaf₁, hcne₁, entry₁, closes₁⟩ := K₁
  obtain ⟨ok₂, hbody₂, ⟨n₂, hC₂, hdomB₂⟩, hslots₂, hins₂, hfne₂, hleaf₂, hcne₂, entry₂, closes₂⟩ := K₂
  obtain ⟨hj1, hcl1, hk1, hext1, hget1, hkids1, hgrow1⟩ :=
    synthesizeChild_nonleaf_miss O hA hD d₁ ok₁ hbody₁ hC₁ hslots₁ hdomB₁ hins₁ hfne₁ hleaf₁ hcne₁
      entry₁ closes₁ hw hcl hk hm₁ h₁
  obtain ⟨hy1, hj1', hcv1'⟩ := synthesizeChild_hit O hA hj1 hget1 h₁'
  have hm₂' : (cv w₁').get? c₂ = none := by
    rw [hcv1']
    cases hq : (cv w₁).get? c₂ with
    | none => rfl
    | some q =>
      rcases hgrow1 c₂ q hq with h0 | h0 | h0
      · rw [hm₂] at h0; cases h0
      · exact absurd h0.symm hc12
      · obtain ⟨x, hx, hxc⟩ := List.mem_map.mp h0
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        exact absurd hxc (hc2not i hi)
  obtain ⟨hj2, hcl2, hk2, hext2, hget2, hkids2, -⟩ :=
    synthesizeChild_nonleaf_miss O hA hD d₂ ok₂ hbody₂ hC₂ hslots₂ hdomB₂ hins₂ hfne₂ hleaf₂ hcne₂
      entry₂ closes₂ hj1' (by rw [hcv1']; exact hcl1) (by rw [hcv1']; exact hk1) hm₂' h₂
  obtain ⟨hy2, hj2', hcv2'⟩ := synthesizeChild_hit O hA hj2 hget2 h₂'
  have hcoh : CacheCoh (cv w₂) :=
    cacheCoh_of_closed_topAgree hcl2 (cacheTopAgree_of_keyTop hk2)
  have hy1c : (cv w₂).get? c₁ = some y₁ := hext2 c₁ y₁ (by rw [hcv1']; exact hget1)
  rw [hcv2'] at *
  refine ⟨hy1, hy2, hj2', hcl2, hk2, hcoh, hy1c, hget2,
    fun a ha b hb hab => hcoh c₁ y₁ c₂ y₂ hy1c hget2 a ha b hb hab, ?_⟩
  intro k₁ hk₁ k₂ hk₂ hn
  obtain ⟨e₁, he₁, a, ha, han⟩ := hkids1 k₁ hk₁
  obtain ⟨e₂, he₂, b, hb, hbn⟩ := hkids2 k₂ hk₂
  have he₁' : (cv w₂).get? (d₁.shape.insts[k₁]).1 = some e₁ := hext2 _ e₁ (by rw [hcv1']; exact he₁)
  have he₂' : (cv w₂).get? (d₂.shape.insts[k₂]).1 = some e₂ := he₂
  rw [← hn] at he₂'
  have hee : e₂ = e₁ := Option.some.inj (he₂'.symm.trans he₁')
  subst hee
  refine ⟨e₂, he₁', ?_, ?_⟩
  · have : a = e₂.1 := hcoh c₁ y₁ _ e₂ hy1c he₁' a (List.mem_cons_of_mem _ ha) e₂.1
      (List.mem_cons_self ..) han
    rw [← this]; exact ha
  · have : b = e₂.1 := hcoh c₂ y₂ _ e₂ hget2 he₂ b (List.mem_cons_of_mem _ hb) e₂.1
      (List.mem_cons_self ..) hbn
    rw [← this]; exact hb

/-- **The parent's closing over the real `topshare` call list `[(c₁,o₁),(c₁,o₁'),(c₂,o₂),(c₂,o₂')]`.** A returning
run of `closeInstsGM` returns the pure `closeInstsG` of `[y₁, y₁, y₂, y₂]`, with the `hcross` shape and the
shared-leaf clause of `topshare_quad`. -/
theorem topshare_closing4 (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {c₁ c₂ : Name} (hc12 : c₁ ≠ c₂) {o₁ o₁' o₂ o₂' : InstOrigin}
    (ho₁ : o₁.child? = none) (ho₁' : o₁'.child? = none) (ho₂ : o₂.child? = none) (ho₂' : o₂'.child? = none)
    {shape : MachineShape} (hP : shape.instTagged = [(c₁, o₁), (c₁, o₁'), (c₂, o₂), (c₂, o₂')])
    (d₁ d₂ : MachineData) (K₁ : CalleeOK O mctx cctx c₁ d₁) (K₂ : CalleeOK O mctx cctx c₂ d₂)
    (hc2not : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₂)
    {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQC O D w) (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w))
    (hm₁ : (cv w).get? c₁ = none) (hm₂ : (cv w).get? c₂ = none)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ y₁ y₂ : Res, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields [y₁, y₁, y₂, y₂] (m₀, d₀) ∧
      JQC O D w' ∧ CacheClosed (cv w') ∧ KeyTop (cv w') ∧ CacheCoh (cv w') ∧
      (cv w').get? c₁ = some y₁ ∧ (cv w').get? c₂ = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      ∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w').get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, wa, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨hwa, rfl⟩ := triple_runs (tripleC_synthRead O hA D) hw hget
  have hcva : cv wa = cv w := by
    have hk0 := O.frame hA _ FramedA.synthGet w hw.1.1
    rw [endW_of_runs hget] at hk0
    exact hk0.1
  dsimp only at hr
  obtain ⟨children, wb, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  rw [hP] at hch
  simp only [List.mapM, List.mapM.loop, ho₁, ho₁', ho₂, ho₂'] at hch
  obtain ⟨y₁, wm, h1, hch⟩ := RunsTo.bind hch
  obtain ⟨y₁', wm', h1', hch⟩ := RunsTo.bind hch
  obtain ⟨y₂, wn, h2, hch⟩ := RunsTo.bind hch
  obtain ⟨y₂', wn', h2', hch⟩ := RunsTo.bind hch
  obtain ⟨hchildren, rfl⟩ := RunsTo.pure_world hch
  have hcl' : CacheClosed (cv wa) := by rw [hcva]; exact hcl
  have hk' : KeyTop (cv wa) := by rw [hcva]; exact hk
  have hm₁' : (cv wa).get? c₁ = none := by rw [hcva]; exact hm₁
  have hm₂' : (cv wa).get? c₂ = none := by rw [hcva]; exact hm₂
  obtain ⟨e1, e2, hj, hc, hkt, hcoh, hg1, hg2, hcross, hshared⟩ :=
    topshare_quad O hA hD hc12 d₁ d₂ K₁ K₂ hc2not hwa hcl' hk' hm₁' hm₂' h1 h1' h2 h2'
  have hlist : children = [y₁, y₁, y₂, y₂] := by rw [hchildren, e1, e2]; rfl
  subst hlist
  exact ⟨y₁, y₂, heq, hj, hc, hkt, hcoh, hg1, hg2, hcross, hshared⟩

/-- **The parent's own entry run (`D = 0`) to the closing's conclusion, for the real `topshare` call list
`[c₁, c₁, c₂, c₂]`.** As `topshare_entry_run`; the start world of the closing (`JQC O 1`, cache `{}`: closed,
`KeyTop`, both callees absent) is DERIVED from the parent's core run (the clear `set {}`, then the harness keeps the
cache value). Premises (named): the parent's data (`dp`: `ok`, `hbody`, `hins`, `hfne`), `entryP`, `closesP`,
`CalleeOK` of each callee, `c₁ ≠ c₂`, `hc2not`. -/
theorem topshare_entry_run4 (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {c c₁ c₂ : Name} (hc12 : c₁ ≠ c₂) {o₁ o₁' o₂ o₂' : InstOrigin}
    (ho₁ : o₁.child? = none) (ho₁' : o₁'.child? = none) (ho₂ : o₂.child? = none) (ho₂' : o₂'.child? = none)
    (dp : MachineData) (okp : dp.ok = true)
    (hbodyp : dp.shape.body = quote dp.dom
      (fun j => inputExpr dp.shape.binders.length (dp.bpos j))
      (fun j => inputExpr dp.shape.binders.length (dp.vpos j)) dp.packed)
    (hinsp : dp.shape.insts ≠ []) (hfnep : dp.shape.instFields ≠ [])
    (hP : dp.shape.instTagged = [(c₁, o₁), (c₁, o₁'), (c₂, o₂), (c₂, o₂')])
    (entryP : MachineDefines mctx mref cctx cref c dp.shape)
    (closesP : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c dp.shape)
    (d₁ d₂ : MachineData) (K₁ : CalleeOK O mctx cctx c₁ d₁) (K₂ : CalleeOK O mctx cctx c₂ d₂)
    (hc2not : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₂)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 : Void IO.RealWorld),
      closeLets dp.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dp.shape) dp.shape.insts.length
        dp.shape.layout.slots.length (t.inputs.map (·.name)) (dp.shape.insts.map (·.2.1))
        dp.shape.instFields [y₁, y₁, y₂, y₂] (closeMachine dp.shape.layout t', d₀) ∧
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
    topshare_closing4 O hA (D := 1) Nat.one_ne_zero hc12 ho₁ ho₁' ho₂ ho₂' hP d₁ d₂ K₁ K₂ hc2not hj1
      (by rw [hcvw1]; exact cacheClosed_empty) (by rw [hcvw1]; exact keyTop_empty)
      (by rw [hcvw1]; simp) (by rw [hcvw1]; simp) hclose
  obtain ⟨hjc, hcvc⟩ := htl hj
  obtain ⟨hj2, hcv2⟩ := htail hjc
  exact ⟨y₁, y₂, t, t', d₀, M, Dg, w10, hlets, hrr, hj2, hcv2.trans hcvc, hc, hk, hcoh, hg1, hg2,
    hcross, hshared⟩

/-! ## `MachineClosesAtStart0` of the parent, from the closing's own facts -/

theorem insts_names4 {dp : MachineData} {c₁ c₂ : Name} {o₁ o₁' o₂ o₂' : InstOrigin}
    (hP : dp.shape.instTagged = [(c₁, o₁), (c₁, o₁'), (c₂, o₂), (c₂, o₂')]) :
    ∀ k (hk : k < dp.shape.insts.length), (dp.shape.insts[k]).1 = if k < 2 then c₁ else c₂ := by
  intro k hk
  obtain ⟨hkT, he⟩ := instTagged_getAt dp.shape hk
  have e2 : dp.shape.instTagged[k]? = some ((dp.shape.insts[k]).1, dp.shape.instOrigins.getD k .ord) := by
    rw [List.getElem?_eq_getElem hkT, he]
  have hk4 : k < 4 := by
    have h := hkT
    rw [hP] at h
    simpa using h
  rw [hP] at e2
  rcases k with _ | _ | _ | _ | k
  all_goals first
    | (exfalso; omega)
    | (simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
        Prod.mk.injEq] at e2; simpa using e2.1.symm)

/-- **The machine synthesis of the parent `topshare` (calls `[c₁, c₁, c₂, c₂]`) does not fall back at the entry's start
world.** From a `JQC O 1` world with cache value `{}`, a run of `synthesizeMachineCertified` does not return `none`:
`closeLets` is accepted (`letsClose_of_data`), and the closing returns `closeInstsG … [y₁, y₁, y₂, y₂]` (`topshare_closing4`)
which is `some` by `closeInstsG_of_kidsPT`, whose children premises are: the interface of each result
(`ChildIfaceP`, from `RealChildA`: the end cache is a `CacheInvA` cache), the same-name pair (`hpair`: the repeated call
is the same child), and `hcross` (the cross-callee agreement of `topshare_quad`). The data facts about the parent
(`hargsN`, `hfieldOut`, `hfieldsNd`, `hsep`, `hparent`, `hfresh`, `hparentD`, `hmk`, `hlen4`) are premises, stated for
the group functions `nameK`, `nk`, `outsK`, `namesK`. -/
theorem machineSynth_ne_none4 (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {c c₁ c₂ : Name} (hc12 : c₁ ≠ c₂) {o₁ o₁' o₂ o₂' : InstOrigin}
    (ho₁ : o₁.child? = none) (ho₁' : o₁'.child? = none) (ho₂ : o₂.child? = none) (ho₂' : o₂'.child? = none)
    (dp : MachineData) (okp : dp.ok = true)
    (hbodyp : dp.shape.body = quote dp.dom
      (fun j => inputExpr dp.shape.binders.length (dp.bpos j))
      (fun j => inputExpr dp.shape.binders.length (dp.vpos j)) dp.packed)
    (haliasp : dp.letsAliasOk = true)
    {nDecl : Nat} (hCp : dp.callsOk nDecl = true)
    (hslotsp : dp.ss.length = dp.shape.layout.slots.length)
    (hdomBp : ∀ b ∈ dp.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hinsp : dp.shape.insts ≠ []) (hfnep : dp.shape.instFields ≠ [])
    (hP : dp.shape.instTagged = [(c₁, o₁), (c₁, o₁'), (c₂, o₂), (c₂, o₂')])
    (hlen4 : dp.shape.insts.length = 4)
    (hmk : ∀ k (hk : k < dp.shape.insts.length), memKey (originAt dp.shape k) = none)
    (d₁ d₂ : MachineData) (K₁ : CalleeOK O mctx cctx c₁ d₁) (K₂ : CalleeOK O mctx cctx c₂ d₂)
    (hc2not : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₂)
    (nameK : Nat → String) (nk : Nat → Nat) (outsK : Nat → List String) (namesK : Nat → List String)
    (hI₁ : ∀ y : Res, RealChildA O c₁ y → ∀ k, k < 2 →
      ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
    (hI₂ : ∀ y : Res, RealChildA O c₂ y → ∀ k, 2 ≤ k → k < 4 →
      ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < dp.shape.insts.length), nk k = (dp.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < dp.shape.insts.length → dp.shape.instFields.getD k "" ∈ outsK k)
    (hfieldsNd : ∀ (k : Nat) (hk : k < dp.shape.insts.length) (k' : Nat)
      (hk' : k' < dp.shape.insts.length), (dp.shape.insts[k]).1 = (dp.shape.insts[k']).1 →
      memKey (originAt dp.shape k) = memKey (originAt dp.shape k') →
      (dp.shape.insts[k]).2.1 = (dp.shape.insts[k']).2.1 →
      dp.shape.instFields.getD k "" = dp.shape.instFields.getD k' "" → k = k')
    (hsep : ∀ (k : Nat) (hk : k < dp.shape.insts.length) (k' : Nat)
      (hk' : k' < dp.shape.insts.length), nameK k = nameK k' →
      (dp.shape.insts[k]).1 = (dp.shape.insts[k']).1 ∧
        memKey (originAt dp.shape k) = memKey (originAt dp.shape k'))
    (hparent : ∀ (k : Nat), k < dp.shape.insts.length → nameK k ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (hfresh : ∀ (gi : Nat) (k : Nat), k < dp.shape.insts.length → ∀ o ∈ dp.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{nameK k}")
    (hparentD : ∀ (k : Nat), k < dp.shape.insts.length → (Sparkle.IR.ModuleName.ofDecl c) ∉ namesK k)
    {tenv : Lean.Environment} {b : Bool} {w9 w10 : Void IO.RealWorld}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    (hw : JQC O 1 w9) (hcv : cv w9 = {})
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c dp.shape)
      mctx mref cctx cref w9 r w10) : r ≠ none := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (mixed_keepsLeaf O hA (stableK O 1 (cv w9))
    (fun e hint top named => translateExprToWire tenv e hint top named) b c
    dp.shape.binders dp.shape.body
    (leafTranslatorKeeps_of_machineData O hA (stableK O 1 (cv w9)) dp okp hbodyp tenv))) ⟨hw, rfl⟩ run
  dsimp only at hr
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp
    (letsClose_of_data dp okp hbodyp haliasp mctx mref cctx cref (profLogIO b) w9 t d' w1 run)
  rw [ht'] at hr
  dsimp only at hr
  split at hr
  · rename_i hi
    exact absurd hi hinsp
  · rename_i hi
    split at hr
    · rename_i hf
      exact absurd (List.isEmpty_iff.mp hf) hfnep
    · rename_i hf
      have hcvw1 : cv w1 = {} := hw1.2.trans hcv
      obtain ⟨y₁, y₂, hrr, hj, hc, hkt, hcoh, hg1, hg2, hcross, -⟩ :=
        topshare_closing4 O hA (D := 1) Nat.one_ne_zero hc12 ho₁ ho₁' ho₂ ho₂' hP d₁ d₂ K₁ K₂ hc2not hw1.1
          (by rw [hcvw1]; exact cacheClosed_empty) (by rw [hcvw1]; exact keyTop_empty)
          (by rw [hcvw1]; simp) (by rw [hcvw1]; simp) hr
      have hreal₁ : RealChildA O c₁ y₁ := hj.2 c₁ y₁ hg1
      have hreal₂ : RealChildA O c₂ y₂ := hj.2 c₂ y₂ hg2
      have hnm := insts_names4 hP
      have hch : ∀ k, ([y₁, y₁, y₂, y₂] : List Res)[k]? = if k < 2 then some y₁ else if k < 4 then some y₂ else none := by
        intro k
        rcases k with _ | _ | _ | _ | k
        · simp
        · simp
        · simp
        · simp
        · have h2 : ¬ (k + 1 + 1 + 1 + 1 < 2) := by omega
          have h4 : ¬ (k + 1 + 1 + 1 + 1 < 4) := by omega
          rw [if_neg h2, if_neg h4]
          simp
      have hsome := closeInstsG_of_kidsPT (tenv := tenv) (declName := c) dp okp hbodyp hCp hslotsp hdomBp
        (logProf := profLogIO b) (t := t) (t' := t') (d₀ := d') (children := [y₁, y₁, y₂, y₂])
        run.mreturns ht' (by rw [hlen4]; rfl) nameK nk outsK namesK
        (by
          intro k c' hk
          rw [hch] at hk
          by_cases h2 : k < 2
          · rw [if_pos h2] at hk
            rw [← Option.some.inj hk]
            exact hI₁ y₁ hreal₁ k h2
          · rw [if_neg h2] at hk
            by_cases h4 : k < 4
            · rw [if_pos h4] at hk
              rw [← Option.some.inj hk]
              exact hI₂ y₂ hreal₂ k (by omega) h4
            · rw [if_neg h4] at hk
              cases hk)
        (by
          intro i j hi hj hnm' hmk'
          have e1 := hnm i hi
          have e2 := hnm j hj
          rw [hch, hch]
          by_cases h1 : i < 2 <;> by_cases h2 : j < 2
          · rw [if_pos h1, if_pos h2]
          · rw [if_pos h1] at e1
            rw [if_neg h2] at e2
            exact absurd (e1.symm.trans (hnm'.trans e2)) hc12
          · rw [if_neg h1] at e1
            rw [if_pos h2] at e2
            exact absurd (e2.symm.trans (hnm'.symm.trans e1)) hc12
          · have hi4 : i < 4 := hlen4 ▸ hi
            have hj4 : j < 4 := hlen4 ▸ hj
            rw [if_neg h1, if_pos hi4, if_neg h2, if_pos hj4])
        (by
          intro i j hi hj ci cj hci hcj hne a ha b hb hab
          have e1 := hnm i hi
          have e2 := hnm j hj
          rw [hch] at hci hcj
          by_cases h1 : i < 2 <;> by_cases h2 : j < 2
          · exact absurd ⟨by rw [e1, e2, if_pos h1, if_pos h2], by rw [hmk i hi, hmk j hj]⟩ hne
          · rw [if_pos h1] at hci
            rw [if_neg h2] at hcj
            have hj4 : j < 4 := hlen4 ▸ hj
            rw [if_pos hj4] at hcj
            rw [← Option.some.inj hci] at ha
            rw [← Option.some.inj hcj] at hb
            exact hcross a ha b hb hab
          · rw [if_neg h1] at hci
            rw [if_pos h2] at hcj
            have hi4 : i < 4 := hlen4 ▸ hi
            rw [if_pos hi4] at hci
            rw [← Option.some.inj hci] at ha
            rw [← Option.some.inj hcj] at hb
            exact (hcross b hb a ha hab.symm).symm
          · exact absurd ⟨by rw [e1, e2, if_neg h1, if_neg h2], by rw [hmk i hi, hmk j hj]⟩ hne)
        hargsN hfieldOut hfieldsNd hsep hparent hfresh hparentD
      intro h
      rw [h] at hrr
      rw [← hrr] at hsome
      simp at hsome

/-- **`topshare_entry_run4` with the START-WORLD form of the parent's no-fallback premise** (`MachineClosesAtStart0`,
instead of `MachineClosesAtA` at every `JQC` world with any cache); `machineSynth_ne_none4` derives it for `topshare`. -/
theorem topshare_entry_run4' (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {c c₁ c₂ : Name} (hc12 : c₁ ≠ c₂) {o₁ o₁' o₂ o₂' : InstOrigin}
    (ho₁ : o₁.child? = none) (ho₁' : o₁'.child? = none) (ho₂ : o₂.child? = none) (ho₂' : o₂'.child? = none)
    (dp : MachineData) (okp : dp.ok = true)
    (hbodyp : dp.shape.body = quote dp.dom
      (fun j => inputExpr dp.shape.binders.length (dp.bpos j))
      (fun j => inputExpr dp.shape.binders.length (dp.vpos j)) dp.packed)
    (hinsp : dp.shape.insts ≠ []) (hfnep : dp.shape.instFields ≠ [])
    (hP : dp.shape.instTagged = [(c₁, o₁), (c₁, o₁'), (c₂, o₂), (c₂, o₂')])
    (entryP : MachineDefines mctx mref cctx cref c dp.shape)
    (closes0 : MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx c dp.shape)
    (d₁ d₂ : MachineData) (K₁ : CalleeOK O mctx cctx c₁ d₁) (K₂ : CalleeOK O mctx cctx c₂ d₂)
    (hc2not : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₂)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 : Void IO.RealWorld),
      closeLets dp.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dp.shape) dp.shape.insts.length
        dp.shape.layout.slots.length (t.inputs.map (·.name)) (dp.shape.insts.map (·.2.1))
        dp.shape.instFields [y₁, y₁, y₂, y₂] (closeMachine dp.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? c₁ = some y₁ ∧ (cv w10).get? c₂ = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      ∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules := by
  obtain ⟨M, Dg, wc, hcore, htail, -⟩ := full_run_tracked O hA (D := 0) h
  obtain ⟨tenv, b, w9, w10, hmach, hw9, hc9, htl⟩ := core_run_tracked0' O hA entryP closes0 hw hcore
  obtain ⟨t, t', d₀, w1, -, hlets, hj1, hcv1, hclose⟩ :=
    machineSynth_closing_split O hA (D' := 1) dp okp hbodyp hinsp hfnep hw9 hmach
  have hcvw1 : cv w1 = {} := hcv1.trans hc9
  obtain ⟨y₁, y₂, hrr, hj, hc, hk, hcoh, hg1, hg2, hcross, hshared⟩ :=
    topshare_closing4 O hA (D := 1) Nat.one_ne_zero hc12 ho₁ ho₁' ho₂ ho₂' hP d₁ d₂ K₁ K₂ hc2not hj1
      (by rw [hcvw1]; exact cacheClosed_empty) (by rw [hcvw1]; exact keyTop_empty)
      (by rw [hcvw1]; simp) (by rw [hcvw1]; simp) hclose
  obtain ⟨hjc, hcvc⟩ := htl hj
  obtain ⟨hj2, hcv2⟩ := htail hjc
  exact ⟨y₁, y₂, t, t', d₀, M, Dg, w10, hlets, hrr, hj2, hcv2.trans hcvc, hc, hk, hcoh, hg1, hg2,
    hcross, hshared⟩

end Tools.ShippingTopShareRun

#print axioms Tools.ShippingTopShareRun.core_run_tracked0'
#print axioms Tools.ShippingTopShareRun.core_run_tracked0
#print axioms Tools.ShippingTopShareRun.machineSynth_closing_split
#print axioms Tools.ShippingTopShareRun.topshare_entry_run
#print axioms Tools.ShippingTopShareRun.topshare_quad
#print axioms Tools.ShippingTopShareRun.topshare_closing4
#print axioms Tools.ShippingTopShareRun.topshare_entry_run4
#print axioms Tools.ShippingTopShareRun.machineSynth_ne_none4
#print axioms Tools.ShippingTopShareRun.topshare_entry_run4'
