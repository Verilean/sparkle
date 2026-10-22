import Tools.ShippingSharedLeafExt
import Tools.ShippingCallsMemPinned
import Tools.ShippingLeafTermKeeps
import Tools.ShippingChildRunAKids
import Tools.ShippingMachineOutcomeA3
import Tools.ShippingClosedKinds
import Tools.ShippingMachineDepthRunR
-- UNBUILT (unit SR8, part A): run names / exits are in REPORT-SR8.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # Shared leaf: the leaf calls of a NON-leaf callee's closing, as real runs (unit SR8, L8an, part A)

`LeafOK n` bundles the data premises the SR6/SR7 leaf miss already takes about the leaf `n`. `leafKid_step`:
ONE real run of `synthesizeChild n` for such an `n` (a cache hit OR the real leaf miss) from a world with
`JQC`, `CacheClosed`, `KeyTop` ends in a world with the same three clauses, `(cv w').get? n = some y`, the cache
extended, and every new key equal to `n`. `closeLoop_leaf`: the `mapM` loop of the general closing over a list of
leaf calls (the loop that `closeInstsGM` runs) does the same for the whole list; the child `k` IS the end
cache's entry at the callee `k`. `closeInstsGM_leafRun`: the closing run with that. -/

namespace Tools.ShippingSharedLeafNL
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
open Tools.ShippingClosedKinds

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The data premises of the SR6/SR7 real leaf miss about the leaf `n` (a machine without calls whose body
is the quotation of a well-formed term, its entry constant and its closing). -/
def LeafOK (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (n : Name) : Prop :=
  ∃ d : MachineData, d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.shape.insts = [] ∧ (∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width) ∧
    MachineDefines mctx mref cctx cref n d.shape ∧
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context), MachineCloses mctx' mref cctx' cref n d.shape)

/-- **One real run of `synthesizeChild n` for a leaf `n`: hit or real miss.** -/
theorem leafKid_step (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {n : Name} (hl : LeafOK mctx mref cctx cref n)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    JQC O D w' ∧ CacheClosed (cv w') ∧ KeyTop (cv w') ∧ (cv w').get? n = some y ∧
      CacheExtends (cv w) (cv w') ∧
      ∀ c r, (cv w').get? c = some r → (cv w).get? c = some r ∨ c = n := by
  cases hm : (cv w).get? n with
  | some r =>
    obtain ⟨rfl, hj, hc⟩ := synthesizeChild_hit O hA hw hm h
    rw [hc]
    exact ⟨hj, hcl, hk, hm, cacheExtends_refl _, fun c r' h' => Or.inl h'⟩
  | none =>
    obtain ⟨d, ok, hbody, hno, outTy, entry, closes⟩ := hl
    obtain ⟨hj, hc, hcl', hk', -, -⟩ :=
      synthesizeChild_leafMiss_nested_ins O hA hD d ok hbody hno outTy entry closes hw hcl hk hm h
    refine ⟨hj, hcl', hk', by rw [hc]; simp, by rw [hc]; exact cacheExtends_insert_missing y hm, ?_⟩
    intro c r' h'
    rw [hc] at h'
    rcases insert_get_cases h' with ⟨e, -⟩ | ⟨-, h''⟩
    · exact Or.inr e
    · exact Or.inl h''

/-- **The loop of the general closing over leaf calls.** -/
theorem closeLoop_leaf (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) (f : Name × InstOrigin → MetaM Res)
    (hf : ∀ x, f x = match x.2.child? with
      | some md => pure md
      | none => synthesizeChild x.1) :
    ∀ (l : List (Name × InstOrigin)) (acc : List Res) (r : List Res) (w w' : Void IO.RealWorld),
      (∀ x ∈ l, x.2.child? = none ∧ LeafOK mctx mref cctx cref x.1) →
      JQC O D w → CacheClosed (cv w) → KeyTop (cv w) →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧ (cv w').get? l[k].1 = some y) ∧
        JQC O D w' ∧ CacheClosed (cv w') ∧ KeyTop (cv w') ∧ CacheExtends (cv w) (cv w') ∧
        (∀ c r', (cv w').get? c = some r' → (cv w).get? c = some r' ∨ c ∈ l.map (·.1))
  | [], acc, r, w, w', _, hj, hcl, hk, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), hj, hcl, hk,
      cacheExtends_refl _, fun c r' h' => Or.inl h'⟩
  | (c, o) :: xs, acc, r, w, w', hleaf, hj, hcl, hk, h => by
    obtain ⟨y, w1, hy, h2⟩ := RunsTo.bind h
    rw [hf] at hy
    dsimp only at hy
    obtain ⟨hch, hlo⟩ := hleaf (c, o) (List.mem_cons_self ..)
    rw [hch] at hy
    obtain ⟨hj1, hcl1, hk1, hget1, hext1, hgrow1⟩ := leafKid_step O hA hD hlo hj hcl hk hy
    obtain ⟨ys, hr, hlen, hks, hj', hcl', hk', hext', hgrow'⟩ :=
      closeLoop_leaf O hA hD f hf xs (y :: acc) r w1 w'
        (fun x hx => hleaf x (List.mem_cons_of_mem _ hx)) hj1 hcl1 hk1 h2
    refine ⟨y :: ys, by simp [hr], by simp [hlen], fun kk hkk => ?_, hj', hcl', hk',
      cacheExtends_trans hext1 hext', fun c' r' hc' => ?_⟩
    · cases kk with
      | zero => exact ⟨y, rfl, hext' c y hget1⟩
      | succ kk =>
        obtain ⟨z, hz, hcz⟩ := hks kk (by simpa using hkk)
        exact ⟨z, by simpa using hz, by simpa using hcz⟩
    · rcases hgrow' c' r' hc' with h3 | h3
      · rcases hgrow1 c' r' h3 with h4 | h4
        · exact Or.inl h4
        · exact Or.inr (by simp [h4])
      · exact Or.inr (by simp [h3])

/-- **The general closing over leaf calls, as a real run.** The children are the end cache's entries at the
callees; the cache clauses are kept; every new key is a callee. -/
theorem closeInstsGM_leafRun (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hleaf : ∀ x ∈ shape.instTagged, x.2.child? = none ∧ LeafOK mctx mref cctx cref x.1)
    (hw : JQC O D w) (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w))
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧
      children.length = shape.insts.length ∧
      (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        (cv w').get? (shape.insts[k]).1 = some y) ∧
      JQC O D w' ∧ CacheClosed (cv w') ∧ KeyTop (cv w') ∧ CacheExtends (cv w) (cv w') ∧
      (∀ c r', (cv w').get? c = some r' → (cv w).get? c = some r' ∨ c ∈ shape.insts.map (·.1)) := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨hw1, rfl⟩ := triple_runs (tripleC_synthRead O hA D) hw hget
  have hcv1 : cv w1 = cv w := by
    have hk0 := O.frame hA _ FramedA.synthGet w hw.1.1
    rw [endW_of_runs hget] at hk0
    exact hk0.1
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨ys, hys, hlen, hks, hj', hcl', hk', hext', hgrow'⟩ :=
    closeLoop_leaf O hA hD
      (fun (x : Name × InstOrigin) => match x.2.child? with
        | some md => pure md
        | none => synthesizeChild x.1) (fun _ => rfl)
      shape.instTagged [] children w1 w' hleaf hw1 (by rw [hcv1]; exact hcl) (by rw [hcv1]; exact hk) hch
  simp only [List.reverse_nil, List.nil_append] at hys
  subst hys
  have hlenI : children.length = shape.insts.length := by
    rw [hlen]; exact instTagged_length' shape
  refine ⟨children, heq, hlenI, fun k hkl => ?_, hj', hcl', hk', by rw [← hcv1]; exact hext', ?_⟩
  · obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
    obtain ⟨y, hky, hcy⟩ := hks k hkT
    rw [he] at hcy
    exact ⟨y, hky, hcy⟩
  · intro c r' hc'
    rw [hcv1] at hgrow'
    rcases hgrow' c r' hc' with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      obtain ⟨k, hkT, rfl⟩ := List.mem_iff_getElem.mp hx
      have hkl : k < shape.insts.length := by rw [← instTagged_length']; exact hkT
      obtain ⟨_, he⟩ := instTagged_getAt shape hkl
      rw [he]
      exact List.mem_map.mpr ⟨_, List.getElem_mem hkl, rfl⟩

/-! ## The machine synthesis of a non-leaf callee (part B1) -/

/-- **The machine synthesis of a machine WITH calls, all calls to leaves, as a real run.** From a `JQC O D'` world
(`D' ≠ 0`; here `D' = D + 1`, the depth of the body) with `CacheClosed`/`KeyTop`, a returning run of
`synthesizeMachineCertified` of `d.shape` to `some (M, Dg)`: the harness keeps the cache VALUE (the translator on
the quoted body, `leafTranslatorKeeps_of_machineData` at `JK`), `closeLets` is pure, and the closing is
`closeInstsGM` over the leaf calls (`closeInstsGM_leafRun`). -/
theorem machineSynth_leafKids (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D' : Nat} (hD' : D' ≠ 0) {tenv : Lean.Environment} {b : Bool} {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hins : d.shape.insts ≠ []) (hfne : d.shape.instFields ≠ [])
    (hleaf : ∀ x ∈ d.shape.instTagged, x.2.child? = none ∧ LeafOK mctx mref cctx cref x.1)
    {w9 w10 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {Dg : Sparkle.IR.AST.Design}
    (hw : JQC O D' w9) (hcl : CacheClosed (cv w9)) (hk : KeyTop (cv w9))
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c d.shape)
      mctx mref cctx cref w9 (some (M, Dg)) w10) :
    ∃ t t' d₀ kids, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c
        d.shape.binders d.shape.body) (t, d₀) ∧
      closeLets d.shape.layout.lets t = some t' ∧
      CloseCalls d.shape t (closeMachine d.shape.layout t') d₀ kids M Dg ∧
      kids.length = d.shape.insts.length ∧
      (∀ k (hk : k < d.shape.insts.length), ∃ y, kids[k]? = some y ∧
        (cv w10).get? (d.shape.insts[k]).1 = some y) ∧
      JQC O D' w10 ∧ CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheExtends (cv w9) (cv w10) ∧
      (∀ c' r', (cv w10).get? c' = some r' → (cv w9).get? c' = some r' ∨
        c' ∈ d.shape.insts.map (·.1)) := by
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
        obtain ⟨kids, hres, hlen, hcache, hj, hcl2, hk2, hext, hgrow⟩ :=
          closeInstsGM_leafRun O hA hD' hleaf hw1.1 (by rw [hw1.2]; exact hcl) (by rw [hw1.2]; exact hk) hr
        refine ⟨t, t', d', kids, run.mreturns, hcl', Or.inr ⟨hfne, hres.symm, ?_⟩, hlen, hcache, hj, hcl2,
          hk2, by rw [← hw1.2]; exact hext, by rw [← hw1.2]; exact hgrow⟩
        intro k hkl md hmd
        obtain ⟨hkT, he⟩ := instTagged_getAt d.shape hkl
        have h0 := (hleaf _ (List.getElem_mem hkT)).1
        rw [he] at h0
        simp only at h0
        rw [hmd] at h0
        cases h0
  · have := RunsTo.pure_eq hr
    cases this

/-! ## The nested core entry, with the worlds tracked (part B2) -/

/-- **A returning run of the nested core entry (`D ≠ 0`) of a machine callee, with the cache tracked.** The
machine synthesis starts in a `JQC O (D + 1)` world with the SAME cache value as the entry's start (the prefix
is cache-neutral, `JK`), and the entry's end world has the SAME cache value as the machine synthesis's end (the
`finally` is cache-neutral, `finK`) and is `JQC O D`. `entry`/`closes` as in `machine_run_of_coreA`. -/
theorem core_run_tracked (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {c : Name} {shape : MachineShape}
    (entry : MachineDefines mctx mref cctx cref c shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c shape)
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {Dg : Sparkle.IR.AST.Design}
    (hw : JQC O D w)
    (hr : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, Dg) w1) :
    ∃ (tenv : Lean.Environment) (b : Bool) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
        mctx mref cctx cref w9 (some (M, Dg)) w10 ∧
      JQC O (D + 1) w9 ∧ cv w9 = cv w ∧ (JQC O (D + 1) w10 → JQC O D w1 ∧ cv w1 = cv w10) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at hr
  simp only [Bool.false_eq_true, ↓reduceIte] at hr
  have hwK : JK O D (cv w) w := ⟨hw, rfl⟩
  obtain ⟨prof, wa, s1, hr⟩ := RunsTo.bind hr
  have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableK O D (cv w))
    (FramedA.ioEnv _))) hwK s1
  obtain ⟨_, wb, s2, hr⟩ := RunsTo.bind hr
  have hw := triple_runs (keeps_iff.mp (keepsA_diag O hA (stableK O D (cv w))
    (Diag.profLog prof.isSome _))) hw s2
  obtain ⟨d, wc, s3, hr⟩ := RunsTo.bind hr
  have hd := triple_runs (tripleA_depthGet O hA (stableK O D (cv w))) hw s3
  have hdD : d = D := hd.2.trans hd.1.1.1.2.2
  have hw := hd.1
  subst hdD
  rcases RunsTo.ite hr with hr | hr
  · obtain ⟨_, _, ht, _⟩ := RunsTo.bind hr
    exact (throwError_not_runs _ ht).elim
  have h0' : ¬ ((d == 0) = true) := by simpa using hD
  simp only [h0', Bool.false_eq_true, ↓reduceIte] at hr
  peelF O hA (stableK O d (cv w)) hr hw; peelF O hA (stableK O d (cv w)) hr hw
  peelF O hA (stableK O d (cv w)) hr hw; peelF O hA (stableK O d (cv w)) hr hw
  peelF O hA (stableK O d (cv w)) hr hw; peelF O hA (stableK O d (cv w)) hr hw
  peelF O hA (stableK O d (cv w)) hr hw
  peelF O hA (stableK O d (cv w)) hr hw; peelF O hA (stableK O d (cv w)) hr hw
  peelF O hA (stableK O d (cv w)) hr hw; peelF O hA (stableK O d (cv w)) hr hw
  peelF O hA (stableK O d (cv w)) hr hw; peelF O hA (stableK O d (cv w)) hr hw
  peelF O hA (stableK O d (cv w)) hr hw
  obtain ⟨_, _, step, hr⟩ := RunsTo.bind hr
  have hw := triple_runs (tripleK_depthSet O hA d (d + 1) (cv w) (R := fun _ _ => False)) hw step
  clear step
  obtain ⟨w4, u, hbody, hfin⟩ := RunsTo.try_finally' hr
  obtain ⟨ci, w2, hget, hbody⟩ := RunsTo.bind hbody
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableK O (d + 1) (cv w))
    (FramedA.constInfo _))) hw hget
  obtain ⟨env, w2b, henv, hbody⟩ := RunsTo.bind hbody
  have hw2b := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableK O (d + 1) (cv w))
    FramedA.env)) hw2 henv
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ hget henv henv
  unfold synthesizeFromConst at hbody
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hbody
  obtain ⟨envR, w5, henv', hbody⟩ := RunsTo.bind hbody
  have hw5 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableK O (d + 1) (cv w))
    FramedA.env)) hw2b henv'
  obtain ⟨mach, w6, hp, hbody⟩ := RunsTo.bind hbody
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ hget henv henv'
  rw [hshape] at hbody
  dsimp only at hbody
  obtain ⟨r, w8, hmach, hbody⟩ := RunsTo.bind hbody
  have hne := closes (tenv := env) prof.isSome (d + 1) _ r w8 hw5.1
    (Nat.succ_le_succ (Nat.zero_le d)) hmach
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
    have h1 := triple_runs (keeps_iff.mp (keepsA_diag O hA (stableK O (d + 1) (cv w8))
      (Diag.profLog prof.isSome _))) ⟨hJ8, rfl⟩ s1'
    have h2 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableK O (d + 1) (cv w8))
      (FramedA.sideModify _ .subModule))) h1 s2'
    have h3 := triple_runs (finK O hA d (cv w8) _ _ _ _ _ _ _) h2 hfin
    exact ⟨h3.1, h3.2⟩

/-! ## The full entry's post-processing, with the cache tracked (part B3) -/

/-- The `top` map of `synthesizeCombinationalWith`: the clean-up applies to the module named like the entry's. -/
def topMap (n : String) (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design) :
    Sparkle.IR.AST.Design :=
  { d with modules := d.modules.map fun x => if x.name == n then f x else x }

theorem topMap_id (n : String) (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (h : ∀ x ∈ d.modules, x.name ≠ n) : topMap n f d = d := by
  unfold topMap
  have hid : ∀ x ∈ d.modules, (if x.name == n then f x else x) = x := by
    intro x hx
    have : ¬ (x.name == n) = true := fun e => h x hx (beq_iff_eq.mp e)
    simp [this]
  rw [List.map_congr_left hid]
  simp

/-- **The full entry, with the worlds tracked.** A returning run of `synthesizeCombinational c` is a returning run
of the core entry followed by the clean-up (`dropZeroWidthModule`, then `mergeChecked`, only on the module named
like the entry's, in the design), and the clean-up keeps `JQC` and the cache value. -/
theorem full_run_tracked (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {c : Name} {w w' : Void IO.RealWorld} {y : Res}
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (wc : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, Dg) wc ∧
      (JQC O D wc → JQC O D w' ∧ cv w' = cv wc) ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) := by
  unfold synthesizeCombinational synthesizeCombinationalWith at h
  obtain ⟨⟨M, Dg⟩, wc, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, Dg, wc, hcore, ?_⟩
  dsimp only at h
  obtain ⟨x, wq, s, h⟩ := RunsTo.bind h
  have hio : JQC O D wc → JQC O D wq ∧ cv wq = cv wc := fun hj =>
    let t := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableK O D (cv wc))
      (FramedA.ioEnv _))) ⟨hj, rfl⟩ s
    ⟨t.1, t.2⟩
  rcases RunsTo.ite h with h | h
  · obtain ⟨hy, rfl⟩ := RunsTo.pure_world h
    refine ⟨hio, Or.inl ?_⟩
    rw [hy]; exact ⟨rfl, rfl⟩
  · obtain ⟨hy, rfl⟩ := RunsTo.pure_world h
    refine ⟨hio, Or.inr ?_⟩
    rw [hy]; exact ⟨rfl, rfl⟩

/-! ## Design lemmas (part B4) -/

theorem foldl_inner_sub (l : List Sparkle.IR.AST.Module) :
    ∀ (acc : List Sparkle.IR.AST.Module),
      (∀ a ∈ acc, a ∈ l.foldl (fun acc c => if acc.any (·.name == c.name) then acc else acc ++ [c]) acc) ∧
      (∀ x ∈ l, ∃ a ∈ l.foldl (fun acc c => if acc.any (·.name == c.name) then acc else acc ++ [c]) acc,
        a.name = x.name) := by
  induction l with
  | nil => intro acc; exact ⟨fun a ha => ha, fun x hx => by cases hx⟩
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons]
    by_cases hx : acc.any (·.name == x.name) = true
    · rw [if_pos hx]
      obtain ⟨h1, h2⟩ := ih acc
      refine ⟨h1, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · obtain ⟨a, ha, han⟩ := List.any_eq_true.mp hx
        exact ⟨a, h1 a ha, by simpa using han⟩
      · exact h2 z hz
    · rw [if_neg hx]
      obtain ⟨h1, h2⟩ := ih (acc ++ [x])
      refine ⟨fun a ha => h1 a (List.mem_append_left _ ha), fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨z, h1 z (by simp), rfl⟩
      · exact h2 z hz

theorem designWith_hasName {kids : List Res} {d : Sparkle.IR.AST.Design} :
    ∀ k ∈ kids, ∃ a ∈ (designWith kids d).modules, a.name = k.1.name := by
  have key : ∀ (kids : List Res) (acc : List Sparkle.IR.AST.Module),
      (∀ a ∈ acc, a ∈ kids.foldl (fun acc (x : Res) =>
        (x.2.modules ++ [x.1]).foldl (fun acc c =>
          if acc.any (·.name == c.name) then acc else acc ++ [c]) acc) acc) ∧
      (∀ k ∈ kids, ∃ a ∈ kids.foldl (fun acc (x : Res) =>
        (x.2.modules ++ [x.1]).foldl (fun acc c =>
          if acc.any (·.name == c.name) then acc else acc ++ [c]) acc) acc, a.name = k.1.name) := by
    intro kids
    induction kids with
    | nil => intro acc; exact ⟨fun a ha => ha, fun k hk => by cases hk⟩
    | cons k ks ih =>
      intro acc
      simp only [List.foldl_cons]
      obtain ⟨ih1, ih2⟩ := ih ((k.2.modules ++ [k.1]).foldl
        (fun acc c => if acc.any (·.name == c.name) then acc else acc ++ [c]) acc)
      obtain ⟨i1, i2⟩ := foldl_inner_sub (k.2.modules ++ [k.1]) acc
      refine ⟨fun a ha => ih1 a (i1 a ha), fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · obtain ⟨a, ha, han⟩ := i2 z.1 (by simp)
        exact ⟨a, ih1 a ha, han⟩
      · exact ih2 z hz
  intro k hk
  exact (key kids d.modules).2 k hk

/-! ## A non-leaf callee's real miss (part C) -/

/-- **The real miss of a NON-leaf callee `c` whose calls are all to leaves.** From a `JQC O D` world (`D ≠ 0`)
with `CacheClosed`/`KeyTop` and `c` absent, a returning run of `synthesizeChild c`: the cache gets `y` at `c`
(`y` the cleaned-up `closeInstsG` of the children), keeps `JQC`/`CacheClosed`/`KeyTop`, extends the start cache,
and EVERY call's child is the cache's entry at the callee, a module with that child's name is in `y`'s design.
Data premises (named): `d` (`ok`, `hbody`, `hC`, `hslots`, `hdomB`), `hins`/`hfne` (calls, struct-result), every call
a non-memory leaf (`hleaf`) different from `c` (`hcne`), `entry` (`MachineDefines`), `closes`
(`MachineClosesAtA`: the machine synthesis does not fall back). No `T`, no pin. -/
theorem synthesizeChild_nonleaf_miss (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ []) (hfne : d.shape.instFields ≠ [])
    (hleaf : ∀ x ∈ d.shape.instTagged, x.2.child? = none ∧ LeafOK mctx mref cctx cref x.1)
    (hcne : ∀ k (hk : k < d.shape.insts.length), (d.shape.insts[k]).1 ≠ c)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c d.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w)) (hmiss : (cv w).get? c = none)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    JQC O D w' ∧ CacheClosed (cv w') ∧ KeyTop (cv w') ∧ CacheExtends (cv w) (cv w') ∧
      (cv w').get? c = some y ∧
      (∀ k (hk : k < d.shape.insts.length), ∃ e, (cv w').get? (d.shape.insts[k]).1 = some e ∧
        ∃ a ∈ y.2.modules, a.name = e.1.name) ∧
      (∀ c' r', (cv w').get? c' = some r' → (cv w).get? c' = some r' ∨ c' = c ∨
        c' ∈ d.shape.insts.map (·.1)) := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hw1⟩ := jqc_cacheGet O hA hw hget
  have hc1 := cacheGet_cv O hA hw hget
  cases hc : m.get? c with
  | some r' => rw [hm] at hc; rw [hmiss] at hc; cases hc
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    have hr : RealChildA O c r := RealChildA.of_jqc O hA hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    obtain ⟨M, Dg, wc, hcore, htail, hpost⟩ := full_run_tracked O hA (D := D) hrun
    obtain ⟨tenv, b, w9, w10, hmach, hw9, hc9, htl⟩ := core_run_tracked O hA hD entry closes hw1 hcore
    have hcl9 : CacheClosed (cv w9) := by rw [hc9, hc1]; exact hcl
    have hk9 : KeyTop (cv w9) := by rw [hc9, hc1]; exact hk
    obtain ⟨t, t', d₀, kids, run, hcl', hcc, hlen, hcache, hj10, hcl10, hk10, hext, hgrow⟩ :=
      machineSynth_leafKids O hA (Nat.succ_ne_zero D) d ok hbody hins hfne hleaf hw9 hcl9 hk9 hmach
    obtain ⟨hjc, hcvc⟩ := htl hj10
    obtain ⟨hj2, hcv2⟩ := htail hjc
    obtain ⟨-, hname0, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl'
    obtain ⟨-, -, hMname, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
    have hMc : M.name = Sparkle.IR.ModuleName.ofDecl c := hMname.trans hname0
    have hcv9 : cv w9 = cv w := hc9.trans hc1
    -- the key `c` is not in the cache after the closing
    have hnot : (cv w10).get? c = none := by
      cases hq : (cv w10).get? c with
      | none => rfl
      | some q =>
        rcases hgrow c q hq with h0 | h0
        · rw [hcv9, hmiss] at h0; cases h0
        · obtain ⟨x, hx, hxc⟩ := List.mem_map.mp h0
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
          exact absurd hxc (hcne i hi)
    -- every module of the entry's design is the top of a cached entry, so none is named like the entry
    have hkidIn : ∀ kd ∈ kids, ∃ c', (cv w10).get? c' = some kd := by
      intro kd hkd
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hkd
      have hi' : i < d.shape.insts.length := hlen ▸ hi
      obtain ⟨e, hke, hce⟩ := hcache i hi'
      have : kids[i] = e := by
        have := List.getElem?_eq_getElem hi
        rw [this] at hke
        exact Option.some.inj hke
      exact ⟨_, this ▸ hce⟩
    have hnoclash : ∀ x ∈ Dg.modules, x.name ≠ M.name := by
      intro x hx hxn
      rw [hDeq] at hx
      rcases mem_designWith hx with h0 | ⟨kd, hkd, hak⟩
      · rw [hd0] at h0; cases h0
      · obtain ⟨c', hc'⟩ := hkidIn kd hkd
        have hmods : x ∈ ModsOf kd := by
          rcases hak with h1 | h1
          · exact List.mem_cons_of_mem _ h1
          · rw [h1]; exact List.mem_cons_self ..
        obtain ⟨c'', r'', hr'', rfl⟩ := hcl10 c' kd hc' x hmods
        have hnm := hk10 c'' r'' hr''
        have : c'' = c := Tools.ShippingModuleName.ofDecl_injective (hnm.symm.trans (hxn.trans hMc))
        subst this
        rw [hnot] at hr''; cases hr''
    have hid1 : topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg = Dg := topMap_id _ _ _ hnoclash
    have hrdesign : y.2 = designWith kids d₀ := by
      rcases hpost with ⟨-, h2⟩ | ⟨-, h2⟩
      · rw [h2, hid1, hDeq]
      · rw [h2, hid1, topMap_id _ _ _ hnoclash, hDeq]
    have hrname : y.1.name = Sparkle.IR.ModuleName.ofDecl c := by
      rcases hpost with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMc
      · rw [h1, Tools.ShippingMachineDepthRun.mergeChecked_name,
          Tools.ShippingMachineDepthRun.dropZW_name]; exact hMc
    -- the insert
    have hc3 := (O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert c y) hj2.1.1 hmod).1
    have hj3 := jqc_insert_runs O hA hj2 hr hmod
    have hcvw2 : cv w2 = cv w10 := hcv2.trans hcvc
    have hcv3 : cv w' = (cv w10).insert c y := by rw [hc3, hcvw2]
    refine ⟨hj3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcv3]; exact cacheClosed_insert_kids hcl10 hnot hrdesign hd0 hkidIn
    · rw [hcv3]; exact keyTop_insert hk10 hrname
    · rw [hcv3]
      have h1 : CacheExtends (cv w) (cv w10) := by rw [← hcv9]; exact hext
      exact cacheExtends_trans h1 (cacheExtends_insert_missing y hnot)
    · rw [hcv3]; exact get?_insert_self _ _ _
    · intro k hkl
      obtain ⟨e, hke, hce⟩ := hcache k hkl
      refine ⟨e, ?_, ?_⟩
      · rw [hcv3, get?_insert_ne _ (hcne k hkl)]; exact hce
      · rw [hrdesign]
        obtain ⟨a, ha, han⟩ := designWith_hasName (kids := kids) (d := d₀) e (List.mem_of_getElem? hke)
        exact ⟨a, ha, han⟩
    · intro c' r' hc'
      rw [hcv3] at hc'
      rcases insert_get_cases hc' with ⟨e, -⟩ | ⟨-, hc''⟩
      · exact Or.inr (Or.inl e)
      · rcases hgrow c' r' hc'' with h0 | h0
        · exact Or.inl (by rw [← hcv9]; exact h0)
        · exact Or.inr (Or.inr h0)

/-! ## The two non-leaf callees of `topshare`, as real runs (part D) -/

/-- **Two non-leaf callees `c₁`, `c₂` (wrap / wrap3) called one after the other; the SHARED leaf.** The two
`synthesizeChild` runs are the two entries of the parent's closing loop (`closeLoop`: `RunsTo.bind` of
`mapM.loop`); each is a real non-leaf miss (`synthesizeChild_nonleaf_miss`), whose calls are real leaf calls
(`closeInstsGM_leafRun`: a miss or a hit at the cache). The end cache is `CacheClosed`/`KeyTop`, hence
`CacheCoh`; the end cache holds both results (the retention of the first entry across the second run is the
`CacheExtends` of the second miss); the `hcross` shape holds for the two results, and for every pair of calls
(one of each callee) to the same leaf `n` the cache's entry `e` at `n` has its module `e.1` INSIDE both
designs. Premises: `hD`, the start world (`JQC`, `CacheClosed`, `KeyTop`, both callees absent), the data of the
two callees (`d₁`/`d₂`: `ok`, `hbody`, `hC`, `hslots`, `hdomB`, `hins`, `hfne`, every call a non-memory leaf with
`LeafOK`, `entry`, `closes`), and name distinctness (`c₁ ≠ c₂`, no call of `c₁` is `c₂`, no call is its own
callee). -/
theorem topshare_pair (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {c₁ c₂ : Name} (hc12 : c₁ ≠ c₂)
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
    {w w₁ w₂ : Void IO.RealWorld} {y₁ y₂ : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w))
    (hm₁ : (cv w).get? c₁ = none) (hm₂ : (cv w).get? c₂ = none)
    (h₁ : RunsTo (synthesizeChild c₁) mctx mref cctx cref w y₁ w₁)
    (h₂ : RunsTo (synthesizeChild c₂) mctx mref cctx cref w₁ y₂ w₂) :
    JQC O D w₂ ∧ CacheClosed (cv w₂) ∧ KeyTop (cv w₂) ∧ CacheCoh (cv w₂) ∧
      (cv w₂).get? c₁ = some y₁ ∧ (cv w₂).get? c₂ = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      ∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w₂).get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules := by
  obtain ⟨hj1, hcl1, hk1, hext1, hget1, hkids1, hgrow1⟩ :=
    synthesizeChild_nonleaf_miss O hA hD d₁ ok₁ hbody₁ hC₁ hslots₁ hdomB₁ hins₁ hfne₁ hleaf₁ hcne₁
      entry₁ closes₁ hw hcl hk hm₁ h₁
  have hm₂' : (cv w₁).get? c₂ = none := by
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
      entry₂ closes₂ hj1 hcl1 hk1 hm₂' h₂
  have hcoh : CacheCoh (cv w₂) :=
    cacheCoh_of_closed_topAgree hcl2 (cacheTopAgree_of_keyTop hk2)
  have hy1 : (cv w₂).get? c₁ = some y₁ := hext2 c₁ y₁ hget1
  refine ⟨hj2, hcl2, hk2, hcoh, hy1, hget2, fun a ha b hb hab => hcoh c₁ y₁ c₂ y₂ hy1 hget2 a ha b hb hab, ?_⟩
  intro k₁ hk₁ k₂ hk₂ hn
  obtain ⟨e₁, he₁, a, ha, han⟩ := hkids1 k₁ hk₁
  obtain ⟨e₂, he₂, b, hb, hbn⟩ := hkids2 k₂ hk₂
  have he₁' : (cv w₂).get? (d₁.shape.insts[k₁]).1 = some e₁ := hext2 _ e₁ he₁
  have he₂' : (cv w₂).get? (d₂.shape.insts[k₂]).1 = some e₂ := he₂
  rw [← hn] at he₂'
  have hee : e₂ = e₁ := Option.some.inj (he₂'.symm.trans he₁')
  subst hee
  refine ⟨e₂, he₁', ?_, ?_⟩
  · have : a = e₂.1 := hcoh c₁ y₁ _ e₂ hy1 he₁' a (List.mem_cons_of_mem _ ha) e₂.1
      (List.mem_cons_self ..) han
    rw [← this]; exact ha
  · have : b = e₂.1 := hcoh c₂ y₂ _ e₂ hget2 he₂ b (List.mem_cons_of_mem _ hb) e₂.1
      (List.mem_cons_self ..) hbn
    rw [← this]; exact hb

end Tools.ShippingSharedLeafNL

#print axioms Tools.ShippingSharedLeafNL.leafKid_step
#print axioms Tools.ShippingSharedLeafNL.closeLoop_leaf
#print axioms Tools.ShippingSharedLeafNL.closeInstsGM_leafRun
#print axioms Tools.ShippingSharedLeafNL.machineSynth_leafKids
#print axioms Tools.ShippingSharedLeafNL.core_run_tracked
#print axioms Tools.ShippingSharedLeafNL.full_run_tracked
#print axioms Tools.ShippingSharedLeafNL.designWith_hasName
#print axioms Tools.ShippingSharedLeafNL.synthesizeChild_nonleaf_miss
#print axioms Tools.ShippingSharedLeafNL.topshare_pair
