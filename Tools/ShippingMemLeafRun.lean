import Tools.ShippingMemLeafCache
import Tools.ShippingSharedLeafNL
import Tools.ShippingCallsMemA
import Tools.ShippingMemOnlyCloses
-- UNBUILT (unit SRM1): see REPORT-SRM1.md for the run names / exits at the final committed SHA.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # Shared leaf with a MEMORY child: the real runs (unit SRM1, ledger L8bd)

The memory-aware versions of the cache / run layer of `Tools/ShippingSharedLeafNL.lean` (`closeLoop_leaf`, `closeInstsGM_leafRun`, `machineSynth_leafKids`,
`synthesizeChild_nonleaf_miss`), over the clauses of `Tools/ShippingMemLeafCache.lean` (`CacheClosedNM`, `KeyTop`, `MemDet` in place of `CacheClosed`).  A call of the closing is
either a MEMORY entry (`x.2.child? = some md`, `md` a built memory module: the closing takes `md`, the cache is untouched) or a callee with a one-step contract `StepNM`
(a hit, or a real miss of that callee).  The same generic miss theorem therefore covers (a) the shared LEAF whose only calls are memory entries, and (b) a callee whose calls are
the memory-bearing leaf.

PROVED here: `closeLoop_gen`, `closeInstsGM_gen`, `machineSynth_gen`, `synthesizeChild_miss_nm`, `stepNM_of_data` (hit-or-miss), `memLeaf_stepNM` (the memory leaf, with
`MachineClosesAtA` of the leaf DERIVED by `machineClosesAtA_of_memOnlyData_names`, not a premise).
PREMISES (named, per machine): `MachineDefines` of every machine, `MachineClosesAtA` of a callee that has callee calls (`closes`, as in `synthesizeChild_nonleaf_miss`), the start-world
clauses, `RefLawsAOps` `O`, `RefLawsATele` `T` (memory leaf only), `AdmCtx`.
NOT proved here (residue, see REPORT-SRM1.md): anything about interfaces — `ChildIfaceP`, `KidFactsA`, `hgk`, `hsep`, `seq_child_runN` — of a machine with a memory child on the `RealChildA`
side (the memory-kid `core_*` chain of `Tools/ShippingMemKid*.lean` is stated over the old-form `RealChild` / `MachineRan`); the parent's closing over several callees and `kary_*` of it. -/

namespace Tools.ShippingMemLeafRun
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
open Tools.ShippingMemLeafCache
open Sparkle.Compiler.MachMemory (memModule memChild?)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The one-step contract of `synthesizeChild n`** under the memory-aware cache clauses: the end world is `JQC O D`, the clauses are kept, the cache holds `y` at `n`, extends the
start cache, and gains only `n` and names of `Gs`. -/
def StepNM (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context) (D : Nat) (n : Name)
    (Gs : List Name) : Prop :=
  ∀ {w w' : Void IO.RealWorld} {y : Res}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) →
    RunsTo (synthesizeChild n) mctx mref cctx cref w y w' →
    JQC O D w' ∧ CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ (cv w').get? n = some y ∧
      CacheExtends (cv w) (cv w') ∧
      ∀ c r, (cv w').get? c = some r → (cv w).get? c = some r ∨ c = n ∨ c ∈ Gs

theorem StepNM.mono {O : RefLawsAOps MkRefd mref cref} {D : Nat} {n : Name} {Gs Gs' : List Name}
    (h : StepNM (mref := mref) (cref := cref) O mctx cctx D n Gs) (hs : ∀ x ∈ Gs, x ∈ Gs') :
    StepNM (mref := mref) (cref := cref) O mctx cctx D n Gs' := by
  intro w w' y hw hcl hk hmd hr
  obtain ⟨a, b, c, d, e, f, g⟩ := h hw hcl hk hmd hr
  exact ⟨a, b, c, d, e, f, fun c' r hc' => (g c' r hc').elim Or.inl fun h' => h'.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr (hs _ h))⟩

/-- **The loop of the general closing over memory entries and `StepNM` callees.** -/
theorem closeLoop_gen (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (Gs : List Name) (f : Name × InstOrigin → MetaM Res)
    (hf : ∀ x, f x = match x.2.child? with
      | some md => pure md
      | none => synthesizeChild x.1) :
    ∀ (l : List (Name × InstOrigin)) (acc : List Res) (r : List Res) (w w' : Void IO.RealWorld),
      (∀ x ∈ l, (∃ md, x.2.child? = some md ∧ MemKid md) ∨
        (x.2.child? = none ∧ StepNM (mref := mref) (cref := cref) O mctx cctx D x.1 Gs)) →
      JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length),
          (∃ md, l[k].2.child? = some md ∧ ys[k]? = some md ∧ MemKid md) ∨
          (l[k].2.child? = none ∧ ∃ y, ys[k]? = some y ∧ (cv w').get? l[k].1 = some y)) ∧
        JQC O D w' ∧ CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheExtends (cv w) (cv w') ∧
        (∀ c r', (cv w').get? c = some r' → (cv w).get? c = some r' ∨ c ∈ l.map (·.1) ∨ c ∈ Gs)
  | [], acc, r, w, w', _, hj, hcl, hk, hmd, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), hj, hcl, hk, hmd,
      cacheExtends_refl _, fun c r' h' => Or.inl h'⟩
  | (c, o) :: xs, acc, r, w, w', hcalls, hj, hcl, hk, hmd, h => by
    obtain ⟨y, w1, hy, h2⟩ := RunsTo.bind h
    rw [hf] at hy
    dsimp only at hy
    rcases hcalls (c, o) (List.mem_cons_self ..) with ⟨md, hmc, hmk⟩ | ⟨hch, hstep⟩
    · rw [hmc] at hy
      obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hy
      obtain ⟨ys, hr, hlen, hks, hj', hcl', hk', hmd', hext', hgrow'⟩ :=
        closeLoop_gen O hA Gs f hf xs (y :: acc) r w1 w' (fun x hx => hcalls x (List.mem_cons_of_mem _ hx))
          hj hcl hk hmd h2
      refine ⟨y :: ys, by simp [hr], by simp [hlen], fun kk hkk => ?_, hj', hcl', hk', hmd', hext',
        fun c' r' hc' => ?_⟩
      · cases kk with
        | zero => exact Or.inl ⟨y, hmc, rfl, hmk⟩
        | succ kk =>
          rcases hks kk (by simpa using hkk) with ⟨md', h1, h2, h3⟩ | ⟨h1, z, hz, hcz⟩
          · exact Or.inl ⟨md', by simpa using h1, by simpa using h2, h3⟩
          · exact Or.inr ⟨by simpa using h1, z, by simpa using hz, by simpa using hcz⟩
      · rcases hgrow' c' r' hc' with h3 | h3 | h3
        · exact Or.inl h3
        · exact Or.inr (Or.inl (by simp [h3]))
        · exact Or.inr (Or.inr h3)
    · rw [hch] at hy
      obtain ⟨hj1, hcl1, hk1, hmd1, hget1, hext1, hgrow1⟩ := hstep hj hcl hk hmd hy
      obtain ⟨ys, hr, hlen, hks, hj', hcl', hk', hmd', hext', hgrow'⟩ :=
        closeLoop_gen O hA Gs f hf xs (y :: acc) r w1 w' (fun x hx => hcalls x (List.mem_cons_of_mem _ hx))
          hj1 hcl1 hk1 hmd1 h2
      refine ⟨y :: ys, by simp [hr], by simp [hlen], fun kk hkk => ?_, hj', hcl', hk', hmd',
        cacheExtends_trans hext1 hext', fun c' r' hc' => ?_⟩
      · cases kk with
        | zero => exact Or.inr ⟨hch, y, rfl, hext' c y hget1⟩
        | succ kk =>
          rcases hks kk (by simpa using hkk) with ⟨md', h1, h2, h3⟩ | ⟨h1, z, hz, hcz⟩
          · exact Or.inl ⟨md', by simpa using h1, by simpa using h2, h3⟩
          · exact Or.inr ⟨by simpa using h1, z, by simpa using hz, by simpa using hcz⟩
      · rcases hgrow' c' r' hc' with h3 | h3 | h3
        · rcases hgrow1 c' r' h3 with h4 | h4 | h4
          · exact Or.inl h4
          · exact Or.inr (Or.inl (by simp [h4]))
          · exact Or.inr (Or.inr h4)
        · exact Or.inr (Or.inl (by simp [h3]))
        · exact Or.inr (Or.inr h3)

/-- **The general closing over memory entries and `StepNM` callees, as a real run.** -/
theorem closeInstsGM_gen (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (Gs : List Name)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hcalls : ∀ x ∈ shape.instTagged, (∃ md, x.2.child? = some md ∧ MemKid md) ∨
      (x.2.child? = none ∧ StepNM (mref := mref) (cref := cref) O mctx cctx D x.1 Gs))
    (hw : JQC O D w) (hcl : CacheClosedNM (cv w)) (hk : KeyTop (cv w)) (hmd : MemDet (cv w))
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧
      children.length = shape.insts.length ∧
      (∀ k (hk : k < shape.insts.length),
        (∃ md, (shape.instOrigins.getD k .ord).child? = some md ∧ children[k]? = some md ∧ MemKid md) ∨
        ((shape.instOrigins.getD k .ord).child? = none ∧ ∃ y, children[k]? = some y ∧
          (cv w').get? (shape.insts[k]).1 = some y)) ∧
      JQC O D w' ∧ CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheExtends (cv w) (cv w') ∧
      (∀ c r', (cv w').get? c = some r' → (cv w).get? c = some r' ∨ c ∈ shape.insts.map (·.1) ∨ c ∈ Gs) := by
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
  obtain ⟨ys, hys, hlen, hks, hj', hcl', hk', hmd', hext', hgrow'⟩ :=
    closeLoop_gen O hA Gs
      (fun (x : Name × InstOrigin) => match x.2.child? with
        | some md => pure md
        | none => synthesizeChild x.1) (fun _ => rfl)
      shape.instTagged [] children w1 w' hcalls hw1 (by rw [hcv1]; exact hcl) (by rw [hcv1]; exact hk)
      (by rw [hcv1]; exact hmd) hch
  simp only [List.reverse_nil, List.nil_append] at hys
  subst hys
  have hlenI : children.length = shape.insts.length := by
    rw [hlen]; exact instTagged_length' shape
  refine ⟨children, heq, hlenI, fun k hkl => ?_, hj', hcl', hk', hmd', by rw [← hcv1]; exact hext', ?_⟩
  · obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
    rcases hks k hkT with ⟨md, h1, h2, h3⟩ | ⟨h1, y, hky, hcy⟩
    · rw [he] at h1
      exact Or.inl ⟨md, h1, h2, h3⟩
    · rw [he] at h1 hcy
      exact Or.inr ⟨h1, y, hky, hcy⟩
  · intro c r' hc'
    rw [hcv1] at hgrow'
    rcases hgrow' c r' hc' with h | h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ?_)
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      obtain ⟨k, hkT, rfl⟩ := List.mem_iff_getElem.mp hx
      have hkl : k < shape.insts.length := by rw [← instTagged_length']; exact hkT
      obtain ⟨_, he⟩ := instTagged_getAt shape hkl
      rw [he]
      exact List.mem_map.mpr ⟨_, List.getElem_mem hkl, rfl⟩
    · exact Or.inr (Or.inr h)

/-- **The machine synthesis of a machine WITH calls (memory entries / `StepNM` callees) as a real run.** -/
theorem machineSynth_gen (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D' : Nat} (_hD' : D' ≠ 0) {tenv : Lean.Environment} {b : Bool} {c : Name} (Gs : List Name)
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hins : d.shape.insts ≠ []) (hfne : d.shape.instFields ≠ [])
    (hcalls : ∀ x ∈ d.shape.instTagged, (∃ md, x.2.child? = some md ∧ MemKid md) ∨
      (x.2.child? = none ∧ StepNM (mref := mref) (cref := cref) O mctx cctx D' x.1 Gs))
    {w9 w10 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {Dg : Sparkle.IR.AST.Design}
    (hw : JQC O D' w9) (hcl : CacheClosedNM (cv w9)) (hk : KeyTop (cv w9)) (hmd : MemDet (cv w9))
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c d.shape)
      mctx mref cctx cref w9 (some (M, Dg)) w10) :
    ∃ t t' d₀ kids, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c
        d.shape.binders d.shape.body) (t, d₀) ∧
      closeLets d.shape.layout.lets t = some t' ∧
      CloseCalls d.shape t (closeMachine d.shape.layout t') d₀ kids M Dg ∧
      kids.length = d.shape.insts.length ∧
      (∀ k (hk : k < d.shape.insts.length),
        (∃ md, (d.shape.instOrigins.getD k .ord).child? = some md ∧ kids[k]? = some md ∧ MemKid md) ∨
        ((d.shape.instOrigins.getD k .ord).child? = none ∧ ∃ y, kids[k]? = some y ∧
          (cv w10).get? (d.shape.insts[k]).1 = some y)) ∧
      JQC O D' w10 ∧ CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheExtends (cv w9) (cv w10) ∧
      (∀ c' r', (cv w10).get? c' = some r' → (cv w9).get? c' = some r' ∨
        c' ∈ d.shape.insts.map (·.1) ∨ c' ∈ Gs) := by
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
        obtain ⟨kids, hres, hlen, hcache, hj, hcl2, hk2, hmd2, hext, hgrow⟩ :=
          closeInstsGM_gen O hA Gs hcalls hw1.1 (by rw [hw1.2]; exact hcl) (by rw [hw1.2]; exact hk)
            (by rw [hw1.2]; exact hmd) hr
        refine ⟨t, t', d', kids, run.mreturns, hcl', Or.inr ⟨hfne, hres.symm, ?_⟩, hlen, hcache, hj, hcl2,
          hk2, hmd2, by rw [← hw1.2]; exact hext, by rw [← hw1.2]; exact hgrow⟩
        intro k hkl md hmd0
        rcases hcache k hkl with ⟨md', h1, h2, -⟩ | ⟨h1, -⟩
        · rw [h1] at hmd0
          cases hmd0
          exact h2
        · rw [h1] at hmd0
          cases hmd0
  · have := RunsTo.pure_eq hr
    cases this

end Tools.ShippingMemLeafRun
