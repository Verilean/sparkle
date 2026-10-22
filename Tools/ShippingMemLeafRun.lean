import Tools.ShippingMemLeafCache
import Tools.ShippingSharedLeafNL
import Tools.ShippingCallsMemA
import Tools.ShippingMemOnlyCloses
-- BUILT (unit SRM1): r10 exit 0 (dev run); the final-SHA rebuild is in REPORT-SRM1.md.
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
CLASS BOUNDARY (the run / cache layer only; an example does not make the class complete).  PROVED for machines whose calls are each (a) a MEMORY entry (the origin's child is a built `memModule`) or (b) a callee with a
`StepNM` contract, at every depth `≠ 0`, under the cache clauses `CacheClosedNM` + `KeyTop` + `MemDet` (so `CacheCoh` of the end cache, `closing_nm`).  Instances: a memory-only machine (`MemOnlyData` + `MemOnlyCloseData`:
every call a memory placeholder of ONE pair of widths, any number of them; its closing is DERIVED); a plain leaf (`LeafOK`; reflection and closing are premises); a callee whose calls are memory entries and/or `StepNM`
callees (`MachineClosesAtA` of the callee is a PREMISE); the parent's closing over `StepNM` callees (the parent itself has no memory entry: `closing_nm` asks `child? = none` for every call).
OPEN (not in the class): see the residue list R1–R5 in REPORT-SRM1.md (the `RealChildA` interface / `KidFactsA` / `seq_child_runN` / composed trace of a machine WITH a memory child; the full `kary_entry_run` assembly).
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
  ∀ (w w' : Void IO.RealWorld) (y : Res), JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) →
    RunsTo (synthesizeChild n) mctx mref cctx cref w y w' →
    JQC O D w' ∧ CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ (cv w').get? n = some y ∧
      CacheExtends (cv w) (cv w') ∧
      ∀ c r, (cv w').get? c = some r → (cv w).get? c = some r ∨ c = n ∨ c ∈ Gs

theorem StepNM.mono {O : RefLawsAOps MkRefd mref cref} {D : Nat} {n : Name} {Gs Gs' : List Name}
    (h : StepNM (mref := mref) (cref := cref) O mctx cctx D n Gs) (hs : ∀ x ∈ Gs, x ∈ Gs') :
    StepNM (mref := mref) (cref := cref) O mctx cctx D n Gs' := by
  intro w w' y hw hcl hk hmd hr
  obtain ⟨a, b, c, d, e, f, g⟩ := h w w' y hw hcl hk hmd hr
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
      obtain ⟨hj1, hcl1, hk1, hmd1, hget1, hext1, hgrow1⟩ := hstep _ _ _ hj hcl hk hmd hy
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


/-! ## The real miss of a machine whose calls are memory entries / `StepNM` callees -/

/-- **The real miss of `c` with memory entries and `StepNM` callees as calls.**  Same walk as `synthesizeChild_nonleaf_miss` (`Tools/ShippingSharedLeafNL.lean`), over the clauses
`CacheClosedNM` / `KeyTop` / `MemDet`.  `Gs` are the names the callees' steps may add (`c ∉ Gs`); `hcne`: no call is `c`.  The entry `y` is `designWith kids d₀` with every kid a cache
entry or a built memory module. -/
theorem synthesizeChild_miss_nm (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {c : Name} (Gs : List Name) (hcG : c ∉ Gs) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ []) (hfne : d.shape.instFields ≠ [])
    (hcalls : ∀ x ∈ d.shape.instTagged, (∃ md, x.2.child? = some md ∧ MemKid md) ∨
      (x.2.child? = none ∧ StepNM (mref := mref) (cref := cref) O mctx cctx (D + 1) x.1 Gs))
    (hcne : ∀ k (hk : k < d.shape.insts.length), (d.shape.insts[k]).1 ≠ c)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c d.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (hcl : CacheClosedNM (cv w)) (hk : KeyTop (cv w)) (hmd : MemDet (cv w)) (hmiss : (cv w).get? c = none)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    JQC O D w' ∧ CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheExtends (cv w) (cv w') ∧
      (cv w').get? c = some y ∧
      (∃ (kids : List Res) (d₀ : Sparkle.IR.AST.Design), y.2 = designWith kids d₀ ∧ d₀.modules = [] ∧
        kids.length = d.shape.insts.length ∧
        (∀ k (hk : k < d.shape.insts.length),
          (∃ md, (d.shape.instOrigins.getD k .ord).child? = some md ∧ kids[k]? = some md ∧ MemKid md) ∨
          ((d.shape.instOrigins.getD k .ord).child? = none ∧ ∃ e, kids[k]? = some e ∧
            (cv w').get? (d.shape.insts[k]).1 = some e))) ∧
      (∀ c' r', (cv w').get? c' = some r' → (cv w).get? c' = some r' ∨ c' = c ∨
        c' ∈ d.shape.insts.map (·.1) ∨ c' ∈ Gs) := by
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
    have hcl9 : CacheClosedNM (cv w9) := by rw [hc9, hc1]; exact hcl
    have hk9 : KeyTop (cv w9) := by rw [hc9, hc1]; exact hk
    have hmd9 : MemDet (cv w9) := by rw [hc9, hc1]; exact hmd
    obtain ⟨t, t', d₀, kids, run, hcl', hcc, hlen, hcache, hj10, hcl10, hk10, hmd10, hext, hgrow⟩ :=
      machineSynth_gen O hA (Nat.succ_ne_zero D) Gs d ok hbody hins hfne hcalls hw9 hcl9 hk9 hmd9 hmach
    obtain ⟨hjc, hcvc⟩ := htl hj10
    obtain ⟨hj2, hcv2⟩ := htail hjc
    obtain ⟨-, hname0, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl'
    obtain ⟨-, -, hMname, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
    have hMc : M.name = Sparkle.IR.ModuleName.ofDecl c := hMname.trans hname0
    have hcv9 : cv w9 = cv w := hc9.trans hc1
    have hnot : (cv w10).get? c = none := by
      cases hq : (cv w10).get? c with
      | none => rfl
      | some q =>
        rcases hgrow c q hq with h0 | h0 | h0
        · rw [hcv9, hmiss] at h0; cases h0
        · obtain ⟨x, hx, hxc⟩ := List.mem_map.mp h0
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
          exact absurd hxc (hcne i hi)
        · exact absurd h0 hcG
    -- every kid is a cache entry or a built memory module
    have hkidIn : ∀ kd ∈ kids, (∃ c', (cv w10).get? c' = some kd) ∨ MemKid kd := by
      intro kd hkd
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hkd
      have hi' : i < d.shape.insts.length := hlen ▸ hi
      have hgi : kids[i]? = some kids[i] := List.getElem?_eq_getElem hi
      rcases hcache i hi' with ⟨md, -, h2, h3⟩ | ⟨-, e, hke, hce⟩
      · rw [hgi] at h2
        cases h2
        exact Or.inr h3
      · rw [hgi] at hke
        cases hke
        exact Or.inl ⟨_, hce⟩
    have hnoclash : ∀ x ∈ Dg.modules, x.name ≠ M.name := by
      intro x hx hxn
      rw [hDeq] at hx
      by_cases hmn : MemNamed x.name
      · obtain ⟨cb, aw, dw, e⟩ := hmn
        exact Tools.ShippingModuleName.ofDecl_ne_ofMem c cb aw dw ((hxn.trans hMc).symm.trans e)
      rcases mem_designWith hx with h0 | ⟨kd, hkd, hak⟩
      · rw [hd0] at h0; cases h0
      · have hmods : x ∈ ModsOf kd := by
          rcases hak with h1 | h1
          · exact List.mem_cons_of_mem _ h1
          · rw [h1]; exact List.mem_cons_self ..
        rcases hkidIn kd hkd with ⟨c', hc'⟩ | hmk
        · obtain ⟨c'', r'', hr'', rfl⟩ := hcl10 c' kd hc' x hmods hmn
          have hnm := hk10 c'' r'' hr''
          have : c'' = c := Tools.ShippingModuleName.ofDecl_injective (hnm.symm.trans (hxn.trans hMc))
          subst this
          rw [hnot] at hr''; cases hr''
        · exact hmn (memMod_memNamed (mods_of_memKid hmk (by simpa using hak)))
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
    have hc3 := (O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert c y) hj2.1.1 hmod).1
    have hj3 := jqc_insert_runs O hA hj2 hr hmod
    have hcvw2 : cv w2 = cv w10 := hcv2.trans hcvc
    have hcv3 : cv w' = (cv w10).insert c y := by rw [hc3, hcvw2]
    refine ⟨hj3, ?_, ?_, ?_, ?_, ?_, ⟨kids, d₀, hrdesign, hd0, hlen, fun k hkl => ?_⟩, ?_⟩
    · rw [hcv3]; exact cacheClosedNM_insert_kids hcl10 hnot hrdesign hd0 hkidIn
    · rw [hcv3]; exact keyTop_insert hk10 hrname
    · rw [hcv3]; exact memDet_insert_kids hmd10 hrname hrdesign hd0 hkidIn
    · rw [hcv3]
      have h1 : CacheExtends (cv w) (cv w10) := by rw [← hcv9]; exact hext
      exact cacheExtends_trans h1 (cacheExtends_insert_missing y hnot)
    · rw [hcv3]; exact get?_insert_self _ _ _
    · rcases hcache k hkl with hmem | ⟨h1, e, hke, hce⟩
      · exact Or.inl hmem
      · refine Or.inr ⟨h1, e, hke, ?_⟩
        rw [hcv3, get?_insert_ne _ (hcne k hkl)]; exact hce
    · intro c' r' hc'
      rw [hcv3] at hc'
      rcases insert_get_cases hc' with ⟨e, -⟩ | ⟨-, hc''⟩
      · exact Or.inr (Or.inl e)
      · rcases hgrow c' r' hc'' with h0 | h0 | h0
        · exact Or.inl (by rw [← hcv9]; exact h0)
        · exact Or.inr (Or.inr (Or.inl h0))
        · exact Or.inr (Or.inr (Or.inr h0))

/-- **Hit or real miss: the one-step contract of a machine with memory entries / `StepNM` calls.** -/
theorem stepNM_of_data (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {c : Name} (Gs : List Name) (hcG : c ∉ Gs) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ []) (hfne : d.shape.instFields ≠ [])
    (hcalls : ∀ x ∈ d.shape.instTagged, (∃ md, x.2.child? = some md ∧ MemKid md) ∨
      (x.2.child? = none ∧ StepNM (mref := mref) (cref := cref) O mctx cctx (D + 1) x.1 Gs))
    (hcne : ∀ k (hk : k < d.shape.insts.length), (d.shape.insts[k]).1 ≠ c)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c d.shape) :
    StepNM (mref := mref) (cref := cref) O mctx cctx D c (d.shape.insts.map (·.1) ++ Gs) := by
  intro w w' y hw hcl hk hmd h
  cases hm : (cv w).get? c with
  | some r =>
    obtain ⟨rfl, hj, hcv⟩ := synthesizeChild_hit O hA hw hm h
    rw [hcv]
    exact ⟨hj, hcl, hk, hmd, hm, cacheExtends_refl _, fun c' r' h' => Or.inl h'⟩
  | none =>
    obtain ⟨hj, hcl', hk', hmd', hext, hget, -, hgrow⟩ :=
      synthesizeChild_miss_nm O hA hD Gs hcG d ok hbody hC hslots hdomB hins hfne hcalls hcne entry closes hw
        hcl hk hmd hm h
    refine ⟨hj, hcl', hk', hmd', hget, hext, fun c' r' hc' => ?_⟩
    rcases hgrow c' r' hc' with h0 | h0 | h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr (List.mem_append_left _ h0))
    · exact Or.inr (Or.inr (List.mem_append_right _ h0))

/-- **A plain (non-memory) leaf: its one-step contract under the memory-aware clauses** (the NM form of `Tools.ShippingSharedLeafNL.leafKid_step`; same real run, only the cache clauses
differ).  Needed for a callee that has a memory child NEXT TO a call of a plain leaf. -/
theorem leafKid_step_nm (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {n : Name} (hl : LeafOK mctx mref cctx cref n) :
    ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D n [] := by
  intro D hD w w' y hw hcl hk hmd h
  cases hm : (cv w).get? n with
  | some r =>
    obtain ⟨rfl, hj, hc⟩ := synthesizeChild_hit O hA hw hm h
    rw [hc]
    exact ⟨hj, hcl, hk, hmd, hm, cacheExtends_refl _, fun c r' h' => Or.inl h'⟩
  | none =>
    obtain ⟨d, ok, hbody, hno, outTy, entry, closes⟩ := hl
    unfold synthesizeChild at h
    obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
    obtain ⟨hm1, hw1⟩ := jqc_cacheGet O hA hw hget
    have hc1 := cacheGet_cv O hA hw hget
    cases hc : m.get? n with
    | some r' => rw [hm1] at hc; rw [hm] at hc; cases hc
    | none =>
      simp only [hc] at h
      obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
      have hr : RealChildA O n r := RealChildA.of_jqc O hA hw1 hrun
      have hI := seqChild_of_realA O d ok hbody hno outTy entry closes hr
      obtain ⟨hw2, hk2⟩ := hkeep_nestedL O hA hD d.shape hno entry (closes mctx cctx)
        (fun c0 => leafTranslatorKeeps_of_machineData O hA (stableK O (D + 1) c0) d ok hbody)
        w1 r w2 hw1 hrun
      obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
      have hc3 := (O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw2.1.1 hmod).1
      have hj3 := jqc_insert_runs O hA hw2 hr hmod
      obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
      have hcv : cv w' = (cv w).insert n y := by rw [hc3, hk2, hc1]
      rw [hcv]
      refine ⟨hj3, cacheClosedNM_insert_leaf hcl hm hI.design, keyTop_insert hk hI.name,
        memDet_insert_leaf hmd hI.name hI.design, get?_insert_self _ _ _, cacheExtends_insert_missing y hm, ?_⟩
      intro c' r' hc'
      rcases insert_get_cases hc' with ⟨e, -⟩ | ⟨-, hc''⟩
      · exact Or.inr (Or.inl e)
      · exact Or.inl hc''

/-- the origin's child of each call, from the names: `TagsAgree` turns `memChild?` of the placeholder name into the origin's `child?`.  Calls are memory placeholders (built memory modules)
or calls of the declaration `G`. -/
theorem hcalls_of_names {shape : MachineShape} (hagree : Tools.ShippingInstTagged.TagsAgree shape) (G : Name)
    (h : ∀ x ∈ shape.instTagged, (∃ cb aw dw, memChild? x.1 = some (memModule cb aw dw)) ∨
      (memChild? x.1 = none ∧ x.1 = G)) :
    ∀ x ∈ shape.instTagged, (∃ md, x.2.child? = some md ∧ MemKid md) ∨ (x.2.child? = none ∧ x.1 = G) := by
  intro x hx
  have ha := hagree x hx
  have hc : memChild? x.1 = x.2.child? := Tools.ShippingInstTagged.memChild_of_tagAgrees ha
  rcases h x hx with ⟨cb, aw, dw, h1⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨memModule cb aw dw, hc ▸ h1, cb, aw, dw, rfl⟩
  · exact Or.inr ⟨hc ▸ h1, h2⟩

/-! ## The shared leaf WITH a memory child, and a callee over it -/

/-- every call of a memory-only machine carries a built memory module (the origin's child) -/
theorem memTags_of_data {d : MachineData} {aw dw : Nat}
    (hmem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      ∃ cb, memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw))
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape) :
    ∀ x ∈ d.shape.instTagged, ∃ md, x.2.child? = some md ∧ MemKid md := by
  intro x hx
  obtain ⟨k, hkT, rfl⟩ := List.mem_iff_getElem.mp hx
  have hk : k < d.shape.insts.length := by rw [← instTagged_length']; exact hkT
  obtain ⟨hkT', he⟩ := instTagged_getAt d.shape hk
  obtain ⟨cb, hc⟩ := hmem k hk
  have h := Tools.ShippingInstTagged.agree_at hagree hk
  rw [hc] at h
  rw [he]
  exact ⟨memModule cb aw dw, h.symm, cb, aw, dw, rfl⟩

/-- **The leaf with memory children: its one-step contract at every depth `≠ 0`.**  `MachineClosesAtA` of the leaf is DERIVED (`machineClosesAtA_of_memOnlyData_names`), not a
premise.  The leaf's calls are all memory placeholders of widths `aw`/`dw` (`MemOnlyData`, `MemOnlyCloseData` are decidable on the stored `machineData`); `hcne`: no placeholder is
the leaf's own name.  Premises: `O`, `T`, `hA`, `MachineDefines` of the leaf.  (The growth set is the placeholder names; they are not cache keys, but this is not used.) -/
theorem memLeaf_stepNM (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {c : Name} {d : MachineData} {nDecl aw dw : Nat}
    (hd : Tools.ShippingMemOnly.MemOnlyData d nDecl aw dw) (hcl : Tools.ShippingMemOnlyCloses.MemOnlyCloseData d)
    (hcne : ∀ k (hk : k < d.shape.insts.length), (d.shape.insts[k]).1 ≠ c)
    (entry : MachineDefines mctx mref cctx cref c d.shape) :
    ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D c (d.shape.insts.map (·.1)) := by
  intro D hD
  have h : StepNM (mref := mref) (cref := cref) O mctx cctx D c (d.shape.insts.map (·.1) ++ []) :=
    stepNM_of_data O hA hD ([] : List Name) (List.not_mem_nil) d hd.ok hd.body hd.calls hd.slots hd.domB hd.ins hd.fne
    (fun x hx => Or.inl (memTags_of_data hd.mem hd.agree x hx)) hcne entry
    (Tools.ShippingCallsMemA.machineClosesAtA_of_memOnlyData_names O T hA hd hcl)
  exact StepNM.mono (Gs' := d.shape.insts.map (·.1)) h (fun x hx => List.mem_append.mp hx |>.elim id (fun h0 => absurd h0 List.not_mem_nil))

/-- **A callee whose calls are all the shared leaf `G`** (the leaf's step contract at every depth `≠ 0` is the premise `hG`): its one-step contract at every depth `≠ 0`.
`closes` (`MachineClosesAtA` of the callee) stays a premise of this theorem: deriving it needs the `ChildIfaceP` of the memory-bearing leaf on the `RealChildA` side (residue R1). -/
theorem calleeOverLeaf_stepNM (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {C G : Name} (Gs : List Name) (hCG : C ∉ Gs) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ []) (hfne : d.shape.instFields ≠ [])
    (hleaf : ∀ x ∈ d.shape.instTagged, x.2.child? = none ∧ x.1 = G)
    (hG : ∀ D', D' ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D' G Gs)
    (hcne : ∀ k (hk : k < d.shape.insts.length), (d.shape.insts[k]).1 ≠ C)
    (entry : MachineDefines mctx mref cctx cref C d.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx C d.shape) :
    ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D C (d.shape.insts.map (·.1) ++ Gs) := by
  intro D hD
  exact stepNM_of_data O hA hD Gs hCG d ok hbody hC hslots hdomB hins hfne
    (fun x hx => Or.inr ⟨(hleaf x hx).1, (hleaf x hx).2 ▸ hG (D + 1) (Nat.succ_ne_zero D)⟩) hcne entry closes

/-- **The parent's closing over callees with step contracts** (K-ary closing, memory-aware): the pure `closeInstsG` of the children, the end cache is `CacheClosedNM`/`KeyTop`/`MemDet`,
hence `CacheCoh`; every call's child is the cache entry at its callee; any two children agree on same-named modules (`hcross`).  Every call is a callee (no memory entry of the parent). -/
theorem closing_nm (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (Gs : List Name)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hcalls : ∀ x ∈ shape.instTagged, x.2.child? = none ∧
      StepNM (mref := mref) (cref := cref) O mctx cctx D x.1 Gs)
    (hw : JQC O D w) (hcl : CacheClosedNM (cv w)) (hk : KeyTop (cv w)) (hmd : MemDet (cv w))
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧
      children.length = shape.insts.length ∧
      (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        (cv w').get? (shape.insts[k]).1 = some y) ∧
      JQC O D w' ∧ CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      CacheExtends (cv w) (cv w') ∧
      (∀ i (_hi : i < children.length) j (_hj : j < children.length) (y y' : Res), children[i]? = some y →
        children[j]? = some y' → ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) := by
  obtain ⟨children, hres, hlen, hks, hj, hcl', hk', hmd', hext, -⟩ :=
    closeInstsGM_gen O hA Gs (fun x hx => Or.inr (hcalls x hx)) hw hcl hk hmd hr
  have hget : ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
      (cv w').get? (shape.insts[k]).1 = some y := by
    intro k hkl
    rcases hks k hkl with ⟨md, h1, -, -⟩ | ⟨-, hy⟩
    · obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
      have := (hcalls _ (List.getElem_mem hkT)).1
      rw [he] at this
      rw [h1] at this
      cases this
    · exact hy
  have hcoh : CacheCoh (cv w') := cacheCoh_of_nm hcl' hk' hmd'
  refine ⟨children, hres, hlen, hget, hj, hcl', hk', hmd', hcoh, hext, ?_⟩
  intro i hi j hj0 y y' hy hy' a ha b hb hab
  have hi' : i < shape.insts.length := hlen ▸ hi
  have hj' : j < shape.insts.length := hlen ▸ hj0
  obtain ⟨y1, h1, g1⟩ := hget i hi'
  obtain ⟨y2, h2, g2⟩ := hget j hj'
  rw [hy] at h1; rw [hy'] at h2
  cases h1; cases h2
  exact hcoh _ _ _ _ g1 g2 a ha b hb hab

end Tools.ShippingMemLeafRun

#print axioms Tools.ShippingMemLeafRun.closeLoop_gen
#print axioms Tools.ShippingMemLeafRun.closeInstsGM_gen
#print axioms Tools.ShippingMemLeafRun.machineSynth_gen
#print axioms Tools.ShippingMemLeafRun.synthesizeChild_miss_nm
#print axioms Tools.ShippingMemLeafRun.stepNM_of_data
#print axioms Tools.ShippingMemLeafRun.memTags_of_data
#print axioms Tools.ShippingMemLeafRun.leafKid_step_nm
#print axioms Tools.ShippingMemLeafRun.hcalls_of_names
#print axioms Tools.ShippingMemLeafRun.memLeaf_stepNM
#print axioms Tools.ShippingMemLeafRun.calleeOverLeaf_stepNM
#print axioms Tools.ShippingMemLeafRun.closing_nm
