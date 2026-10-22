import Tools.ShippingTopShareNoParent
import Tools.ShippingQuadLeafGeneric
-- UNBUILT (unit SR21): see STATUS-SR21.md for the run names.
-- SCOPE (binding, ledger L8ba): the RUNTIME layer of the shared-leaf class generalised from TWO callees to a LIST of K callees.  A parent whose call list is
-- `cs.flatMap (fun e => [e.c, e.c])` (every callee called twice: a cache MISS then a cache HIT, all origins without a memory child) and whose callees are
-- pairwise different, whose calls are never one of the callees (`hnc`), is closed by `synthesizeChild` on the K groups in order.  PROVED here (by induction on
-- the callee list, no hypothesis on K): `kary_group` (one miss + one hit), `kary_loop` (the `List.mapM.loop` over the K groups), `kary_closing` (the parent's
-- `closeInstsGM` is the pure `closeInstsG` of `Y.flatMap (fun y => [y, y])`, with the cache facts), `kary_machineSynth_ne_none` (the parent's machine synthesis
-- does not fall back at the start world), `kary_entry_run_ret_np` (the parent's own run with the returned value linked and no module of `Dg` named like the entry).
-- These are the K-ary forms of `topshare_quad_keys`, `topshare_closing4_keys`, `machineSynth_ne_none4`, `topshare_entry_run4_ret_np` (`Tools/ShippingTopShareRun.lean`,
-- `Tools/ShippingTopShareNoParent.lean`), which stay untouched.  The statements are over `MachineData` and names; nothing about a particular declaration occurs.
-- PREMISES (named): `CalleeOK` of every callee (data facts + `MachineDefines` + `MachineClosesAtA` of the callee), the pairwise distinct callee names, the call/callee
-- name separation `hnc`, the parent's data facts, `JQC O 0 w`.  `RealChildA` is a history of past synthesis results, not semantic correctness in the current environment.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingKaryRun
open Tools.ShippingTopShareRun Tools.ShippingTopShareNoParent
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

/-- One callee of a parent: its declaration name, its machine data and its number of declared inputs. -/
structure KCal where
  c : Name
  d : MachineData
  n : Nat

/-- the duplicated list is indexed by half the position -/
theorem dup_getElem? {α β : Type} (g : α → β) (l : List α) (k : Nat) :
    (l.flatMap fun a => [g a, g a])[k]? = (l[k / 2]?).map g := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    rcases k with _ | _ | k
    · simp
    · simp
    · have h : (k + 1 + 1) / 2 = k / 2 + 1 := by omega
      rw [h]
      simp [List.flatMap_cons, ih]

theorem dup_length' {α β : Type} (g : α → β) (l : List α) : (l.flatMap fun a => [g a, g a]).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

/-- **ONE callee, called twice: a cache MISS then a cache HIT.**  (`topshare_quad_keys` for one callee.) -/
theorem kary_group (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {c : Name} {d : MachineData} (K : CalleeOK O mctx cctx c d)
    {w w₁ w₂ : Void IO.RealWorld} {y y' : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w)) (hm : (cv w).get? c = none)
    (h₁ : RunsTo (synthesizeChild c) mctx mref cctx cref w y w₁)
    (h₂ : RunsTo (synthesizeChild c) mctx mref cctx cref w₁ y' w₂) :
    y' = y ∧ JQC O D w₂ ∧ CacheClosed (cv w₂) ∧ KeyTop (cv w₂) ∧ CacheExtends (cv w) (cv w₂) ∧
      (cv w₂).get? c = some y ∧
      (∀ k (hk : k < d.shape.insts.length), ∃ e, (cv w₂).get? (d.shape.insts[k]).1 = some e ∧
        ∃ a ∈ y.2.modules, a.name = e.1.name) ∧
      (∀ c' r', (cv w₂).get? c' = some r' → (cv w).get? c' = some r' ∨ c' = c ∨
        c' ∈ d.shape.insts.map (·.1)) := by
  obtain ⟨ok, hbody, ⟨n, hC, hdomB⟩, hslots, hins, hfne, hleaf, hcne, entry, closes⟩ := K
  obtain ⟨hj1, hcl1, hk1, hext1, hget1, hkids1, hgrow1⟩ :=
    synthesizeChild_nonleaf_miss O hA hD d ok hbody hC hslots hdomB hins hfne hleaf hcne entry closes hw hcl hk hm h₁
  obtain ⟨hy, hj2, hcv2⟩ := synthesizeChild_hit O hA hj1 hget1 h₂
  rw [hcv2]
  exact ⟨hy, hj2, hcl1, hk1, hext1, hget1, hkids1, hgrow1⟩

/-- **The K groups, by induction on the callee list.**  A returning `List.mapM.loop f L acc` over the call list `cs.flatMap (fun e => [e.c, e.c])`, all origins
without a child (`f` is `synthesizeChild` on those), from a closed `KeyTop` `JQC` world in which no callee is cached, returns `Y.flatMap (fun y => [y, y])` for
one result `Y[j]` per callee, and the end cache is closed, `KeyTop`, extends the start cache, holds `Y[j]` at the callee `cs[j].c`, holds for every call of
`cs[j]` an entry whose top is named like a module of `Y[j]`, and has only keys that are start keys, callees, or calls of a callee. -/
theorem kary_loop (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {f : Name × InstOrigin → MetaM Res} :
    ∀ (cs : List KCal) (L : List (Name × InstOrigin)) (acc r : List Res) (w w' : Void IO.RealWorld),
      (∀ e ∈ cs, CalleeOK O mctx cctx e.c e.d) → (cs.map (·.c)).Nodup →
      (∀ e ∈ cs, ∀ e' ∈ cs, ∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) →
      L.map (·.1) = cs.flatMap (fun e => [e.c, e.c]) → (∀ x ∈ L, x.2.child? = none) →
      JQC O D w → CacheClosed (cv w) → KeyTop (cv w) → (∀ e ∈ cs, (cv w).get? e.c = none) →
      RunsTo (List.mapM.loop f L acc) mctx mref cctx cref w r w' →
      (∀ x : Name × InstOrigin, x.2.child? = none → f x = synthesizeChild x.1) →
      ∃ Y : List Res, Y.length = cs.length ∧ r = acc.reverse ++ Y.flatMap (fun y => [y, y]) ∧
        JQC O D w' ∧ CacheClosed (cv w') ∧ KeyTop (cv w') ∧ CacheExtends (cv w) (cv w') ∧
        (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w').get? (cs[j]).c = some y) ∧
        (∀ j (hj : j < cs.length) (y : Res), Y[j]? = some y →
          ∀ k (hk : k < (cs[j]).d.shape.insts.length), ∃ e, (cv w').get? ((cs[j]).d.shape.insts[k]).1 = some e ∧
            ∃ a ∈ y.2.modules, a.name = e.1.name) ∧
        (∀ c' r', (cv w').get? c' = some r' → (cv w).get? c' = some r' ∨ c' ∈ cs.map (·.c) ∨
          c' ∈ cs.flatMap (fun e => e.d.shape.insts.map (·.1))) := by
  intro cs
  induction cs with
  | nil =>
    intro L acc r w w' hK hnd hnc hL hch hw hcl hk habs h hf
    have hL0 : L = [] := by simpa using hL
    subst hL0
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    refine ⟨[], rfl, by simp, hw, hcl, hk, fun _ _ h => h, ?_, ?_, ?_⟩
    · intro j hj; exact absurd hj (Nat.not_lt_zero _)
    · intro j hj; exact absurd hj (Nat.not_lt_zero _)
    · intro c' r' h; exact Or.inl h
  | cons e cs ih =>
    intro L acc r w w' hK hnd hnc hL hch hw hcl hk habs h hf
    rcases L with _ | ⟨x1, _ | ⟨x2, L'⟩⟩
    · simp at hL
    · simp at hL
    · simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.cons.injEq] at hL
      obtain ⟨e1, e2, hL'⟩ := hL
      have hx1 : x1.2.child? = none := hch x1 (List.mem_cons_self ..)
      have hx2 : x2.2.child? = none := hch x2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
      obtain ⟨y', w2, hy', h⟩ := RunsTo.bind h
      rw [hf x1 hx1, e1] at hy
      rw [hf x2 hx2, e2] at hy'
      have hKe : CalleeOK O mctx cctx e.c e.d := hK e (List.mem_cons_self ..)
      have hme : (cv w).get? e.c = none := habs e (List.mem_cons_self ..)
      obtain ⟨hyy, hj2, hcl2, hk2, hext2, hget2, hkids2, hgrow2⟩ :=
        kary_group O hA hD hKe hw hcl hk hme hy hy'
      have hyy' : y = y' := hyy.symm
      subst hyy'
      have hnd' : e.c ∉ cs.map (·.c) ∧ (cs.map (·.c)).Nodup := by
        simpa [List.nodup_cons] using hnd
      have habs' : ∀ e' ∈ cs, (cv w2).get? e'.c = none := by
        intro e' he'
        cases hq : (cv w2).get? e'.c with
        | none => rfl
        | some q =>
          rcases hgrow2 e'.c q hq with h0 | h0 | h0
          · rw [habs e' (List.mem_cons_of_mem _ he')] at h0; cases h0
          · exact absurd (h0 ▸ List.mem_map_of_mem (f := (·.c)) he') hnd'.1
          · obtain ⟨x, hx, hxc⟩ := List.mem_map.mp h0
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
            exact absurd hxc (hnc e (List.mem_cons_self ..) e' (List.mem_cons_of_mem _ he') i hi)
      obtain ⟨Y', hlen, hr, hj, hcl', hk', hext', hget', hkids', hgrow'⟩ :=
        ih L' (y :: y :: acc) r w2 w'
          (fun e' he' => hK e' (List.mem_cons_of_mem _ he')) hnd'.2
          (fun a ha b hb k hk => hnc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) k hk)
          hL' (fun x hx => hch x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
          hj2 hcl2 hk2 habs' h hf
      refine ⟨y :: Y', by simp [hlen], ?_, hj, hcl', hk', fun c r' h0 => hext' c r' (hext2 c r' h0), ?_, ?_, ?_⟩
      · rw [hr]; simp
      · intro j hj0
        rcases j with _ | j
        · exact ⟨y, rfl, hext' _ _ hget2⟩
        · exact hget' j (Nat.lt_of_succ_lt_succ hj0)
      · intro j hj0 y0 hy0
        rcases j with _ | j
        · have : y0 = y := (Option.some.inj hy0).symm
          subst this
          intro k hk0
          obtain ⟨e0, he0, hm0⟩ := hkids2 k hk0
          exact ⟨e0, hext' _ _ he0, hm0⟩
        · exact hkids' j (Nat.lt_of_succ_lt_succ hj0) y0 hy0
      · intro c' r' h0
        rcases hgrow' c' r' h0 with h1 | h1 | h1
        · rcases hgrow2 c' r' h1 with h2 | h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inl (by simp [h2]))
          · exact Or.inr (Or.inr (by simp [List.mem_append, h2]))
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
        · exact Or.inr (Or.inr (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr h1))

/-- **The parent's `closeInstsGM` over K groups** (K-ary `topshare_closing4_keys`): the result is the pure `closeInstsG` of the duplicated list of results, the end
cache is closed, `KeyTop`, `CacheCoh`; `Y[j]` is cached at the callee `cs[j].c`; any two results agree on their module names; the shared-leaf clause for every pair of
calls; the growth of the keys. -/
theorem kary_closing (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) (cs : List KCal) {shape : MachineShape}
    (hK : ∀ e ∈ cs, CalleeOK O mctx cctx e.c e.d) (hnd : (cs.map (·.c)).Nodup)
    (hnc : ∀ e ∈ cs, ∀ e' ∈ cs, ∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c)
    (hP : shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c]))
    (hch : ∀ x ∈ shape.instTagged, x.2.child? = none)
    {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQC O D w) (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w))
    (habs : ∀ e ∈ cs, (cv w).get? e.c = none)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ Y : List Res, Y.length = cs.length ∧
      r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields (Y.flatMap fun y => [y, y]) (m₀, d₀) ∧
      JQC O D w' ∧ CacheClosed (cv w') ∧ KeyTop (cv w') ∧ CacheCoh (cv w') ∧
      (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w').get? (cs[j]).c = some y) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (cs[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (cs[j]).d.shape.insts.length),
          ((cs[i]).d.shape.insts[k₁]).1 = ((cs[j]).d.shape.insts[k₂]).1 →
          ∃ e, (cv w').get? (((cs[i]).d.shape.insts[k₁]).1) = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules) ∧
      (∀ c' r', (cv w').get? c' = some r' → (cv w).get? c' = some r' ∨ c' ∈ cs.map (·.c) ∨
        c' ∈ cs.flatMap (fun e => e.d.shape.insts.map (·.1))) := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, wa, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨hwa, rfl⟩ := triple_runs (tripleC_synthRead O hA D) hw hget
  have hcva : cv wa = cv w := by
    have hk0 := O.frame hA _ FramedA.synthGet w hw.1.1
    rw [endW_of_runs hget] at hk0
    exact hk0.1
  dsimp only at hr
  obtain ⟨children, wb, hch', hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  have hcl' : CacheClosed (cv wa) := by rw [hcva]; exact hcl
  have hk' : KeyTop (cv wa) := by rw [hcva]; exact hk
  have habs' : ∀ e ∈ cs, (cv wa).get? e.c = none := by
    intro e he; rw [hcva]; exact habs e he
  obtain ⟨Y, hlen, hrr, hj, hcl2, hk2, hext, hget', hkids, hgrow⟩ :=
    kary_loop O hA hD cs shape.instTagged [] children wa w' hK hnd hnc hP hch hwa hcl' hk' habs' hch'
      (fun ⟨c, o⟩ hx => by
        simp only [] at hx ⊢
        simp [hx])
  have hcoh : CacheCoh (cv w') := cacheCoh_of_closed_topAgree hcl2 (cacheTopAgree_of_keyTop hk2)
  have hchildren : children = Y.flatMap (fun y => [y, y]) := by rw [hrr]; simp
  refine ⟨Y, hlen, by rw [hchildren] at heq; first | exact heq | exact heq.symm, hj, hcl2, hk2, hcoh, hget', ?_, ?_, ?_⟩
  · intro i hi j hj0 y y' hy hy' a ha b hb hab
    obtain ⟨y1, hy1, hg1⟩ := hget' i hi
    obtain ⟨y2, hy2, hg2⟩ := hget' j hj0
    rw [hy] at hy1; rw [hy'] at hy2
    cases hy1; cases hy2
    exact hcoh _ _ _ _ hg1 hg2 a ha b hb hab
  · intro i hi j hj0 y y' hy hy' k₁ hk₁ k₂ hk₂ hn
    obtain ⟨y1, hy1, hg1⟩ := hget' i hi
    obtain ⟨y2, hy2, hg2⟩ := hget' j hj0
    rw [hy] at hy1; rw [hy'] at hy2
    cases hy1; cases hy2
    obtain ⟨e₁, he₁, a, ha, han⟩ := hkids i hi y hy k₁ hk₁
    obtain ⟨e₂, he₂, b, hb, hbn⟩ := hkids j hj0 y' hy' k₂ hk₂
    rw [← hn] at he₂
    have hee : e₂ = e₁ := Option.some.inj (he₂.symm.trans he₁)
    subst hee
    refine ⟨e₂, he₁, ?_, ?_⟩
    · have : a = e₂.1 := hcoh _ _ _ e₂ hg1 he₁ a (List.mem_cons_of_mem _ ha) e₂.1 (List.mem_cons_self ..) han
      rw [← this]; exact ha
    · have : b = e₂.1 := hcoh _ _ _ e₂ hg2 he₂ b (List.mem_cons_of_mem _ hb) e₂.1 (List.mem_cons_self ..) hbn
      rw [← this]; exact hb
  · intro c' r' h0
    rcases hgrow c' r' h0 with h1 | h1
    · left; rw [← hcva]; exact h1
    · exact Or.inr h1

/-- `insts` names of a K-grouped call list: call `k` is a call of the callee `k / 2`. -/
theorem kary_insts_names {shape : MachineShape} {cs : List KCal}
    (hP : shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c])) :
    ∀ k (hk : k < shape.insts.length), (cs[k / 2]?).map (·.c) = some (shape.insts[k]).1 := by
  intro k hk
  have h1 := dup_getElem? (fun e : KCal => e.c) cs k
  rw [← h1, ← hP, Tools.ShippingInstTagged.instTagged_map_fst]
  simp [List.getElem?_eq_getElem hk]

theorem kary_insts_length {shape : MachineShape} {cs : List KCal}
    (hP : shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c])) :
    shape.insts.length = 2 * cs.length := by
  have h := congrArg List.length hP
  simp only [List.length_map, Tools.ShippingInstTagged.instTagged_length] at h
  rw [h]
  exact dup_length' (fun e : KCal => e.c) cs

end Tools.ShippingKaryRun
