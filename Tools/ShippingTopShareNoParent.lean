import Tools.ShippingTopShareRet
-- BUILT (unit SR12): n4 exit 0 (Tools.ShippingTopShareNoParent); see REPORT-SR12.md for the final-SHA rebuild.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.
-- SCOPE (SR12, ledger L8ar): for the real `topshare` run, NO module of the core run's design `Dg` is named like the entry (`M.name`), so the entry's clean-up
-- `topMap M.name f` is the identity on `Dg` (`topMap_id`) and the returned `y.2` IS `Dg`.  This is DERIVED, not assumed:
--   * `closeInstsG_name_design`: the closing keeps the module name and the design is `designWith children d₀`;
--   * `noParent_of_cache`: a module of `designWith children d₀` is a module of some child, and by `CacheClosed` + `KeyTop` it is the top of a cached entry
--     named `ofDecl c'`; with `ofDecl` injective and `c` absent from the cache, none is named `ofDecl c`; `d₀.modules = []` (`closedBody_kinds_of_run`);
--   * `topshare_quad_keys` / `topshare_closing4_keys`: copies of `topshare_quad` / `topshare_closing4` (SR10) with ONE extra conclusion: every key of the
--     end cache is a start key, `c₁`, `c₂`, or a call of `d₁` / `d₂` (the growth information of `synthesizeChild_nonleaf_miss`, which the originals discard);
--   * `topshare_entry_run4_ret_np`: `topshare_entry_run4_ret` (same proof text) + `noclash`.
-- DATA premises (named, supplied by the instance from the real machine data): `hCp`/`hslotsp`/`hdomBp` of the parent (as in `closedBody_kinds_of_run`),
-- and the four name facts `c ≠ c₁`, `c ≠ c₂`, no call of `d₁`/`d₂` is `c`.  The generic theorem does NOT assume "no parent module".
namespace Tools.ShippingTopShareNoParent
open Tools.ShippingTopShareRun
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

/-- `closeInstsG` keeps the closed module's name and joins the children into the design. -/
theorem closeInstsG_name_design {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String} {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)) :
    m.name = m₀.name ∧ d = Sparkle.IR.Machine.designWith children d₀ := by
  refine ⟨?_, Tools.ShippingCacheCoherentClose.closeInstsG_design h⟩
  unfold Sparkle.IR.Machine.closeInstsG at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
    exact (Sparkle.IR.Machine.withClockFor_same children m₀).1
  · cases h

/-- **No module of the joined design is named like the entry's `ofDecl c`**, when every child is a cached entry of a closed `KeyTop` cache
that has no entry at `c`, the harness's own design has no module, and the closed module is named `ofDecl c`. -/
theorem noParent_of_cache {cache : Std.HashMap Name Res} (hcl : CacheClosed cache) (hk : KeyTop cache)
    {c : Name} (hnot : cache.get? c = none) {kids : List Res} (hkidIn : ∀ kd ∈ kids, ∃ c', cache.get? c' = some kd)
    {d₀ Dg : Sparkle.IR.AST.Design} (hd0 : d₀.modules = []) (hDg : Dg = designWith kids d₀)
    {M : Sparkle.IR.AST.Module} (hMc : M.name = Sparkle.IR.ModuleName.ofDecl c) :
    ∀ x ∈ Dg.modules, x.name ≠ M.name := by
  intro x hx hxn
  rw [hDg] at hx
  rcases Tools.ShippingSharedLeafExt.mem_designWith hx with h0 | h1
  · rw [hd0] at h0; cases h0
  · obtain ⟨kd, hkd, hak⟩ := h1
    obtain ⟨c', hc'⟩ := hkidIn kd hkd
    have hmods : x ∈ ModsOf kd := by
      rcases hak with h1 | h1
      · exact List.mem_cons_of_mem _ h1
      · rw [h1]; exact List.mem_cons_self ..
    obtain ⟨c'', r'', hr'', rfl⟩ := hcl c' kd hc' x hmods
    have hnm := hk c'' r'' hr''
    have : c'' = c := Tools.ShippingModuleName.ofDecl_injective (hnm.symm.trans (hxn.trans hMc))
    subst this
    rw [hnot] at hr''; cases hr''

/-- `topshare_quad` (SR10) with ONE extra conclusion: every key of the end cache is a start key, `c₁`, `c₂`, or a call of `d₁` / `d₂`. -/
theorem topshare_quad_keys (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
      (∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w₂').get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      (∀ c' r', (cv w₂').get? c' = some r' → (cv w).get? c' = some r' ∨ c' = c₁ ∨ c' = c₂ ∨
        c' ∈ d₁.shape.insts.map (·.1) ∨ c' ∈ d₂.shape.insts.map (·.1)) := by
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
  obtain ⟨hj2, hcl2, hk2, hext2, hget2, hkids2, hgrow2⟩ :=
    synthesizeChild_nonleaf_miss O hA hD d₂ ok₂ hbody₂ hC₂ hslots₂ hdomB₂ hins₂ hfne₂ hleaf₂ hcne₂
      entry₂ closes₂ hj1' (by rw [hcv1']; exact hcl1) (by rw [hcv1']; exact hk1) hm₂' h₂
  obtain ⟨hy2, hj2', hcv2'⟩ := synthesizeChild_hit O hA hj2 hget2 h₂'
  have hcoh : CacheCoh (cv w₂) :=
    cacheCoh_of_closed_topAgree hcl2 (cacheTopAgree_of_keyTop hk2)
  have hy1c : (cv w₂).get? c₁ = some y₁ := hext2 c₁ y₁ (by rw [hcv1']; exact hget1)
  have hkeys : ∀ c' r', (cv w₂).get? c' = some r' → (cv w).get? c' = some r' ∨ c' = c₁ ∨ c' = c₂ ∨
      c' ∈ d₁.shape.insts.map (·.1) ∨ c' ∈ d₂.shape.insts.map (·.1) := by
    intro c' r' hq
    rcases hgrow2 c' r' hq with h0 | h0 | h0
    · rw [hcv1'] at h0
      rcases hgrow1 c' r' h0 with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inl h0))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h0)))
  rw [hcv2'] at *
  refine ⟨hy1, hy2, hj2', hcl2, hk2, hcoh, hy1c, hget2,
    fun a ha b hb hab => hcoh c₁ y₁ c₂ y₂ hy1c hget2 a ha b hb hab, ?_, hkeys⟩
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

/-- `topshare_closing4` (SR10) with the key information of `topshare_quad_keys`. -/
theorem topshare_closing4_keys (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
      (∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w').get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      (∀ c' r', (cv w').get? c' = some r' → (cv w).get? c' = some r' ∨ c' = c₁ ∨ c' = c₂ ∨
        c' ∈ d₁.shape.insts.map (·.1) ∨ c' ∈ d₂.shape.insts.map (·.1)) := by
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
  obtain ⟨e1, e2, hj, hc, hkt, hcoh, hg1, hg2, hcross, hshared, hkeys⟩ :=
    topshare_quad_keys O hA hD hc12 d₁ d₂ K₁ K₂ hc2not hwa hcl' hk' hm₁' hm₂' h1 h1' h2 h2'
  have hlist : children = [y₁, y₁, y₂, y₂] := by rw [hchildren, e1, e2]; rfl
  subst hlist
  exact ⟨y₁, y₂, heq, hj, hc, hkt, hcoh, hg1, hg2, hcross, hshared, by rw [← hcva]; exact hkeys⟩

/-- **`topshare_entry_run4_ret` (SR10, same proof text) + `noclash`: no module of the core run's design `Dg` is named like `M`.**
Extra DATA premises (supplied by the instance from the real machine data): `hCp`/`hslotsp`/`hdomBp` of the parent machine, and the name facts
`c ≠ c₁`, `c ≠ c₂`, `c` is no call of `d₁` / `d₂`.  WORDING: no module of `Dg` is named `M.name`; not a statement about the semantics. -/
theorem topshare_entry_run4_ret_np (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {c c₁ c₂ : Name} (hc12 : c₁ ≠ c₂) {o₁ o₁' o₂ o₂' : InstOrigin}
    (ho₁ : o₁.child? = none) (ho₁' : o₁'.child? = none) (ho₂ : o₂.child? = none) (ho₂' : o₂'.child? = none)
    (dp : MachineData) (okp : dp.ok = true)
    (hbodyp : dp.shape.body = quote dp.dom
      (fun j => inputExpr dp.shape.binders.length (dp.bpos j))
      (fun j => inputExpr dp.shape.binders.length (dp.vpos j)) dp.packed)
    (hinsp : dp.shape.insts ≠ []) (hfnep : dp.shape.instFields ≠ [])
    {nDecl : Nat} (hCp : dp.callsOk nDecl = true) (hslotsp : dp.ss.length = dp.shape.layout.slots.length)
    (hdomBp : ∀ b ∈ dp.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hP : dp.shape.instTagged = [(c₁, o₁), (c₁, o₁'), (c₂, o₂), (c₂, o₂')])
    (entryP : MachineDefines mctx mref cctx cref c dp.shape)
    (closes0 : MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx c dp.shape)
    (d₁ d₂ : MachineData) (K₁ : CalleeOK O mctx cctx c₁ d₁) (K₂ : CalleeOK O mctx cctx c₂ d₂)
    (hc2not : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₂)
    (hcc₁ : c ≠ c₁) (hcc₂ : c ≠ c₂)
    (hcd₁ : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c)
    (hcd₂ : ∀ k (hk : k < d₂.shape.insts.length), (d₂.shape.insts[k]).1 ≠ c)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      closeLets dp.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dp.shape) dp.shape.insts.length
        dp.shape.layout.slots.length (t.inputs.map (·.name)) (dp.shape.insts.map (·.2.1))
        dp.shape.instFields [y₁, y₁, y₂, y₂] (closeMachine dp.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? c₁ = some y₁ ∧ (cv w10).get? c₂ = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) := by
  obtain ⟨M, Dg, wc, hcore, htail, hpost⟩ := full_run_tracked O hA (D := 0) h
  obtain ⟨tenv, b, w9, w10, hmach, hw9, hc9, htl⟩ := core_run_tracked0' O hA entryP closes0 hw hcore
  obtain ⟨t, t', d₀, w1, run, hlets, hj1, hcv1, hclose⟩ :=
    machineSynth_closing_split O hA (D' := 1) dp okp hbodyp hinsp hfnep hw9 hmach
  have hcvw1 : cv w1 = {} := hcv1.trans hc9
  obtain ⟨y₁, y₂, hrr, hj, hc, hk, hcoh, hg1, hg2, hcross, hshared, hkeys⟩ :=
    topshare_closing4_keys O hA (D := 1) Nat.one_ne_zero hc12 ho₁ ho₁' ho₂ ho₂' hP d₁ d₂ K₁ K₂ hc2not hj1
      (by rw [hcvw1]; exact cacheClosed_empty) (by rw [hcvw1]; exact keyTop_empty)
      (by rw [hcvw1]; simp) (by rw [hcvw1]; simp) hclose
  obtain ⟨hjc, hcvc⟩ := htl hj
  obtain ⟨hj2, hcv2⟩ := htail hjc
  -- the parent key `c` is absent from the end cache
  have hnot : (cv w10).get? c = none := by
    cases hq : (cv w10).get? c with
    | none => rfl
    | some q =>
      rcases hkeys c q hq with h0 | h0 | h0 | h0 | h0
      · rw [hcvw1] at h0; simp at h0
      · exact absurd h0 hcc₁
      · exact absurd h0 hcc₂
      · obtain ⟨x, hx, hxc⟩ := List.mem_map.mp h0
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        exact absurd hxc (hcd₁ i hi)
      · obtain ⟨x, hx, hxc⟩ := List.mem_map.mp h0
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        exact absurd hxc (hcd₂ i hi)
  obtain ⟨-, hname0, hd0⟩ := closedBody_kinds_of_run dp okp hbodyp hCp hslotsp hdomBp run hlets
  obtain ⟨hMn, hDeq⟩ := closeInstsG_name_design hrr.symm
  have hMc : M.name = Sparkle.IR.ModuleName.ofDecl c := hMn.trans hname0
  have hnoclash : ∀ x ∈ Dg.modules, x.name ≠ M.name :=
    noParent_of_cache hc hk hnot (kids := [y₁, y₁, y₂, y₂])
      (fun kd hkd => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkd
        rcases hkd with rfl | rfl | rfl | rfl
        · exact ⟨_, hg1⟩
        · exact ⟨_, hg1⟩
        · exact ⟨_, hg2⟩
        · exact ⟨_, hg2⟩) hd0 hDeq hMc
  exact ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hrr, hj2, hcv2.trans hcvc, hc, hk, hcoh, hg1, hg2,
    hcross, hshared, hcore, hcvc, hpost, hnoclash⟩

/-- With no module of `Dg` named `M.name`, the entry's clean-up `topMap` is the identity: `y.2 = Dg` in both clean-up cases. -/
theorem returned_design_eq {M : Sparkle.IR.AST.Module} {Dg y2 : Sparkle.IR.AST.Design}
    (hno : ∀ x ∈ Dg.modules, x.name ≠ M.name)
    (h : y2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg ∨
      y2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
        (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg)) : y2 = Dg := by
  have h1 : topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg = Dg := topMap_id _ _ _ hno
  rcases h with h | h
  · rw [h, h1]
  · rw [h, h1, topMap_id _ _ _ hno]

end Tools.ShippingTopShareNoParent

#print axioms Tools.ShippingTopShareNoParent.closeInstsG_name_design
#print axioms Tools.ShippingTopShareNoParent.noParent_of_cache
#print axioms Tools.ShippingTopShareNoParent.topshare_quad_keys
#print axioms Tools.ShippingTopShareNoParent.topshare_closing4_keys
#print axioms Tools.ShippingTopShareNoParent.topshare_entry_run4_ret_np
#print axioms Tools.ShippingTopShareNoParent.returned_design_eq
