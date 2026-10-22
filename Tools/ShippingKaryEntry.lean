import Tools.ShippingKaryRun
-- UNBUILT (unit SR21): see STATUS-SR21.md for the run names.
-- SCOPE (binding, ledger L8ba): the parent-level RUN theorems of the K-callee shared-leaf class, on top of `Tools/ShippingKaryRun.lean` (`kary_closing`).  PROVED here, by
-- the same proofs as the two-callee forms, with the list of callees `cs : List KCal` in place of `c₁ c₂ d₁ d₂`:
--  * `kary_machineSynth_ne_none` (K-ary `machineSynth_ne_none4`): the parent's machine synthesis does not fall back at the entry's start world (`JQC O 1`, cache `{}`);
--  * `kary_entry_run_ret_np` (K-ary `topshare_entry_run4_ret_np`): the parent's own run (`D = 0`) with the returned value linked to the core run's `(M, Dg)` and NO module of `Dg` named like
--    the entry; the cache facts of the K results.
-- The statements are over `MachineData`, names and the list `cs`; no declaration of any example occurs.  PREMISES (named): `CalleeOK` of every callee, distinct callee names, `hnc`, the data
-- facts of the parent (`hargsN`, `hfieldOut`, `hfieldsNd`, `hsep`, `hparent`, `hfresh`, `hparentD`, `hmk`), the interface of each result (`hI`: from `RealChildA`, a history of past
-- synthesis results, not semantic correctness in the current environment).  No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingKaryEntry
open Tools.ShippingKaryRun
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

theorem dup_getElem?_id {α : Type} (l : List α) (k : Nat) : (l.flatMap fun a => [a, a])[k]? = l[k / 2]? := by
  simpa using dup_getElem? (fun a : α => a) l k

theorem dup_length {α : Type} (l : List α) : (l.flatMap fun a => [a, a]).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]; omega

/-- distinct names: the callee index is determined by the name -/
theorem kary_idx_of_name {cs : List KCal} (hnd : (cs.map (·.c)).Nodup) {a b : Nat} {x y : KCal}
    (hx : cs[a]? = some x) (hy : cs[b]? = some y) (h : x.c = y.c) : a = b := by
  have ha := (List.getElem?_eq_some_iff.mp hx).1
  exact (List.getElem?_inj (l := cs.map (·.c)) (i := a) (j := b) (by simpa using ha) hnd).mp
    (by simp [List.getElem?_map, hx, hy, h])

/-- **The parent's machine synthesis does not fall back at the entry's start world** (K-ary `machineSynth_ne_none4`). -/
theorem kary_machineSynth_ne_none (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (cs : List KCal) {c : Name}
    (hK : ∀ e ∈ cs, CalleeOK O mctx cctx e.c e.d) (hnd : (cs.map (·.c)).Nodup)
    (hnc : ∀ e ∈ cs, ∀ e' ∈ cs, ∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c)
    (dp : MachineData) (okp : dp.ok = true)
    (hbodyp : dp.shape.body = quote dp.dom
      (fun j => inputExpr dp.shape.binders.length (dp.bpos j))
      (fun j => inputExpr dp.shape.binders.length (dp.vpos j)) dp.packed)
    (haliasp : dp.letsAliasOk = true)
    {nDecl : Nat} (hCp : dp.callsOk nDecl = true)
    (hslotsp : dp.ss.length = dp.shape.layout.slots.length)
    (hdomBp : ∀ b ∈ dp.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hinsp : dp.shape.insts ≠ []) (hfnep : dp.shape.instFields ≠ [])
    (hP : dp.shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c]))
    (hchild : ∀ x ∈ dp.shape.instTagged, x.2.child? = none)
    (hmk : ∀ k (hk : k < dp.shape.insts.length), memKey (originAt dp.shape k) = none)
    (nameK : Nat → String) (nk : Nat → Nat) (outsK : Nat → List String) (namesK : Nat → List String)
    (hI : ∀ (j : Nat) (hj : j < cs.length) (y : Res), RealChildA O (cs[j]).c y → ∀ k, k / 2 = j →
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
      obtain ⟨Y, hlen, hrr, hj, hc, hkt, hcoh, hget, hcross, hshared, hkeys⟩ :=
        kary_closing O hA (D := 1) Nat.one_ne_zero cs hK hnd hnc hP hchild hw1.1
          (by rw [hcvw1]; exact cacheClosed_empty) (by rw [hcvw1]; exact keyTop_empty)
          (by intro e he; rw [hcvw1]; simp) hr
      have hnm := kary_insts_names hP
      have hlenI := kary_insts_length hP
      have hch : ∀ k, (Y.flatMap fun y => [y, y])[k]? = Y[k / 2]? := dup_getElem?_id Y
      have hsome := closeInstsG_of_kidsPT (tenv := tenv) (declName := c) dp okp hbodyp hCp hslotsp hdomBp
        (logProf := profLogIO b) (t := t) (t' := t') (d₀ := d') (children := Y.flatMap fun y => [y, y])
        run.mreturns ht' (by rw [dup_length, hlen, hlenI]) nameK nk outsK namesK
        (by
          intro k c' hk
          rw [hch] at hk
          have hk2 : k / 2 < cs.length := by
            have := (List.getElem?_eq_some_iff.mp hk).1
            omega
          obtain ⟨y, hy, hg⟩ := hget (k / 2) hk2
          rw [hy] at hk
          have hyc : y = c' := Option.some.inj hk
          subst hyc
          exact hI (k / 2) hk2 y (hj.2 _ _ hg) k rfl)
        (by
          intro i j hi hj0 hnm' hmk'
          have e1 := hnm i hi
          have e2 := hnm j hj0
          have hij : i / 2 = j / 2 := by
            obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.mp e1
            obtain ⟨y, hy, hye⟩ := Option.map_eq_some_iff.mp e2
            exact kary_idx_of_name hnd hx hy (by rw [hxe, hye]; exact hnm')
          rw [hch, hch, hij])
        (by
          intro i j hi hj0 ci cj hci hcj hne a ha b hb hab
          have e1 := hnm i hi
          have e2 := hnm j hj0
          rw [hch] at hci hcj
          have hi2 : i / 2 < cs.length := by omega
          have hj2 : j / 2 < cs.length := by omega
          have hne2 : i / 2 ≠ j / 2 := by
            intro hij
            apply hne
            refine ⟨?_, by rw [hmk i hi, hmk j hj0]⟩
            rw [hij] at e1
            rw [e1] at e2
            exact Option.some.inj e2
          exact hcross (i / 2) hi2 (j / 2) hj2 ci cj hci hcj a ha b hb hab)
        hargsN hfieldOut hfieldsNd hsep hparent hfresh hparentD
      intro h
      rw [h] at hrr
      rw [← hrr] at hsome
      simp at hsome

/-- **The parent's own run with the returned value linked and no parent module in `Dg`** (K-ary `topshare_entry_run4_ret_np`). -/
theorem kary_entry_run_ret_np (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (cs : List KCal) {c : Name}
    (hK : ∀ e ∈ cs, CalleeOK O mctx cctx e.c e.d) (hnd : (cs.map (·.c)).Nodup)
    (hnc : ∀ e ∈ cs, ∀ e' ∈ cs, ∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c)
    (dp : MachineData) (okp : dp.ok = true)
    (hbodyp : dp.shape.body = quote dp.dom
      (fun j => inputExpr dp.shape.binders.length (dp.bpos j))
      (fun j => inputExpr dp.shape.binders.length (dp.vpos j)) dp.packed)
    (hinsp : dp.shape.insts ≠ []) (hfnep : dp.shape.instFields ≠ [])
    {nDecl : Nat} (hCp : dp.callsOk nDecl = true) (hslotsp : dp.ss.length = dp.shape.layout.slots.length)
    (hdomBp : ∀ b ∈ dp.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hP : dp.shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c]))
    (hchild : ∀ x ∈ dp.shape.instTagged, x.2.child? = none)
    (entryP : MachineDefines mctx mref cctx cref c dp.shape)
    (closes0 : MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx c dp.shape)
    (hcc : ∀ e ∈ cs, c ≠ e.c)
    (hcd : ∀ e ∈ cs, ∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ c)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = cs.length ∧
      closeLets dp.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dp.shape) dp.shape.insts.length
        dp.shape.layout.slots.length (t.inputs.map (·.name)) (dp.shape.insts.map (·.2.1))
        dp.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine dp.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (cs[j]).c = some y) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (cs[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (cs[j]).d.shape.insts.length),
          ((cs[i]).d.shape.insts[k₁]).1 = ((cs[j]).d.shape.insts[k₂]).1 →
          ∃ e, (cv w10).get? (((cs[i]).d.shape.insts[k₁]).1) = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules) ∧
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
  obtain ⟨Y, hlen, hrr, hj, hc, hk, hcoh, hget, hcross, hshared, hkeys⟩ :=
    kary_closing O hA (D := 1) Nat.one_ne_zero cs hK hnd hnc hP hchild hj1
      (by rw [hcvw1]; exact cacheClosed_empty) (by rw [hcvw1]; exact keyTop_empty)
      (by intro e he; rw [hcvw1]; simp) hclose
  obtain ⟨hjc, hcvc⟩ := htl hj
  obtain ⟨hj2, hcv2⟩ := htail hjc
  have hnot : (cv w10).get? c = none := by
    cases hq : (cv w10).get? c with
    | none => rfl
    | some q =>
      rcases hkeys c q hq with h0 | h0 | h0
      · rw [hcvw1] at h0; simp at h0
      · obtain ⟨e, he, hec⟩ := List.mem_map.mp h0
        exact absurd hec.symm (hcc e he)
      · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp h0
        obtain ⟨x, hx1, hx2⟩ := List.mem_map.mp hx
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx1
        exact absurd hx2 (hcd e he i hi)
  obtain ⟨-, hname0, hd0⟩ := closedBody_kinds_of_run dp okp hbodyp hCp hslotsp hdomBp run hlets
  obtain ⟨hMn, hDeq⟩ := closeInstsG_name_design hrr.symm
  have hMc : M.name = Sparkle.IR.ModuleName.ofDecl c := hMn.trans hname0
  have hnoclash : ∀ x ∈ Dg.modules, x.name ≠ M.name :=
    noParent_of_cache hc hk hnot (kids := Y.flatMap fun y => [y, y])
      (fun kd hkd => by
        obtain ⟨y0, hy0, hyk⟩ := List.mem_flatMap.mp hkd
        have hyk' : kd = y0 := by simpa using hyk
        subst hyk'
        obtain ⟨jj, hyy⟩ := List.mem_iff_getElem?.mp hy0
        have hjl : jj < cs.length := by
          have := (List.getElem?_eq_some_iff.mp hyy).1
          omega
        obtain ⟨y1, hy1, hg1⟩ := hget jj hjl
        have e : y1 = kd := Option.some.inj (hy1.symm.trans hyy)
        exact ⟨_, by rw [← e]; exact hg1⟩) hd0 hDeq hMc
  exact ⟨Y, t, t', d₀, M, Dg, w10, wc, hlen, hlets, hrr, hj2, hcv2.trans hcvc, hc, hk, hcoh, hget, hcross, hshared,
    hcore, hcvc, hpost, hnoclash⟩

end Tools.ShippingKaryEntry

#print axioms Tools.ShippingKaryEntry.kary_machineSynth_ne_none
#print axioms Tools.ShippingKaryEntry.kary_entry_run_ret_np
