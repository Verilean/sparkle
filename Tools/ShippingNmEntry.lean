import Tools.ShippingNmGroup
import Tools.ShippingKaryEntry
-- BUILT (unit SRM2): e1 exit 0 (dev run); the final-SHA rebuild is in REPORT-SRM2.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # Memory-aware entry / machineRun / closes0 of the parent (unit SRM2, ledger L8bd2)

The NM analogue of `Tools.ShippingKaryEntry` and `Tools.ShippingKaryLeafGeneric` (`kary_machineSynth_ne_none`, `kary_entry_run_ret_np`, `kary_closes0`, `kary_machineRun`, `kary_entry_run`) for a parent
whose callees are memory-aware (`NCal` / `CalleeNM` of `Tools/ShippingNmGroup.lean`): the parent's machine synthesis does not fall back at the entry's start world, its own run (`D = 0`) with the
returned value linked to the core run's `(M, Dg)` and NO module of `Dg` named like the entry; the cache facts are the NM clauses (`CacheClosedNM`, `KeyTop`, `MemDet`, `CacheCoh`), plus the per-call kid
facts and the SHARED-LEAF DESIGN CLAUSE of `nm_closing`.

PREMISES (named): `CalleeNM` of every callee (`NmCallees`), the parent's decidable data facts (`NmParentData`), `MachineDefines` of the parent, and `hIface`: the interface `ChildIfaceP` of every
`RealChildA` result of every callee.  `hIface` is OPEN for a callee with a memory child (residue R1 of SRM1: the memory-kid `core_*` chain of `Tools/ShippingMemKid*.lean` is stated over the old-form
`RealChild` / `MachineRan`, not over `RealChildA`); for a plain callee it is `leafCallee_ifaceP`.  `RealChildA` is a history of past synthesis results, not semantic correctness in the current environment.
CLASS BOUNDARY: as in `Tools/ShippingNmGroup.lean` (K callees, each called twice, no memory origin in the parent's own calls).  An example does not make the class complete.
STILL OPEN for an ENDPOINT of such a parent (named, not proved here): R1 `hIface` / `MachineClosesAtA` of a callee with a memory child, via the `RealChildA` side (`hnomem` in `core_kids_facts_ranA` / `core_outsIn_ranA` / `core_inPorts_ranA` / `deepChild_ifaceP`);
R2 `KidFactsA` / `hgk` / `hsep` for those callees; R3 `seq_child_runN` of the memory-bearing leaf; R5 the composed trace (`kary_ranA` … `kary_soundLA`) with memory kids; the NM forms of `kary_returned` (`y.2 = Dg`) and `kary_wired`. -/

namespace Tools.ShippingNmEntry
open Tools.ShippingNmGroup Tools.ShippingKaryEntry
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
open Tools.ShippingMemLeafCache Tools.ShippingMemLeafRun
open Sparkle.Compiler.MachMemory (memModule memChild?)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- distinct names: the callee index is determined by the name -/
theorem nm_idx_of_name {cs : List NCal} (hnd : (cs.map (·.c)).Nodup) {a b : Nat} {x y : NCal}
    (hx : cs[a]? = some x) (hy : cs[b]? = some y) (h : x.c = y.c) : a = b := by
  have ha := (List.getElem?_eq_some_iff.mp hx).1
  exact (List.getElem?_inj (l := cs.map (·.c)) (i := a) (j := b) (by simpa using ha) hnd).mp
    (by simp [List.getElem?_map, hx, hy, h])

/-- **No module of the parent's `Dg` is named like the entry** (NM form of `noParent_of_cache`): the kids are cache entries whose designs may carry memory modules; those are not named like a declaration. -/
theorem noParent_nm {cache : Std.HashMap Name Res} (hcl : CacheClosedNM cache) (hk : KeyTop cache)
    {c : Name} (hnot : cache.get? c = none) {kids : List Res} (hkidIn : ∀ kd ∈ kids, ∃ c', cache.get? c' = some kd)
    {d₀ Dg : Sparkle.IR.AST.Design} (hd0 : d₀.modules = []) (hDg : Dg = designWith kids d₀)
    {M : Sparkle.IR.AST.Module} (hMc : M.name = Sparkle.IR.ModuleName.ofDecl c) :
    ∀ x ∈ Dg.modules, x.name ≠ M.name := by
  intro x hx hxn
  rw [hDg] at hx
  by_cases hmn : MemNamed x.name
  · obtain ⟨cb, aw, dw, e⟩ := hmn
    exact Tools.ShippingModuleName.ofDecl_ne_ofMem c cb aw dw ((hxn.trans hMc).symm.trans e)
  rcases mem_designWith hx with h0 | ⟨kd, hkd, hak⟩
  · rw [hd0] at h0; cases h0
  · obtain ⟨c', hc'⟩ := hkidIn kd hkd
    have hmods : x ∈ ModsOf kd := by
      rcases hak with h1 | h1
      · exact List.mem_cons_of_mem _ h1
      · rw [h1]; exact List.mem_cons_self ..
    obtain ⟨c'', r'', hr'', rfl⟩ := hcl c' kd hc' x hmods hmn
    have hnm := hk c'' r'' hr''
    have : c'' = c := Tools.ShippingModuleName.ofDecl_injective (hnm.symm.trans (hxn.trans hMc))
    subst this
    rw [hnot] at hr''; cases hr''

/-- the callee name at call `k` (call `k` belongs to callee `k / 2`) -/
def nName (cs : List NCal) (k : Nat) : String :=
  match cs[k / 2]? with
  | some e => Sparkle.IR.ModuleName.ofDecl e.c
  | none => ""
/-- the callee's own-input count at call `k` -/
noncomputable def nNk (cs : List NCal) (k : Nat) : Nat :=
  match cs[k / 2]? with
  | some e => machNIn e.d.shape
  | none => 0
/-- the callee's output names at call `k` -/
noncomputable def nOuts (cs : List NCal) (k : Nat) : List String :=
  match cs[k / 2]? with
  | some e => e.d.shape.layout.outs.map (·.name)
  | none => []
/-- the module names inside the callee's design at call `k` -/
def nNames (cs : List NCal) (k : Nat) : List String :=
  match cs[k / 2]? with
  | some e => e.names
  | none => []

/-- **The decidable data facts of the PARENT** `dP` (named `c`, `n` declared inputs) with the call list `cs.flatMap (fun e => [e.c, e.c])` and no memory origin among its own calls
(`KaryParentData` without the shared-leaf name `G`: the separation of the parent from the modules inside the callees' designs is `cneNames`). -/
structure NmParentData (dP : MachineData) (cs : List NCal) (c : Name) (n : Nat) : Prop where
  ok : dP.ok = true
  body : dP.shape.body = quote dP.dom
    (fun j => inputExpr dP.shape.binders.length (dP.bpos j))
    (fun j => inputExpr dP.shape.binders.length (dP.vpos j)) dP.packed
  alias : dP.letsAliasOk = true
  callsOk : dP.callsOk n = true
  slots : dP.ss.length = dP.shape.layout.slots.length
  domB : ∀ b ∈ dP.shape.binders.drop n, b.2 ≠ .domain
  insts_ne : dP.shape.insts ≠ []
  fne : dP.shape.instFields ≠ []
  names : dP.shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c])
  child : ∀ x ∈ dP.shape.instTagged, x.2.child? = none
  nomemKey : ∀ (k : Nat) (hk : k < dP.shape.insts.length), memKey (originAt dP.shape k) = none
  argsN : ∀ (k : Nat) (hk : k < dP.shape.insts.length), nNk cs k = (dP.shape.insts[k]).2.1.length
  fieldOut : ∀ (k : Nat), k < dP.shape.insts.length → dP.shape.instFields.getD k "" ∈ nOuts cs k
  fieldsNd : ∀ (k : Nat) (hk : k < dP.shape.insts.length) (k' : Nat) (hk' : k' < dP.shape.insts.length),
    (dP.shape.insts[k]).1 = (dP.shape.insts[k']).1 →
    memKey (originAt dP.shape k) = memKey (originAt dP.shape k') →
    (dP.shape.insts[k]).2.1 = (dP.shape.insts[k']).2.1 →
    dP.shape.instFields.getD k "" = dP.shape.instFields.getD k' "" → k = k'
  outHead : ∀ o ∈ dP.shape.layout.outs, o.name.toList.head? ≠ some 'i'
  nodup : (cs.map (·.c)).Nodup
  cne : ∀ e ∈ cs, c ≠ e.c
  cneNames : ∀ e ∈ cs, Sparkle.IR.ModuleName.ofDecl c ∉ e.names

/-- **The callees' contracts** (all `CalleeNM`) and the name separations: no callee is a call or a growth name of another callee, the parent is no call or growth name of a callee. -/
structure NmCallees (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context) (c : Name) (cs : List NCal) : Prop where
  K : ∀ e ∈ cs, CalleeNM O mctx cctx e
  nc : ∀ e ∈ cs, ∀ e' ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) ∧ e'.c ∉ e.Gs
  cd : ∀ e ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ c) ∧ c ∉ e.Gs

/-- **The interface of every callee result** (`RealChildA` is a history of past synthesis results): the premise `hIface` of the theorems below.  OPEN (residue R1) for a callee with a memory child. -/
def CalleeIface (O : RefLawsAOps MkRefd mref cref) (cs : List NCal) : Prop :=
  ∀ e ∈ cs, ∀ y : Res, RealChildA O e.c y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl e.c) (machNIn e.d.shape) (e.d.shape.layout.outs.map (·.name)) e.names y.1 y.2

theorem nm_idx_lt {dP : MachineData} {cs : List NCal} (hP : dP.shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c]))
    {k : Nat} (hk : k < dP.shape.insts.length) : k / 2 < cs.length := by
  have := nm_insts_length hP
  omega

/-- the entry of call `k` is the callee `k / 2` -/
theorem nm_call_callee {dP : MachineData} {cs : List NCal}
    (hP : dP.shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c]))
    {k : Nat} (hk : k < dP.shape.insts.length) :
    cs[k / 2]? = some (cs[k / 2]'(nm_idx_lt hP hk)) ∧ (dP.shape.insts[k]).1 = (cs[k / 2]'(nm_idx_lt hP hk)).c := by
  have h := nm_insts_names hP k hk
  have hl := nm_idx_lt hP hk
  have e : cs[k / 2]? = some (cs[k / 2]'hl) := List.getElem?_eq_getElem hl
  rw [e] at h
  exact ⟨e, (Option.some.inj h).symm⟩

/-- **The parent's machine synthesis does not fall back at the entry's start world** (NM form of `kary_machineSynth_ne_none`). -/
theorem nm_machineSynth_ne_none (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (cs : List NCal) {c : Name}
    (hK : ∀ e ∈ cs, CalleeNM O mctx cctx e) (hnd : (cs.map (·.c)).Nodup)
    (hnc : ∀ e ∈ cs, ∀ e' ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) ∧ e'.c ∉ e.Gs)
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
      obtain ⟨Y, hlen, hrr, hj, hc, hkt, hmd, hcoh, hget, hcross, -, -, -⟩ :=
        nm_closing O hA (D := 1) Nat.one_ne_zero cs hK hnd hnc hP hchild hw1.1
          (by rw [hcvw1]; exact cacheClosedNM_empty) (by rw [hcvw1]; exact keyTop_empty)
          (by rw [hcvw1]; exact memDet_empty)
          (by intro e he; rw [hcvw1]; simp) hr
      have hnm := nm_insts_names hP
      have hlenI := nm_insts_length hP
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
            exact nm_idx_of_name hnd hx hy (by rw [hxe, hye]; exact hnm')
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

/-- **The parent's own run with the returned value linked and no parent module in `Dg`** (NM form of `kary_entry_run_ret_np`). -/
theorem nm_entry_run_ret_np (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (cs : List NCal) {c : Name}
    (hK : ∀ e ∈ cs, CalleeNM O mctx cctx e) (hnd : (cs.map (·.c)).Nodup)
    (hnc : ∀ e ∈ cs, ∀ e' ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) ∧ e'.c ∉ e.Gs)
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
    (hcd : ∀ e ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ c) ∧ c ∉ e.Gs)
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
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (cs[j]).c = some y) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < cs.length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < (cs[j]).d.shape.insts.length),
          (∃ md, ((cs[j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? ((cs[j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          (((cs[j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? ((cs[j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? ((cs[j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (cs[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (cs[j]).d.shape.insts.length),
          ((cs[i]).d.shape.insts[k₁]).1 = ((cs[j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? (((cs[i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? (((cs[i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
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
  obtain ⟨Y, hlen, hrr, hj, hc, hk, hmd, hcoh, hget, hcross, hup, hshared, hkeys⟩ :=
    nm_closing O hA (D := 1) Nat.one_ne_zero cs hK hnd hnc hP hchild hj1
      (by rw [hcvw1]; exact cacheClosedNM_empty) (by rw [hcvw1]; exact keyTop_empty)
      (by rw [hcvw1]; exact memDet_empty)
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
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨x, hx1, hx2⟩ := List.mem_map.mp hx
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx1
          exact absurd hx2 ((hcd e he).1 i hi)
        · exact absurd hx (hcd e he).2
  obtain ⟨-, hname0, hd0⟩ := closedBody_kinds_of_run dp okp hbodyp hCp hslotsp hdomBp run hlets
  obtain ⟨hMn, hDeq⟩ := closeInstsG_name_design hrr.symm
  have hMc : M.name = Sparkle.IR.ModuleName.ofDecl c := hMn.trans hname0
  have hnoclash : ∀ x ∈ Dg.modules, x.name ≠ M.name :=
    noParent_nm hc hk hnot (kids := Y.flatMap fun y => [y, y])
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
  exact ⟨Y, t, t', d₀, M, Dg, w10, wc, hlen, hlets, hrr, hj2, hcv2.trans hcvc, hc, hk, hmd, hcoh, hget, hcross, hup, hshared,
    hcore, hcvc, hpost, hnoclash⟩

/-- `MachineClosesAtStart0` of the K-callee parent over memory-aware callees DERIVED (NM form of `kary_closes0`); `hIface` is the premise of the callee results' interface (OPEN R1 for a callee with a memory child). -/
theorem nm_closes0 (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {dP : MachineData} {cs : List NCal} {c : Name} {nP : Nat}
    (hP : NmParentData dP cs c nP) (hC : NmCallees O mctx cctx c cs) (hIface : CalleeIface O cs) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx c dP.shape := by
  intro tenv b w9 r w10 hj hcv hr
  refine nm_machineSynth_ne_none O hA cs hC.K hP.nodup hC.nc
    dP hP.ok hP.body hP.alias hP.callsOk hP.slots hP.domB hP.insts_ne hP.fne hP.names hP.child hP.nomemKey
    (nName cs) (nNk cs) (nOuts cs) (nNames cs) ?_ hP.argsN hP.fieldOut hP.fieldsNd ?_ ?_ ?_ ?_
    hj hcv hr
  · intro j hj0 y hy k hk2
    have e : cs[k / 2]? = some cs[j] := by rw [hk2]; exact List.getElem?_eq_getElem hj0
    have hi := hIface _ (List.getElem_mem hj0) y hy
    simpa only [nName, nNk, nOuts, nNames, e] using hi
  · intro k hk k' hk' hn
    obtain ⟨-, h1⟩ := nm_call_callee hP.names hk
    obtain ⟨-, h2⟩ := nm_call_callee hP.names hk'
    have hn' : (cs[k / 2]'(nm_idx_lt hP.names hk)).c = (cs[k' / 2]'(nm_idx_lt hP.names hk')).c := by
      have a1 := (nm_call_callee hP.names hk).1
      have a2 := (nm_call_callee hP.names hk').1
      simp only [nName, a1, a2] at hn
      exact Tools.ShippingModuleName.ofDecl_injective hn
    exact ⟨h1.trans (hn'.trans h2.symm), by rw [hP.nomemKey k hk, hP.nomemKey k' hk']⟩
  · intro k hk hn
    have a1 := (nm_call_callee hP.names hk).1
    simp only [nName, a1] at hn
    exact hP.cne _ (List.getElem_mem _) (Tools.ShippingModuleName.ofDecl_injective hn.symm)
  · intro gi k _ o ho
    exact Tools.ShippingCallsGate.instName_ne_of_head (hP.outHead o ho) gi _
  · intro k hk hx
    have a1 := (nm_call_callee hP.names hk).1
    simp only [nNames, a1] at hx
    exact hP.cneNames _ (List.getElem_mem _) hx

/-- `MachineRunJQC` of the parent at depth `1` from ONE core run at depth `0` (NM form of `kary_machineRun`). -/
theorem nm_machineRun (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {dP : MachineData} {cs : List NCal} {c : Name} {nP : Nat}
    (hP : NmParentData dP cs c nP) (hC : NmCallees O mctx cctx c cs) (hIface : CalleeIface O cs)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 c dP.shape m design := by
  obtain ⟨tenv, b, w9, w10, hmach, hw9, -, -⟩ :=
    core_run_tracked0' O hA entryP (nm_closes0 O hA hP hC hIface) hw hcore
  exact ⟨tenv, b, w9, w10, hmach, hw9⟩

/-- **The parent's own run with the returned value linked and no parent module in `Dg`** (NM form of `kary_entry_run`). -/
theorem nm_entry_run (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {dP : MachineData} {cs : List NCal} {c : Name} {nP : Nat}
    (hP : NmParentData dP cs c nP) (hC : NmCallees O mctx cctx c cs) (hIface : CalleeIface O cs)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = cs.length ∧
      closeLets dP.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dP.shape) dP.shape.insts.length
        dP.shape.layout.slots.length (t.inputs.map (·.name)) (dP.shape.insts.map (·.2.1))
        dP.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine dP.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (cs[j]).c = some y) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < cs.length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < (cs[j]).d.shape.insts.length),
          (∃ md, ((cs[j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? ((cs[j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          (((cs[j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? ((cs[j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? ((cs[j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (cs[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (cs[j]).d.shape.insts.length),
          ((cs[i]).d.shape.insts[k₁]).1 = ((cs[j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? (((cs[i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? (((cs[i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) :=
  nm_entry_run_ret_np O hA cs hC.K hP.nodup hC.nc
    dP hP.ok hP.body hP.insts_ne hP.fne hP.callsOk hP.slots hP.domB hP.names hP.child entryP
    (nm_closes0 O hA hP hC hIface) hP.cne hC.cd hw h

end Tools.ShippingNmEntry

#print axioms Tools.ShippingNmEntry.nm_machineSynth_ne_none
#print axioms Tools.ShippingNmEntry.nm_entry_run_ret_np
#print axioms Tools.ShippingNmEntry.nm_closes0
#print axioms Tools.ShippingNmEntry.nm_machineRun
#print axioms Tools.ShippingNmEntry.nm_entry_run
