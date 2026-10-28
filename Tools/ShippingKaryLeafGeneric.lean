import Tools.ShippingKaryEntry
-- BUILT (unit SR21): k4 exit 0 (Tools.ShippingKaryLeafGeneric, dev run); the final-SHA rebuild is in REPORT-SR21.md.
-- SCOPE (binding, ledger L8ba): the DATA bundle of a parent with K ≥ 1 callees sharing ONE leaf, and the K-ary generic forms of `quad_closes0`, `quad_machineRun`,
-- `quad_entry_run_ret_np` (`Tools/ShippingQuadLeafGeneric.lean`, untouched).  The parent's call list is `cs.flatMap (fun e => [e.c, e.c])` (every callee called twice, no
-- memory child), the callees are pairwise different, and every callee is a `LeafCalleeData` of the same leaf `G` (`LeafData dG`).  K = 2 is the old QUAD class
-- (`QuadParentData` is bridged in `Tools/ShippingKaryComposed.lean`).  The data facts of `KaryParentData` are decidable on the stored `machineData` (an instance proves them
-- by `decide`); `MachineDefines` of the parent / callees / leaf, `O`, `T`, `hA`, `MachineCloses` of the leaf stay premises.  `RealChildA` is a history of past synthesis
-- results, not semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingKaryLeafGeneric
open Tools.ShippingKaryRun Tools.ShippingKaryEntry
open Tools.ShippingQuadLeafGeneric
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

/-- the callee name at call `k` (call `k` belongs to callee `k / 2`) -/
def kName (cs : List KCal) (k : Nat) : String :=
  match cs[k / 2]? with
  | some e => Sparkle.IR.ModuleName.ofDecl e.c
  | none => ""
/-- the callee's own-input count at call `k` -/
noncomputable def kNk (cs : List KCal) (k : Nat) : Nat :=
  match cs[k / 2]? with
  | some e => machNIn e.d.shape
  | none => 0
/-- the callee's output names at call `k` -/
noncomputable def kOuts (cs : List KCal) (k : Nat) : List String :=
  match cs[k / 2]? with
  | some e => e.d.shape.layout.outs.map (·.name)
  | none => []

/-- The decidable data facts of the PARENT `dP` (named `c`, `n` declared inputs) with the call list `cs.flatMap (fun e => [e.c, e.c])`.  (`QuadParentData` for K = 2; the
`c₁ ≠ c₂ / c ≠ c₁ / c ≠ c₂` of that bundle are `nodup` / `cne`; the separation `sep` is derived.) -/
structure KaryParentData (dP : MachineData) (cs : List KCal) (c G : Name) (n : Nat) : Prop where
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
  argsN : ∀ (k : Nat) (hk : k < dP.shape.insts.length), kNk cs k = (dP.shape.insts[k]).2.1.length
  fieldOut : ∀ (k : Nat), k < dP.shape.insts.length → dP.shape.instFields.getD k "" ∈ kOuts cs k
  fieldsNd : ∀ (k : Nat) (hk : k < dP.shape.insts.length) (k' : Nat) (hk' : k' < dP.shape.insts.length),
    (dP.shape.insts[k]).1 = (dP.shape.insts[k']).1 →
    memKey (originAt dP.shape k) = memKey (originAt dP.shape k') →
    (dP.shape.insts[k]).2.1 = (dP.shape.insts[k']).2.1 →
    dP.shape.instFields.getD k "" = dP.shape.instFields.getD k' "" → k = k'
  outHead : ∀ o ∈ dP.shape.layout.outs, o.name.toList.head? ≠ some 'i'
  nodup : (cs.map (·.c)).Nodup
  cne : ∀ e ∈ cs, c ≠ e.c
  cneG : c ≠ G

/-- the bundle of the callees' data facts: every callee is a `LeafCalleeData` of the shared leaf -/
def KaryCallees (cs : List KCal) (dG : MachineData) (G : Name) : Prop :=
  ∀ e ∈ cs, LeafCalleeData e.d dG e.c G e.n

/-- the callees' `MachineDefines` -/
def KaryEntries (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (cs : List KCal) : Prop :=
  ∀ e ∈ cs, MachineDefines mctx mref cctx cref e.c e.d.shape

theorem kary_calleeOK (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {cs : List KCal} {dG : MachineData} {G : Name}
    (hG : LeafData dG) (hC : KaryCallees cs dG G) (hent : KaryEntries mctx mref cctx cref cs)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) :
    ∀ e ∈ cs, CalleeOK O mctx cctx e.c e.d :=
  fun e he => leafCallee_calleeOK O T hA hG (hC e he) (hent e he) hR0 hcl

theorem kary_nc {cs : List KCal} {dG : MachineData} {G : Name} (hC : KaryCallees cs dG G) :
    ∀ e ∈ cs, ∀ e' ∈ cs, ∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c := by
  intro e he e' he' k hk h
  rw [((hC e he).kids k hk).1] at h
  exact (hC e' he').GneC h

theorem kary_idx_lt {dP : MachineData} {cs : List KCal} (hP : dP.shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c]))
    {k : Nat} (hk : k < dP.shape.insts.length) : k / 2 < cs.length := by
  have := kary_insts_length hP
  omega

/-- the entry of call `k` is the callee `k / 2` -/
theorem kary_call_callee {dP : MachineData} {cs : List KCal}
    (hP : dP.shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c]))
    {k : Nat} (hk : k < dP.shape.insts.length) :
    cs[k / 2]? = some (cs[k / 2]'(kary_idx_lt hP hk)) ∧ (dP.shape.insts[k]).1 = (cs[k / 2]'(kary_idx_lt hP hk)).c := by
  have h := kary_insts_names hP k hk
  have hl := kary_idx_lt hP hk
  have e : cs[k / 2]? = some (cs[k / 2]'hl) := List.getElem?_eq_getElem hl
  rw [e] at h
  exact ⟨e, (Option.some.inj h).symm⟩

/-- `MachineClosesAtStart0` of the K-callee parent DERIVED (K-ary `quad_closes0`). -/
theorem kary_closes0 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {dP dG : MachineData} {cs : List KCal} {c G : Name} {nP : Nat}
    (hP : KaryParentData dP cs c G nP)
    (hG : LeafData dG) (hC : KaryCallees cs dG G) (hent : KaryEntries mctx mref cctx cref cs)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx c dP.shape := by
  intro tenv b w9 r w10 hj hcv hr
  refine kary_machineSynth_ne_none O hA cs (kary_calleeOK O T hA hG hC hent hR0 hcl) hP.nodup (kary_nc hC)
    dP hP.ok hP.body hP.alias hP.callsOk hP.slots hP.domB hP.insts_ne hP.fne hP.names hP.child hP.nomemKey
    (kName cs) (kNk cs) (kOuts cs) (fun _ => [Sparkle.IR.ModuleName.ofDecl G]) ?_ hP.argsN hP.fieldOut hP.fieldsNd ?_ ?_ ?_ ?_
    hj hcv hr
  · intro j hj0 y hy k hk2
    have e : cs[k / 2]? = some cs[j] := by rw [hk2]; exact List.getElem?_eq_getElem hj0
    have hi := leafCallee_ifaceP O T hA hG (hC _ (List.getElem_mem hj0)) (hent _ (List.getElem_mem hj0)) hR0 hcl hy
    simpa only [kName, kNk, kOuts, e] using hi
  · intro k hk k' hk' hn
    obtain ⟨-, h1⟩ := kary_call_callee hP.names hk
    obtain ⟨-, h2⟩ := kary_call_callee hP.names hk'
    have hn' : (cs[k / 2]'(kary_idx_lt hP.names hk)).c = (cs[k' / 2]'(kary_idx_lt hP.names hk')).c := by
      have a1 := (kary_call_callee hP.names hk).1
      have a2 := (kary_call_callee hP.names hk').1
      simp only [kName, a1, a2] at hn
      exact Tools.ShippingModuleName.ofDecl_injective hn
    exact ⟨h1.trans (hn'.trans h2.symm), by rw [hP.nomemKey k hk, hP.nomemKey k' hk']⟩
  · intro k hk hn
    have a1 := (kary_call_callee hP.names hk).1
    simp only [kName, a1] at hn
    exact hP.cne _ (List.getElem_mem _) (Tools.ShippingModuleName.ofDecl_injective hn.symm)
  · intro gi k _ o ho
    exact Tools.ShippingCallsGate.instName_ne_of_head (hP.outHead o ho) gi _
  · intro k hk hx
    exact Tools.ShippingModuleName.ofDecl_ne hP.cneG (List.mem_singleton.mp hx)

/-- `MachineRunJQC` of the parent at depth `1` from ONE core run at depth `0` (K-ary `quad_machineRun`). -/
theorem kary_machineRun (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {dP dG : MachineData} {cs : List KCal} {c G : Name} {nP : Nat}
    (hP : KaryParentData dP cs c G nP)
    (hG : LeafData dG) (hC : KaryCallees cs dG G) (hent : KaryEntries mctx mref cctx cref cs)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 c dP.shape m design := by
  obtain ⟨tenv, b, w9, w10, hmach, hw9, -, -⟩ :=
    core_run_tracked0' O hA entryP (kary_closes0 O T hA hP hG hC hent hR0 hcl) hw hcore
  exact ⟨tenv, b, w9, w10, hmach, hw9⟩

/-- **The parent's own run with the returned value linked and no parent module in `Dg`** (K-ary `quad_entry_run_ret_np`). -/
theorem kary_entry_run (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {dP dG : MachineData} {cs : List KCal} {c G : Name} {nP : Nat}
    (hP : KaryParentData dP cs c G nP)
    (hG : LeafData dG) (hC : KaryCallees cs dG G) (hent : KaryEntries mctx mref cctx cref cs)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
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
      (∀ x ∈ Dg.modules, x.name ≠ M.name) :=
  kary_entry_run_ret_np O hA cs (kary_calleeOK O T hA hG hC hent hR0 hcl) hP.nodup (kary_nc hC)
    dP hP.ok hP.body hP.insts_ne hP.fne hP.callsOk hP.slots hP.domB hP.names hP.child entryP
    (kary_closes0 O T hA hP hG hC hent hR0 hcl) hP.cne
    (fun e he k hk h' => hP.cneG (h'.symm.trans ((hC e he).kids k hk).1)) hw h

end Tools.ShippingKaryLeafGeneric

#print axioms Tools.ShippingKaryLeafGeneric.kary_closes0
#print axioms Tools.ShippingKaryLeafGeneric.kary_machineRun
#print axioms Tools.ShippingKaryLeafGeneric.kary_entry_run
