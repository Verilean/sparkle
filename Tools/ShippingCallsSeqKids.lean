import Tools.ShippingSeqChildIface

/-! # `MachineClosesAt` for calls with several outputs and calls of sequential children

The closing premise of the hierarchical endpoints, DERIVED for a machine
whose calls go through the general closing (`closeInstsGM`) and whose
children are machine children without calls of their own (each read by the
`RealChild` witness the run's closing returns, as `ChildIfaceG`).

What stays a condition, decided per declaration and NOT derived from the
shape reader: S3 (`callsOk`), the slots are the layout's, the binders after
the declaration's have ports, each entry's field is an output of its child,
two entries of one call read different fields, the calls' names are
separated (N1), no call names the parent, no output port is named as an
instance. Not here: memory children, children with calls of their own. -/
namespace Tools.ShippingCallsSeqKids
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingCallsGate Tools.ShippingCallsRunG Tools.ShippingSeqChildIface
open Tools.ShippingInstStmtG Tools.ShippingCallsStmtsG Tools.ShippingDesignWith
open Sparkle.IR.OptCheck (seqStmtOk)

theorem memParams_none_of_seqOk {m : Sparkle.IR.AST.Module} (h : m.body.all seqStmtOk = true) :
    Sparkle.Compiler.MachMemory.memParams? m = none := by
  unfold Sparkle.Compiler.MachMemory.memParams?
  split
  · rename_i heq
    rw [heq] at h
    simp [seqStmtOk] at h
  · rfl

theorem noInstOfB_of_seqOk {body : List Stmt} (h : body.all seqStmtOk = true) (nm : String) :
    noInstOfB nm body = true := by
  unfold noInstOfB
  rw [List.all_eq_true] at h ⊢
  intro st hs
  have := h st hs
  cases st <;> simp_all [seqStmtOk]

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000 in
/-- **`MachineClosesAt` for the general closing over machine children without
calls.** -/
theorem machineClosesAt_of_seqKids {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (nk : Nat → Nat) (outsK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ChildIfaceG (d.shape.insts[k]).1 (nk k) (outsK k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsK k)
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (gi : Nat), ∀ c ∈ d.shape.insts, ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{(Sparkle.IR.ModuleName.ofDecl c.1)}") :
    MachineClosesAt mctx mref cctx cref declName d.shape := by
  have hl : Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape :=
    letsClose_of_data d ok hbody halias mctx mref cctx cref
  intro tenv b w r w' hw' hdp hr
  obtain ⟨L, hw⟩ := invV_of_invW mctx cctx hw'
  have hB := fun L' : RefLaws mref cref => bodyRel L'
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d₀⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := harness_inv L hB (fun L' => harnessRel_of L' (translateRel L')) hw run
  have hd1 : L.dval w1 ≠ 0 := by
    rw [Tools.ShippingCallsSame.harness_depth L hB (fun L' => harnessRel_of L' (translateRel L'))
      hw run]
    exact dval_ne_of_depthPos mctx cctx L hdp
  dsimp only at hr
  obtain ⟨t', hcl⟩ := Option.isSome_iff_exists.mp (hl (profLogIO b) w t d₀ w1 run)
  rw [hcl] at hr
  dsimp only at hr
  split at hr
  · have := RunsTo.pure_eq hr
    rw [this]
    exact Option.some_ne_none _
  split at hr
  · rename_i he
    exact absurd (List.isEmpty_iff.mp he) hfne
  obtain ⟨children, rfl, hreal, hpair, -⟩ := closeInstsGM_run_all L hB hw1 hd1 hnomem hr
  have key : (closeInstsG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) d.shape.instFields children
      (closeMachine d.shape.layout t', d₀)).isSome = true := by
    obtain ⟨hlenC, hall⟩ := hreal
    have hfull : ∀ (k : Nat) (c : Res), children[k]? = some c → ∃ hk : k < d.shape.insts.length,
        ChildIfaceG (d.shape.insts[k]).1 (nk k) (outsK k) c.1 c.2 := by
      intro k c hc
      have hk : k < d.shape.insts.length := by
        rw [← hlenC]
        exact (List.getElem?_eq_some_iff.mp hc).1
      obtain ⟨y, hy, hre⟩ := hall k hk
      rw [hc] at hy
      cases hy
      exact ⟨hk, hkid k hk c hre⟩
    have hcons : ∀ a ∈ children, ∀ c ∈ children, a.1.name = c.1.name → a.1 = c.1 := by
      intro a ha c hc' hn
      obtain ⟨i, hi, hai⟩ := List.getElem_of_mem ha
      obtain ⟨j, hj, hcj⟩ := List.getElem_of_mem hc'
      obtain ⟨hki, fi⟩ := hfull i a (by rw [List.getElem?_eq_getElem hi, hai])
      obtain ⟨hkj, fj⟩ := hfull j c (by rw [List.getElem?_eq_getElem hj, hcj])
      rw [fi.name, fj.name] at hn
      have hni : (d.shape.insts.map (·.1))[i]? = some (d.shape.insts[i]).1 := by simp [hki]
      have hnj : (d.shape.insts.map (·.1))[j]? = some (d.shape.insts[j]).1 := by simp [hkj]
      have hcc := hsep _ (List.mem_of_getElem? hni) _ (List.mem_of_getElem? hnj) hn
      rw [← hcc] at hnj
      have hsame : children[i]? = children[j]? := by
        rcases Nat.lt_trichotomy i j with h | h | h
        · exact hpair i j _ h hni hnj
        · rw [h]
        · exact (hpair j i _ h hnj hni).symm
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, hai, hcj] at hsame
      exact congrArg Prod.fst (Option.some.inj hsame)
    have hdesC : ∀ c ∈ children, c.2.modules = [] ∧ c.1.body.all seqStmtOk = true := by
      intro c hc
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨_, full⟩ := hfull k c hk
      exact ⟨full.design, full.seqOk⟩
    have hlenM : children.length = (d.shape.insts.map (·.2.1)).length := by simp [hlenC]
    refine closeInstsG_of_run d ok hbody hC hslots hdomB run.mreturns hcl hlenC ?_ hcons ?_ ?_ ?_
    · intro k c hc
      obtain ⟨hk, full⟩ := hfull k c hc
      refine ⟨?_, full.inNd, ?_, full.outsIn, full.outsNd, ?_⟩
      · intro args hargs
        obtain ⟨x, hx, rfl⟩ := inst_get hargs
        have hx' : d.shape.insts[k] = x := by
          have := List.getElem?_eq_getElem hk
          rw [hx] at this
          exact (Option.some.inj this).symm
        rw [full.nIn, hargsN k hk, hx']
      · have := hfieldOut k hk
        rw [← full.outs] at this
        obtain ⟨p, hp, he⟩ := List.mem_map.mp this
        exact ⟨p, hp, he⟩
      · rw [full.name]
        exact hparent _ (List.getElem_mem hk)
    · intro k k' key hkk hkk' hf
      obtain ⟨args, c, ha, hc, rfl⟩ := keys_get hlenM hkk
      obtain ⟨args', c', ha', hc', he⟩ := keys_get hlenM hkk'
      simp only [Prod.mk.injEq] at he
      obtain ⟨hk, full⟩ := hfull k c hc
      obtain ⟨hk', full'⟩ := hfull k' c' hc'
      obtain ⟨x, hx, hxa⟩ := inst_get ha
      obtain ⟨x', hx', hxa'⟩ := inst_get ha'
      have e1 : d.shape.insts[k] = x := by
        have := List.getElem?_eq_getElem hk
        rw [hx] at this
        exact (Option.some.inj this).symm
      have e2 : d.shape.insts[k'] = x' := by
        have := List.getElem?_eq_getElem hk'
        rw [hx'] at this
        exact (Option.some.inj this).symm
      have hn : (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1) = (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k']).1) := by
        rw [← full.name, ← full'.name]
        exact he.1
      have hni : (d.shape.insts[k]).1 ∈ d.shape.insts.map (·.1) :=
        List.mem_map_of_mem (List.getElem_mem hk)
      have hnj : (d.shape.insts[k']).1 ∈ d.shape.insts.map (·.1) :=
        List.mem_map_of_mem (List.getElem_mem hk')
      exact hfieldsNd k hk k' hk' (hsep _ hni _ hnj hn)
        (by rw [e1, e2, hxa, hxa']; exact he.2) hf
    · intro gi c hc o ho
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨hk', full⟩ := hfull k c hk
      rw [full.name]
      exact hfresh gi _ (List.getElem_mem hk') o ho
    · intro hd0
      obtain ⟨hres, hmods⟩ := designWith_resolves hd0 (fun c hc => (hdesC c hc).1) hcons
      refine ⟨?_, ?_, ?_⟩
      · rw [List.all_eq_true]
        intro c hc
        unfold Sparkle.Compiler.MachMemory.memSelf
        rw [memParams_none_of_seqOk (hdesC c hc).2]
      · rw [List.all_eq_true]
        intro c hc
        simp [hres c hc, (hdesC c hc).1]
      · rw [List.all_eq_true]
        intro g hg
        obtain ⟨c, hc, rfl⟩ := hmods g hg
        exact noInstOfB_of_seqOk (hdesC c hc).2 _
  intro h0
  rw [h0] at key
  cases key

end Tools.ShippingCallsSeqKids
