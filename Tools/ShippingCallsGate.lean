import Tools.ShippingCallsRun
import Tools.ShippingCallsShape
import Tools.ShippingCallsClose
import Tools.ShippingCallsSame
import Tools.ShippingGateChildComb
import Tools.ShippingReflectCtx

variable {tenv : Lean.Environment}

/-! # `MachineClosesAt` for one-output calls of gate children

The closing premise of the hierarchical endpoints, DERIVED for a machine
whose calls are one-output calls of combinational gate children:

* `closeInsts_of_run`: for a run of the harness on the machine's data and the
  `let` closing of its transition, `closeInsts` returns a module on children
  with the child-side facts (`ChildComb`, an empty design, as many inputs as
  the call has arguments, a name other than the parent's, name-consistent,
  no output port named as an instance);
* `childFull_of_real`: a `RealChild` of a gate declaration has those facts
  (`gate_child_fullFacts` at the child's own run, the reflection moved to its
  contexts);
* `machineClosesAt_of_gateKids`: `MachineClosesAt`, the children's facts read
  off the `RealChild` witnesses the run's closing returns.

What stays a condition, decided per declaration and NOT derived from the
shape reader: S3 (`callsOk`), the calls name distinct declarations (two calls
of one declaration need the cache's witness — not here), no call names the
parent, no output port is named as an instance, at least one `let`. -/
namespace Tools.ShippingCallsGate
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingInlineSoundness (EntryDefines)

theorem argBound_le {K : Nat} : ∀ (args : List Nat) (m0 : Nat), m0 ≤ K → (∀ a ∈ args, a < K) →
    args.foldl (fun m a => max m (a + 1)) m0 ≤ K
  | [], _, h, _ => h
  | b :: rest, m0, h, ha => by
    have hb := ha b (List.mem_cons_self ..)
    exact argBound_le rest _ (by show max m0 (b + 1) ≤ K; omega)
      (fun a h' => ha a (List.mem_cons_of_mem _ h'))

theorem core_wf {kb kv : Nat} {vw : Nat → Nat} {c : Nat} (core : Term (.bits c)) :
    ∀ (fs : List (Σ w : Nat, Term (.bits w))), (packLets fs core).2.WF kb kv vw → core.WF kb kv vw
  | [], h => h
  | _ :: fs, h => core_wf core fs h.2

/-- A name that does not start with `i` is no instance name. -/
theorem instName_ne_of_head {s : String} (h : s.toList.head? ≠ some 'i') (k : Nat) (nm : String) :
    s ≠ s!"inst{k}_{nm}" := by
  intro e
  exact h (e ▸ Tools.ShippingCallsParent.instName_head k nm)

theorem inst_get {insts : List (Name × List Nat × MixedGateBinder)} {k : Nat} {args : List Nat}
    (h : (insts.map (·.2.1))[k]? = some args) : ∃ c, insts[k]? = some c ∧ c.2.1 = args := by
  rw [List.getElem?_map] at h
  cases hc : insts[k]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    exact ⟨c, rfl, by simpa using h⟩

end Tools.ShippingCallsGate

namespace Tools.ShippingMachineAuto.MachineData

/-- The data conditions of the one-output closing of gate children: S3, the
slots are the layout's, the binders after the declaration's have ports, and
no call has several outputs. (No condition on the number of `let`s.) -/
def gateCallsOk (d : MachineData) (nDecl : Nat) : Bool :=
  d.callsOk nDecl && decide (d.ss.length = d.shape.layout.slots.length) &&
  decide (∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain) && d.shape.instFields.isEmpty

end Tools.ShippingMachineAuto.MachineData

namespace Tools.ShippingCallsGate
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingInlineSoundness (EntryDefines)

set_option maxHeartbeats 2000000 in
/-- **The pure closing returns a module, for a real run of the harness.** -/
theorem closeInsts_of_run {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true)
    {logProf : String → IO Unit} {t t' : Sparkle.IR.AST.Module} {d₀ : Design}
    {children : List (Sparkle.IR.AST.Module × Design)}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
      d.shape.binders d.shape.body) (t, d₀))
    (hcl : closeLets d.shape.layout.lets t = some t')
    (hchL : children.length = d.shape.insts.length)
    (hchild : ∀ (k : Nat) (c : Sparkle.IR.AST.Module × Design), children[k]? = some c →
      ChildComb c.1 ∧ c.2.modules = [] ∧
      (∀ args : List Nat, (d.shape.insts.map (·.2.1))[k]? = some args →
        c.1.inputs.length = args.length) ∧
      c.1.name ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hcons : ∀ a ∈ children, ∀ b ∈ children, a.1.name = b.1.name → a.1 = b.1)
    (hfreshOuts : ∀ (k : Nat) (c : Sparkle.IR.AST.Module × Design), children[k]? = some c →
      ∀ o ∈ d.shape.layout.outs, o.name ≠ s!"inst{k}_{c.1.name}") :
    (closeInsts (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) children
      (closeMachine d.shape.layout t', d₀)).isSome = true := by
  simp only [MachineData.gateCallsOk, MachineData.callsOk, Bool.and_eq_true, decide_eq_true_eq,
    List.isEmpty_iff] at hS
  obtain ⟨⟨⟨⟨⟨⟨hnIn, hargs⟩, hfields⟩, hcoreR⟩, hslots⟩, hdomB⟩, -⟩ := hS
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, _, _, _, outsOk, outsNodup, hwf, hb, hv,
    _, _, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  obtain ⟨hfitL, -⟩ := scoped_fit d.letBs d.letFields _ hscoped
  have hlsLen : d.letFields.length = d.ls.length := by simp [MachineData.letFields]
  have hletBs : d.letBs.length = d.shape.binders.length - (d.nIn + d.ss.length) := by
    simp [MachineData.letBs]
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  have hA : (d.shape.binders.take nDecl).length = nDecl := by
    rw [List.length_take]
    omega
  have hsplit : d.shape.binders = d.shape.binders.take nDecl ++ d.shape.binders.drop nDecl :=
    (List.take_append_drop ..).symm
  have hBlen : (d.shape.binders.drop nDecl).length =
      d.shape.insts.length + d.ss.length + d.letBs.length := by
    rw [List.length_drop]
    omega
  have hcoreWF := core_wf d.core.2 d.letFields hwf
  obtain ⟨PI, ls, bodyB, w, P, bnd, hin, hPI, hlsL, hndI, hinW, hwAlloc, hbodyT, hacy, hnamed, hnw,
      hP, hF, hdes, hname⟩ :=
    transition_calls_facts (cs := d.callBounds) nd len hrun hm nameLegal hposv d.letFields d.core.2
      hwf hb' hv' hbody hsplit hdomB hBlen hfitL
      (by rw [hA]; exact fieldsOK_of_B d.letFields 0 d.core.2 hfields hwf)
      (by
        rw [hA, hlsLen]
        exact uses_of_reads (fun j hj hr => ⟨hj, posOk_rule hr⟩)
          (fun j hj hr => ⟨hj, posOk_rule hr⟩) d.core.2 hcoreWF hcoreR)
  have hmn : machNIn d.shape = PI.length := by
    rw [hPI]
    unfold machNIn
    rw [show d.shape.binders.length - d.shape.insts.length - d.shape.layout.slots.length -
      d.shape.layout.lets = nDecl by omega]
  rw [hmn, ← hslots]
  rw [hlets] at hcl
  have hargs' : ∀ (k : Nat) (args : List Nat), (d.shape.insts.map (·.2.1))[k]? = some args →
      ∀ a ∈ args, a < d.letBs.length := by
    intro k args hk a ha
    obtain ⟨c, hc, rfl⟩ := inst_get hk
    have := List.all_eq_true.mp (List.all_eq_true.mp hargs c (List.mem_of_getElem? hc)) a ha
    have : a < d.ls.length := by simpa using this
    omega
  refine closeInsts_of_facts (cs := d.callBounds) hcl hin hlsL hndI hinW hwAlloc hbodyT hacy
    hnamed hnw hP hF outsOk outsNodup (by simp) hchL hargs' ?_ ?_ (by rw [hD, hdes]; rfl) ?_ hcons
    hfreshOuts
  · intro j hj
    refine ⟨argBound (d.shape.insts[j]).2.1, by simp [MachineData.callBounds, hj], ?_⟩
    refine argBound_le _ 0 (Nat.zero_le _) (fun a ha => ?_)
    exact hargs' j _ (by simp [hj]) a ha
  · intro k args c hk hc a ha
    obtain ⟨x, hx, rfl⟩ := inst_get hk
    simp only [MachineData.callBounds, List.getElem?_map, hx, Option.map_some,
      Option.some.injEq] at hc
    rw [← hc]
    exact argBound_spec _ 0 a ha
  · intro k c hk
    obtain ⟨h1, h2, h3, h4⟩ := hchild k c hk
    exact ⟨h1, h2, h3, by rw [hname]; exact h4⟩

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A real child of a gate declaration has the child-side facts** — from
its OWN run (the `RealChild` witness), the declaration's reflection moved to
that run's contexts. -/
theorem childFull_of_real {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChild mref cref c y) : ChildFull c bs y.1 y.2 := by
  obtain ⟨mctx', cctx', w, w', -, hr⟩ := h.inv
  exact gate_child_fullFacts hr (Tools.ShippingReflectCtx.EntryDefines.ctx entry) old peel he hb hv

/-- **What the parent's closing needs of a child's full-entry result**: the
child-side `kidsCombB` facts, the number of its input ports, its name, and a
design with no module. (A gate child gives it by `ChildFull.iface`; a
slotless machine child by `machineChild_iface`.) -/
def ChildIface (c : Name) (n : Nat) (b : Sparkle.IR.AST.Module) (design : Design) : Prop :=
  ChildComb b ∧ b.inputs.length = n ∧ b.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ design.modules = []

theorem ChildFull.iface {c : Name} {bs : List (Name × MixedGateBinder)}
    {b : Sparkle.IR.AST.Module} {design : Design} (h : ChildFull c bs b design) :
    ChildIface c ((bs.filter fun x => x.2 != .domain).length) b design := by
  refine ⟨h.comb, ?_, h.name, h.design⟩
  have := congrArg List.length h.tys
  simpa using this

set_option maxHeartbeats 1000000 in
/-- **`MachineClosesAt` for one-output calls of gate children.** The children
are the ones the run's closing returns: each is read by its `RealChild`
witness (`hkid`). -/
theorem machineClosesAt_of_gateKids {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true)
    (nk : Nat → Nat)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y → ChildIface (d.shape.insts[k]).1 (nk k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{k}_{(Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1)}") :
    MachineClosesAt mctx mref cctx cref declName d.shape := by
  have hf : d.shape.instFields = [] := by
    simp only [MachineData.gateCallsOk, Bool.and_eq_true, List.isEmpty_iff] at hS
    exact hS.2
  have hl : Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape :=
    letsClose_of_data d ok hbody halias mctx mref cctx cref
  intro tenv b w r w' hw' hdp hr
  obtain ⟨L, hw⟩ := invV_of_invW mctx cctx hw'
  have hB := fun L' : RefLaws mref cref => bodyRel L'
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d₀⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := harness_inv L hB (fun L' => harnessRel_of L' (translateRel L')) hw run
  -- the depth is positive here (inside an entry) and the harness keeps it
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
  rotate_left
  · rename_i hne
    exact absurd (List.isEmpty_iff.mpr hf) hne
  -- the children the run's closing returns: real compiles, and two calls of
  -- one declaration get the same child (the cache, kept under the calls
  -- between at a positive depth)
  obtain ⟨children, rfl, hreal, hpair, -⟩ :=
    Tools.ShippingCallsSame.closeInstsM_run_all L hB hw1 hd1 hr
  have key : (closeInsts (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) children
      (closeMachine d.shape.layout t', d₀)).isSome = true := by
    obtain ⟨hlenC, hall⟩ := hreal
    -- each child, by the witness of its own run
    have hfull : ∀ (k : Nat) (c : Res), children[k]? = some c → ∃ hk : k < d.shape.insts.length,
        ChildIface (d.shape.insts[k]).1 (nk k) c.1 c.2 := by
      intro k c hc
      have hk : k < d.shape.insts.length := by
        rw [← hlenC]
        exact (List.getElem?_eq_some_iff.mp hc).1
      obtain ⟨y, hy, hor⟩ := hall k hk
      rw [hc] at hy
      cases hy
      rcases hor with hmem | hre
      · rw [hnomem _ (List.getElem_mem hk)] at hmem
        cases hmem
      · exact ⟨hk, hkid k hk c hre⟩
    refine closeInsts_of_run d ok hbody hS run.mreturns hcl hlenC ?_ ?_ ?_
    · intro k c hc
      obtain ⟨hk, full⟩ := hfull k c hc
      obtain ⟨fcomb, flen, fname, fdes⟩ := full
      refine ⟨fcomb, fdes, ?_, ?_⟩
      · intro args hargs
        obtain ⟨x, hx, rfl⟩ := inst_get hargs
        have hx' : d.shape.insts[k] = x := by
          have := List.getElem?_eq_getElem hk
          rw [hx] at this
          exact (Option.some.inj this).symm
        rw [flen, hargsN k hk, hx']
      · rw [fname]
        exact hparent _ (List.getElem_mem hk)
    · intro a ha c hc' hn
      obtain ⟨i, hi, hai⟩ := List.getElem_of_mem ha
      obtain ⟨j, hj, hcj⟩ := List.getElem_of_mem hc'
      obtain ⟨hki, fi⟩ := hfull i a (by rw [List.getElem?_eq_getElem hi, hai])
      obtain ⟨hkj, fj⟩ := hfull j c (by rw [List.getElem?_eq_getElem hj, hcj])
      rw [fi.2.2.1, fj.2.2.1] at hn
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
    · intro k c hc o ho
      obtain ⟨hk, full⟩ := hfull k c hc
      rw [full.2.2.1]
      exact hfresh k hk o ho
  intro h0
  rw [h0] at key
  cases key

end Tools.ShippingCallsGate
