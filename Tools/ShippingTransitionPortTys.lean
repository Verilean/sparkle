import Tools.ShippingClosedPorts

variable {tenv : Lean.Environment}

/-! # The TYPES of the transition's ports, and its wires (G1, conjunct 8)

`instOutWidthsOk` asks of every instance-driven wire `w` — the transition's
input for a call entry `k`, at position `machNIn + k` — that its DECLARED
width in the full entry's module is the child's output port's. The parent
side is here:

* `inputPorts_tail_types` (pure): the ports of the binders split at any
  position `n` after which no binder is a domain; the ports of the tail
  have the binders' types (`kindTy`), one for one.
* `transitionPortTys_of_run`: on a real harness run of a machine with calls
  — the transition's wire names are distinct and allocated, its inputs are
  wires, and its inputs are `P1 ++ P2` with `P2` the ports of the binders
  from `nDecl` on (calls, slots, `let`s), each of its binder's type.
* `closeLets_wires`, `closeMachine_wires_sup`: closing keeps the wires and
  adds `next…` wires only.
* `port_of_name`, `zip_split`, `kindTy_shape`: lists and types.

So the type of the call port `k` is `kindTy (binders[nDecl + k]).2`: the
kind the READER gave the binder of the call's result. Nothing in the
transition, the closing or the data checks compares it with the child
module's output port; see `Tools/ShippingChecksWidths.lean`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingTransitionPortTys
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingTopoBody Tools.ShippingTopoChecks Tools.ShippingTopoLinked
open Tools.ShippingCloseInstsSome Tools.ShippingCloseChecks Tools.ShippingCloseMachineFacts
open Tools.ShippingInstStmt Tools.ShippingGateChildComb Tools.ShippingKidsComb
open Tools.ShippingCallsParent Tools.ShippingCallsStmts Tools.ShippingDesignWith
open Tools.ShippingRankRun Tools.ShippingRankNames Tools.ShippingCallsRank
open Tools.ShippingClosedOrder Tools.ShippingMachineCloses
open Tools.ShippingCloseLetsSplit (closedBody)
open Tools.ShippingMachineClose (concatParts?_mem mem_frontAliases mem_insertAliases)
open Tools.ShippingCallsAssembly
open Sparkle.IR.OptCheck (seqStmtOk)
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingChildInv
open Tools.ShippingCallsGate

/-- A zip splits where both lists do. -/
theorem zip_split {α β : Type} (n : Nat) (l : List α) (r : List β) (h : l.length = r.length) :
    l.zip r = (l.take n).zip (r.take n) ++ (l.drop n).zip (r.drop n) := by
  have h1 : (l.take n).length = (r.take n).length := by
    rw [List.length_take, List.length_take, h]
  rw [← List.zip_append h1, List.take_append_drop, List.take_append_drop]

/-- A binder's port type is one bit or a bit vector. -/
theorem kindTy_shape (k : MixedGateBinder) :
    Tools.ShippingMachineEntry.kindTy k = .bit ∨
      ∃ n, Tools.ShippingMachineEntry.kindTy k = .bitVector n := by
  cases k with
  | domain => exact Or.inl rfl
  | bool => exact Or.inl rfl
  | bits n => exact Or.inr ⟨n, rfl⟩

/-- In a list of ports with distinct names, a port is its name's. -/
theorem port_of_name {l : List Port} (hnd : (l.map (·.name)).Nodup) {r q : Port}
    (hr : r ∈ l) (hq : q ∈ l) (h : r.name = q.name) : r = q := by
  have h1 := Tools.ShippingEntrySoundness.find?_of_nodup hnd hr
  have h2 := Tools.ShippingEntrySoundness.find?_of_nodup hnd hq
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-- `closeLets` keeps the wires. -/
theorem closeLets_wires {K : Nat} {t t' : Sparkle.IR.AST.Module} (h : closeLets K t = some t') :
    t'.wires = t.wires := by
  unfold closeLets at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h; rfl
        · cases h

/-- A wire of the closed machine is a wire of the transition or a `next…`
wire. -/
theorem closeMachine_wires_sup (lay : Layout) (t : Sparkle.IR.AST.Module) :
    ∀ p ∈ (closeMachine lay t).wires, p ∈ t.wires ∨ ∃ x, p.name = nextName x := by
  unfold closeMachine
  split
  · intro p hp
    exact Or.inl hp
  · intro p hp
    have hp' : p ∈ t.wires ++ (t.inputs.drop (t.inputs.length - lay.slots.length)).map
        (fun p => ({ name := nextName p.name, ty := p.ty } : Port)) := hp
    rcases List.mem_append.mp hp' with h | h
    · exact Or.inl h
    · obtain ⟨q, _, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨q.name, rfl⟩

/-- **The ports of the binders, split at a position after which no binder is
a domain**: the tail's ports have the tail's binders' types. -/
theorem inputPorts_tail_types {bools : Lean.FVarId → Bool}
    {bits : (id : Lean.FVarId) → (n : Nat) → BitVec n}
    (bs : List (Lean.Name × MixedGateBinder)) (ids : List Lean.FVarId)
    (len : ids.length = bs.length) (n : Nat) (hdom : ∀ b ∈ bs.drop n, b.2 ≠ .domain)
    {a : Tools.ShippingMixedEntrySoundness.Setup} {tin : List Port}
    (hin : tin = Tools.ShippingMachineEntry.inputPorts bools bits (bs.zip ids) a) :
    ∃ P1 P2 : List Port, tin = P1 ++ P2 ∧ P2.length = (bs.drop n).length ∧
      ∀ (k : Nat) (q : Port) (bn : Lean.Name × MixedGateBinder), P2[k]? = some q →
        (bs.drop n)[k]? = some bn → q.ty = Tools.ShippingMachineEntry.kindTy bn.2 := by
  rw [zip_split n bs ids len.symm, Tools.ShippingMachineEntry.inputPorts_append] at hin
  have hnd : ∀ b ∈ (bs.drop n).zip (ids.drop n), b.1.2 ≠ .domain :=
    fun b hb => hdom b.1 (List.of_mem_zip hb).1
  have Z := Tools.ShippingMachineEntry.inputPorts_types (bools := bools) (bits := bits)
    ((bs.drop n).zip (ids.drop n))
    (Tools.ShippingMixedEntrySoundness.prepare bools bits ((bs.take n).zip (ids.take n)) a) hnd
  refine ⟨_, _, hin, ?_, ?_⟩
  · have h1 := Z.length_eq
    simp only [List.length_zip, List.length_drop] at h1 ⊢
    omega
  · intro k q bn hq hb
    have hi : k < (ids.drop n).length := by
      have := (List.getElem?_eq_some_iff.mp hb).1
      simp only [List.length_drop] at this ⊢
      omega
    have hbz : ((bs.drop n).zip (ids.drop n))[k]? = some (bn, (ids.drop n)[k]) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨hb, List.getElem?_eq_getElem hi⟩
    exact Z.get k q _ hq hbz


set_option maxHeartbeats 2000000 in
/-- **On a real harness run of a machine with calls**: the transition's wire
names are distinct and allocated, its inputs are wires, and the ports of the
binders from `nDecl` on — the calls', the slots', the `let`s' — are the last
inputs, each of its binder's type. -/
theorem transitionPortTys_of_run {declName : Lean.Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    {logProf : String → IO Unit} {t : Sparkle.IR.AST.Module} {d₀ : Design}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
      d.shape.binders d.shape.body) (t, d₀)) :
    (t.wires.map (·.name)).Nodup ∧ (∀ p ∈ t.wires, Allocated p.name) ∧
    (∀ p ∈ t.inputs, p ∈ t.wires) ∧
    ∃ P1 P2 : List Port, t.inputs = P1 ++ P2 ∧
      P2.length = (d.shape.binders.drop nDecl).length ∧
      P2.length = d.shape.insts.length + d.shape.layout.slots.length + d.shape.layout.lets ∧
      ∀ (k : Nat) (q : Port) (bn : Lean.Name × MixedGateBinder), P2[k]? = some q →
        (d.shape.binders.drop nDecl)[k]? = some bn →
        q.ty = Tools.ShippingMachineEntry.kindTy bn.2 := by
  simp only [MachineData.callsOk, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨hnIn, hargs⟩, hfields⟩, hcoreR⟩ := hC
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
  obtain ⟨raw, -, hinputs⟩ :=
    Tools.ShippingMachineEntry.transition_facts nd len hrun hm nameLegal hwf hb' hv' hbody
  have zero : Tools.ShippingMixedSourceBridge.SourceInputs declName d.shape.binders ids cache
      (fun _ => false) (fun _ n => 0#n) (fun _ => 0) :=
    Tools.ShippingMachineEntry.admissible_zero _ _
  obtain ⟨_, _, _, ready, _, _, _, _, base⟩ := raw _ _ _ (fun _ _ => 0) zero
  have pb := base hposv
  obtain ⟨P1, P2, hsp, hP2len, hP2ty⟩ :=
    inputPorts_tail_types d.shape.binders ids len nDecl hdomB
      (hinputs (fun _ => false) (fun _ n => 0#n))
  refine ⟨ready.wiresNodup, pb.wireNames, pb.inputWires, P1, P2, hsp, hP2len, ?_, hP2ty⟩
  rw [hP2len, List.length_drop]
  omega

end Tools.ShippingTransitionPortTys
