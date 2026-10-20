import Tools.ShippingUnifiedProtection

/-! # One emitted slice assignment, at the level of builder states

The certified slice lowering (`Tools/ShippingUnifiedRecursion.lean`,
`slice_fresh`; `Tools/ShippingUnifiedProtection.lean`, `slice_order`) is
stated for ONE program,

```
do let sw ← rec ae h false false
   emitSliceResult (sliceRhs start len sw) len hint named
```

and its proofs invert a run of `emitSliceResult` (`makeWire`, then
`emitAssign`, nothing in between). The legacy `Signal.fst` / `Signal.snd`
arms (`Rec.handleTupleProjections`) emit the same wire and the same
assignment, but two oracle calls sit BETWEEN the allocation and the
assignment, so their run is not a run of `emitSliceResult` — and a `Returns`
of that program cannot be assembled from the parts (`Returns` hides the
world). What CAN be reused is everything those proofs do after the
inversion, which is about builder states only:

* `allocate_assign_outcome` (value, `Inv`) — used as it is;
* `sliceRhs_simple`, `sliceRhs_typed`, `sliceRhs_eval`, `sliceRhs_refs` —
  used as they are;
* `Frame.makeWire` (a `bitVector` wire), `Frame.emitAssign` — used as they
  are.

**Proved here** (the two pieces that exist only under a `Returns`
hypothesis in the certified files, restated on states; their proofs are the
certified ones with the inversion removed):

* `frame_makeWire_bit` — `Frame` of allocating a `bit` wire (the allocation
  part of `emit_bool_frame`);
  `frame_makeWire_width` — … of allocating a wire of type
  `hwTypeFromWidth w`;
* `allocAssign_order` — `OrderInv` after allocating a fresh wire and
  assigning it an expression that reads used wires only (`emit_cast_order` /
  `emit_bool_order` with the wire's type general).

and the node-level statements, generic in the program:

* `sliceNode_spec` — for an action each of whose runs is: a run of the
  sub-action `sub` (returning the wire `sw`), then the allocation of a wire
  of type `hwTypeFromWidth w` and the assignment `sliceRhs start w sw` to
  it: from `ActionSpec sub … (.bits M u)`, `ActionSpec action …
  (.bits w (u.extractLsb' start w))` (`slice_fresh`'s proof);
* `sliceNode_order` — its order statement (`slice_order`'s proof). -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Reorder
open Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedProtection
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTranslationOrder
open Tools.ShippingCompareLoweringSoundness
open Tools.ShippingEntrySoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires)

/-- Allocating a `bit` wire extends the builder state by a frame. -/
theorem frame_makeWire_bit (s : CircuitState) (hint : String) (named : Bool) :
    Frame s (CircuitM.makeWire hint Sparkle.IR.Type.HWType.bit named s).2 := by
  have hm := CircuitM.makeWire_spec hint Sparkle.IR.Type.HWType.bit named s
  refine ⟨?_, ?_, CircuitM.makeWire_sourceBindings _ _ _ _, ?_, ?_, ?_,
    makeWire_outputs _ _ _ _, makeWire_inputs _ _ _ _, ?_, ?_, ?_, ?_⟩
  · intro p hp; rw [hm.2.2.2]; exact List.mem_cons_of_mem _ hp
  · intro z hz; rw [hm.2.1]; simp [Std.HashSet.contains_insert, hz]
  · intro w e he; left; rw [CircuitM.makeWire_translateRecord] at he; exact he
  · exact WiresOk.fresh hm.1 hm.2.1 hm.2.2.2
  · intro hs p hp
    rw [hm.2.2.2] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl rfl
    · exact hs p hp
  · intro hs; rw [hm.2.2.1]; exact hs
  · change (CircuitM.makeWire hint Sparkle.IR.Type.HWType.bit named s).2.module.parameters = _
    rw [makeWire_module]; rfl
  · change (CircuitM.makeWire hint Sparkle.IR.Type.HWType.bit named s).2.module.isPrimitive = _
    rw [makeWire_module]; rfl
  · intro p hp
    rw [hm.2.2.2] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inr (CircuitM.makeWire_allocated hint Sparkle.IR.Type.HWType.bit named s)
    · exact Or.inl hp

/-- Allocating a wire of type `hwTypeFromWidth w` extends the builder state
by a frame. -/
theorem frame_makeWire_width (s : CircuitState) (hint : String) (w : Nat) (named : Bool) :
    Frame s (CircuitM.makeWire hint (Sparkle.IR.Type.hwTypeFromWidth w) named s).2 := by
  by_cases h1 : w = 1
  · subst h1
    exact frame_makeWire_bit s hint named
  · have hty : Sparkle.IR.Type.hwTypeFromWidth w = Sparkle.IR.Type.HWType.bitVector w := by
      unfold Sparkle.IR.Type.hwTypeFromWidth
      simp [h1]
    rw [hty]
    exact Tools.ShippingMixedBinarySoundness.Frame.makeWire s hint w named

/-- Allocation of a fresh wire and its assignment keep the acyclic order: the
right-hand side reads only already-used wires and the target is new. -/
theorem allocAssign_order {s t : CircuitState} {w hint : String}
    {ty : Sparkle.IR.Type.HWType} {named : Bool} {rhs : Sparkle.IR.AST.Expr}
    (hw : w = (CircuitM.makeWire hint ty named s).1)
    (ht : t = (CircuitM.emitAssign w rhs (CircuitM.makeWire hint ty named s).2).2)
    (order : OrderInv s)
    (refs : ∀ x ∈ refsOf rhs, s.usedNames.contains x = true) : OrderInv t := by
  have alloc := CircuitM.makeWire_spec hint ty named s
  have fresh : s.usedNames.contains w = false := hw ▸ alloc.1
  have old : w ∉ footprint s.module.body := by
    intro hp; have used := order.2 w hp; rw [fresh] at used; cases used
  have noSelf : w ∉ refsOf rhs := by
    intro hp; have used := refs w hp; rw [fresh] at used; cases used
  constructor
  · rw [ht, emitAssign_body_cons, alloc.2.2.1, List.reverse_cons]
    exact acyclic_snoc order.1
      (fun h => old ((footprint_reverse_mem _ _).mp h)) noSelf
  · intro x hx
    rw [ht, emitAssign_body_cons, alloc.2.2.1, footprint_cons] at hx
    rw [ht, emitAssign_usedNames, alloc.2.1, ← hw]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [Std.HashSet.contains_insert]
    · rcases List.mem_append.mp hx with hx | hx
      · simp [Std.HashSet.contains_insert, refs x hx]
      · simp [Std.HashSet.contains_insert, order.2 x hx]

/-- What a run of a slice node is, on builder states: a run of the
sub-action, then a wire of type `hwTypeFromWidth w` allocated and assigned
`sliceRhs start w sw`. -/
def SliceRuns (action sub : CompilerM String) (ctx : CompilerState) (hint : String)
    (named : Bool) (start w : Nat) : Prop :=
  ∀ (s t : CircuitState) (r : String), Returns action ctx s r t →
    ∃ (sw : String) (s1 : CircuitState), Returns sub ctx s sw s1 ∧
      r = (CircuitM.makeWire hint (Sparkle.IR.Type.hwTypeFromWidth w) named s1).1 ∧
      t = (CircuitM.emitAssign r (sliceRhs start w sw)
        (CircuitM.makeWire hint (Sparkle.IR.Type.hwTypeFromWidth w) named s1).2).2

/-- The frame of the allocation and the assignment of a slice node. -/
theorem sliceEmit_frame {s1 t : CircuitState} {r sw hint : String} {named : Bool}
    {start w : Nat} (hlen : 0 < w)
    (ht : t = (CircuitM.emitAssign r (sliceRhs start w sw)
      (CircuitM.makeWire hint (Sparkle.IR.Type.hwTypeFromWidth w) named s1).2).2) :
    Frame s1 t := by
  rw [ht]
  exact (frame_makeWire_width s1 hint w named).trans
    (Tools.ShippingMixedBinarySoundness.Frame.emitAssign _ r _
      (sliceRhs_simple start w hlen sw))

/-- **Frame and outcome of a slice node** (the proof of `slice_fresh`, on a
run given by its parts). -/
theorem sliceNode_spec {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {action sub : CompilerM String}
    {hint : String} {named : Bool} {M w start : Nat} {u : BitVec M}
    (hlen : 0 < w) (hr : start + w ≤ M)
    (run : SliceRuns action sub ctx hint named start w)
    (ca : ActionSpec sub ctx inputs we mems initial (.bits M u)) :
    ActionSpec action ctx inputs we mems initial
      (.bits w (BitVec.extractLsb' start w u)) := by
  constructor
  · intro s t r lookup hrun
    obtain ⟨sw, s1, hsub, _, ht⟩ := run s t r hrun
    exact (ca.frame s s1 sw lookup hsub).trans (sliceEmit_frame hlen ht)
  · intro s t r prior hinv widths hrun
    obtain ⟨sw, s1, hsub, hres, ht⟩ := run s t r hrun
    have lookup := Lookup.ofInputs hinv.inputs
    have fa := ca.frame s s1 sw lookup hsub
    have fe : Frame s1 t := sliceEmit_frame hlen ht
    have aout := ca.sem s s1 sw prior hinv (fe.decls.widths widths) hsub
    obtain ⟨va, ia, av, af⟩ := aout.execution
    have step := allocate_assign_outcome (v := .bits w (BitVec.extractLsb' start w u)) ia hres ht
      (Tools.ShippingUnifiedRecursion.hwTypeFromWidth_bitWidth w)
      (sliceRhs_typed hlen hr aout.width) (sliceRhs_eval hlen av) widths
    obtain ⟨result, inv, val, frame⟩ := step.execution
    exact ⟨step.used, step.width, fun z hz => step.grows z (fa.used z hz), result, inv, val,
      fun z hz => (frame z (fa.used z hz)).trans (af z hz)⟩

/-- **Order of a slice node** (the proof of `slice_order`, on a run given by
its parts). -/
theorem sliceNode_order {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {action sub : CompilerM String}
    {hint : String} {named : Bool} {M w start : Nat} {u : BitVec M}
    (hlen : 0 < w)
    (run : SliceRuns action sub ctx hint named start w)
    (ca : ActionSpec sub ctx inputs we mems initial (.bits M u))
    (oa : ActionOrder sub ctx inputs we mems initial) :
    ActionOrder action ctx inputs we mems initial := by
  intro s t r prior hrun h widths order
  obtain ⟨sw, s1, hsub, hres, ht⟩ := run s t r hrun
  have fe : Frame s1 t := sliceEmit_frame hlen ht
  have wa := fe.decls.widths widths
  have aout := ca.sem s s1 sw prior h wa hsub
  have o1 := oa s s1 sw prior hsub h wa order
  refine allocAssign_order hres ht o1 ?_
  intro x hx
  cases sliceRhs_refs hx
  exact aout.used

end Tools.ShippingLegacySem
