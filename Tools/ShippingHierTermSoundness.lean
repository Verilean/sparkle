import Tools.ShippingInstanceLeaf
import Tools.ShippingUnifiedExecutionSoundness

/-! The certified entry for cones over ARBITRARY leaves, in the linked
semantics.

`synthesizeMixedCertified` on a body that is a quoted unified term whose
leaves each bring their own meaning and contract — input binders, instance
calls of linked children, or anything else proved against the contract —
produces a module whose LINKED evaluation (instance statements executed
against the child table) drives `out` with the term's evaluation. -/
namespace Tools.ShippingHierTermSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedEntrySoundness (lookup_of_ports)
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedOutputSoundness (PortInputs declaredWidths declaredWidths_agree)
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingCompareLoweringSoundness (ScalarWidthsAgree)
open Tools.ShippingMixedLiteralSoundness (DeclGrows)
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingHierarchySoundness Tools.ShippingLinkCtx
open Tools.ShippingUnifiedExecutionSoundness (pack_width)

section generic
variable [LinkCtx] [ChildSem]

/-- At the first leaf there is no emitted code or cache record. -/
theorem initial_link {ctx ρ β we mems initial s}
    (body : s.module.body = []) (record : s.translateRecord = {})
    (inputs : Tools.ShippingMixedInvariant.Inputs ctx ρ β we s initial) :
    Inv ctx (inputValues ρ β) we mems initial s initial :=
  ⟨LinkCtx.runs_nil body, Inputs.of_mixed inputs, Records.empty record,
    LinkCtx.typed_nil body⟩

/-- The actual leaf emitter preserves declaration uniqueness. -/
theorem emitLeaves_structure_link {rec ctx inputs we mems initial s t e v cache logProf returned}
    (contract : Contract rec ctx inputs we mems initial e v)
    (lookup : Lookup ctx inputs s) (wires : WiresOk s)
    (hr : Returns (emitLeaves rec cache logProf [("out", e)] none 0) ctx s returned t) :
    DeclGrows s t ∧ WiresOk t := by
  obtain ⟨w, sm, ty, tr, fresh, ht, _⟩ := emitLeaves_single hr
  have frame := contract.frame "out" false true s sm w lookup tr
  have wm := frame.wires wires
  refine ⟨?_, ?_, ?_⟩
  · intro p hp; rw [ht, emitAssign_wires]; exact frame.decls p hp
  · rw [ht, emitAssign_wires]; exact wm.1
  · intro p hp
    rw [ht, emitAssign_wires] at hp
    have hu := wm.2 p hp
    rw [ht, emitAssign_usedNames, addOutput_state]
    simp [Std.HashSet.contains_insert, hu]

/-- A real `emitLeaves` run drives `out` with the leaf contract's value, in
whatever semantic context the contract was proved. -/
theorem emitLeaves_runs_link {ctx inputs we mems initial prior s t e cache logProf returned}
    {v : Value}
    (contract : Contract (fun e hint top named => translateExprToWire e hint top named)
      ctx inputs we mems initial e v)
    (h : Inv ctx inputs we mems initial s prior) (widths : ScalarWidthsAgree we t)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", e)] none 0)
      ctx s returned t) :
    ∃ result, LinkCtx.Runs we mems initial t result ∧ result "out" = v.toNat := by
  obtain ⟨w, sm, ty, translate, fresh, ht, _⟩ := emitLeaves_single hr
  have wm : ScalarWidthsAgree we sm := by
    intro p hp; apply widths p; rw [ht, emitAssign_wires]; exact hp
  have step := contract.sem "out" false true s sm w prior h wm translate
  obtain ⟨middle, inv, val, frame⟩ := step.execution
  refine ⟨write middle "out" v.toNat, ?_, by simp [write]⟩
  rw [ht]
  exact LinkCtx.runs_emit (LinkCtx.runs_body (s := sm) rfl inv.runs)
    (by simpa [evalExpr] using congrArg some val)

end generic

/-- The linked value observed at `out`. -/
def HierValue (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (m : Sparkle.IR.AST.Module) (initial : Env) (mems : MEnv) (expected : Nat) : Prop :=
  ∃ result, evalAssignsH (moduleWidths m) children mems m.body initial = some result ∧
    result "out" = expected

/-- A leaf's meaning, with the child semantics explicit. -/
def LeafMeaning (C : ChildSem) (inputs : FVarId → Option Value) (e : Lean.Expr)
    (v : Value) : Prop :=
  @Meaning C inputs e v

/-- A leaf's contract at every width environment and fuel, in the linked
semantic context of `children`. -/
def LeafContract (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (C : ChildSem)
    (ctx : CompilerState) (inputs : FVarId → Option Value) (mems : MEnv) (initial : Env)
    (e : Lean.Expr) (v : Value) : Prop :=
  ∀ (we : WEnv) (fuel : Nat),
    @Contract (hierLink children).toLinkCtx C (translateFuelFix translateStep fuel)
      ctx inputs we mems initial e v

/-- Linked source preservation for a cone over arbitrary leaves: whenever the
quoted body's leaves carry their meanings and contracts, the compiled
module's linked evaluation observes the term's evaluation at `out`. -/
def HierConePreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (C : ChildSem)
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) (mems : MEnv),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits initial (bs.zip ids) a →
    ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (bE vE : Nat → Lean.Expr)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (w : Nat) → BitVec w)
      {srt : SType} (e : Term srt),
    e.WF kb kv vw →
    (∀ j, j < kb → LeafMeaning C (inputValues p.bools p.bits) (bE j) (.bool (bvals j))) →
    (∀ j, j < kv → LeafMeaning C (inputValues p.bools p.bits) (vE j)
      (.bits (vw j) (vvals j (vw j)))) →
    (∀ j, j < kb → LeafContract children C p.context (inputValues p.bools p.bits)
      mems initial (bE j) (.bool (bvals j))) →
    (∀ j, j < kv → LeafContract children C p.context (inputValues p.bools p.bits)
      mems initial (vE j) (.bits (vw j) (vvals j (vw j)))) →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body = quote dom bE vE e →
    HierValue children m initial mems (pack srt (eval bvals vvals e)).toNat

theorem synthesizeMixedCertified_hierCone_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    HierConePreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, nameLegal⟩ :=
    synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro children C bools bits initial mems a p values dom kb kv vw bE vE bvals vvals srt e he
    hbM hvM hbC hvC qeq
  letI : HierCtx := hierLink children
  letI : ChildSem := C
  have empty := empty_layout (entryCompilerState false cache) declName.toString initial
  have prepared := prepare_layout (bs.zip ids) a empty.1 empty.2 values
  have leaf := prepare_returns (bs.zip ids) a (bools := bools) (bits := bits) run
  rw [qeq] at leaf
  have contract : Contract (fun e hint top named => translateExprToWire e hint top named)
      p.context (inputValues p.bools p.bits) (declaredWidths st) mems initial
      (quote dom bE vE e) (pack srt (eval bvals vvals e)) :=
    fuel_contract_leaves translateFuelLimit hbM hvM
      (fun j hj fuel => hbC j hj (declaredWidths st) fuel)
      (fun j hj fuel => hvC j hj (declaredWidths st) fuel) e he
  obtain ⟨growth, finalWires⟩ := emitLeaves_structure_link contract
    (lookup_of_ports prepared.1 prepared.2.1) prepared.2.1 leaf
  have widths := declaredWidths_agree finalWires
  have inv0 : Inv p.context (inputValues p.bools p.bits) (declaredWidths st) mems initial
      p.state initial :=
    initial_link prepared.2.2.1 prepared.2.2.2 (prepared.1.inputs prepared.2.1 growth widths)
  obtain ⟨result, evalr, value⟩ := emitLeaves_runs_link contract inv0 widths leaf
  have wireEq : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have bodyEq : m.body = st.module.finalize.body := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  refine ⟨result, ?_, value⟩
  rw [moduleWidths_finish wireEq finalWires, bodyEq]
  exact evalr

end Tools.ShippingHierTermSoundness
