import Tools.ShippingTransitionClosed

/-! # The packed wire of a transition, before and after `closeLets` (G1)

`closeMachine` closes a transition whose body ends in `assign out = w`
(`packedWire?`). Two facts so that this premise is a fact of a run:

* `closeLets_packed`: `closeLets` keeps "the body ends in `assign out = …`"
  — with no `let` it returns the module itself, otherwise it builds
  `… ++ [assign out = core]`;
* `transition_out`: the harness's module, on the quotation of a well-formed
  term, ends in `assign out = w` (the spine theorem `harness_spine_at`, at
  the level the entry theorems work at — same hypotheses as
  `Tools.ShippingTransitionClosed.transition_closed`).

Nothing else is claimed. -/
namespace Tools.ShippingChecksPacked
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.IR.Machine Sparkle.IR.Type
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose Tools.ShippingMachineTrace
open Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSpine Tools.ShippingCloseLetsSplit Tools.ShippingHarnessSpine
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingSpineOrder Tools.ShippingClosedOrder Tools.ShippingCloseLetsRun
open Tools.ShippingMachineCloses
open Sparkle.IR.Reorder

/-- **`closeLets` keeps the final `assign out = …`.** -/
theorem closeLets_packed {K : Nat} {t t' : Sparkle.IR.AST.Module} {w : String}
    (h : closeLets K t = some t') (hw : packedWire? t.body = some w) :
    (packedWire? t'.body).isSome = true := by
  unfold closeLets at h
  split at h
  · cases h
    simp [hw]
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h
          simp [packedWire?]
        · cases h

/-- **The harness's module ends in `assign out = w`.** -/
theorem transition_out {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr} {m : Sparkle.IR.AST.Module}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {returned : String}
    {st : CircuitState}
    (nd : ids.Nodup) (len : ids.length = bs.length)
    (run : Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) (bs.zip ids))
        (entryCompilerState false cache) (CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)) returned st)
    (hm : m = (addClockResetIfSequential st.module).finalize)
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {srt : SType} (e : Term srt) (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hbody : body = quote dom (fun j => inputExpr bs.length (bpos j))
      (fun j => inputExpr bs.length (vpos j)) e) :
    ∃ B w, m.body = B ++ [.assign "out" (.ref w)] := by
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  have zero : SourceInputs declName bs ids cache (fun _ => false) (fun _ n => 0#n)
      (fun _ => 0) := admissible_zero _ _
  subst hbody
  obtain ⟨B, w, hB, -⟩ := harness_spine_at run hm (boolValues ids fun _ => false)
    (bitValues ids fun _ n => 0#n) (fun _ => 0) zero
    (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
    kb kv vw (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) (fun _ => false) (fun _ n => 0#n)
    e he
    (by
      intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      have bound := (List.getElem_of_getElem? pos).choose
      have lookup := prepare_bool_lookup (bools := boolValues ids fun _ => false)
        (bits := bitValues ids fun _ n => 0#n) (bs.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)) fresh (zip_member len pos)
      simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup)
    (by
      intro j hj
      obtain ⟨name, pos⟩ := hv j hj
      have bound := (List.getElem_of_getElem? pos).choose
      have lookup := prepare_bits_lookup (bools := boolValues ids fun _ => false)
        (bits := bitValues ids fun _ n => 0#n) (bs.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)) fresh (zip_member len pos)
      simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup)
    (by
      apply instantiated_quote _ _ _ he
      · intro j hj
        obtain ⟨name, pos⟩ := hb j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose
      · intro j hj
        obtain ⟨name, pos⟩ := hv j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose)
  exact ⟨B, w, hB⟩

/-- The packed wire of the harness's module. -/
theorem transition_packed {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr} {m : Sparkle.IR.AST.Module}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {returned : String}
    {st : CircuitState}
    (nd : ids.Nodup) (len : ids.length = bs.length)
    (run : Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) (bs.zip ids))
        (entryCompilerState false cache) (CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)) returned st)
    (hm : m = (addClockResetIfSequential st.module).finalize)
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {srt : SType} (e : Term srt) (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hbody : body = quote dom (fun j => inputExpr bs.length (bpos j))
      (fun j => inputExpr bs.length (vpos j)) e) :
    ∃ w, packedWire? m.body = some w := by
  obtain ⟨B, w, hB⟩ := transition_out nd len run hm e he hb hv hbody
  exact ⟨w, by simp [packedWire?, hB]⟩

end Tools.ShippingChecksPacked
