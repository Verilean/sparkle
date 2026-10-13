import Tools.ShippingHarnessClosed

/-! # A transition / gate module reads its input ports and wires driven earlier

`harness_closed` at the level the entry theorems work at: for a run of the
harness on the quotation of a well-formed term over the binders, the
returned module's body is closed over ITS input ports (`readsClosedB
(m.inputs.map name) m.body`), and is assignments only. No closed-reads
premise. -/
namespace Tools.ShippingTransitionClosed
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

open Tools.ShippingHarnessClosed

set_option maxHeartbeats 1000000 in
theorem transition_closed {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr} {m : Sparkle.IR.AST.Module}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {returned : String}
    {st : CircuitState}
    (nd : ids.Nodup) (len : ids.length = bs.length)
    (run : Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) (bs.zip ids))
        (entryCompilerState false cache) (CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)) returned st)
    (hm : m = (addClockResetIfSequential st.module).finalize)
    (nameLegal : Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true)
    (positive : PositiveBinders bs)
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {srt : SType} (e : Term srt) (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hbody : body = quote dom (fun j => inputExpr bs.length (bpos j))
      (fun j => inputExpr bs.length (vpos j)) e) :
    readsClosedB (m.inputs.map (·.name)) m.body = true ∧
      (∀ stmt ∈ m.body, ∃ l r, stmt = Stmt.assign l r) ∧
      (∃ ow, PrintBaseAt ow m) ∧ TypedPostReady m ∧
      st.design = (CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)).design ∧ m.name = (Sparkle.IR.ModuleName.ofDecl declName) := by
  have facts := transition_facts nd len run hm nameLegal he hb hv hbody
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  have zero : SourceInputs declName bs ids cache (fun _ => false) (fun _ n => 0#n)
      (fun _ => 0) := admissible_zero _ _
  obtain ⟨_, _, _, ready, _, _, _, _, base⟩ := facts.1 _ _ _ (fun _ _ => 0) zero
  have pb := base positive
  have hin := facts.2.2 (boolValues ids fun _ => false) (bitValues ids fun _ n => 0#n)
  have hassign : ∀ stmt ∈ m.body, ∃ l r, stmt = Stmt.assign l r := Acyclic.assign pb.order
  have zipAt : ∀ (pos : Nat) (binder : Name × MixedGateBinder), bs[pos]? = some binder →
      (bs.zip ids)[pos]? = some (binder, ids[pos]!) := by
    intro pos binder hpos
    have bound : pos < bs.length := (List.getElem?_eq_some_iff.mp hpos).1
    exact List.getElem?_zip_eq_some.mpr ⟨hpos, by
      simp [List.getElem?_eq_getElem (show pos < ids.length by omega),
        List.getElem!_eq_getElem?_getD]⟩
  subst hbody
  have h := harness_closed run hm (boolValues ids fun _ => false) (bitValues ids fun _ n => 0#n)
    (fun _ => 0) zero
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
    fresh
    (fun j hj => by
      obtain ⟨name, hpos⟩ := hb j hj
      exact ⟨bpos j, (name, .bool), zipAt _ _ hpos, by simp⟩)
    (fun j hj => by
      obtain ⟨name, hpos⟩ := hv j hj
      exact ⟨vpos j, (name, .bits (vw j)), zipAt _ _ hpos, by simp⟩)
    hassign
  rw [hin]
  refine ⟨h.1, hassign, ⟨_, pb⟩, ready, h.2.1, ?_⟩
  have hname : (addClockResetIfSequential st.module).name = st.module.name := by
    unfold addClockResetIfSequential
    dsimp only
    split
    · split <;> split <;> rfl
    · rfl
  rw [hm, ← h.2.2]
  simpa only [Module.finalize] using hname

end Tools.ShippingTransitionClosed
