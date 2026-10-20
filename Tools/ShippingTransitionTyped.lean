import Tools.ShippingTransitionPortTys
import Tools.ShippingCloseLetsRun

variable {tenv : Lean.Environment}

/-! # The transition module is typed: the export (G1, step 1)

For the harness run of a machine's transition (the packed term of
`MachineData`), `Tools.ShippingMachineEntry.transition_facts` has, inside
`RawValueAt`, `TypedPostReady t` and `PrintBaseAt W t` at the packed term's
width `W`; `transition_calls_facts` (`Tools/ShippingCallsRun.lean`) uses
them and does not export them, and hides the width behind `∃ ow`.

`transition_typed_of_run`: from the data conditions (`d.ok`), the body's
quotation and the run —

* `TypedPostReady t`: distinct wire names, `out` no wire, every statement an
  assignment `l := e` with `TypedExpr (weOf t) e n` and `weOf t l = n` or
  `l = "out"`;
* `PrintBaseAt (packLets d.letFields d.core.2).1 t`: scalar wires with
  allocated names, the inputs wires with distinct names, the body in
  dependency order, the `out` assignment typed at the PACKED term's width;
* the body ends in `out := w`, and `w` has the spine of the `let` fields
  with their widths (`SpineW`; `transition_spine`).

No shape condition on the calls is needed (`callsOk` is not a hypothesis).
The proof is the first part of `closedPorts_of_run`'s
(`Tools/ShippingClosedPorts.lean`), copied, with `transition_spine` in place
of `transition_calls_facts`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingTransitionTyped
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

set_option maxHeartbeats 2000000 in
/-- **The transition of a machine is typed and printable at the packed
term's width, and its packed wire has the `let` spine.** -/
theorem transition_typed_of_run {declName : Lean.Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {logProf : String → IO Unit} {t : Sparkle.IR.AST.Module} {d₀ : Design}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
      d.shape.binders d.shape.body) (t, d₀)) :
    Tools.ShippingTypedPostSoundness.TypedPostReady t ∧
    PrintBaseAt (packLets d.letFields d.core.2).1 t ∧
    ∃ (B : List Stmt) (w : String), t.body = B ++ [.assign "out" (.ref w)] ∧
      Tools.ShippingCloseLetsRun.SpineW t.wires t.body (d.letFields.map (·.1)) w := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, _, _, _, outsOk, outsNodup, hwf, hb, hv,
    _, _, hscoped, _, _, _, _, _, _, _, _⟩ := ok
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
  obtain ⟨raw, -, -⟩ :=
    Tools.ShippingMachineEntry.transition_facts nd len hrun hm nameLegal hwf hb' hv' hbody
  have zero : Tools.ShippingMixedSourceBridge.SourceInputs declName d.shape.binders ids cache
      (fun _ => false) (fun _ n => 0#n) (fun _ => 0) :=
    Tools.ShippingMachineEntry.admissible_zero _ _
  obtain ⟨_, _, _, ready, _, _, _, _, base⟩ := raw _ _ _ (fun _ _ => 0) zero
  have pb := base hposv
  obtain ⟨B, w, hB, hspine, -, -⟩ :=
    Tools.ShippingCloseLetsRun.transition_spine nd len hrun hm nameLegal hposv d.letFields
      d.core.2 hwf hb' hv' hbody
  exact ⟨ready, pb, B, w, hB, hspine⟩

end Tools.ShippingTransitionTyped
