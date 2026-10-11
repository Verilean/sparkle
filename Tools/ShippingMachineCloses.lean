import Tools.ShippingCloseLetsRun
import Tools.ShippingSpineOrder
import Tools.ShippingClosedOrder

/-! # `closeLets` accepts the harness' transition: the six conditions, assembled

From a run of the certified harness on a packed machine body
(`transition_spine`, `spine_links`) and the pure ordering theorem
(`closed_acyclic`) to `(closeLets …).isSome`, and with
`machineCloses_noCalls_iff` to `MachineCloses` for shapes without calls. -/
namespace Tools.ShippingMachineCloses
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
open Tools.ShippingSpineOrder Tools.ShippingClosedOrder

/-- Binders bound later do not change an earlier binding. -/
theorem prepare_visible_keep {bools bits} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup) (id : FVarId),
      id ∉ L.map Prod.snd →
      visible (prepare bools bits L a).context (prepare bools bits L a).state.sourceBindings id =
        visible a.context a.state.sourceBindings id
  | [], _, _, _ => rfl
  | ((name, kind), id') :: rest, a, id, hid => by
    rw [List.map_cons, List.mem_cons, not_or] at hid
    rw [prepare, prepare_visible_keep rest _ id hid.2]
    cases kind with
    | domain => rfl
    | bool => exact visible_old hid.1
    | bits n => exact visible_old hid.1

/-- **The wire bound to the `k`-th binder is the `k`-th input port's**, for a
walk over binders none of which is a domain. -/
theorem prepare_visible_port {bools bits} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup), (L.map Prod.snd).Nodup →
      (∀ b ∈ L, b.1.2 ≠ .domain) → ∀ (k : Nat) (b : (Name × MixedGateBinder) × FVarId) (port : Port),
      L[k]? = some b → (inputPorts bools bits L a)[k]? = some port →
      visible (prepare bools bits L a).context (prepare bools bits L a).state.sourceBindings b.2 =
        some port.name
  | [], _, _, _, _, _, _, hb, _ => by cases hb
  | ((name, kind), id) :: rest, a, nd, hk, k, b, port, hb, hp => by
    rw [List.map_cons, List.nodup_cons] at nd
    have hrest : ∀ b ∈ rest, b.1.2 ≠ .domain := fun b hb => hk b (List.mem_cons_of_mem _ hb)
    cases k with
    | zero =>
      cases hb
      rw [prepare, prepare_visible_keep rest _ id nd.1]
      cases kind with
      | domain => exact absurd rfl (hk _ List.mem_cons_self)
      | bool => cases hp; exact visible_new
      | bits n => cases hp; exact visible_new
    | succ k =>
      rw [prepare]
      cases kind with
      | domain => exact absurd rfl (hk _ List.mem_cons_self)
      | bool => exact prepare_visible_port rest _ nd.2 hrest k b port hb hp
      | bits n => exact prepare_visible_port rest _ nd.2 hrest k b port hb hp

end Tools.ShippingMachineCloses
