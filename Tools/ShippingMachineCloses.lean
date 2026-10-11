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
open Tools.ShippingSpineOrder Tools.ShippingClosedOrder Tools.ShippingCloseLetsRun

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

/-! ## The aliases `letOperands` picks, with what the run says of each -/

/-- What the run says of the alias list, position by position from `i`: the
operand is declared at the width `m`; there is a suffix `pre` of the builder's
body with the operand's source (`Src`) and reads within `Vk i`; and the
operand, if protected, is in `Vk i`. -/
def Facts (P : String → Prop) (bnd : FVarId → Option String) (Vk : Nat → String → Prop)
    (wires : List Port) (bodyB : List Stmt) :
    Nat → List (Port × String) → List Lean.Expr → List Nat → Prop
  | _, [], [], [] => True
  | i, pa :: al, e :: es, m :: ws =>
    wireWidth wires pa.2 = m ∧
      (∃ pre, pre <:+ bodyB ∧ Src P bnd pre e pa.2 ∧
        ∀ l r, Stmt.assign l r ∈ pre → ReadsOK P (Vk i) r) ∧
      (P pa.2 → Vk i pa.2) ∧ Facts P bnd Vk wires bodyB (i + 1) al es ws
  | _, _, _, _ => False

/-- **The aliases are the run's links.** With the spine (and its widths) on
the final body and the per-field facts on the builder's body — the same
statements, by the body's one-driver order — `letOperands` succeeds, on
exactly the operands the facts are about. -/
theorem letOperands_facts {P : String → Prop} {bnd : FVarId → Option String}
    {Vk : Nat → String → Prop} {wires : List Port} {body bodyB : List Stmt}
    (hacy : Acyclic body) (hsub : ∀ st ∈ bodyB, st ∈ body) :
    ∀ (ls : List Port) (ws : List Nat) (es : List Lean.Expr) (i : Nat) (w : String),
      ls.length = ws.length → SpineW wires body ws w → LP P bnd Vk bodyB i es w →
      es.length = ws.length →
      ∃ al core, letOperands body ls w = some (al, core) ∧ al.map (·.1) = ls ∧
        Facts P bnd Vk wires bodyB i al es ws ∧
        (ws ≠ [] → ∃ x a, concatParts? body x = some (a, core))
  | [], [], [], _, w, _, _, _, _ => ⟨[], w, rfl, rfl, trivial, fun h => absurd rfl h⟩
  | p :: ls, m :: ws, e :: es, i, w, hl, hs, hlp, he => by
    obtain ⟨a, b, hc, hw, hs'⟩ := hs
    obtain ⟨x, y, pre, hm, hpre, hsrc, hv, hrd, hlp'⟩ := hlp
    have hxy := concatParts?_of_mem hacy (hsub _ hm)
    rw [hc] at hxy
    cases hxy
    obtain ⟨al, core, hlo, hmap, hf, hcore⟩ := letOperands_facts hacy hsub ls ws es (i + 1) b
      (by simpa using hl) hs' hlp' (by simpa using he)
    refine ⟨(p, a) :: al, core, ?_, by rw [List.map_cons, hmap], ⟨hw, ⟨pre, hpre, hsrc, hrd⟩, hv, hf⟩,
      fun _ => ?_⟩
    · simp only [letOperands, hc, hlo]
    · by_cases hws : ws = []
      · subst hws
        cases ls with
        | nil =>
          simp only [letOperands] at hlo
          cases hlo
          exact ⟨w, a, hc⟩
        | cons _ _ => simp at hl
      · exact hcore hws
  | [], _ :: _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, _, _, he => by simp at he
  | [], [], _ :: _, _, _, _, _, _, he => by simp at he

end Tools.ShippingMachineCloses
