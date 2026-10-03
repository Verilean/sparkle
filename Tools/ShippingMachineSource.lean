import Sparkle.Core.CircuitMonad

/-! # The state stream of a `circuit do`, for any number of slots

`runCircuitH inits body` is a `Signal.loop` over the tuple of all register
slots: every slot is a `Signal.register` of its pending write, the writes
being read off the body applied to the live state. This file proves — once,
for an arbitrary slot list — what that loop computes: the state starts at the
initial tuple and, each cycle, becomes the tuple of the pending writes'
values. It is a statement about the Signal library only; no compiler is
involved. -/
namespace Tools.ShippingMachineSource
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- The values of a tuple of pending-write Signals at one cycle. -/
def valsAt {dom : DomainConfig} : (αs : List Type) → Circuit.SigList dom αs → Nat → HList αs
  | [], _, _ => ()
  | _ :: αs, ws, t => (ws.1.val t, valsAt αs ws.2 t)

/-- One register per slot, packed: the initial tuple at cycle 0, the pending
writes' values one cycle later. -/
theorem packRegister_val {dom : DomainConfig} :
    ∀ (αs : List Type) (inits : HList αs) (ws : Circuit.SigList dom αs),
      (packRegister αs inits ws).val 0 = inits ∧
      ∀ t, (packRegister αs inits ws).val (t + 1) = valsAt αs ws t
  | [], _, _ => ⟨rfl, fun _ => rfl⟩
  | _ :: αs, inits, ws => by
    obtain ⟨h0, hs⟩ := packRegister_val αs inits.2 ws.2
    constructor
    · show ((Signal.register inits.1 ws.1).val 0, (packRegister αs inits.2 ws.2).val 0) = inits
      rw [h0]; rfl
    · intro t
      show ((Signal.register inits.1 ws.1).val (t + 1),
        (packRegister αs inits.2 ws.2).val (t + 1)) = _
      rw [hs t]; rfl

/-- **The state recurrence of the packed register loop.** If the pending
writes are pointwise in the live state (true of every combinational cone: its
value at a cycle depends on its inputs at that cycle only), the loop's state
is the initial tuple at cycle 0 and the writes' values afterwards. -/
theorem loop_state {dom : DomainConfig} (αs : List Type) [Inhabited (HList αs)]
    (inits : HList αs) (W : Signal dom (HList αs) → Circuit.SigList dom αs)
    (hW : ∀ (l l' : Signal dom (HList αs)) (t : Nat), l.val t = l'.val t →
      valsAt αs (W l) t = valsAt αs (W l') t) :
    (Signal.loop (fun live => packRegister αs inits (W live))).val 0 = inits ∧
    ∀ t, (Signal.loop (fun live => packRegister αs inits (W live))).val (t + 1) =
      valsAt αs (W (Signal.loop (fun live => packRegister αs inits (W live)))) t := by
  constructor
  · show Signal.loopGo _ 0 = inits
    rw [Signal.loopGo_eq]
    exact (packRegister_val αs inits _).1
  · intro t
    show Signal.loopGo _ (t + 1) = _
    rw [Signal.loopGo_eq, (packRegister_val αs inits _).2 t]
    apply hW
    show (if t < t + 1 then Signal.loopGo _ t else default) = _
    rw [if_pos (by omega)]
    rfl

/-- Pointwiseness from one definitional fact per declaration: the writes at a
cycle are the writes computed from the CONSTANT state signal holding that
cycle's state. For a combinational cone this is `rfl`. -/
theorem pointwise_of_const {dom : DomainConfig} {αs : List Type}
    (W : Signal dom (HList αs) → Circuit.SigList dom αs)
    (hc : ∀ (l : Signal dom (HList αs)) (t : Nat),
      valsAt αs (W l) t = valsAt αs (W ⟨fun _ => l.val t⟩) t) :
    ∀ (l l' : Signal dom (HList αs)) (t : Nat), l.val t = l'.val t →
      valsAt αs (W l) t = valsAt αs (W l') t := by
  intro l l' t h
  rw [hc l t, hc l' t, h]

/-- The state loop of a `circuit do`: the packed registers of the writes its
body leaves pending when applied to the live state. -/
def stateLoop {dom : DomainConfig} {αs : List Type} {ρ : Type} [Inhabited (HList αs)]
    (inits : HList αs)
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
      Circuit dom (Circuit.SigList dom αs) ρ) : Signal dom (HList αs) :=
  Signal.loop (fun live =>
    packRegister αs inits
      (body (mkRegList live αs (fun s => s) (fun f => f)) (mkHolds αs live)).snd)

/-- `runCircuitH` is its body applied to the state loop, by definition. -/
theorem runCircuitH_eq {dom : DomainConfig} {αs : List Type} {ρ : Type} [HasDomain ρ dom]
    [HListWireable αs] [Inhabited (HList αs)] (inits : HList αs)
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
      Circuit dom (Circuit.SigList dom αs) ρ) :
    runCircuitH inits body =
      (body (mkRegList (stateLoop inits body) αs (fun s => s) (fun f => f))
        (mkHolds αs (stateLoop inits body))).fst := rfl

/-- **The state of a `circuit do`.** At cycle 0 the initial tuple; afterwards
the values, one cycle earlier, of the writes the body leaves pending — for
any body whose pending writes are pointwise in the state. -/
theorem circuit_state {dom : DomainConfig} {αs : List Type} {ρ : Type}
    [Inhabited (HList αs)] (inits : HList αs)
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
      Circuit dom (Circuit.SigList dom αs) ρ)
    (hW : ∀ (l l' : Signal dom (HList αs)) (t : Nat), l.val t = l'.val t →
      valsAt αs (body (mkRegList l αs (fun s => s) (fun f => f)) (mkHolds αs l)).snd t =
        valsAt αs (body (mkRegList l' αs (fun s => s) (fun f => f)) (mkHolds αs l')).snd t) :
    (stateLoop inits body).val 0 = inits ∧
    ∀ t, (stateLoop inits body).val (t + 1) =
      valsAt αs (body (mkRegList (stateLoop inits body) αs (fun s => s) (fun f => f))
        (mkHolds αs (stateLoop inits body))).snd t :=
  loop_state αs inits
    (fun live => (body (mkRegList live αs (fun s => s) (fun f => f)) (mkHolds αs live)).snd) hW

/-- **The state loop as a stream.** When the pending writes at a cycle are a
function `F` of the live values at that cycle (a `rfl` per declaration),
the state loop starts at the reset values and advances by `F`. -/
theorem stateLoop_stream {dom : DomainConfig} {αs : List Type} {ρ : Type}
    [Inhabited (HList αs)] (inits : HList αs)
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
      Circuit dom (Circuit.SigList dom αs) ρ)
    (F : Nat → HList αs → HList αs)
    (H : ∀ (S : Signal dom (HList αs)) (t : Nat),
      valsAt αs (body (mkRegList S αs (fun s => s) (fun f => f)) (mkHolds αs S)).snd t =
        F t (S.val t)) :
    (stateLoop inits body).val 0 = inits ∧
    ∀ t, (stateLoop inits body).val (t + 1) = F t ((stateLoop inits body).val t) := by
  have hW : ∀ (l l' : Signal dom (HList αs)) (t : Nat), l.val t = l'.val t →
      valsAt αs (body (mkRegList l αs (fun s => s) (fun f => f)) (mkHolds αs l)).snd t =
        valsAt αs (body (mkRegList l' αs (fun s => s) (fun f => f)) (mkHolds αs l')).snd t := by
    intro l l' t h
    rw [H l t, H l' t, h]
  obtain ⟨h0, hs⟩ := circuit_state inits body hW
  exact ⟨h0, fun t => by rw [hs t, H]⟩

end Tools.ShippingMachineSource
