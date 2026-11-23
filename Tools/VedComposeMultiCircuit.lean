import Tools.VedComposeMultiLoop
import Sparkle.Core.CircuitMonad

/-!
# VED compose, multi-circuit parent (unit 15): the fused register pack of two wired circuits

Two `circuit do` blocks wired by a `let` outside both (`let a := stageA go; stageB a.ph`) are two `runCircuitH`: the
loop of `stageA` over `HList αA`, and the loop of `stageB` over `HList αB` whose writes read the first loop.  One
`runCircuitH` over `αA ++ αB` (registers of A first, then those of B) has the same two loops as the two components of its state.

* `happend`, `htake`, `hdrop`, `sappend`, `stake`, `sdrop`: append / split of `HList` and `Circuit.SigList`.
* `packRegister_append_val`: `packRegister` over the appended lists is, pointwise, the pair of the two packs.
* `loop_append`: with pointwise write functions `WA` (reads A's state) and `WB` (reads A's state and B's state), the loop of
  the fused pack (writes `sappend (WA (htake L)) (WB (htake L) (hdrop L))`) is pointwise `happend` of the loop of A and the loop
  of B on A's loop.  The two pointwise hypotheses are the facts a generator proves by `simp` on the reduced writes.

Nothing here is assumed about a circuit: the hypotheses are about the write functions only.
-/

open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

namespace Tools.VedComposeMultiCircuit

/-- Append of two register files. -/
def happend : (αA : List Type) → {αB : List Type} → HList αA → HList αB → HList (αA ++ αB)
  | [], _, _, hb => hb
  | _ :: as, _, ha, hb => (ha.1, happend as ha.2 hb)

/-- The first part of an appended register file. -/
def htake : (αA : List Type) → {αB : List Type} → HList (αA ++ αB) → HList αA
  | [], _, _ => ()
  | _ :: as, _, h => (h.1, htake as h.2)

/-- The second part of an appended register file. -/
def hdrop : (αA : List Type) → {αB : List Type} → HList (αA ++ αB) → HList αB
  | [], _, h => h
  | _ :: as, _, h => hdrop as h.2

/-- Append of two pending-write lists. -/
def sappend {dom : DomainConfig} : (αA : List Type) → {αB : List Type} →
    Circuit.SigList dom αA → Circuit.SigList dom αB → Circuit.SigList dom (αA ++ αB)
  | [], _, _, wb => wb
  | _ :: as, _, wa, wb => (wa.1, sappend as wa.2 wb)

/-- The first part of an appended pending-write list. -/
def stake {dom : DomainConfig} : (αA : List Type) → {αB : List Type} →
    Circuit.SigList dom (αA ++ αB) → Circuit.SigList dom αA
  | [], _, _ => ()
  | _ :: as, _, w => (w.1, stake as w.2)

/-- The second part of an appended pending-write list. -/
def sdrop {dom : DomainConfig} : (αA : List Type) → {αB : List Type} →
    Circuit.SigList dom (αA ++ αB) → Circuit.SigList dom αB
  | [], _, w => w
  | _ :: as, _, w => sdrop as w.2

/-- The values of a pending-write list at time `t`. -/
def sat {dom : DomainConfig} : (αs : List Type) → Circuit.SigList dom αs → Nat → HList αs
  | [], _, _ => ()
  | _ :: as, w, t => (w.1.val t, sat as w.2 t)

theorem htake_happend : ∀ (αA : List Type) {αB : List Type} (a : HList αA) (b : HList αB),
    htake αA (happend αA a b) = a
  | [], _, a, _ => by cases a; rfl
  | _ :: as, _, a, b => by
    show (a.1, htake as (happend as a.2 b)) = a
    rw [htake_happend as a.2 b]

theorem hdrop_happend : ∀ (αA : List Type) {αB : List Type} (a : HList αA) (b : HList αB),
    hdrop αA (happend αA a b) = b
  | [], _, _, _ => rfl
  | _ :: as, _, a, b => hdrop_happend as a.2 b

theorem happend_htake_hdrop : ∀ (αA : List Type) {αB : List Type} (h : HList (αA ++ αB)),
    happend αA (htake αA h) (hdrop αA h) = h
  | [], _, _ => rfl
  | _ :: as, _, h => by
    show (h.1, happend as (htake as h.2) (hdrop as h.2)) = h
    rw [happend_htake_hdrop as h.2]
    rfl

/-- The register pack at time `t`. -/
theorem packRegister_val {dom : DomainConfig} : ∀ (αs : List Type) (i : HList αs) (w : Circuit.SigList dom αs) (t : Nat),
    (packRegister αs i w).val t = match t with | 0 => i | n + 1 => sat αs w n
  | [], i, _, t => by cases t <;> rfl
  | _ :: as, i, w, t => by
    cases t with
    | zero =>
      show (i.1, (packRegister as i.2 w.2).val 0) = i
      rw [packRegister_val as i.2 w.2 0]
    | succ n =>
      show (w.1.val n, (packRegister as i.2 w.2).val (n + 1)) = (w.1.val n, sat as w.2 n)
      rw [packRegister_val as i.2 w.2 (n + 1)]

theorem sat_sappend : ∀ (αA : List Type) {αB : List Type} (wa : Circuit.SigList dom αA) (wb : Circuit.SigList dom αB) (t : Nat),
    sat (αA ++ αB) (sappend αA wa wb) t = happend αA (sat αA wa t) (sat αB wb t)
  | [], _, _, _, _ => rfl
  | _ :: as, _, wa, wb, t => by
    show (wa.1.val t, sat (as ++ _) (sappend as wa.2 wb) t) = (wa.1.val t, happend as (sat as wa.2 t) (sat _ wb t))
    rw [sat_sappend as wa.2 wb t]

/-- The register pack over the appended lists is, at every time, the pair of the two packs. -/
theorem packRegister_append_val {dom : DomainConfig} (αA : List Type) {αB : List Type}
    (iA : HList αA) (iB : HList αB) (wa : Circuit.SigList dom αA) (wb : Circuit.SigList dom αB) (t : Nat) :
    (packRegister (αA ++ αB) (happend αA iA iB) (sappend αA wa wb)).val t
      = happend αA ((packRegister αA iA wa).val t) ((packRegister αB iB wb).val t) := by
  rw [packRegister_val, packRegister_val, packRegister_val]
  cases t with
  | zero => rfl
  | succ n => exact sat_sappend αA wa wb n

/-- The pack of a pointwise write function is causal in the state. -/
theorem pack_causal {dom : DomainConfig} {α : Type} (αs : List Type) (i : HList αs) (W : Signal dom α → Circuit.SigList dom αs)
    (hW : ∀ t (x y : Signal dom α), x.val t = y.val t → sat αs (W x) t = sat αs (W y) t) :
    ∀ t (x y : Signal dom α), (∀ j, j < t → x.val j = y.val j) → (packRegister αs i (W x)).val t = (packRegister αs i (W y)).val t := by
  intro t x y h
  rw [packRegister_val, packRegister_val]
  cases t with
  | zero => rfl
  | succ n => exact hW n x y (h n (Nat.lt_succ_self n))

/-- The loop of the first circuit. -/
@[reducible] def loopA {dom : DomainConfig} {αA : List Type} [Inhabited (HList αA)] (iA : HList αA)
    (WA : Signal dom (HList αA) → Circuit.SigList dom αA) : Signal dom (HList αA) :=
  Signal.loop (fun x => packRegister αA iA (WA x))

/-- The loop of the second circuit, which reads the first loop. -/
@[reducible] def loopB {dom : DomainConfig} {αA αB : List Type} [Inhabited (HList αA)] [Inhabited (HList αB)]
    (iA : HList αA) (iB : HList αB) (WA : Signal dom (HList αA) → Circuit.SigList dom αA)
    (WB : Signal dom (HList αA) → Signal dom (HList αB) → Circuit.SigList dom αB) : Signal dom (HList αB) :=
  Signal.loop (fun y => packRegister αB iB (WB (loopA iA WA) y))

/-- Two circuits wired feed-forward are the two components of the loop of the fused register pack. -/
theorem loop_append {dom : DomainConfig} (αA αB : List Type) [Inhabited (HList αA)] [Inhabited (HList αB)]
    [Inhabited (HList (αA ++ αB))] (iA : HList αA) (iB : HList αB)
    (WA : Signal dom (HList αA) → Circuit.SigList dom αA)
    (WB : Signal dom (HList αA) → Signal dom (HList αB) → Circuit.SigList dom αB)
    (hWA : ∀ t (x y : Signal dom (HList αA)), x.val t = y.val t → sat αA (WA x) t = sat αA (WA y) t)
    (hWB : ∀ t (x x' : Signal dom (HList αA)) (y y' : Signal dom (HList αB)), x.val t = x'.val t → y.val t = y'.val t →
       sat αB (WB x y) t = sat αB (WB x' y') t) :
    ∀ t, (Signal.loop (fun L : Signal dom (HList (αA ++ αB)) =>
          packRegister (αA ++ αB) (happend αA iA iB)
            (sappend αA (WA (Signal.map (htake αA) L)) (WB (Signal.map (htake αA) L) (Signal.map (hdrop αA) L))))).val t
      = happend αA ((loopA iA WA).val t) ((loopB iA iB WA WB).val t) := by
  have hA := pack_causal αA iA WA hWA
  have hfixA : ∀ t, (packRegister αA iA (WA (loopA iA WA))).val t = (loopA iA WA).val t := by
    intro t
    show _ = Signal.loopGo (fun x => packRegister αA iA (WA x)) t
    rw [Signal.loopGo_eq]
    exact (hA t _ _ (fun i hi => by
      show (if i < t then Signal.loopGo (fun x => packRegister αA iA (WA x)) i else default) = _
      rw [if_pos hi]; rfl)).symm
  have hB : ∀ t (x x' : Signal dom (HList αA)) (y y' : Signal dom (HList αB)), (∀ i, i < t → x.val i = x'.val i) →
       (∀ i, i < t → y.val i = y'.val i) → (packRegister αB iB (WB x y)).val t = (packRegister αB iB (WB x' y')).val t := by
    intro t x x' y y' hx hy
    rw [packRegister_val, packRegister_val]
    cases t with
    | zero => rfl
    | succ n => exact hWB n x x' y y' (hx n (Nat.lt_succ_self n)) (hy n (Nat.lt_succ_self n))
  have hfixB : ∀ t, (packRegister αB iB (WB (loopA iA WA) (loopB iA iB WA WB))).val t = (loopB iA iB WA WB).val t := by
    intro t
    show _ = Signal.loopGo (fun y => packRegister αB iB (WB (loopA iA WA) y)) t
    rw [Signal.loopGo_eq]
    exact (hB t _ _ _ _ (fun _ _ => rfl) (fun i hi => by
      show (if i < t then Signal.loopGo (fun y => packRegister αB iB (WB (loopA iA WA) y)) i else default) = _
      rw [if_pos hi]; rfl)).symm
  have e1 : Signal.map (htake αA) (⟨fun i => happend αA ((loopA iA WA).val i) ((loopB iA iB WA WB).val i)⟩ :
        Signal dom (HList (αA ++ αB))) = loopA iA WA :=
    Tools.VedU2HierMulti.signal_ext (fun i => htake_happend αA _ _)
  have e2 : Signal.map (hdrop αA) (⟨fun i => happend αA ((loopA iA WA).val i) ((loopB iA iB WA WB).val i)⟩ :
        Signal dom (HList (αA ++ αB))) = loopB iA iB WA WB :=
    Tools.VedU2HierMulti.signal_ext (fun i => hdrop_happend αA _ _)
  refine Tools.VedU2HierMulti.loop_unique _ ?_
    (⟨fun i => happend αA ((loopA iA WA).val i) ((loopB iA iB WA WB).val i)⟩ : Signal dom (HList (αA ++ αB))) ?_
  · intro t x y h
    rw [packRegister_append_val, packRegister_append_val]
    have h1 : ∀ i, i < t → (Signal.map (htake αA) x).val i = (Signal.map (htake αA) y).val i := fun i hi => by
      show htake αA (x.val i) = htake αA (y.val i); rw [h i hi]
    have h2 : ∀ i, i < t → (Signal.map (hdrop αA) x).val i = (Signal.map (hdrop αA) y).val i := fun i hi => by
      show hdrop αA (x.val i) = hdrop αA (y.val i); rw [h i hi]
    rw [hA t _ _ h1, hB t _ _ _ _ h1 h2]
  · intro t
    rw [packRegister_append_val, e1, e2, hfixA t, hfixB t]

end Tools.VedComposeMultiCircuit
