import Lean
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

register_option ved.compose.multiCircuit : Bool := {
  defValue := false
  descr := "VED compose: a declaration of TWO wired closed circuits (the second reads the first) is fused into one circuit over the appended registers"
}

/-- Append of two register files. -/
@[reducible] def happend : (αA : List Type) → {αB : List Type} → HList αA → HList αB → HList (αA ++ αB)
  | [], _, _, hb => hb
  | _ :: as, _, ha, hb => (ha.1, happend as ha.2 hb)

/-- The first part of an appended register file. -/
@[reducible] def htake : (αA : List Type) → {αB : List Type} → HList (αA ++ αB) → HList αA
  | [], _, _ => ()
  | _ :: as, _, h => (h.1, htake as h.2)

/-- The second part of an appended register file. -/
@[reducible] def hdrop : (αA : List Type) → {αB : List Type} → HList (αA ++ αB) → HList αB
  | [], _, h => h
  | _ :: as, _, h => hdrop as h.2

/-- Append of two pending-write lists. -/
@[reducible] def sappend {dom : DomainConfig} : (αA : List Type) → {αB : List Type} →
    Circuit.SigList dom αA → Circuit.SigList dom αB → Circuit.SigList dom (αA ++ αB)
  | [], _, _, wb => wb
  | _ :: as, _, wa, wb => (wa.1, sappend as wa.2 wb)

/-- The first part of an appended pending-write list. -/
@[reducible] def stake {dom : DomainConfig} : (αA : List Type) → {αB : List Type} →
    Circuit.SigList dom (αA ++ αB) → Circuit.SigList dom αA
  | [], _, _ => ()
  | _ :: as, _, w => (w.1, stake as w.2)

/-- The second part of an appended pending-write list. -/
@[reducible] def sdrop {dom : DomainConfig} : (αA : List Type) → {αB : List Type} →
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


/-! ### The fused body of two circuits: `fuseBody`, and `fuse_run`

`fuseBody bodyA wA bodyB` is the body of ONE `runCircuitH` over `αA ++ αB`: it runs `bodyA` on the state part of A and `bodyB`
(whose closed argument `wA (output of A)` is the part of B that reads A) on the state part of B, and concatenates the writes.
The state parts are recovered from the pending-write seed `mkHolds` by `liveOfSigs`. -/

/-- The state signal of a pending-write list of live reads (the inverse of `mkHolds`). -/
@[reducible] def liveOfSigs {dom : DomainConfig} : (αs : List Type) → Circuit.SigList dom αs → Signal dom (HList αs)
  | [], _ => Signal.pure ()
  | _ :: as, w => bundle2 w.1 (liveOfSigs as w.2)

theorem liveOfSigs_mkHolds {dom : DomainConfig} : ∀ (αs : List Type) (L : Signal dom (HList αs)),
    liveOfSigs αs (mkHolds αs L) = L
  | [], L => Tools.VedU2HierMulti.signal_ext (fun t => by rfl)
  | _ :: as, L => by
    have ih := liveOfSigs_mkHolds as (Signal.map Prod.snd L)
    refine Tools.VedU2HierMulti.signal_ext (fun t => ?_)
    show ((L.val t).1, ((liveOfSigs as (mkHolds as (Signal.map Prod.snd L))).val t)) = L.val t
    rw [ih]
    rfl

theorem liveOfSigs_stake_mkHolds {dom : DomainConfig} : ∀ (αA : List Type) {αB : List Type} (L : Signal dom (HList (αA ++ αB))),
    liveOfSigs αA (stake αA (mkHolds (αA ++ αB) L)) = Signal.map (htake αA) L
  | [], _, L => Tools.VedU2HierMulti.signal_ext (fun t => by rfl)
  | _ :: as, _, L => by
    have ih := liveOfSigs_stake_mkHolds as (Signal.map Prod.snd L)
    refine Tools.VedU2HierMulti.signal_ext (fun t => ?_)
    show ((L.val t).1, ((liveOfSigs as (stake as (mkHolds (as ++ _) (Signal.map Prod.snd L)))).val t))
      = ((L.val t).1, htake as (L.val t).2)
    rw [ih]
    rfl

theorem liveOfSigs_sdrop_mkHolds {dom : DomainConfig} : ∀ (αA : List Type) {αB : List Type} (L : Signal dom (HList (αA ++ αB))),
    liveOfSigs αB (sdrop αA (mkHolds (αA ++ αB) L)) = Signal.map (hdrop αA) L
  | [], _, L => liveOfSigs_mkHolds _ L
  | _ :: as, _, L => by
    have ih := liveOfSigs_sdrop_mkHolds as (Signal.map Prod.snd L)
    show liveOfSigs _ (sdrop as (mkHolds (as ++ _) (Signal.map Prod.snd L))) = _
    rw [ih]
    rfl

section Fuse
variable {dom : DomainConfig} {αA αB : List Type} {ρA ρB τ : Type} [HasDomain ρA dom] [HasDomain ρB dom]

/-- The fused body. -/
@[reducible] def fuseBody
    (bodyA : RegList dom (HList αA) (Circuit.SigList dom αA) αA → Circuit dom (Circuit.SigList dom αA) ρA)
    (wA : ρA → τ)
    (bodyB : τ → RegList dom (HList αB) (Circuit.SigList dom αB) αB → Circuit dom (Circuit.SigList dom αB) ρB) :
    RegList dom (HList (αA ++ αB)) (Circuit.SigList dom (αA ++ αB)) (αA ++ αB) →
      Circuit dom (Circuit.SigList dom (αA ++ αB)) ρB :=
  fun _regs holds =>
    let LA := liveOfSigs αA (stake αA holds)
    let LB := liveOfSigs αB (sdrop αA holds)
    let rA := bodyA (mkRegList LA αA (fun s => s) (fun f => f)) (mkHolds αA LA)
    let rB := bodyB (wA rA.fst) (mkRegList LB αB (fun s => s) (fun f => f)) (mkHolds αB LB)
    (rB.fst, sappend αA rA.snd rB.snd)


variable [HListWireable αA] [HListWireable αB] [HListWireable (αA ++ αB)]
  [Inhabited (HList αA)] [Inhabited (HList αB)] [Inhabited (HList (αA ++ αB))]

/-- The write function of A's circuit over its state signal. -/
@[reducible] def writesA
    (bodyA : RegList dom (HList αA) (Circuit.SigList dom αA) αA → Circuit dom (Circuit.SigList dom αA) ρA) :
    Signal dom (HList αA) → Circuit.SigList dom αA :=
  fun x => (bodyA (mkRegList x αA (fun s => s) (fun f => f)) (mkHolds αA x)).snd

/-- The write function of B's circuit over A's state signal (the closed argument) and its own state signal. -/
@[reducible] def writesB
    (bodyA : RegList dom (HList αA) (Circuit.SigList dom αA) αA → Circuit dom (Circuit.SigList dom αA) ρA)
    (wA : ρA → τ)
    (bodyB : τ → RegList dom (HList αB) (Circuit.SigList dom αB) αB → Circuit dom (Circuit.SigList dom αB) ρB) :
    Signal dom (HList αA) → Signal dom (HList αB) → Circuit.SigList dom αB :=
  fun x y => (bodyB (wA (bodyA (mkRegList x αA (fun s => s) (fun f => f)) (mkHolds αA x)).fst)
    (mkRegList y αB (fun s => s) (fun f => f)) (mkHolds αB y)).snd

/-- Two `runCircuitH` wired feed-forward (B's body reads `wA` of A's result) are ONE `runCircuitH` over the appended registers,
when the two write functions are pointwise in the state they read (the facts a generator proves on the reduced writes). -/
theorem fuse_run (iA : HList αA) (iB : HList αB)
    (bodyA : RegList dom (HList αA) (Circuit.SigList dom αA) αA → Circuit dom (Circuit.SigList dom αA) ρA)
    (wA : ρA → τ)
    (bodyB : τ → RegList dom (HList αB) (Circuit.SigList dom αB) αB → Circuit dom (Circuit.SigList dom αB) ρB)
    (hWA : ∀ t (x y : Signal dom (HList αA)), x.val t = y.val t →
      sat αA (writesA bodyA x) t = sat αA (writesA bodyA y) t)
    (hWB : ∀ t (x x' : Signal dom (HList αA)) (y y' : Signal dom (HList αB)), x.val t = x'.val t → y.val t = y'.val t →
      sat αB (writesB bodyA wA bodyB x y) t = sat αB (writesB bodyA wA bodyB x' y') t) :
    runCircuitH (αs := αA ++ αB) (happend αA iA iB) (fuseBody bodyA wA bodyB)
      = runCircuitH (αs := αB) iB (bodyB (wA (runCircuitH (αs := αA) iA bodyA))) := by
  have hloop := loop_append αA αB iA iB (writesA bodyA) (writesB bodyA wA bodyB) hWA hWB
  have hF : (fun live : Signal dom (HList (αA ++ αB)) =>
        packRegister (αA ++ αB) (happend αA iA iB)
          (((fuseBody bodyA wA bodyB) (mkRegList live (αA ++ αB) (fun s => s) (fun f => f))
            (mkHolds (αA ++ αB) live)).snd))
      = (fun L : Signal dom (HList (αA ++ αB)) =>
          packRegister (αA ++ αB) (happend αA iA iB)
            (sappend αA (writesA bodyA (Signal.map (htake αA) L))
              (writesB bodyA wA bodyB (Signal.map (htake αA) L) (Signal.map (hdrop αA) L)))) := by
    funext L
    have e3 := liveOfSigs_stake_mkHolds αA L
    have e4 := liveOfSigs_sdrop_mkHolds αA L
    dsimp only [fuseBody, writesA, writesB]
    rw [e3, e4]
  have hS : (Signal.loop (fun live : Signal dom (HList (αA ++ αB)) =>
        packRegister (αA ++ αB) (happend αA iA iB)
          (((fuseBody bodyA wA bodyB) (mkRegList live (αA ++ αB) (fun s => s) (fun f => f))
            (mkHolds (αA ++ αB) live)).snd)))
      = (⟨fun t => happend αA ((loopA iA (writesA bodyA)).val t) ((loopB iA iB (writesA bodyA) (writesB bodyA wA bodyB)).val t)⟩ :
          Signal dom (HList (αA ++ αB))) := by
    rw [hF]
    exact Tools.VedU2HierMulti.signal_ext hloop
  have e1 : Signal.map (htake αA) (⟨fun t => happend αA ((loopA iA (writesA bodyA)).val t)
        ((loopB iA iB (writesA bodyA) (writesB bodyA wA bodyB)).val t)⟩ : Signal dom (HList (αA ++ αB))) = loopA iA (writesA bodyA) :=
    Tools.VedU2HierMulti.signal_ext (fun i => htake_happend αA _ _)
  have e2 : Signal.map (hdrop αA) (⟨fun t => happend αA ((loopA iA (writesA bodyA)).val t)
        ((loopB iA iB (writesA bodyA) (writesB bodyA wA bodyB)).val t)⟩ : Signal dom (HList (αA ++ αB))) = loopB iA iB (writesA bodyA) (writesB bodyA wA bodyB) :=
    Tools.VedU2HierMulti.signal_ext (fun i => hdrop_happend αA _ _)
  show ((fuseBody bodyA wA bodyB) _ _).fst = _
  rw [show (Signal.loop (fun live : Signal dom (HList (αA ++ αB)) =>
        packRegister (αA ++ αB) (happend αA iA iB)
          (((fuseBody bodyA wA bodyB) (mkRegList live (αA ++ αB) (fun s => s) (fun f => f))
            (mkHolds (αA ++ αB) live)).snd))) = _ from hS]
  dsimp only [fuseBody]
  rw [liveOfSigs_stake_mkHolds, liveOfSigs_sdrop_mkHolds, e1, e2]

end Fuse

end Tools.VedComposeMultiCircuit
