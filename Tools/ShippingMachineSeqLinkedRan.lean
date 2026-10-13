import Tools.ShippingMachineSeqLinkedR

/-! # The three wired heads over `MachineRan` (round par/g-1)

WRITTEN, NOT BUILT. NEW file; no built file is edited by it.

The depth generators take the wired endpoint of a parent from one of three
heads (`Tools/ShippingMachineSeqLinkedR.lean`: `machine_traceL_of_loop_causalRA`,
`_of_comb_callsRA`, `_of_data_causalRA`), each of which asks the run, the
reflection, `MachineClosesAt` and `ChildBnd` and hands all four to
`Tools.ShippingMachineTraceX.machine_trace_lets_of_streamBRA`. That theorem
is now split (`machine_trace_lets_of_streamBRA_ran`, over
`Tools.ShippingMachineRan.MachineRan`); the heads below are the three built
heads with the same four binders replaced by `ran`.

The LEADING binders (the data and the source hypotheses) are unchanged and
in the built order, so a generator that has the arguments of
`f.machine_sound`'s proof term (`Tools.ShippingMachineSeqCommand.endpointParts`)
applies `<head>RA_ran` to them exactly as the built generators apply
`<head>RA`; after them the binders are `{mctx} {mref} {cctx} {cref} {m}
{design} (ran)`.

The three proofs are COPIES (by script) of the built ones — 25, 6 and 30
lines; the built heads are not corollaries of these (that would be an edit
of a fourth built file for no gain: nothing else needs it). -/
namespace Tools.ShippingMachineCausal
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineTraceX (MachineTraceLBX ServedReal machine_trace_lets_of_streamBRA_ran)

set_option maxHeartbeats 2000000 in
/-- `machine_traceL_of_loop_causalRA` over `MachineRan` (round par/g-1): the statement and the
proof of the built head (`Tools/ShippingMachineSeqLinkedR.lean`), COPIED by script with
the run, the reflection, the closing and the boundary replaced by `ran`. The leading
binders (through the last data hypothesis) are the built head's, in its order. If the
original changes, this copy does not follow. -/
theorem machine_traceL_of_loop_causalRA_ran {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) {α : ι → Type} [∀ i, Inhabited (α i)] {ρ : ι → Type}
    (σ : (i : ι) → α i → HList (tys d.ss))
    (inits : HList (tys d.ss))
    (f : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Signal (dom i) (α i))
    (res : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Signal (dom i) (α i) → ρ i)
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (h0 : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i)),
      σ i ((f i bools bits l).val 0) = inits)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i))
      (t : Nat),
      σ i ((f i bools bits l).val (t + 1)) =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).v (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (L : Signal (dom i) (α i))
      (t : Nat),
      (obsR i (res i bools bits L)).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).v (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (res i bools bits (Signal.loop (f i bools bits))))
    (hcausal : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (l l' : Signal (dom i) (α i)) (t : Nat), (∀ c, c ≤ t → l.val c = l'.val c) →
      (∀ p w, (ext i bools bits l p w).val t = (ext i bools bits l' p w).val t) ∧
      (∀ p, (extB i bools bits l p).val t = (extB i bools bits l' p).val t))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref declName d.shape m design) :
    MachineTraceLBX (ServedReal mctx mref cctx cref declName d.shape m design) declName d m design dom src
      (fun i bools bits => ext i bools bits (Signal.loop (f i bools bits)))
      (fun i bools bits => extB i bools bits (Signal.loop (f i bools bits)))
      (letObsLoop d dom σ f ext extB) := by
  refine machine_trace_lets_of_streamBRA_ran d dom inits src (letObsLoop d dom σ f ext extB) ok hbody
    hinit _ _ ?_ ran
  intro i bools bits
  refine ⟨fun t => σ i ((Signal.loop (f i bools bits)).val t), ?_, ?_, ?_, ?_⟩
  · show σ i (Signal.loopGo (f i bools bits) 0) = inits
    rw [Signal.loopGo_eq]
    exact h0 i bools bits _
  · intro t
    show σ i (Signal.loopGo (f i bools bits) (t + 1)) = _
    rw [Signal.loopGo_eq, writes]
    have hag : ∀ c, c ≤ t →
        (⟨fun s => if s < t + 1 then Signal.loopGo (f i bools bits) s else default⟩ :
          Signal (dom i) (α i)).val c = (Signal.loop (f i bools bits)).val c := by
      intro c hc
      show (if c < t + 1 then _ else _) = Signal.loopGo (f i bools bits) c
      rw [if_pos (by omega)]
    obtain ⟨hv, hb⟩ := hcausal i bools bits _ _ t hag
    rw [hag t (Nat.le_refl t),
      typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls _ _ _ _ t _ hb hv]
  · intro j
    rw [hsrc i bools bits]
    exact hres i bools bits _ j
  · intro j q g l hg hl
    simp only [letObsLoop, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
    rw [← hg]

set_option maxHeartbeats 2000000 in
/-- `machine_traceL_of_comb_callsRA` over `MachineRan` (round par/g-1): the statement and the
proof of the built head (`Tools/ShippingMachineSeqLinkedR.lean`), COPIED by script with
the run, the reflection, the closing and the boundary replaced by `ran`. The leading
binders (through the last data hypothesis) are the built head's, in its order. If the
original changes, this copy does not follow. -/
theorem machine_traceL_of_comb_callsRA_ran {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) (inits : HList (tys d.ss))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (hnext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      inits = evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits)
          t inits).b (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits)
          t inits).v (d.vpos j) w)
        d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      (src i bools bits).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits)
            t inits).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits)
            t inits).v (d.vpos k) w)
          o.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref declName d.shape m design) :
    MachineTraceLBX (ServedReal mctx mref cctx cref declName d.shape m design) declName d m design dom src ext extB (letObsComb d dom inits ext extB) := by
  refine machine_trace_lets_of_streamBRA_ran d dom inits src (letObsComb d dom inits ext extB) ok hbody
    hinit ext extB ?_ ran
  intro i bools bits
  refine ⟨fun _ => inits, rfl, fun t => hnext i bools bits t, hres i bools bits, ?_⟩
  intro j q g l hg hl
  simp only [letObsComb, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
  rw [← hg]

set_option maxHeartbeats 2000000 in
/-- `machine_traceL_of_data_causalRA` over `MachineRan` (round par/g-1): the statement and the
proof of the built head (`Tools/ShippingMachineSeqLinkedR.lean`), COPIED by script with
the run, the reflection, the closing and the boundary replaced by `ran`. The leading
binders (through the last data hypothesis) are the built head's, in its order. If the
original changes, this copy does not follow. -/
theorem machine_traceL_of_data_causalRA_ran {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) [Inhabited (HList (tys d.ss))] {ρ : ι → Type}
    (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst)
    (hcausal : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S S' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (∀ c, c ≤ t → S.val c = S'.val c) →
      (∀ p w, (ext i bools bits S p w).val t = (ext i bools bits S' p w).val t) ∧
      (∀ p, (extB i bools bits S p).val t = (extB i bools bits S' p).val t))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref declName d.shape m design) :
    MachineTraceLBX (ServedReal mctx mref cctx cref declName d.shape m design) declName d m design dom src
      (fun i bools bits => ext i bools bits (stateLoop inits (body i bools bits)))
      (fun i bools bits => extB i bools bits (stateLoop inits (body i bools bits)))
      (letObsB d dom inits body ext extB) := by
  refine machine_trace_lets_of_streamBRA_ran d dom inits src (letObsB d dom inits body ext extB) ok hbody
    hinit _ _ ?_ ran
  intro i bools bits
  have hW : ∀ (l l' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (∀ c, c ≤ t → l.val c = l'.val c) →
      valsAt (tys d.ss) (writesOn (body i bools bits) l) t =
        valsAt (tys d.ss) (writesOn (body i bools bits) l') t := by
    intro l l' t h
    show valsAt (tys d.ss) (body i bools bits (mkRegList l (tys d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys d.ss) l)).snd t =
      valsAt (tys d.ss) (body i bools bits (mkRegList l' (tys d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys d.ss) l')).snd t
    obtain ⟨hv, hb⟩ := hcausal i bools bits l l' t h
    rw [writes i bools bits l t, writes i bools bits l' t, h t (Nat.le_refl t),
      typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l) (extB i bools bits l')
        (ext i bools bits l) (ext i bools bits l') t (l'.val t) hb hv]
  obtain ⟨h0, hs⟩ := circuit_state_causal inits (body i bools bits) hW
  refine ⟨fun t => (stateLoop inits (body i bools bits)).val t, h0, ?_, ?_, ?_⟩
  · intro t
    show (stateLoop inits (body i bools bits)).val (t + 1) = _
    rw [hs t]
    exact writes i bools bits _ t
  · intro j
    rw [hsrc i bools bits]
    exact hres i bools bits (stateLoop inits (body i bools bits)) j
  · intro j q g l hg hl
    simp only [letObsB, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
    rw [← hg]
end Tools.ShippingMachineCausal
