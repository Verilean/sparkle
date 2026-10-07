import Tools.ShippingMachineCausalCtx

/-! # Hand-written loops with causal calls, with their wiring

`machine_trace_of_loop_causal` (ShippingMachineCausalCtx) is the endpoint of
a hand-written `Signal.loop` whose body reads calls (structure results,
sequential children, memories). Its twin here concludes the wired form
(`MachineTraceLB`): the module's instance statements and, per hardware
`let`, the `let` wire's value at every cycle (`letObsLoop`) — what the
composition with the children reads (the calls' argument wires). -/
namespace Tools.ShippingMachineCausal
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness

/-- The hardware `let`s' values on the loop's state stream, one observation
per `let`. -/
def letObsLoop (d : MachineData) {ι : Type} (dom : ι → DomainConfig) {α : ι → Type}
    [∀ i, Inhabited (α i)] (σ : (i : ι) → α i → HList (tys d.ss))
    (f : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Signal (dom i) (α i))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Nat → Signal (dom i) Bool) :
    (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat) :=
  fun i bools bits => d.ls.map fun l => fun j => enc l.1 (eval
    (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls
      (extB i bools bits (Signal.loop (f i bools bits)))
      (ext i bools bits (Signal.loop (f i bools bits))) j
      (σ i ((Signal.loop (f i bools bits)).val j))).b (d.bpos k))
    (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls
      (extB i bools bits (Signal.loop (f i bools bits)))
      (ext i bools bits (Signal.loop (f i bools bits))) j
      (σ i ((Signal.loop (f i bools bits)).val j))).v (d.vpos k) w) l.2)

set_option maxHeartbeats 2000000 in
/-- `machine_trace_of_loop_causal` with the wiring and the `let` wires. -/
theorem machine_traceL_of_loop_causal {declName : Name} (d : MachineData) {ι : Type}
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
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceLB declName d m design dom src
      (fun i bools bits => ext i bools bits (Signal.loop (f i bools bits)))
      (fun i bools bits => extB i bools bits (Signal.loop (f i bools bits)))
      (letObsLoop d dom σ f ext extB) := by
  refine machine_trace_lets_of_streamB d dom inits src (letObsLoop d dom σ f ext extB) ok hbody
    hinit _ _ ?_ hr entry closes
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

/-- The hardware `let`s' values of a declaration without registers (the
state the constant `inits`). -/
def letObsComb (d : MachineData) {ι : Type} (dom : ι → DomainConfig) (inits : HList (tys d.ss))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool) :
    (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat) :=
  fun i bools bits => d.ls.map fun l => fun j => enc l.1 (eval
    (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) j
      inits).b (d.bpos k))
    (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) j
      inits).v (d.vpos k) w) l.2)

set_option maxHeartbeats 2000000 in
/-- `machine_trace_of_comb_calls` with the wiring and the `let` wires. -/
theorem machine_traceL_of_comb_calls {declName : Name} (d : MachineData) {ι : Type}
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
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceLB declName d m design dom src ext extB (letObsComb d dom inits ext extB) := by
  refine machine_trace_lets_of_streamB d dom inits src (letObsComb d dom inits ext extB) ok hbody
    hinit ext extB ?_ hr entry closes
  intro i bools bits
  refine ⟨fun _ => inits, rfl, fun t => hnext i bools bits t, hres i bools bits, ?_⟩
  intro j q g l hg hl
  simp only [letObsComb, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
  rw [← hg]

end Tools.ShippingMachineCausal
