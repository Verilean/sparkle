import Tools.ShippingMachineLoop

/-! # Hand-written loops and bare registers, wired

`machine_trace_of_loop` / `machine_trace_of_regs` with the WIRED conclusion
(`MachineTraceL`: the trace together with the module's wiring facts,
`MachineWired`), from the same data and `rfl`s. The wiring is what
`machine_ships_wired` reads to discharge the cleanup / merge / optimizer
gates. -/
namespace Tools.ShippingMachineLoopL
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge Tools.ShippingEntrySoundness
open Tools.ShippingMachineLoop

/-- `machine_trace_of_stream` (inputs as they are), wired. -/
theorem machine_traceL_of_stream {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig)
    (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (stream : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∃ σ : Nat → HList (tys d.ss), σ 0 = inits ∧
        (∀ t, σ (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ t)).v
            (d.vpos j) w) d.nexts) ∧
        ∀ j, (src i bools bits).map (fun f => f j) =
          d.outs.map fun o => enc o.1 (eval
            (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits j (σ j)).b
              (d.bpos k))
            (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits j (σ j)).v
              (d.vpos k) w) o.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src (fun _ _ bits => bits) (fun _ _ _ => []) :=
  machine_trace_lets_of_stream d dom inits src (fun _ _ _ => []) ok hbody hinit
    (fun _ _ bits => bits)
    (fun i bools bits => by
      obtain ⟨σ, a, b, c⟩ := stream i bools bits
      exact ⟨σ, a, b, c, fun _ _ _ _ h => by simp at h⟩) hr entry closes

set_option maxHeartbeats 2000000 in
/-- `machine_trace_of_loop`, wired. -/
theorem machine_traceL_of_loop {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) {α : ι → Type} [∀ i, Inhabited (α i)] {ρ : ι → Type}
    (σ : (i : ι) → α i → HList (tys d.ss))
    (inits : HList (tys d.ss))
    (f : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Signal (dom i) (α i))
    (res : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Signal (dom i) (α i) → ρ i)
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
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
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (l.val t))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (l.val t))).v
            (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (L : Signal (dom i) (α i))
      (t : Nat),
      (obsR i (res i bools bits L)).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (L.val t))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (L.val t))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (res i bools bits (Signal.loop (f i bools bits))))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src (fun _ _ bits => bits) (fun _ _ _ => []) := by
  refine machine_traceL_of_stream d dom inits src ok hbody hinit ?_ hr entry closes
  intro i bools bits
  obtain ⟨hs0, hss⟩ := loop_stream (f i bools bits) (σ i) inits
    (fun t x => evalTerms
      (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).b (d.bpos j))
      (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).v (d.vpos j) w)
      d.nexts)
    (h0 i bools bits) (writes i bools bits)
  refine ⟨fun t => σ i ((Signal.loop (f i bools bits)).val t), hs0, hss, ?_⟩
  intro j
  rw [hsrc i bools bits]
  exact hres i bools bits _ j

set_option maxHeartbeats 2000000 in
/-- `machine_trace_of_regs`, wired. -/
theorem machine_traceL_of_regs {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) (inits : HList (tys d.ss))
    (σ : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (h0 : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)), σ i bools bits 0 = inits)
    (hstep : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      σ i bools bits (t + 1) = evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i bools bits t)).b
          (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i bools bits t)).v
          (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      (src i bools bits).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i bools bits t)).b
            (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i bools bits t)).v
            (d.vpos k) w) o.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src (fun _ _ bits => bits) (fun _ _ _ => []) :=
  machine_traceL_of_stream d dom inits src ok hbody hinit
    (fun i bools bits => ⟨σ i bools bits, h0 i bools bits, hstep i bools bits, hres i bools bits⟩)
    hr entry closes

end Tools.ShippingMachineLoopL
