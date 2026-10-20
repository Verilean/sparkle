import Tools.ShippingMachineAuto

/-! # A hand-written `Signal.loop` state machine

Many IP modules are written without `circuit do`: the state is a tuple of
registers, the body reads it through `Signal.fst`/`Signal.snd` and returns
`bundleAll! [Signal.register init₀ next₀, …]`, and the declaration is
`let s := Signal.loop body; result s`. That is the same machine as a
`circuit do`: a state stream starting at the reset values and advancing by
the next values. This file proves it once — for any loop body and any
encoding `σ` of its state into the machine's typed tuple — and gives the
trace theorem of the compiled module from the same data as
`machine_trace_of_data`, with three `rfl`s per declaration: the body's
value at cycle 0 is the reset tuple (`h0`), its value one cycle later is the
next-value terms on the state (`writes`), and the declaration is its result
on the loop (`hsrc`). -/
namespace Tools.ShippingMachineLoop
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge Tools.ShippingEntrySoundness

/-- A Bool as one bit, as the machine packs it (`toField`'s mux, evaluated). -/
def boolBits (b : Bool) : BitVec 1 := if b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0

/-- **The state stream of a `Signal.loop`.** If the body's value at cycle 0 is
(under `σ`) the reset value whatever signal it is given, and its value one
cycle later is a function `F` of the given signal's value at that cycle,
then the loop's state, under `σ`, starts at the reset value and advances by
`F`. (A loop body made of registers has exactly these two facts.) -/
theorem loop_stream {D : DomainConfig} {α : Type} [Inhabited α] {H : Type}
    (f : Signal D α → Signal D α) (σ : α → H) (init : H) (F : Nat → H → H)
    (h0 : ∀ l, σ ((f l).val 0) = init)
    (hs : ∀ l t, σ ((f l).val (t + 1)) = F t (σ (l.val t))) :
    σ ((Signal.loop f).val 0) = init ∧
    ∀ t, σ ((Signal.loop f).val (t + 1)) = F t (σ ((Signal.loop f).val t)) := by
  constructor
  · show σ (Signal.loopGo f 0) = init
    rw [Signal.loopGo_eq]
    exact h0 _
  · intro t
    show σ (Signal.loopGo f (t + 1)) = F t (σ (Signal.loopGo f t))
    rw [Signal.loopGo_eq, hs]
    show F t (σ (if t < t + 1 then Signal.loopGo f t else default)) = _
    rw [if_pos (by omega)]

set_option maxHeartbeats 2000000 in
/-- **Source to RTL for a `Signal.loop` state machine, from data.** The loop
body `f` (for every domain and inputs), the encoding `σ` of its state, the
result `res` of the declaration over a state signal: with the check `ok`,
the body equation, the reset check and the four `rfl`s, every module a run
of the real synthesis entry returns at the machine boundary shows the
declaration. -/
theorem machine_trace_of_loop {declName : Name} (d : MachineData) {ι : Type}
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
    MachineTrace declName d m dom src := by
  refine machine_trace_of_stream d dom inits src ok hbody hinit (fun _ _ bits => bits) ?_ hr
    entry closes
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
/-- **Source to RTL for a combinational declaration with `let`s, from data.**
A machine without slots: the state is a constant tuple `inits` (the empty
one), the next values leave it unchanged (`hnext`, a `rfl`), and the outputs
are the output terms on the inputs of the cycle (`hres`, a `rfl` against the
declaration itself). -/
theorem machine_trace_of_comb {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) (inits : HList (tys d.ss))
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
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).b (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).v (d.vpos j) w)
        d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      (src i bools bits).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).v (d.vpos k) w)
          o.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTrace declName d m dom src :=
  machine_trace_of_stream d dom inits src ok hbody hinit (fun _ _ bits => bits)
    (fun i bools bits => ⟨fun _ => inits, rfl, fun t => hnext i bools bits t, hres i bools bits⟩)
    hr entry closes

set_option maxHeartbeats 2000000 in
/-- **Source to RTL for a declaration of bare registers, from data.** The
registers (`Signal.register init x`, outside any loop) are the slots; their
values in the source form the state stream `σ` (given), whose three facts —
the reset values at cycle 0, the next values one cycle later, the outputs —
are each a `rfl` for a declaration (a register's value at `t + 1` is its
input's at `t`). -/
theorem machine_trace_of_regs {declName : Name} (d : MachineData) {ι : Type}
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
    MachineTrace declName d m dom src :=
  machine_trace_of_stream d dom inits src ok hbody hinit (fun _ _ bits => bits)
    (fun i bools bits => ⟨σ i bools bits, h0 i bools bits, hstep i bools bits, hres i bools bits⟩)
    hr entry closes

end Tools.ShippingMachineLoop
