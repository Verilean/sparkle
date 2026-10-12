import Tools.ShippingLegacySemWalk1

/-! # Handler walks, 2: `handleMux`, `handleMemory`; the facts assembled

Same method as `Tools/ShippingLegacySemWalk1.lean`.

**Expected elaborated shapes** (not observed):

* `Rec.handleMux tr e name args hint named` =
  `if (name.toString.endsWith ".lutMuxTree" && decide (args.size ≥ 5)) = true
   then ARM₁ (which itself falls through to the rest when the table is empty)
   else if (name.toString.endsWith ".mux" && decide (args.size ≥ 3)) = true
   then ARM₂ else pure none`.
* `Rec.handleMemory tr e name args hint named` =
  `if (name.toString.endsWith ".memory" && !name.toString.endsWith ".memoryComboRead"
        && decide (args.size ≥ 4)) = true then ARM₁
   else if (name.toString.endsWith ".memoryComboRead" && decide (args.size ≥ 4)) = true
   then ARM₂ else pure none`.

`plainChain_partial` then states what is left of `PlainChain` for a head
that fails the name tests walked so far: the four handlers not yet walked
(`handleCircuitMonad`, `handleTupleProjections`, `handleBitVecOps`,
`handleLoop`) stay hypotheses. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- **`handleMux` on a head whose name ends in neither `.lutMuxTree` nor
`.mux`.** -/
theorem handleMux_none {tr : TranslateFn} {e : Lean.Expr} {name : Name}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s : CircuitState}
    (hlut : name.toString.endsWith ".lutMuxTree" = false)
    (hmux : name.toString.endsWith ".mux" = false) :
    Ensures (Rec.handleMux tr e name args hint named) ctx s
      (fun r t => r = none ∧ t = s) := by
  unfold Rec.handleMux
  try dsimp only
  plain_none

/-- **`handleMemory` on a head whose name ends in neither `.memory` nor
`.memoryComboRead`.** -/
theorem handleMemory_none {tr : TranslateFn} {e : Lean.Expr} {name : Name}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s : CircuitState}
    (hmem : name.toString.endsWith ".memory" = false)
    (hcombo : name.toString.endsWith ".memoryComboRead" = false) :
    Ensures (Rec.handleMemory tr e name args hint named) ctx s
      (fun r t => r = none ∧ t = s) := by
  unfold Rec.handleMemory
  try dsimp only
  plain_none

/-- The name tests of the five handlers walked so far, failing. -/
structure PlainName (name : Name) : Prop where
  notIte : (name == ``ite) = false
  notDite : (name == ``dite) = false
  decRec : (name == ``Decidable.rec) = false
  decCases : (name == ``Decidable.casesOn) = false
  ap : (name == ``Sparkle.Core.Signal.Signal.ap) = false
  register : name.toString.endsWith ".register" = false
  registerE : name.toString.endsWith ".registerWithEnable" = false
  lut : name.toString.endsWith ".lutMuxTree" = false
  mux : name.toString.endsWith ".mux" = false
  memory : name.toString.endsWith ".memory" = false
  combo : name.toString.endsWith ".memoryComboRead" = false

/-- **`PlainChain`, five of its nine facts discharged**: for a head that
fails the walked name tests, the facts of the four handlers not yet walked
are what is left. -/
theorem plainChain_partial {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {name : Name} {args : Array Lean.Expr} (hn : PlainName name)
    (circuit : ∀ (hint : String) (named : Bool),
      ReturnsNone (Rec.handleCircuitMonad (fun e h t n => rec e h t n) e name args hint named)
        ctx)
    (tuple : ∀ (hint : String) (named : Bool),
      ReturnsNone (Rec.handleTupleProjections (fun e h t n => rec e h t n) e name args hint
        named) ctx)
    (bitvec : ∀ (hint : String) (named : Bool),
      ReturnsNone (Rec.handleBitVecOps (fun e h t n => rec e h t n) e name args hint named) ctx)
    (loop : ∀ (hint : String) (named : Bool),
      ReturnsNone (Rec.handleLoop (fun e h t n => rec e h t n) e name args hint named) ctx) :
    PlainChain rec ctx e name args where
  errors := fun hint named s t u hr =>
    handleErrorPatterns_frame (s := s) hn.notIte hn.notDite hn.decRec hn.decCases u t hr
  circuit := circuit
  tuple := tuple
  applicative := fun hint named =>
    returnsNone_of_ensures fun s => handleApplicative_none (s := s) hn.ap
  bitvec := bitvec
  register := fun hint named =>
    returnsNone_of_ensures fun s => handleRegister_none (s := s) hn.register hn.registerE
  mux := fun hint named =>
    returnsNone_of_ensures fun s => handleMux_none (s := s) hn.lut hn.mux
  memory := fun hint named =>
    returnsNone_of_ensures fun s => handleMemory_none (s := s) hn.memory hn.combo
  loop := loop

end Tools.ShippingLegacySem
