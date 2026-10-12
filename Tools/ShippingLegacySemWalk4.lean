import Tools.ShippingLegacySemWalk3

/-! # Handler walks, 4: `handleTupleProjections`, `handleCircuitMonad`; all nine facts

Same method. **Expected elaborated shapes** (not observed):

* `Rec.handleTupleProjections tr e name args hint named` =
  `if (name == ``Signal.fst || name == ``Signal.snd || name == ``bundle2 ||
       name == ``Signal.map) = true then ARMS else pure none`
  (from `let isTupleName := …; unless isTupleName do return none`; the `let`
  is inlined by `dsimp only`).
* `Rec.handleCircuitMonad tr e name args hint named` =
  `if (name == ``Bind.bind || name == ``Pure.pure) = true then ARM₁ (falls
   through in three sub-cases) else if (name == ``Prod.mk && …) = true then
   ARM₂ else if ((name == ``Prod.fst || name == ``Prod.snd) && …) = true then
   ARM₃ else pure none`.

`plainChain_of_names`: with the five facts of walks 1 and 2 and the two of
walk 3, ALL NINE handler facts of `PlainChain` hold for a head that fails the
name tests (`PlainName`, `NotBitVecOp`, `PlainName2`). What is left of
`bodyReachesInline_of_walk` is then `hpre`, `hchain`, `hunfold`. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- The name tests of walks 3 and 4 (beside `NotBitVecOp`), failing. -/
structure PlainName2 (name : Name) : Prop where
  vecGet : (name == ``Sparkle.Core.Vector.HWVector.get) = false
  memoize : name.toString.endsWith ".memoize" = false
  notLoop : name.toString.endsWith ".loop" = false
  sigFst : (name == ``Sparkle.Core.Signal.Signal.fst) = false
  sigSnd : (name == ``Sparkle.Core.Signal.Signal.snd) = false
  bundle2 : (name == ``Sparkle.Core.Signal.bundle2) = false
  sigMap : (name == ``Sparkle.Core.Signal.Signal.map) = false
  notBind : (name == ``Bind.bind) = false
  notPure : (name == ``Pure.pure) = false
  prodMk : (name == ``Prod.mk) = false
  prodFst : (name == ``Prod.fst) = false
  prodSnd : (name == ``Prod.snd) = false

/-- **`handleTupleProjections` on a head that is none of its four names.** -/
theorem handleTupleProjections_none {tr : TranslateFn} {e : Lean.Expr} {name : Name}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s : CircuitState}
    (h1 : (name == ``Sparkle.Core.Signal.Signal.fst) = false)
    (h2 : (name == ``Sparkle.Core.Signal.Signal.snd) = false)
    (h3 : (name == ``Sparkle.Core.Signal.bundle2) = false)
    (h4 : (name == ``Sparkle.Core.Signal.Signal.map) = false) :
    Ensures (Rec.handleTupleProjections tr e name args hint named) ctx s
      (fun r t => r = none ∧ t = s) := by
  unfold Rec.handleTupleProjections
  try dsimp only
  first
    | (simp only [h1, h2, h3, h4,
        Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.or_self,
        Bool.not_false, Bool.false_eq_true, eq_self, if_false, if_true]
       exact Ensures.pure ⟨rfl, rfl⟩)
    | plain_none

/-- **`handleCircuitMonad` on a head that is none of its five names.** -/
theorem handleCircuitMonad_none {tr : TranslateFn} {e : Lean.Expr} {name : Name}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s : CircuitState}
    (h1 : (name == ``Bind.bind) = false) (h2 : (name == ``Pure.pure) = false)
    (h3 : (name == ``Prod.mk) = false) (h4 : (name == ``Prod.fst) = false)
    (h5 : (name == ``Prod.snd) = false) :
    Ensures (Rec.handleCircuitMonad tr e name args hint named) ctx s
      (fun r t => r = none ∧ t = s) := by
  unfold Rec.handleCircuitMonad
  try dsimp only
  first
    | (simp only [h1, h2, h3, h4, h5,
        Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.or_self,
        Bool.not_false, Bool.false_eq_true, eq_self, if_false, if_true]
       exact Ensures.pure ⟨rfl, rfl⟩)
    | plain_none

/-- **All nine handler facts** for a head that fails every name test of the
chain before `handleDefinitionUnfold`. -/
theorem plainChain_of_names {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {name : Name} {args : Array Lean.Expr} (hn : PlainName name) (hb : NotBitVecOp name)
    (hm : PlainName2 name) : PlainChain rec ctx e name args :=
  plainChain_partial hn
    (fun hint named => returnsNone_of_ensures fun s =>
      handleCircuitMonad_none (s := s) hm.notBind hm.notPure hm.prodMk hm.prodFst hm.prodSnd)
    (fun hint named => returnsNone_of_ensures fun s =>
      handleTupleProjections_none (s := s) hm.sigFst hm.sigSnd hm.bundle2 hm.sigMap)
    (fun hint named => returnsNone_of_ensures fun s => handleBitVecOps_none (s := s) hb)
    (fun hint named => returnsNone_of_ensures fun s =>
      handleLoop_none (s := s) hm.vecGet hm.memoize hm.notLoop)

end Tools.ShippingLegacySem
