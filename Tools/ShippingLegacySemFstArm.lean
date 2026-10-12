import Tools.ShippingLegacySemFst

/-! # The accepting arms of `Rec.handleTupleProjections`: program text and the statements to prove

STATEMENTS ONLY — nothing is proved in this file. It fixes, as type-checked
definitions, the pieces the walk of the `Signal.fst` / `Signal.snd` arms
decomposes into (`docs/parallel/G2-legacy-round23.md`, §item 3), so that the
three decisions named there can be taken against exact statements. Not
imported by any test.

**Program text** (`Sparkle/Compiler/Elab.lean`, `Rec.handleTupleProjections`,
5647–5757): after the name test (5654–5660; `unless isTupleName do return
none`), for `name = Signal.fst`, `args.size ≥ 1` (5662–5684) the arm is
`fstArmProg` below without its `trace`; for `name = Signal.snd` (5687–5700)
`sndArmProg`. They are transcriptions, written so that `FstArmIs` /
`SndArmIs` can be proved by inverting the handler step by step.

**The statements**

* `FstArmIs`, `SndArmIs` — a successful run of the handler on the name is a
  successful run of the transcription on the last argument (the `trace` and
  the name tests removed). Class: program walk (provable with
  `returns_trace_then` and the `Returns` inversions; not attempted blind).
* `WireWidthReads ctx s w n` — every successful run of
  `CompilerM.getWireWidth w` from `s` returns `n` and leaves `s`. THE WORLD
  PREMISE of decision 3: `getWireWidth` (210–233) reads the `IO.Ref`
  `sparkleWireWidthCache` first and falls back to the builder state's ports
  only on a miss. `Returns` says nothing about the reference's contents, so
  the slice bounds (`totalWidth := min wireWidth typeTotal`, 5680–5682) are
  not determined by the run. It holds when the cache agrees with the builder
  state (the cache is written by `makeWire` / `addInput` / `addOutput` only),
  an invariant of the WORLD that no statement of this development carries.
* `ArgRunsBody tr ctx e` — the cacheable argument call is a run of the body
  (decision 2): `ShimAt … e "s" false false` of
  `Tools/ShippingLegacySemDispatch.lean`, restated for reference. False of a
  run that hits a stale entry of the expression cache.
-/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Sparkle.IR.Type (HWType)
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- The `Signal.fst` arm (5664–5684), transcribed without its `trace`. -/
def fstArmProg (tr : TranslateFn) (e s : Lean.Expr) (hint : String) (named : Bool) :
    CompilerM (Option String) := do
  let wireS ← tr s "s" false false
  let wireWidth ← CompilerM.getWireWidth wireS
  let exprType ← cachedInferType e
  let hwType ← inferHWTypeFromSignal exprType
  let resWire ← CompilerM.makeWire hint hwType named
  let width : Nat := match hwType with
    | HWType.bitVector w => w
    | HWType.bit => 1
    | _ => 8
  let sType ← cachedInferType s
  let sHWType ← inferHWTypeFromSignal sType
  let typeTotal : Nat := match sHWType with
    | HWType.bitVector w => w
    | HWType.bit => 1
    | _ => 8
  let totalWidth := min wireWidth typeTotal
  let lo : Nat := if totalWidth ≥ width then totalWidth - width else 0
  let hi : Nat := if totalWidth ≥ 1 then totalWidth - 1 else 0
  CompilerM.emitAssign resWire
    (Sparkle.IR.AST.Expr.slice (Sparkle.IR.AST.Expr.ref wireS) hi lo)
  return some resWire

/-- The `Signal.snd` arm (5689–5700), transcribed without its `trace`. -/
def sndArmProg (tr : TranslateFn) (e s : Lean.Expr) (hint : String) (named : Bool) :
    CompilerM (Option String) := do
  let wireS ← tr s "s" false false
  let wireWidth ← CompilerM.getWireWidth wireS
  let exprType ← cachedInferType e
  let hwType ← inferHWTypeFromSignal exprType
  let resWire ← CompilerM.makeWire hint hwType named
  let width : Nat := match hwType with
    | HWType.bitVector w => w
    | HWType.bit => 1
    | _ => 8
  let actualWidth := min width wireWidth
  let hi : Nat := if actualWidth ≥ 1 then actualWidth - 1 else 0
  CompilerM.emitAssign resWire
    (Sparkle.IR.AST.Expr.slice (Sparkle.IR.AST.Expr.ref wireS) hi 0)
  return some resWire

/-- STATEMENT (not proved): the handler on `Signal.fst` is its accepting
arm. -/
def FstArmIs : Prop :=
  ∀ (tr : TranslateFn) (e : Lean.Expr) (args : Array Lean.Expr) (hint : String)
    (named : Bool) (ctx : CompilerState) (s t : CircuitState) (r : Option String),
    1 ≤ args.size →
    Returns (Rec.handleTupleProjections tr e ``Sparkle.Core.Signal.Signal.fst args hint named)
      ctx s r t →
    Returns (fstArmProg tr e args[args.size - 1]! hint named) ctx s r t

/-- STATEMENT (not proved): the handler on `Signal.snd` is its accepting
arm. -/
def SndArmIs : Prop :=
  ∀ (tr : TranslateFn) (e : Lean.Expr) (args : Array Lean.Expr) (hint : String)
    (named : Bool) (ctx : CompilerState) (s t : CircuitState) (r : Option String),
    1 ≤ args.size →
    Returns (Rec.handleTupleProjections tr e ``Sparkle.Core.Signal.Signal.snd args hint named)
      ctx s r t →
    Returns (sndArmProg tr e args[args.size - 1]! hint named) ctx s r t

/-- THE WORLD PREMISE of the slice bounds (decision 3): the width read for
the wire `w` from the state `s` is `n`. -/
def WireWidthReads (ctx : CompilerState) (s : CircuitState) (w : String) (n : Nat) : Prop :=
  ∀ (k : Nat) (t : CircuitState),
    Returns (CompilerM.getWireWidth w) ctx s k t → k = n ∧ t = s

/-- THE CACHE PREMISE of the argument call (decision 2): a successful run of
the shim on the argument, at the arm's flags, is a run of the body. -/
def ArgRunsBody (tr : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) : Prop :=
  ∀ (s t : CircuitState) (w : String),
    Returns (Rec.translateExprToWireCached tr e "s" false false) ctx s w t →
    Returns (Rec.translateExprToWireImpl (fun e h t n => tr e h t n) e "s" false false)
      ctx s w t

end Tools.ShippingLegacySem
