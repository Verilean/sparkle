import Lean
import Sparkle.Core.Signal

/-! # Tuple-typed input ports on the machine route

A declaration input `ab : Signal dom (BitVec a × BitVec b)` (or a triple)
is ONE port holding the components packed, the first in the high bits — the
legacy lowering's interface (`_gen_ab[a+b-1:0]`, `ab.fst = _gen_ab[a+b-1:b]`),
and the mirror of a tuple RESULT (`machTupleKinds?`). The machine reader
reads the binder as that packed `BitVec (a + b)` port `x` and the body with
`ab` replaced by `unpackE x`:

  `bundle2 (x.map (BitVec.extractLsb' b a ·)) (x.map (BitVec.extractLsb' 0 b ·))`

(`bundle3` for a triple), so a projection `ab.fst` is a slice of the port by
`bundleIota`. The endpoint generator applies the declaration to the same
`unpackE` of its input signal: the theorem is about the port carrying the
packed tuple. -/
namespace Sparkle.Compiler.MachTupleIn
open Lean

/-- A `Nat` literal (raw or `OfNat.ofNat Nat n _`). -/
def natLit? : Lean.Expr → Option Nat
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const ``OfNat.ofNat _) (.const ``Nat _)) (.lit (.natVal n))) _ => some n
  | _ => none

/-- `OfNat.ofNat Nat n _`, as the elaborator writes a literal. -/
def natE (n : Nat) : Lean.Expr :=
  mkApp3 (.const ``OfNat.ofNat [.zero]) (.const ``Nat []) (.lit (.natVal n))
    (mkApp (.const ``instOfNatNat []) (.lit (.natVal n)))

/-- A positive literal width `BitVec w`. -/
def bitVecWidth? : Lean.Expr → Option Nat
  | .app (.const ``BitVec _) w => (natLit? w).bind fun n => if 0 < n then some n else none
  | _ => none

/-- The component widths of a pair or triple of `BitVec`s. -/
def tupleWidths? : Lean.Expr → Option (List Nat)
  | .app (.app (.const ``Prod _) a) (.app (.app (.const ``Prod _) b) c) => do
    pure [← bitVecWidth? a, ← bitVecWidth? b, ← bitVecWidth? c]
  | .app (.app (.const ``Prod _) a) b => do
    pure [← bitVecWidth? a, ← bitVecWidth? b]
  | _ => none

/-- A tuple-typed input `Signal dom (A × B [× C])`: its domain and component
widths. -/
def tupleInput? (ty : Lean.Expr) : Option (Lean.Expr × List Nat) :=
  match ty with
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) dom) t =>
    (tupleWidths? t).map fun ws => (dom, ws)
  | _ => none

/-- `x.map (fun v => BitVec.extractLsb' lo len v)` on a `BitVec n` signal. -/
def sliceMapE (dom x : Lean.Expr) (n lo len : Nat) : Lean.Expr :=
  let bv (k : Nat) := mkApp (.const ``BitVec []) (natE k)
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero]) dom (bv n) (bv len)
    (.lam `v (bv n)
      (mkApp4 (.const ``BitVec.extractLsb' []) (natE n) (natE lo) (natE len) (.bvar 0)) .default)
    x

/-- The tuple a packed port `x : Signal dom (BitVec (Σ ws))` holds, the first
component in the high bits. -/
def unpackE (dom : Lean.Expr) (ws : List Nat) (x : Lean.Expr) : Lean.Expr :=
  let n := ws.foldl (· + ·) 0
  let bv (k : Nat) := mkApp (.const ``BitVec []) (natE k)
  match ws with
  | [a, b] =>
    mkApp5 (.const ``Sparkle.Core.Signal.bundle2 [.zero]) dom (bv a) (bv b)
      (sliceMapE dom x n b a) (sliceMapE dom x n 0 b)
  | [a, b, c] =>
    mkApp7 (.const ``Sparkle.Core.Signal.bundle3 [.zero]) dom (bv a) (bv b) (bv c)
      (sliceMapE dom x n (b + c) a) (sliceMapE dom x n c b) (sliceMapE dom x n 0 c)
  | _ => x

/-- Under the declaration's binders: a binder of a tuple-typed input is read
as its packed port — its type the packed `Signal dom (BitVec n)`, the body
with the binder replaced by `unpackE` of itself. Other binders are kept. -/
partial def packTupleInputs : Lean.Expr → Lean.Expr
  | .lam nm ty b bi =>
    match tupleInput? ty with
    | some (dom, ws) =>
      let n := ws.foldl (· + ·) 0
      let ty' := mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom
        (mkApp (.const ``BitVec []) (natE n))
      -- keep the binder: `bvar 0` becomes `unpackE (bvar 0)`, the others unchanged
      let b' := (b.liftLooseBVars 1 1).instantiate1 (unpackE (dom.liftLooseBVars 0 1) ws (.bvar 0))
      .lam nm ty' (packTupleInputs b') bi
    | none => .lam nm ty (packTupleInputs b) bi
  | e => e

end Sparkle.Compiler.MachTupleIn
