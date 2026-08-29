/-
  Sparkle IR — mathematical semantics (proof-facing).

  A TOTAL evaluator for the scalar fragment of `Expr`, intended as the
  denotation that certified-roundtrip theorems are stated against:

      ⟦ lower (emit x) ⟧ = ⟦ x ⟧

  Design notes, in order of importance:

  * TOTAL, not `partial`.  A `partial def` produces no unfolding
    equations, so nothing can be proven about it — this is why the
    shipping pipeline (73 `partial def`s across Parser/Lower/Verilog/
    Optimize) cannot be the direct subject of theorems.  The verified
    core is written total; the shipping code is tied to it by
    cross-checking tests (verified-core / validated-shell split).

  * Values are `Nat` with EXPLICIT masking to the context width, not
    `BitVec n`.  The IR is width-annotated at consts/slices only, so a
    width-indexed value type would force every theorem through `Σ n,
    BitVec n` casts.  `Nat`+mask mirrors what both backends actually
    compute (CSim's `& mask` discipline, Verilog's context truncation)
    and keeps lemmas cast-free.  Two-state only: X/Z are outside the
    model, exactly as in CSim.

  * `Env` maps names to values, `WEnv` to widths.  Refs are looked up
    unmasked — well-formedness (every stored value already masked) is a
    hypothesis of the preservation theorems, not re-enforced per read.

  * The fragment: const/ref, the bitwise/arith/compare/shift/mux ops,
    concat, and constant-bound slice.  `sliceDim` (symbolic widths) and
    `index` (memories) return `none`; they enter the semantics when the
    proof reaches memories.
-/

import Sparkle.IR.AST

namespace Sparkle.IR.Semantics

open Sparkle.IR.AST

abbrev Env := String → Nat
abbrev WEnv := String → Nat

/-- Truncate to `w` bits. -/
def mask (w : Nat) (v : Nat) : Nat := v % (2 ^ w)

/-- Two's-complement interpretation of a masked value, for signed ops. -/
def toSigned (w : Nat) (v : Nat) : Int :=
  if v < 2 ^ (w - 1) then (v : Int) else (v : Int) - (2 ^ w : Nat)

/-- Width of an expression under a width environment (the proof-facing
    twin of the backends' `inferExprWidth`; binary ops take the MAX of
    their operands, matching hardware and the fixed CSim rule). -/
def widthOf (we : WEnv) : Expr → Nat
  | .const _ w => w
  | .ref n => we n
  | .op .mux args =>
    match args with
    | [_, t, _] => widthOf we t
    | _ => 0
  | .op .eq _ | .op .lt_u _ | .op .lt_s _ | .op .le_u _ | .op .le_s _
  | .op .gt_u _ | .op .gt_s _ | .op .ge_u _ | .op .ge_s _ => 1
  | .op .not args =>
    match args with
    | [a] => widthOf we a
    | _ => 0
  | .op _ args =>
    match args with
    | [a, b] => max (widthOf we a) (widthOf we b)
    | [a] => widthOf we a
    | _ => 0
  | .concat args => go args
  | .slice _ hi lo => hi - lo + 1
  | .sliceDim _ _ _ => 0
  | .index _ _ => 0
where
  go : List Expr → Nat
    | [] => 0
    | a :: rest => widthOf we a + go rest

/-- Evaluate one operator over already-evaluated, already-masked operand
    values.  `w` is the result's context width. -/
def evalOp (we : WEnv) (operator : Operator) (args : List Expr)
    (vals : List Nat) (w : Nat) : Option Nat :=
  match operator, args, vals with
  | .and, _, [a, b] => some (mask w (a &&& b))
  | .or,  _, [a, b] => some (mask w (a ||| b))
  | .xor, _, [a, b] => some (mask w (a ^^^ b))
  | .not, [x], [a] =>
    let wx := widthOf we x
    some (mask wx (a ^^^ (2 ^ wx - 1)))
  | .add, _, [a, b] => some (mask w (a + b))
  | .sub, _, [a, b] => some (mask w (a + (2 ^ w - mask w b)))
  | .mul, _, [a, b] => some (mask w (a * b))
  | .eq,  _, [a, b] => some (if a = b then 1 else 0)
  | .lt_u, _, [a, b] => some (if a < b then 1 else 0)
  | .le_u, _, [a, b] => some (if a ≤ b then 1 else 0)
  | .gt_u, _, [a, b] => some (if b < a then 1 else 0)
  | .ge_u, _, [a, b] => some (if b ≤ a then 1 else 0)
  | .lt_s, [x, y], [a, b] =>
    let wc := max (widthOf we x) (widthOf we y)
    some (if toSigned wc a < toSigned wc b then 1 else 0)
  | .le_s, [x, y], [a, b] =>
    let wc := max (widthOf we x) (widthOf we y)
    some (if toSigned wc a ≤ toSigned wc b then 1 else 0)
  | .gt_s, [x, y], [a, b] =>
    let wc := max (widthOf we x) (widthOf we y)
    some (if toSigned wc b < toSigned wc a then 1 else 0)
  | .ge_s, [x, y], [a, b] =>
    let wc := max (widthOf we x) (widthOf we y)
    some (if toSigned wc b ≤ toSigned wc a then 1 else 0)
  | .shl, _, [a, b] => some (mask w (a <<< b))
  | .shr, _, [a, b] => some (a >>> b)
  | .asr, [x, _], [a, b] =>
    let wx := widthOf we x
    let s := toSigned wx a
    some (mask wx (Int.toNat ((s >>> b) % (2 ^ wx : Nat))))
  | .mux, _, [c, t, f] => some (if c ≠ 0 then t else f)
  | .neg, _, [a] => some (mask w (2 ^ w - mask w a))
  | _, _, _ => none

mutual
/-- Total evaluator for the scalar fragment.  `none` = outside the
    fragment (symbolic widths, memory reads) or malformed arity. -/
def evalExpr (we : WEnv) (env : Env) : Expr → Option Nat
  | .const v w =>
    -- Two's-complement encode negatives into w bits, like the emitters.
    some (mask w (Int.toNat (((v % (2 ^ w : Nat)) + (2 ^ w : Nat)) % (2 ^ w : Nat))))
  | .ref n => some (env n)
  | .op operator args => do
    let vals ← evalList we env args
    evalOp we operator args vals (widthOf we (.op operator args))
  | .concat args => do
    let vals ← evalList we env args
    -- MSB-first: the FIRST element lands in the high bits.
    some (go args vals)
  | .slice e hi lo => do
    let v ← evalExpr we env e
    some (mask (hi - lo + 1) (v >>> lo))
  | .sliceDim _ _ _ => none
  | .index _ _ => none
where
  go : List Expr → List Nat → Nat
    | a :: as, v :: vs =>
      let restW := (as.zip vs).foldl (fun acc (p : Expr × Nat) => acc + widthOf we p.1) 0
      (mask (widthOf we a) v) <<< restW ||| go as vs
    | _, _ => 0

def evalList (we : WEnv) (env : Env) : List Expr → Option (List Nat)
  | [] => some []
  | a :: rest => do
    let v ← evalExpr we env a
    let vs ← evalList we env rest
    some (v :: vs)
end

/- Behavioral pins: the semantics agrees with hardware intuition on
   small cases (evaluated at compile time). -/
section Guards
private def we0 : WEnv := fun _ => 8
private def env0 : Env := fun n => if n == "a" then 0xA5 else 0x3C
#guard evalExpr we0 env0 (.op .and [.ref "a", .ref "b"]) = some 0x24
#guard evalExpr we0 env0 (.op .add [.ref "a", .ref "b"]) = some 0xE1
-- 8-bit overflow wraps: 0xA5 + 0xA5 = 0x14A → 0x4A
#guard evalExpr we0 env0 (.op .add [.ref "a", .ref "a"]) = some 0x4A
-- NOT is width-bounded (the emitter bug class, at the semantics level)
#guard evalExpr we0 env0 (.op .not [.ref "a"]) = some 0x5A
-- concat is MSB-first; slice picks the middle byte back out
#guard evalExpr we0 env0 (.concat [.ref "a", .ref "b"]) = some 0xA53C
#guard evalExpr we0 env0 (.slice (.concat [.ref "a", .ref "b"]) 15 8) = some 0xA5
-- mux takes the else arm on 0
#guard evalExpr we0 env0 (.op .mux [.const 0 1, .ref "a", .ref "b"]) = some 0x3C
end Guards

end Sparkle.IR.Semantics
