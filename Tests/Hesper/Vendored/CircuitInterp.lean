/-
  Vendored interpreter for Hesper's Circuit DSL — Lean-side semantic
  evaluation of Hesper's `ScalarExp` (and a tractable subset of
  `Prim`).

  ## Provenance and PR plan

  Source repo:  https://github.com/Verilean/hesper
  Source files:
    - Hesper/Circuit/IR.lean    (ScalarExp, Prim, ReduceOp)
    - Hesper/CircuitV2/IR.lean  (CircuitV2 frontend; not yet used here)

  Hesper's `Circuit` IR is explicitly designed to be a pure inductive
  AST that can be inspected, hashed, rewritten — see the comment at
  the top of `Circuit/IR.lean`. What is **not** in upstream Hesper is
  a Lean-level **evaluator** for these ASTs (the existing lowerings
  emit WGSL / PTX and run on real GPUs). Without an evaluator, we
  cannot make a "Sparkle ≡ Hesper Circuit DSL" claim inside Lean.

  This file is the evaluator. The intention is to upstream it as a
  PR to Hesper so the whole community gets a reference semantics
  for Circuit IR. Until then, we vendor it here so the Sparkle ↔
  Hesper proofs can use it.

  ## Scope

  We evaluate the slice of `ScalarExp` that BitLinear / Q·K^T /
  softmax need:
    - `input`, `const`, arithmetic (add/sub/mul/div/neg)
    - transcendentals (`exp`, `rsqrt`, `tanh`, `gelu`, `silu`)
    - comparison (`lt`), `select`, `mod`, `idiv`, `toFloat`
    - `indexed` (gather)

  Warp-level primitives (`warpSum`, `warpBroadcast`,
  `warpShuffleXor`) are evaluated as if every lane sees the same
  values — i.e. the warp-collapsed semantics. This is correct for
  matmul/attention dot products where every lane in a warp computes
  the same partial sum (the warp-level reduction is a permutation-
  invariant sum).

  We use **`Float`** for the underlying numeric type, matching
  WGSL's `f32`.  Per `feedback_hesper_float_bridge.md`, we
  bridge to Sparkle's `BitVec`/`Int` via `native_decide` on
  fixtures, not via axiomatic `Float.toReal` lemmas.
-/

namespace Sparkle.Tests.Hesper.Vendored.CircuitInterp

/-- Vendored copy of Hesper's `ReduceOp` (Hesper.Circuit.IR). -/
inductive ReduceOp where
  | sum | max | sumOfSquares
  deriving Repr, BEq

/-- Vendored copy of Hesper's `ScalarExp` body for `pointwise` ops.

    Identical to upstream `Hesper.Circuit.ScalarExp` except for
    namespace. We keep the constructor names byte-identical so that
    a future upstream PR can drop this file in place of vendoring. -/
inductive ScalarExp where
  | input  (idx : Nat)
  | const  (v : Float)
  | laneIdx
  | indexed (bufIdx : Nat) (addr : ScalarExp)
  | warpSum (a : ScalarExp)
  | warpBroadcast (a : ScalarExp)
  | warpShuffleXor (a : ScalarExp) (mask : Nat)
  | add    (a b : ScalarExp)
  | sub    (a b : ScalarExp)
  | mul    (a b : ScalarExp)
  | div    (a b : ScalarExp)
  | neg    (a : ScalarExp)
  | rsqrt  (a : ScalarExp)
  | exp    (a : ScalarExp)
  | tanh   (a : ScalarExp)
  | gelu   (a : ScalarExp)
  | silu   (a : ScalarExp)
  | cos    (a : ScalarExp)
  | sin    (a : ScalarExp)
  | pow    (a b : ScalarExp)
  | lt     (a b : ScalarExp)
  | select (cond t f : ScalarExp)
  | mod    (a b : ScalarExp)
  | idiv   (a b : ScalarExp)
  | toFloat (a : ScalarExp)
  deriving Repr, Inhabited

/-! ## Environment

The evaluator takes:
  - a list of input tensors (one per `input i`),
  - the current lane index (for `laneIdx`),
  - a list of indexed buffers (for `indexed bufIdx addr`).

Tensors are flat `Array Float`s indexed by lane. -/

structure EvalEnv where
  /-- Inputs read at `laneIdx` by `ScalarExp.input i`. -/
  inputs    : Array (Array Float)
  /-- The current lane this evaluation is for. -/
  laneIdx   : Nat
  /-- Buffers read at arbitrary addresses by `ScalarExp.indexed`. -/
  buffers   : Array (Array Float)
  /-- Warp size for `warpSum` / `warpBroadcast` / `warpShuffleXor`. -/
  warpSize  : Nat := 32
  /-- All lane values for the warp (used by warp-level prims). -/
  warpLanes : Array (Array Float) := #[]

/-! ## Helpers

Floating-point primitives matching WGSL semantics where they
diverge from Lean stdlib: `rsqrt`, `gelu`, `silu`. -/

def f32_rsqrt (x : Float) : Float := 1.0 / x.sqrt

def f32_silu (x : Float) : Float := x / (1.0 + (-x).exp)

/-- GELU approximation: `0.5 * x * (1 + tanh(sqrt(2/π) * (x + 0.044715 x³)))`.
    Matches WGSL's typical implementation. -/
def f32_gelu (x : Float) : Float :=
  let c    : Float := 0.7978845608    -- sqrt(2/π)
  let inner := c * (x + 0.044715 * x * x * x)
  0.5 * x * (1.0 + inner.tanh)

/-! ## Evaluator

The evaluator is structural recursion on `ScalarExp`. For warp-level
primitives we evaluate the body once per lane in `env.warpLanes`,
then combine. -/

partial def ScalarExp.eval (env : EvalEnv) : ScalarExp → Float
  | .input i =>
    -- Read the i-th input at the current lane.
    (env.inputs.getD i #[]).getD env.laneIdx 0.0
  | .const v          => v
  | .laneIdx          => env.laneIdx.toFloat
  | .indexed bufIdx addr =>
    let a := ScalarExp.eval env addr
    -- WGSL semantics: cast to u32 via truncation.
    let idx := a.toUInt32.toNat
    (env.buffers.getD bufIdx #[]).getD idx 0.0
  | .warpSum a =>
    -- Warp-collapsed semantics: sum the value of `a` evaluated at
    -- every lane in `env.warpLanes`. If the warpLanes array is
    -- empty (single-lane evaluation), we just evaluate `a` once.
    if env.warpLanes.isEmpty then ScalarExp.eval env a
    else Id.run do
      let mut acc : Float := 0.0
      for lane in [:env.warpSize] do
        let env' := { env with laneIdx := lane, inputs := env.warpLanes }
        acc := acc + ScalarExp.eval env' a
      pure acc
  | .warpBroadcast a =>
    -- Lane-0 value, broadcast to all lanes.
    let inputs' := if env.warpLanes.isEmpty then env.inputs else env.warpLanes
    let env' := { env with laneIdx := 0, inputs := inputs' }
    ScalarExp.eval env' a
  | .warpShuffleXor a mask =>
    let target := env.laneIdx ^^^ mask
    let inputs' := if env.warpLanes.isEmpty then env.inputs else env.warpLanes
    let env' := { env with laneIdx := target, inputs := inputs' }
    ScalarExp.eval env' a
  | .add a b          => ScalarExp.eval env a + ScalarExp.eval env b
  | .sub a b          => ScalarExp.eval env a - ScalarExp.eval env b
  | .mul a b          => ScalarExp.eval env a * ScalarExp.eval env b
  | .div a b          => ScalarExp.eval env a / ScalarExp.eval env b
  | .neg a            => -(ScalarExp.eval env a)
  | .rsqrt a          => f32_rsqrt (ScalarExp.eval env a)
  | .exp a            => (ScalarExp.eval env a).exp
  | .tanh a           => (ScalarExp.eval env a).tanh
  | .gelu a           => f32_gelu (ScalarExp.eval env a)
  | .silu a           => f32_silu (ScalarExp.eval env a)
  | .cos a            => (ScalarExp.eval env a).cos
  | .sin a            => (ScalarExp.eval env a).sin
  | .pow a b          => (ScalarExp.eval env a).pow (ScalarExp.eval env b)
  | .lt a b           => if ScalarExp.eval env a < ScalarExp.eval env b then 1.0 else 0.0
  | .select c t f     =>
    if ScalarExp.eval env c != 0.0
    then ScalarExp.eval env t else ScalarExp.eval env f
  | .mod a b          =>
    let a' := ScalarExp.eval env a
    let b' := ScalarExp.eval env b
    -- WGSL `%` for f32 is `a - b * trunc(a/b)`.
    a' - b' * (a' / b').toUInt32.toFloat
  | .idiv a b         =>
    let a' := (ScalarExp.eval env a).toUInt32.toNat
    let b' := (ScalarExp.eval env b).toUInt32.toNat
    if b' = 0 then 0.0 else (a' / b').toFloat
  | .toFloat a        => ScalarExp.eval env a

/-! ## Pointwise op evaluation

Run a `ScalarExp` body across `n` lanes, given input tensors. -/

def evalPointwise (body : ScalarExp) (inputs : Array (Array Float))
    (n : Nat) (warpSize : Nat := 32) : Array Float := Id.run do
  let mut out : Array Float := Array.replicate n 0.0
  for i in [:n] do
    let env : EvalEnv := {
      inputs := inputs, laneIdx := i, buffers := #[],
      warpSize := warpSize, warpLanes := inputs
    }
    out := out.set! i (ScalarExp.eval env body)
  pure out

/-! ## Reduce evaluation

`Prim.reduce` over an `Array Float` along the last axis. -/

def evalReduce (op : ReduceOp) (input : Array Float) : Float :=
  match op with
  | .sum =>
    input.foldl (· + ·) 0.0
  | .max =>
    if input.isEmpty then 0.0
    else input.foldl Max.max input[0]!
  | .sumOfSquares =>
    input.foldl (fun acc x => acc + x * x) 0.0

/-! ## Sanity checks (small fixtures)

Each `native_decide` confirms the evaluator's wiring against
hand-computed Float values. -/

/-! Float equality is not `Decidable` (NaN ≠ NaN), but `Float.==` is
    a `Bool` and `BEq` lifts to `Array`. We use `... == ...` rather
    than `... = ...` so `native_decide` can chew the goals. -/

example :
    (ScalarExp.eval
      { inputs := #[#[1.0, 2.0, 3.0]], laneIdx := 1, buffers := #[] }
      (.input 0) == 2.0) = true := by
  native_decide

example :
    (ScalarExp.eval
      { inputs := #[#[1.0, 2.0]], laneIdx := 0, buffers := #[] }
      (.add (.input 0) (.const 5.0)) == 6.0) = true := by
  native_decide

example :
    (ScalarExp.eval
      { inputs := #[#[2.0, 3.0]], laneIdx := 1, buffers := #[] }
      (.mul (.input 0) (.input 0)) == 9.0) = true := by
  native_decide

example :
    (evalPointwise
      (.add (.input 0) (.input 1))
      #[#[1.0, 2.0, 3.0], #[10.0, 20.0, 30.0]]
      3
      == #[11.0, 22.0, 33.0]) = true := by
  native_decide

example :
    (evalReduce ReduceOp.sum #[1.0, 2.0, 3.0, 4.0] == 10.0) = true := by
  native_decide

example :
    (evalReduce ReduceOp.max #[1.0, 5.0, 3.0, 4.0] == 5.0) = true := by
  native_decide

end Sparkle.Tests.Hesper.Vendored.CircuitInterp
