/-
  Hardware Type System

  Defines the concrete types that can be represented in synthesizable hardware.
  This is a subset of Lean types that excludes higher-order functions, dependent types, etc.
-/

import Sparkle.Data.BitPack

namespace Sparkle.IR.Type

open Sparkle.Data.BitPack

/--
  A hardware dimension that is either concrete or depends on retained module
  parameters. This is deliberately a small, closed language: the compiler must
  reject Lean computations it cannot preserve instead of evaluating them only
  at a parameter's default value.
-/
inductive DimExpr where
  | literal (value : Nat)
  | parameter (name : String)
  | add (lhs rhs : DimExpr)
  | sub (lhs rhs : DimExpr)
  | mul (lhs rhs : DimExpr)
  | div (lhs rhs : DimExpr)
  | mod (lhs rhs : DimExpr)
  | pow (base exponent : DimExpr)
  | clog2 (value : DimExpr)
  | min (lhs rhs : DimExpr)
  | max (lhs rhs : DimExpr)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace DimExpr

def isConcrete : DimExpr → Bool
  | .literal _ => true
  | _ => false

def toNat? : DimExpr → Option Nat
  | .literal value => some value
  | _ => none

def mkAdd : DimExpr → DimExpr → DimExpr
  | .literal 0, rhs => rhs
  | lhs, .literal 0 => lhs
  | .literal lhs, .literal rhs => .literal (lhs + rhs)
  | lhs, rhs => .add lhs rhs

def mkSub : DimExpr → DimExpr → DimExpr
  | lhs, .literal 0 => lhs
  | .literal lhs, .literal rhs => .literal (lhs - rhs)
  | lhs, rhs => .sub lhs rhs

def mkMul : DimExpr → DimExpr → DimExpr
  | .literal 0, _ => .literal 0
  | _, .literal 0 => .literal 0
  | .literal 1, rhs => rhs
  | lhs, .literal 1 => lhs
  | .literal lhs, .literal rhs => .literal (lhs * rhs)
  | lhs, rhs => .mul lhs rhs

/-- Evaluate a retained hardware dimension for one concrete parameter
    configuration. Arithmetic that would make a hardware dimension
    ill-defined fails closed instead of inheriting `Nat`'s saturating/default
    behavior. In particular, subtraction may not underflow, division and
    modulo require a non-zero divisor, and `clog2 0` is rejected. -/
partial def evaluate (bindings : List (String × Nat)) : DimExpr → Except String Nat
  | .literal value => return value
  | .parameter name =>
    match bindings.lookup name with
    | some value => return value
    | none => throw s!"missing specialization binding for parameter '{name}'"
  | .add lhs rhs => return (← evaluate bindings lhs) + (← evaluate bindings rhs)
  | .sub lhs rhs => do
    let lhsValue ← evaluate bindings lhs
    let rhsValue ← evaluate bindings rhs
    if lhsValue < rhsValue then
      throw s!"hardware dimension subtraction underflow: {lhsValue} - {rhsValue}"
    return lhsValue - rhsValue
  | .mul lhs rhs => return (← evaluate bindings lhs) * (← evaluate bindings rhs)
  | .div lhs rhs => do
    let lhsValue ← evaluate bindings lhs
    let rhsValue ← evaluate bindings rhs
    if rhsValue == 0 then throw "hardware dimension division by zero"
    return lhsValue / rhsValue
  | .mod lhs rhs => do
    let lhsValue ← evaluate bindings lhs
    let rhsValue ← evaluate bindings rhs
    if rhsValue == 0 then throw "hardware dimension modulo by zero"
    return lhsValue % rhsValue
  | .pow base exponent => return (← evaluate bindings base) ^ (← evaluate bindings exponent)
  | .clog2 value => do
    let value ← evaluate bindings value
    if value == 0 then throw "clog2 is undefined for hardware dimension 0"
    if value == 1 then return 0
    return Nat.log2 (value - 1) + 1
  | .min lhs rhs => return Nat.min (← evaluate bindings lhs) (← evaluate bindings rhs)
  | .max lhs rhs => return Nat.max (← evaluate bindings lhs) (← evaluate bindings rhs)

partial def toString : DimExpr → String
  | .literal value => s!"{value}"
  | .parameter name => name
  | .add lhs rhs => s!"({lhs.toString} + {rhs.toString})"
  | .sub lhs rhs => s!"({lhs.toString} - {rhs.toString})"
  | .mul lhs rhs => s!"({lhs.toString} * {rhs.toString})"
  | .div lhs rhs => s!"({lhs.toString} / {rhs.toString})"
  | .mod lhs rhs => s!"({lhs.toString} % {rhs.toString})"
  | .pow base exponent => s!"({base.toString} ** {exponent.toString})"
  | .clog2 value => s!"clog2({value.toString})"
  | .min lhs rhs => s!"min({lhs.toString}, {rhs.toString})"
  | .max lhs rhs => s!"max({lhs.toString}, {rhs.toString})"

instance : ToString DimExpr where
  toString := DimExpr.toString

end DimExpr

/--
  Hardware Type: The subset of types that can be synthesized to hardware.

  - Bit: Single bit (wire)
  - BitVector: n-bit vector
  - Array: Fixed-size array (for memories/ROMs)
-/
inductive HWType where
  | bit : HWType
  | bitVector (width : Nat) : HWType
  | bitVectorDim (width : DimExpr) : HWType
  | array (size : Nat) (elemType : HWType) : HWType
  deriving Repr, BEq, DecidableEq, Inhabited


namespace HWType

/-- Get the bit width of a hardware type -/
def bitWidth : HWType → Nat
  | bit => 1
  | bitVector w => w
  | bitVectorDim (.literal w) => w
  | bitVectorDim width => panic! s!"symbolic hardware width {width} is not concrete"
  | array size elemType => size * elemType.bitWidth

/-- Checked concrete width for consumers that do not support retained dimensions. -/
def bitWidth? : HWType → Option Nat
  | .bit => some 1
  | .bitVector width => some width
  | .bitVectorDim (.literal width) => some width
  | .bitVectorDim _ => none
  | .array size elemType => elemType.bitWidth?.map (size * ·)

/-- Return the packed width without discarding symbolic dimensions. -/
def bitWidthDim : HWType → DimExpr
  | bit => .literal 1
  | bitVector width => .literal width
  | bitVectorDim width => width
  | array size elemType => DimExpr.mkMul (.literal size) elemType.bitWidthDim

/-- Check if a hardware type is a single bit -/
def isBit : HWType → Bool
  | bit => true
  | _ => false

/-- Check if a hardware type is a bit vector -/
def isBitVector : HWType → Bool
  | bitVector _ => true
  | bitVectorDim _ => true
  | _ => false

/-- Check if a hardware type is an array -/
def isArray : HWType → Bool
  | array _ _ => true
  | _ => false

/-- Convert hardware type to a human-readable string -/
def toString : HWType → String
  | bit => "Bit"
  | bitVector 1 => "Bit"
  | bitVector w => s!"BitVec{w}"
  | bitVectorDim width => s!"BitVec({width})"
  | array size elemType => s!"Array[{size}]({elemType.toString})"

instance : ToString HWType where
  toString := HWType.toString

end HWType

/-- Convert a Lean type with BitPack instance to HWType -/
def toHWType (α : Type u) (n : Nat) [BitPack α n] : HWType :=
  if n == 1 then
    .bit
  else
    .bitVector n

/-- Helper to infer HWType from a Nat width -/
def hwTypeFromWidth (w : Nat) : HWType :=
  if w == 1 then .bit else .bitVector w

/-- Construct a packed hardware type while preserving a symbolic dimension. -/
def hwTypeFromDim (width : DimExpr) : HWType :=
  match width with
  | .literal value => hwTypeFromWidth value
  | _ => .bitVectorDim width

/-- 8-bit hardware type -/
def byte : HWType := .bitVector 8

/-- 16-bit hardware type -/
def word16 : HWType := .bitVector 16

/-- 32-bit hardware type -/
def word32 : HWType := .bitVector 32

/-- 64-bit hardware type -/
def word64 : HWType := .bitVector 64

/-- Boolean hardware type -/
def hwBool : HWType := .bit

/-- Reset kind: synchronous or asynchronous.

    Lives here (not in `Sparkle.Core.Domain`) so the IR layer can
    reference it without importing `Core/Domain.lean` (which would
    create a layering inversion).  `Sparkle.Core.Domain` re-exports
    this so user code keeps seeing `Sparkle.Core.Domain.ResetKind`. -/
inductive ResetKind where
  | synchronous  : ResetKind  -- Reset is sampled on the clock edge.
  | asynchronous : ResetKind  -- Reset takes effect the moment it asserts.
  deriving Repr, BEq, DecidableEq, Inhabited

end Sparkle.IR.Type
