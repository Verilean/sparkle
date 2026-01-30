/-
  Hardware Type System

  Defines the concrete types that can be represented in synthesizable hardware.
  This is a subset of Lean types that excludes higher-order functions, dependent types, etc.
-/

import Sparkle.Data.BitPack

namespace Sparkle.IR.Type

open Sparkle.Data.BitPack

/--
  Hardware Type: The subset of types that can be synthesized to hardware.

  - Bit: Single bit (wire)
  - BitVector: n-bit vector
  - Array: Fixed-size array (for memories/ROMs)
-/
inductive HWType where
  | bit : HWType
  | bitVector (width : Nat) : HWType
  | array (size : Nat) (elemType : HWType) : HWType
  deriving Repr, BEq, DecidableEq, Inhabited


namespace HWType

/-- Get the bit width of a hardware type -/
def bitWidth : HWType → Nat
  | bit => 1
  | bitVector w => w
  | array size elemType => size * elemType.bitWidth

/-- Check if a hardware type is a single bit -/
def isBit : HWType → Bool
  | bit => true
  | _ => false

/-- Check if a hardware type is a bit vector -/
def isBitVector : HWType → Bool
  | bitVector _ => true
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

end Sparkle.IR.Type
