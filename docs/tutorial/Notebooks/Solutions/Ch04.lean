import Sparkle

/-!
# Chapter 4 — reference solutions
-/

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Solutions.Ch04

declare_signal_state Alu5Out
  | result    : BitVec 4 := 0#4
  | flagsZero : Bool     := false

def OP_ADD : BitVec 3 := 0#3
def OP_SUB : BitVec 3 := 1#3
def OP_AND : BitVec 3 := 2#3
def OP_OR  : BitVec 3 := 3#3
def OP_SHL : BitVec 3 := 4#3

/-- Solution to Ch04 §4.8 — ALU with five ops including SHL. -/
def alu5 {dom : DomainConfig}
    (op : Signal dom (BitVec 3))
    (a b : Signal dom (BitVec 4)) : Signal dom Alu5Out :=
  let isAdd := op === OP_ADD
  let isSub := op === OP_SUB
  let isAnd := op === OP_AND
  let isOr  := op === OP_OR
  let result :=
    Signal.mux isAdd (a + b)
      (Signal.mux isSub (a - b)
        (Signal.mux isAnd (a &&& b)
          (Signal.mux isOr (a ||| b) (a <<< b))))
  let zero := result === 0#4
  Alu5Out.mk (result := result) (flagsZero := zero)

/-- Behavioural spec. -/
def alu5Spec (op : BitVec 3) (a b : BitVec 4) : (BitVec 4 × Bool) :=
  let r :=
    if op == OP_ADD then a + b
    else if op == OP_SUB then a - b
    else if op == OP_AND then a &&& b
    else if op == OP_OR  then a ||| b
    else a <<< b
  (r, r == 0#4)

end Notebooks.Solutions.Ch04
