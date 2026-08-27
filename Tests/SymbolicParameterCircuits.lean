import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

def symbolicXor {dom : DomainConfig} {W : Nat}
    (lhs rhs : Signal dom (BitVec W)) : Signal dom (BitVec W) :=
  lhs ^^^ rhs

def symbolicConcat {dom : DomainConfig} {HI LO : Nat}
    (hi : Signal dom (BitVec HI))
    (lo : Signal dom (BitVec LO)) : Signal dom (BitVec (HI + LO)) :=
  hi ++ lo

def symbolicSliceLow {dom : DomainConfig} {W : Nat}
    (x : Signal dom (BitVec (W + 1))) : Signal dom (BitVec W) :=
  x.map (BitVec.extractLsb' 0 W ·)

def symbolicZeroExtend {dom : DomainConfig} {W : Nat}
    (x : Signal dom (BitVec W)) : Signal dom (BitVec (W + 1)) :=
  x.map (·.zeroExtend (W + 1))
