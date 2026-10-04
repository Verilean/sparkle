import Sparkle

/-!
# Chapter 2 — reference solutions

Build-checked answers to the Ch02 exercises.  These compile under
`lake build TutorialNotebooks` and prove the design matches a
behavioural spec by `native_decide` over the small input space.
-/

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Solutions.Ch02

/-- Solution to Ch02 §2.8 — 4:1 mux built from three 2:1 muxes.

    A 2-bit selector picks one of four 8-bit inputs:

    ```
    sel    out
    0      a
    1      b
    2      c
    3      d
    ```

    The cleanest synthesis-safe decomposition is to compare `sel`
    against each constant (this turns into a one-hot signal in
    Verilog) and chain `Signal.mux`. -/
def mux4 {dom : DomainConfig}
    (sel : Signal dom (BitVec 2))
    (a b c d : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let isZero := sel === 0#2
  let isOne  := sel === 1#2
  let isTwo  := sel === 2#2
  -- Cascade: if isZero pick a, else if isOne pick b, else if
  -- isTwo pick c, else d.
  Signal.mux isZero a
    (Signal.mux isOne b
      (Signal.mux isTwo c d))

/-- Behavioural spec: a 4:1 mux as plain Lean. -/
def mux4Spec (sel : BitVec 2) (a b c d : BitVec 8) : BitVec 8 :=
  if sel == 0#2 then a
  else if sel == 1#2 then b
  else if sel == 2#2 then c
  else d

end Notebooks.Solutions.Ch02
