
# Chapter 7 — Proofs: Equivalence Checking

Two designs are **equivalent** if, for every input, they
produce the same output.  In Sparkle this is just a
∀-statement on the next-state functions:

```text
theorem rippleAdder_eq_behavioralAdder :
    ∀ a b cin, rippleAdd4 a b cin = behavioralAdd4 a b cin := by
  decide
```

For small input spaces (a few bits each) `decide` (or
`native_decide` for faster evaluation) closes the proof
exhaustively.  For larger spaces we factor the problem
(per-bit lemmas + composition) — but the small case covers
a lot of useful designs.

```lean
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch07

```
## 7.1 Two adders, same answer

We compare a **ripple-carry** 4-bit adder (built from
single-bit full adders, the structural form) against a
**behavioural** 4-bit adder (just `a + b`).

```lean
/-- Single-bit full adder: returns (sum, cout). -/
def fullAdder1 (a b cin : Bool) : Bool × Bool :=
  let xorAB := xor a b
  let sum   := xor xorAB cin
  let cout  := (a && b) || (xorAB && cin)
  (sum, cout)

```
The ripple-carry version chains four `fullAdder1`s, threading
the carry from each bit to the next.

```lean
def rippleAdd4 (a b : BitVec 4) (cin : Bool) : BitVec 4 × Bool :=
  let a0 := a.getLsbD 0
  let a1 := a.getLsbD 1
  let a2 := a.getLsbD 2
  let a3 := a.getLsbD 3
  let b0 := b.getLsbD 0
  let b1 := b.getLsbD 1
  let b2 := b.getLsbD 2
  let b3 := b.getLsbD 3
  let (s0, c0) := fullAdder1 a0 b0 cin
  let (s1, c1) := fullAdder1 a1 b1 c0
  let (s2, c2) := fullAdder1 a2 b2 c1
  let (s3, c3) := fullAdder1 a3 b3 c2
  -- Reassemble s3..s0 into a BitVec 4.
  let bit (b : Bool) : BitVec 1 := if b then 1#1 else 0#1
  let result : BitVec 4 := (bit s3 ++ bit s2 ++ bit s1 ++ bit s0)
  (result, c3)

```
The behavioural version uses BitVec arithmetic directly.

```lean
def behavioralAdd4 (a b : BitVec 4) (cin : Bool) : BitVec 4 × Bool :=
  -- Extend to 5 bits to capture carry-out.
  let a5 : BitVec 5 := a.zeroExtend 5
  let b5 : BitVec 5 := b.zeroExtend 5
  let c5 : BitVec 5 := if cin then 1#5 else 0#5
  let sum5 := a5 + b5 + c5
  -- Low 4 bits = result, bit 4 = cout.
  let result : BitVec 4 := sum5.truncate 4
  let cout : Bool := sum5.getLsbD 4
  (result, cout)

```
## 7.2 The equivalence proof

Both functions take `BitVec 4 × BitVec 4 × Bool` (256 + 256 +
2 = ~131k cases), so `native_decide` finishes in milliseconds.

```lean
theorem rippleAdd4_eq_behavioralAdd4 :
    ∀ (a b : BitVec 4) (cin : Bool),
      rippleAdd4 a b cin = behavioralAdd4 a b cin := by
  decide

```
## 7.3 Why this is hardware equivalence

Once we lift both functions to Sparkle signals (combinational
— no registers — so the next-state IS the output), the
equivalence is preserved by Sparkle's compiler: both designs
emit different SystemVerilog (one is a ripple of XOR/AND/OR,
the other is a Verilog `+`), but **on every input both
produce the same output bits**.  That is what equivalence
checking gives you.

Real EDA tools (Synopsys Formality, Cadence Conformal) do the
same job at the gate level.  Sparkle's advantage: the proof
is mechanical Lean code, version-controlled, reproducible,
and re-run on every CI build.

## 7.4 The `#verify_eq` macros

For the common case "compare two signals over a fixed set of
input traces", Sparkle ships three macros:

- `#verify_eq sigA sigB n` — compare the first `n` cycles.
- `#verify_eq_at sigA sigB t` — compare at cycle `t`.
- `#verify_eq_git sigA sigB ref n` — compare against a
  committed reference trace.

See `docs/reference/Verification_Framework.md` for the full
interface.  We don't include `#verify_eq` examples in this
notebook because they `IO`-print a result — that's better
exercised in a real notebook session, not under `lake build`.

## 7.5 Exercise — equivalence of two muxes

Prove: a 2:1 multiplexer `Signal.mux sel a b` produces the
same value (at every cycle) as the behavioural form
`if sel.val t then a.val t else b.val t`.  Hint: the proof
is two `unfold`s and a `rfl`, because Sparkle's `mux` IS
defined that way.

Reference solution in `Solutions/Ch07.lean`.

```lean
-- TODO: prove `mux2_eq_behavioral`.

end Notebooks.Ch07
```
