
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

## 7.3b Equivalence on the Signal, cycle by cycle

§7.3 said the equivalence "lifts to signals" — here it is concretely.
A Signal-level equivalence is just `∀ t, A.val t = B.val t`, and because
the operators reduce pointwise (`(x + y).val t = x.val t + y.val t`),
each cycle collapses to a plain `BitVec` fact you can `bv_decide`.

Two combinational expressions that compute the same value every cycle —
here `a + b` and `b + a` — are equal *as signals* (shown as a statement,
like §7's opening; the operator forms reduce pointwise so each cycle is a
plain `BitVec` goal):

```text
theorem add_comm_sig {dom : DomainConfig} (a b : Signal dom (BitVec 4)) :
    ∀ t, (a + b).val t = (b + a).val t := by
  intro t
  -- `show` rewrites both sides to their per-cycle BitVec form…
  show a.val t + b.val t = b.val t + a.val t
  bv_decide   -- …then it is just commutativity on `BitVec 4`.
```

When one side is defined *as* the behavioural spec the proof is even
shorter: `Signal.mux sel a b` is *by definition* `⟨fun t => if sel.val t
then a.val t else b.val t⟩`, so the Signal-level statement
`∀ t, (Signal.mux sel a b).val t = (if sel.val t then a.val t else
b.val t)` is closed by a single `rfl` — a structural multiplexer and its
behavioural `if-then-else` spec are *definitionally the same signal*.

This is the same equivalence the pure-`BitVec` theorem in §7.2 states,
now phrased on the actual `Signal` outputs — `∀ t` is the temporal
"for every cycle", exactly as `□` was in Ch 6.

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

## 7.4b `#verify_emit` — is the emitted Verilog still my circuit?

Everything above compares two things *you wrote*.  There is one more
equivalence you usually take on faith: that the SystemVerilog Sparkle
**emits** for your circuit still means what the circuit means.  The
`#verify_emit` command turns that faith into a kernel-checked theorem:

```text
import Tools.SVParser.VerifyEmit

def acc (en : Signal defaultDomain (BitVec 1))
    (d : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let r ← Signal.reg 0#4
    r <~ Signal.mux (en.map (· == 1#1)) (r + d) r
    return r

#verify_emit acc
-- ✅ #verify_emit `acc`: emitted SystemVerilog proven equivalent —
--    2 cone obligations (registers + outputs), ports/registers/inits
--    structurally matched
```

Under the hood it closes the whole emission loop *inside Lean*:

1. synthesize `acc` to the IR (the same path `#synthesizeVerilog` takes);
2. emit SystemVerilog text from that IR;
3. parse the text back with Sparkle's own SystemVerilog front-end —
   the one hardened against the XiangShan corpus (Ch 8's round-trip
   pipeline);
4. for every register's next-state cone and every output cone, on both
   sides, inline everything down to (inputs ∪ registers), reflect the
   two expressions into pure `BitVec` terms, and prove them equal with
   `bv_decide` — a real theorem per cone, checked by the Lean kernel,
   with no external tool trusted.

The comparison holds under `rst = 0` (asserted reset is decided by the
register construct itself on both sides), and structural checks pin the
rest: same ports, same registers, same initial values, same reset kind.
Stepwise cone equality plus equal initial state is sequential
equivalence by induction.

Like the `#verify_eq` family, run it interactively or via
`lake env lean` (bv_decide's known `lake build` caveat applies); see
`Tests/Verification/VerifyEmitDemo.lean` for a runnable demo.  Scope:
single-module designs without memories, at DSL-scale widths — for
production-scale *ingested* Verilog the same question is answered
statistically by the XiangShan CI gate (yosys formal equivalence +
three-way co-simulation) instead of by proof.

### The other direction: `#verify_dsl_roundtrip`

The IR is not only a compilation target — it can be printed back as
`circuit do` source.  `#verify_dsl_roundtrip` closes that loop and
proves it:

```text
import Tools.SVParser.DslEmit

def mix (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let x ← Signal.reg 0#8
    let y ← Signal.reg 0#8
    x <~ (a ^^^ b)
    y <~ ((x &&& b) ||| a)
    return (x + y)

#verify_dsl_roundtrip mix
-- generated circuit-DSL source:
-- def mix_dslRT (a : Signal defaultDomain (BitVec 8)) (b : …) : … :=
--   circuit do
--     let r0 ← Signal.reg (0#8)
--     let r1 ← Signal.reg (0#8)
--     r0 <~ (a ^^^ b)
--     r1 <~ ((r0 &&& b) ||| a)
--     return (r0 + r1)
-- ✅ decompiled circuit-DSL re-synthesizes to an equivalent design —
--    3 cone obligations proven
```

It synthesizes your definition, *decompiles* the IR to fresh
`circuit do` text, elaborates that text as a new definition,
re-synthesizes it, and proves the two designs' cones equal — so the
printed source is not merely plausible-looking, it provably denotes the
same circuit.  (Register names become `r0, r1, …` and inputs keep their
parameter names; the comparison α-renames before calling `bv_decide`.)

Two reasons to care.  First, it is the round-trip test for the *Lean*
side of the toolchain, mirroring the Verilog→IR→Verilog testing the
SystemVerilog front-end gets from the XiangShan corpus (Ch 8).  Second,
the same decompiler is the path from ingested RTL to *maintainable*
Sparkle source: parse a Verilog module, and print it back as a DSL
definition you can read, edit and prove about — with this command
checking the printer never lies.  The v1 operator subset is
`{const, ref, +, -, *, &&&, |||, ^^^, ~, ++, slice, <<< / >>> by a
constant, ==, mux}`, single module, one output, no memories.

## 7.5 Exercise — adder trees agree

Following `add_comm_sig` (§7.3b), prove that two ways of summing three
signals — left- and right-associated — agree on every cycle:

```text
∀ t, ((a + b) + c).val t = (a + (b + c)).val t
```

Hint: same shape — `intro t`, `show` the per-cycle `BitVec 4` goal, then
`bv_decide`.

Reference solution in `Solutions/Ch07.lean`.

```lean
-- TODO: prove `quad_eq_shift2`.

end Notebooks.Ch07
```
