# VED U1: single-module large DAG goals (R83 R84 R212 R103)

Issue `sparkle-ved-u1-wire-share`.  The original declarations of the real-IP rows

| row | declaration | what makes the goal large |
|---|---|---|
| R83 | `synth_crsfCrc8` (`crc8HW`) | 8 chained bit steps, each uses its argument 3 times: the unfolded step is a DAG of ~160 nodes whose tree has 2.5 * 10^8 |
| R84 | `synth_droneCanCrc16` (`crc16CcittHW`) | the same at 16 bits |
| R212 | `crc32EngineTop` (`crc32Engine`) | the same at 32 bits (`poly &&& (0 - (crc &&& 1))`), tree 1.1 * 10^5 |
| R103 | `lqrLoopTop` (`demoLQR`) | two 32-bit registers, signed 64-bit products (`sext ||| field`, `% 2^64`, `/ 65536`), clamps, tree 1.7 * 10^6 |

are accepted by `#ved_u1` (stored type `==` `U1Stmt c m F`, axioms `[propext, Classical.choice, Quot.sound]`),
with no change of statement, hypothesis or axiom.

## What blew up (R83 first, then the others)

The generated loop script (`loopScriptFor`, one register) read the DAG as a tree in five places, one after the
other; each was found with the stage timer (a tactic that appends the time to a file, between the stages) and `perf`:

1. `ved_loop_unfold`: `repeat (rw [loop_val_unfold ..])`.  The failing last `rw` unifies the pattern with every
   `Signal.val _ (s+1)` node of the unfolded body, and each unification unfolds the node.
2. `ved_loop_gen`: `loopsOf` (a tree walk) and `generalize` (`kabstract`).
3. `ved_bit_simp`: `omega` as the discharger of its side conditions reads the goal as a tree (R83: 80 s, no effect).
4. `ved_or_lit`, `ved_bits_facts`, `ved_mul_facts` (`natOrs` / `natBitOps` / `natMuls` without a visited set).
5. `ved_wire` itself: `^^^`, `&&&`, `|||` were atoms for `omega` (no equality between wires could be proved), `atomsOf`
   was a tree walk, and after a failing step `all_goals` recovered from the error and the closing step ran
   `omega` on the huge goal.  The second goal of the script (`case h0`) unfolded with the same `rw`.

## What was done

* `Tools/VedU1WireShare.lean` (new): `ved_loop_unfold_share` (the occurrences of `(Signal.loop F).val t` found by a walk
  over the shared subterms and replaced with `Expr.replace`, the equality `loop_val_unfold` used through `congrArg`),
  `ved_loop_gen_share` (loops by a DAG walk, generalisation by replacement, the occurrence of the state recognised by
  the loop and the cycle: `HList [BitVec 8]` and `BitVec 8 × HList []` are two spellings of one state type),
  `ved_bit_simp_share` (skipped on a goal that `ved_wire` takes and that has bit operations), `ved_pack_wire_all`
  (the failure of the wire step fails the script).
* `Tools/VedU1Wire.lean` (`ved_wire`): on a goal with bit operations (`bitsMinOps`) the atoms become wires too, `^^^` /
  `&&&` / `|||` are operation nodes (evaluated on the samples, with intervals), the proved equalities between wires are
  substituted (`substWires`: the operations over equal wires become the same atom for `omega`), the bit operations that
  stay get facts (`a ^^^ b < 2^n`, `a &&& b <= a`, `c ||| x = c + x` as an implication), the `^^^ 1` / `&&& 1` / `||| 1`
  of a one-bit field are rewritten to `/ 2`, `% 2` (tried second: the rewritten terms are large for `omega`); the
  `ite` instances that no longer match their condition after wiring are repaired (`fixIteInst`); a goal below
  `shareMinTree` with at least `bitsSmallOps` bit operations is tried with `ved_wire` first (R212), the packing step
  is the fallback.
* `Tools/VedU1Loop.lean`: visited sets in `natOrs` / `natBitOps` / `natMuls`; `treeSizeVal` keyed by the address of the
  node (the structural key compared large shared terms); the constants `bitsMinOps`, `bitsSmallOps`.
* `Tools/VedU1Entry.lean`: the script calls the `_share` tactics (5 one-line changes) and `simp` in the two loop simp sets
  gets `(maxSteps := 4000000)` (the 16-bit body exceeds the default 100 000).

Everything is untrusted proof search: the kernel checks the result; the numeric samples only propose equalities.

## Measurements (standard script, this machine, alone; the standard harness limit is 900 s)

| row | result | seconds | peak RSS |
|---|---|---|---|
| R83 `synth_crsfCrc8` | strict | 62 | 4.2 GB |
| R84 `synth_droneCanCrc16` | strict | 70 | 4.6 GB |
| R212 `crc32EngineTop` | strict | 43 | 3.8 GB |
| R103 `lqrLoopTop` | strict | 107 | 5.1 GB |

`Tests/Ved/U1WireShareCheck.lean` (positives: 3-step 8-bit and 2-step 16-bit CRC chains; controls: another initial
value for both, the arms of a step swapped, another polynomial: refused at `[proof]`, nothing left behind).
