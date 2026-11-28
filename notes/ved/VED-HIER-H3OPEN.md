# VED-HIER-H3OPEN: several child instances on the parent's register state, the child output feeding the loop

> **Development record, not user documentation; not kept current.** The current description is [docs/VED.md](../../docs/VED.md).

> Historical design record. Describes the unit branch of the H3 hierarchy work, merged with PR #167; it is not kept in step with current `main` (file names, line numbers and option defaults may have moved). Index: [notes/README.md](../README.md); current description: [docs/VED.md](../../docs/VED.md).

Rows R193 `synth_sha512Block_out0` and R194 `synth_sha512Block_done` (`Tests/IP/Crypto/SHA512BlockHWTest.lean`).  The
statement `U2HRStmt` is unchanged (`Tools/VedU2HierReg.lean`, `Tools/VedU2HierStmt.lean`: no diff).

## Status

* The new method is accepted strict by `#ved_u2_hier` on small families (`Tests/Ved/U2HierMultiCheck.lean`): the same
  child on two different state nets (`multiTwo`, four instances), one net in two registers (`multiShared`, the shape of
  sha512's `kMux`), two different children (`multiKids`).  Stored type `==` `U2HRStmt`, axioms within `propext`,
  `Classical.choice`, `Quot.sound`.
* R193/R194 pass every stage before the parent proof (open parent, loop knot, the open parent's deep run) and stop at
  `[proof]`: the parent proof of a 34-register parent is far over the budget (see "Cost").  Not strict.

## Why H2c-state did not apply

`sha512BlockHW` is a `circuit do` with 34 registers.  `kMux` is called twice inside the loop body on the round counter and
its output feeds the working registers' next values; the declaration `(sha512BlockHW …).out0` is not a call of the child.
H2c-state needs the declaration to BE one call on a closed argument, the call being dead in the loop (the loop of the
argument differs from the open parent's loop only in dead code, a kernel conversion).  Here the call is live in the feedback.

## Design

1. **Calls found by reduction.**  `body regs holds` is reduced (`reducible`) for a free state `live`; the child calls become
   closed terms over `live` and the inputs (`Tools/VedU2HierMultiGen.lean`).  Distinct calls (child, arguments) are the
   ORACLES `o_j`; N instances of one child module share one child theorem (the existing per-module `kid_step` fact), the
   instances are paired with the calls by the equality class of their input nets (a wrong pairing fails in the proof).
2. **The open parent** is the original `circuit do` with every call replaced by its oracle (a free signal parameter): it is
   a `runCircuitH`, so `#verify_elab_deep` runs on it unchanged.
3. **The loop knot** (`Tools/VedU2HierMultiLoop.lean`, `loop_knot`): with `F o x` the loop body of the open parent and
   `Os x` the oracle the real children give for the state `x`, the declaration's loop `Q = loop (fun x => F (Os x) x)` equals
   the open loop with the oracle fixed along it, `Q = loop (F (Os Q))`.  Three facts about the body are proved by a
   generated `simp only` script (`hcF` causal in the state, `hcO` reads the oracle only in the past, `hOs` the oracle reads
   the state at the same cycle only); the child's definition is unfolded for `hOs`, so a child whose body `simp` cannot
   unfold is refused.  The kernel equation `decl xs = ved_open xs (G e₁[Q]) …` (`_eq`) and the knot (`_knot`) are theorems
   with standard axioms; they replace the `Eq.refl` of H2b/H2c-state.
4. **The composition** is the existing one (`outputsOnHS_of_stepRK`, one induction on the cycles: invariant → instance
   arguments agree → child outputs agree → parent output and next state agree → invariant), now with N instances; the
   argument agreement reads the exported state theorem through the knot (`ved_rw_loops` matches the declaration's loop
   constant `…ved_open_…_Q` like a `Signal.loop` term).  The output is read from the declaration's own port of the open
   parent (`_eq`, `_deep_trace`).
5. **Register-bundle reads** (`Tools/VedU2HierMultiBundle.lean`, `Tools/VedU2HierMultiChain.lean`): `circuit do` bundles the
   registers into nested pairs and reads register `k` through `k` slices.  The H2c proof evaluated the concatenation into
   `Nat` arithmetic (an 2000-bit number for sha512).  `bundle_slice_fact` states once that a slice that is exactly one
   element of a concatenation has that element's value; the script uses it once per peeled pair and facts are generated only
   for the registers the net reads.  With it a 12-register family is 160 s instead of more than 12 GB.

Single-instance rows (R223, R092, R211, R210, R228) keep the H2c-state path: `multi` is chosen only for more than one
instance (or child) when an instance reads register outputs.

## Hooks in shared files

* `Tools/DeepElab.lean`: the tail arm for the input family (`finTailArm inpSArms nI`; a parent with more than 15 inputs
  was "Missing cases"); option `sparkle.deepPorts` (prove only the named ports of a struct-valued circuit; default: all).
* `Tools/VedU2HierEntry.lean`: `OpenInfo.knot`, `InstInfo.bsl`, `InstInfo.needSlots` (defaults: no change).
* `Tools/VedU2HierRegEntry.lean`: the choice of the new open parent, the instance/call pairing, the knot in the script
  (`stateFacts`, output through the equation), `maxSteps` for `simp … at hin`, `decide +kernel` for the shape facts, debug
  output (`VED_HIER_DEBUG`, `VED_HIER_PROFILE`), the open parent is proved for the declaration's own port.
* `Tools/VedU2HierStateArgs.lean`: `Sp.knot`, `topState`.  `Tools/VedU2HierLoopRw.lean`: the declaration's loop constant.

## Cost (this machine, `kjob lake env lean`, guard 23068672)

Scale ladder, `scratch`-generated family `toyN` (n registers of 16 bits + counter, two calls on the counter):

| n | parent proof | peak |
|---|---|---|
| 4 | 29 s | 2.3 GB |
| 6 | 44 s | 2.7 GB |
| 8 | 67 s | 3.2 GB |
| 12 | 160 s | 3.5 GB |
| 16 | refused at `[proof]`: the 8000000-heartbeat floor after 573 s | 6.8 GB |
| 20 | refused at `[proof]`: the heartbeat floor after 11 min | 10.7 GB |

R193 (34 registers of 64 bits, 340 statements): open parent + knot + deep run of the declaration's port 150 s; `[proof]`
reaches the 8000000-heartbeat floor after 15.5 min (guard peak 9.4 GB); with the heartbeat limit lifted it is still running
after 50 min.  Dominant costs by the profile of the family: the one `simp` that evaluates the whole arrangement
(`evalAssignsI`: 8 s at n=6, 34 s at n=12, 84 s at n=16), `omega` calls (0.6-1.2 s each at n=12, up to 26 s each at n=16), `decide`.
A tactic that clears the hypotheses unrelated to the goal before the closers (tried, not kept) did not change these.

## Next

The parent proof compares the IR evaluation of the whole arrangement with the open parent's compiled cones register by
register.  The open parent's own IR (instances replaced by oracle inputs) already has that comparison as the deep route's
fidelity theorem; a verified decidable check that the returned module's body is that IR with each instance replaced by its
oracle wire would replace the symbolic evaluation of 340 statements by `decide +kernel`.
