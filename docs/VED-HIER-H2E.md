# VED-HIER-H2E: open parents R210 / R228 and the nested export's budget

Real-IP rows R210 `synth_arpResponderByte` and R228 `synth_icmpRequesterByte` are accepted strict by `#ved_u2_hier`
(stored type `==` `U2HRStmt`, axioms within `propext`, `Classical.choice`, `Quot.sound`, no statement or hypothesis change).

## What was added

* `ved_hier_close` rewrites the complement of a bounded value (`Tools/VedU2HierXor.lean`) and the concatenations of the
  one's-complement adder (`Tools/VedU2HierBvAppend.lean`).
* `ved_rw_loops` (`Tools/VedU2HierLoopRw.lean`) rewrites the loops of the goal to `BitVec.ofNat w (irS ...)` by definitional
  matching, so unfolded nested loops match the exported state theorems.
* `ved_port_ctx` clears the hypotheses the goal does not speak of before `omega`.
* A limit reached while the register-parent proof is elaborated (`maxHeartbeats`, `maxRecDepth`) is a refusal at `[proof]`.
* Options `ved.u2.hierRecDepth`, `ved.u2.hierHeartbeats`, `ved.u2.nestedRecDepth`, `ved.u2.nestedHeartbeats` are floors on
  the limits (`0` = no extra floor); defaults 100000 / 8000000 / 65536 / 1600000, the former constants.

## Checks and their cost

`U2HierOpenDeep2Check` (8-bit `compW`, 16-bit `onesW`; refusals on `compRef`, one on `onesRef`) and `U2HierOpenDeep3Check`
(`reqW`: the unfolded nested loop; the helper and the budget runs) take about 5 minutes and 5 GB each.  Refusal controls
whose refused proof search runs long are not in the Checks: a wrong constant on `onesRef` was killed at 12 GB after 579 s;
the other `onesRef`/`reqRef` mutations take 60-115 s each.  The same mutations on `compRef` refuse in about 7 s.
