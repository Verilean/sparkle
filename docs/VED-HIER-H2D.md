# H2d: the open parent's `#verify_elab_deep` on real-IP-shaped circuits

Issue sparkle-ved-hier2-h2d. Statement (`U2HRStmt c m d decl`), axioms and trusted components are unchanged.

| Obstacle | Cause | Change |
|---|---|---|
| `Missing cases: (Fin.mk (succ^18 _) _)` (R211, R228, R092) | the generated `match` on a `Fin n` literal index (`_nm`, 13 registers + 5 inputs) is closed by the match compiler's contradiction search, whose fixed fuel (16) the `Fin` tail exceeds | `Tools/DeepFinArms.lean`: a final arm `⟨k + n, h⟩ => absurd h _` above 15 arms; literal arms unchanged |
| `no IR register block matches the top-level circuit's registers` (R211) | the top circuit's registers are not one contiguous IR block: a nested circuit's registers sit between them | `DeepElab`: candidates also include the registers left when one block of each nested node is removed |
| replay minutes per port | `signal_run` replay per port; the checker never reads it | option `sparkle.deepNoReplay`, set by the checker; trace theorem, fidelity facts and audit unchanged |
| a call argument that is a register of a NESTED circuit | only the top loop's state was exported | `Tools/DeepNestedState.lean`: `<port>_deep_state_n<j>`; `Tools/VedU2HierStateArgs.lean` uses them (and the copies' equalities) |
| a call argument that is a derived net over register state | the state theorem speaks of `loopFOf`, the declaration's term has the loop and the helper circuits unfolded | `Tools/VedU2HierStateArgs.lean`, `Tools/DeepHelpers*.lean` |
| a port that does not read the circuit's loop fails (R210 `replyDmac`) and aborts the command | `closers exhausted`: `generalize … (loopFOf _ _)` finds no top loop in the goal | option `sparkle.deepContinue`: the port is reported `FAILED` and the next one is attempted; `attributeDeepErrors` ties its errors to it |

Round 2 (the open parent's REGISTER-STEP proof on real IP, R211 `synth_arpRequesterByte`):

| Obstacle | Cause (measured) | Change |
|---|---|---|
| `omega could not prove the goal` at the last closer | the goals are `if`/`bif` identities over the register atoms; (a) `omega` does not read `^^^` (`~~~` of a bit is `x ^^^ 1`), `&&&`, `|||`; (b) `(0#1).toNat` of a Bool input's encoding is an opaque atom; (c) the state of a loop is a PACK `a * K + (b * K' + c % K') % K`, read back by `/` `%` at every `if` | `Tools/VedU2HierClose.lean`, `ved_hier_close`: the pack is read back first (`ved_div_add_mul`, `ved_add_mul_mod`, `ved_mul_add_mod`, `Nat.mod_eq_of_lt`, side conditions by `omega`), the context is cleared of propositions `omega` cannot read, then `omega`, then split + literal reductions + `omega` |
| the goal of each register mentions the child's argument terms (4000 lines per goal) | `unfold inpU at *` copied the child's derived-argument terms (the loop of the whole circuit) into every register atom `deep.irState nm (inpU ins) t i` | only the APPLIED `inpU ins t j` is unfolded (`hinpU`); the child's range fact `hlo` and the conjunction `hR` are cleared before the next-value goals |
| `(kernel) deep recursion detected` (a 56-bit pack: 80 s, 20 GB) | `simp` applies `Nat.shiftLeft_zero` (a `rfl` lemma) as a definitional step without a proof term; the kernel then checks `x <<< 0 ≡ x` for `x = (a * 2^k + b) % 2^w` by unfolding `Nat.mod` on a literal modulus (minimal reproduction: three registers 24 + 8 + 24 bits and a child on a derived argument; 40 bits 3.6 GB, 48 bits 8.8 GB, 56 bits fails) | `Tools/VedU2HierStep.lean`: `shl_zero` (a non-`rfl` proof), the library lemma erased from `netSimpL` |
| the strict audit rejects `…_deep_trace._native.bv_decide.ax_N` | the trace closers of `#verify_elab_deep` try `bv_decide` before `simp_all` | option `sparkle.deepNoNative` (set by the checker): closers without `bv_decide`; `ved_bv_close` (`Tools/DeepNoNative.lean`): split the conjunction, the `bif`s, every single-bit atom, every `if`, evaluate the branches |
| `evalOp` left unevaluated (`~~~` of the checksum, R228) | `evalOp_not_lit` needs `a < 2 ^ widthOf x` and the operand has no range fact | second pass with the range-free forms (`rawOpL`); `widthOf.go` is unfolded (`2 ^ max 16 (widthOf.go …)` made `omega` fail) |
| `Missing cases: (Fin.mk (succ^17 _) _)` (R092) | the register-indexed `match` arms (initial values, next-state cones, state seeds) lacked the tail arm | `finTailArm` on every register-indexed `match` |
| `maximum recursion depth` in a closer | `first`/`try` rethrow runtime exceptions | `ved_rt`: a runtime exception becomes an ordinary failure |

Checks: `Tests/Ved/U2HierOpenDeepCheck.lean` (positive `wideW`: 57-bit pack, `~~~`, Bool flag over a conjunction, derived child argument; five refused controls).
