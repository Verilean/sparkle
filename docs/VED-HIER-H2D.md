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

Checks: `Tests/Ved/U2HierOpenDeepCheck.lean`.

Open (see the report): on R211 the generated parent proof now runs to its last closer (`omega`) after ~14 min / 13 GB; no real row is strict yet.
