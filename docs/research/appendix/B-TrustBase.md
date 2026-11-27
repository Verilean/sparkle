# Appendix B: trust base

[Back to the research README](../README.md). Rungs refer to the
[guarantee ladder](../README.md#the-guarantee-ladder).

## Rung 2 (source to returned IR), per-circuit theorems

What is trusted when a row of [appendix F](F-AllCommandRows.md) is strict:

| Item | Role |
|---|---|
| The Lean 4 kernel (`leanprover/lean4:v4.32.1`) | checks the theorem against the stored statement |
| The three standard axioms `propext`, `Classical.choice`, `Quot.sound` | the only axioms the strict audit allows (`Tools/VedStrictAudit.lean`, `strictAllowed`) |
| The definitions in the statement: the IR semantics `Sparkle/IR/Semantics.lean`, the contract (`CorrStmt`, `ShapeCore`, `WidthStmt`), `srcOf` | a statement is only as meaningful as these definitions; they are read by humans, not proved |
| The *statement* the entry registers | compared by `==` with the expected type; an entry cannot weaken it silently |

**Not trusted** (generation only; the kernel checks the result): the generated scripts, the
tactics, `simp` sets, the `ved_*` automation, caches of the entry (`ved_omega_c` and friends).
A bug there can cause a refusal or an unsound-looking acceptance that the kernel then rejects;
it cannot make a false theorem accepted, unless it changes the *statement* or the *audit*.

## What is excluded, and why it is not counted strict

* **`native_decide`.** Uses the compiled evaluator as an axiom (`Lean.ofReduceBool`-style
  auxiliary axioms). The strict audit rejects any `*._native.native_decide.ax_*` auxiliary.
  `#verify_elab_deep` still ends with a replay step `_deep_signal_run` that uses `native_decide`;
  that link is **not** strict ([VED.md](../../VED.md#trust-base)). The option `sparkle.deepNoNative`
  (set by the checker) generates closers without it.
* **`bv_decide`.** Relies on an external SAT solver and a reflected LRAT checker; the audit
  rejects `*._native.bv_decide.ax_*`. The checker's closers avoid `bv_decide`.
* **"axioms clean" in a command's PROVEN message** is not a strictness claim; only the strict
  audit is.

## Where the ladder leaves the kernel

| Rung | Trusted, not proved |
|---|---|
| 3 optimiser | all of `optimizeModule` / `optimizeDesign` |
| 4 SV text | the emitter and parser beyond the proved fragment; 73 `partial def` on the path (the proof works on total "twins" tied to the shipping code by executable cross-checks, `Tools/SVParser/RoundtripProof.lean`) |
| 5 SV semantics | no formal SystemVerilog semantics is connected |
| 6 hardware | synthesis tools, place and route, silicon |
| writer | `#ved_write_checked` proves the writer receives the checked IR; the writer's own functions are trusted |

## The general theorem

The compiler general theorem is conditional on laws about the Lean runtime, reflection facts and
data checks that are not supplied (see [CompilerGeneralTheorem.md](../CompilerGeneralTheorem.md)).

## The measurement

The coverage numbers come from a harness and a ledger generator that are not part of this tree.
They are *not* part of the trust base of a theorem, but they are the trust base of the *count*:
a reviewer approved the count and noted that the checksum list could not be re-checked
independently ([D-Evidence.md](D-Evidence.md)).
