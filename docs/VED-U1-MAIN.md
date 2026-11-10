# U1 strict entry on main (PR-2)

This branch, `ved/u1-main`, is stacked on PR #147 (`ved/main-intro` `4845255b`). It brings the U1 entry from `par/ved-plan` `0a36bae0` to main.

## What U1 is

`#ved_u1 f` and `#ved_u1_deep f` synthesise `f` once, with `synthesizeCombinational`, the function `#synthesizeVerilog` calls. They return the module only after three steps succeed:

1. **The theorem.** A theorem `f.ved_u1 : U1Stmt f.ved_contract f.ved_mod f` is stated over the original constant `f` and the returned module.
2. **The kernel.** The kernel checks it synchronously, with exactly that type.
3. **The strict audit.** `#ved_strict_audit` accepts only `propext`, `Classical.choice` and `Quot.sound`, with no `native_decide`.

Otherwise the command refuses with `VED U1 REFUSED f [stage]`.

- `#ved_u1` uses a generated script. It covers register-free bodies and one-register delays.
- `#ved_u1_deep` uses the standard-axiom facts that `#verify_elab_deep` generated (`_deep_trace`, `_deep_next`, `_deep_inits`, `_deep_out`). It covers k ≥ 1 registers (see the multi-register section below) with Bool or bit-vector data inputs and one output.

Everything else is refused.

## Changes against `par/ved-plan`

- **The entry is `synthesizeCombinational`.** Main has no `synthesizeEntry` and no inliner fuel guard.
- **`declWidth` is defined in the contract.**
- **`Tools/VedIRDecEq.lean`.** Main's AST derives no `DecidableEq`, so the instances live in the U1 tools; no compiler file is changed.
- **The order-free meaning (user decision 2026-11-09).**
  - **The problem.** Main's compiler emits some `circuit do` bodies with a wire read before its assignment. `accK9` is an example: `_tmp_op_a_2 := _tmp_loop_body_7[7:0]` comes before `_tmp_loop_body_7 := _tmp_a_5`.
    - As continuous assignments, and in the printed Verilog, the order carries no meaning.
    - The IR semantics' `evalAssigns` folds the list once from top to bottom, so such a read sees a seed value.
  - **The statement now.** `OutputsStmt` speaks about every arrangement of the body in which each wire is assigned before it is read (`WO [] b`). `runModule_perm` (`Sparkle/IR/ReorderInvariance.lean`) makes all of these arrangements agree.
  - **`OrderStmt`.** It requires one checked arrangement, `OrderOk`, decided in the kernel. It also rules out what has no order-free meaning:
    - a combinational cycle;
    - an assignment that reads its own target;
    - a read of a name that is neither an input, a register output nor assigned;
    - duplicate register or memory names;
    - an output with no driver, an assignment to an input, a name that is both assigned and a register output (review of PR #148: the seed default must never stand in for a missing driver).
  - **The module is not reordered.** The arrangement is proof data only (`f.ved_body`). The entry refuses at `[order]` when no arrangement exists.
  - **The old statement is recovered.** `outputs_body` gives the in-order statement over `m.body` whenever that order is already well-ordered.
- **The checks are pinned to main's IR.**
  - `delay8` on main is one register plus `out := register`.
  - The output mutation now reads the input; the `poc`-era concat-field mutation is a no-op on main.

## Checks

These are built by `ved-pr`; job `ved-u1-ord-4bf8c9dd`, exit 0.

- **`Tests/Ved/U1ContractCheck.lean`:**
  - the toy delay, with the full statement;
  - the declaration-table and width controls;
  - the order controls: read-before-assign accepted once reordered; cycle, self-read and undriven read refused.
- **`Tests/Ved/U1EntryCheck.lean`:**
  - `delay8`, `ident8`, `delay8k` and `delay8b` accepted;
  - mutated modules refused at `[proof]`;
  - kernel counterexamples;
  - multi-output refused.
- **`Tests/Ved/U1DeepCheck.lean`:**
  - `accK9` and `natInit5` accepted on main, with a body that is not well-ordered in its own order;
  - the dependency closure contains no native replay;
  - other declarations' facts and proofs, and `native_decide` proofs, are refused.

## What it does not claim

- **The artifact.** The guarantee is about the module `synthesizeCombinational` returned. It is not about the printed Verilog (`toVerilog (optimizeModule m)`).
- **Scope.** One output, no memories or instances, and runs with reset held at 0.
- **Coverage.** Nothing here is "327 supported" or strict-complete; that belongs to the release gate (Issue `sparkle-ved-release-gate`).
- **The design document.** The design document named in the tool headers (`docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md`) is on `par/ved-plan`, not on main.

## `#ved_u1_deep` with several registers and Bool inputs

Issue `sparkle-ved-multireg`. Nothing in `Sparkle/`, in `Tools/DeepElab.lean` or in the statement (`U1Stmt`, `OutputsStmt`, `ShapeCore`, `regsOf`, `st0`) changed; the contract already states multi-register modules (`regsOf` lists every register, `st0` looks each up by name) and Bool ports (`PTy.bit`).

- **The rule.** The invariant of the step obligation is, for every register slot `i` of the Cdo, `st (_nm ⟨i,_⟩) = Cdo.irState … s ⟨i,_⟩`. The correspondence is by the `_nm` names; widths, masks and initial values come from `_deep_inits` and the module's wires, closed inside the kernel proof. The step is still discharged on the checked arrangement (`OrderOk m nm.body`) and carried by `outputs_of_order`.
- **Bool inputs.** The contract side is `PTy.sig .bit`; the deep side is `_inp`'s `bif b then 1#1 else 0#1`. The proof uses `InputsOk` only.
- **Hygiene.** The generated hypotheses are macro-scoped; user parameters are never captured.
- **Check.** `Tests/Ved/U1MultiRegCheck.lean` (`lake build Tests.Ved.U1MultiRegCheck`):
  - accepted, std3 axioms, full type compared with `==`: two registers with a Bool reset, four independent counters, a held register with a Bool enable and a bit-vector input, a 3-state FSM with a hold, user parameters named `u`, `m`;
  - refused at `[proof]`, nothing left under the base: one register's next value changed (2 and 4 registers), two same-width registers swapped in the module (2 and 4), another declaration's DeepElab constants, a wrong initial value (2 and 4).
  `U1DeepCheck`, `U1EntryCheck` and `DeepHygieneCheck` still pass.
- **Representatives, in their own file context** (`#verify_elab_deep` then `set_option Elab.async false in #ved_u1_deep`, scratch files outside the tree; wall time includes loading the imports, peak RSS of the whole `lean` process). These are reference runs by the implementing agent, made before the kjob build-cache seeding fix. They are not independent-probe measurements and are NOT added to the strict count of the fixed 327-row inventory; that count comes only from the separate measurement with an independent probe:

  | row | declaration | result | wall (verify only / + deep U1) | peak RSS |
  |---|---|---|---|---|
  | R58 | `twoRegResetCdo` | strict (std3) | 13.0 s / 19.2 s | 1.98 GB |
  | R62 | `fourCounterCdo` | strict (std3) | 22.2 s / 30.0 s | 2.21 GB |
  | R59 | `heldRegCdo` | strict (std3) | 14.4 s / 16.1 s | 1.91 GB |
  | R61 | `fsmHoldCdo` | strict (std3) | 15.5 s / 20.1 s | 2.02 GB |
  | R57 | `resetCounterCdo` | strict (std3) | 14.1 s / 14.4 s | 1.81 GB |
  | R258 | `counterEnableDSL` | strict (std3) | 13.8 s / 13.3 s | 1.84 GB |

- **What is not claimed.**
  - R66 (`baselineNoSubmodule`) and R212 (`crc32EngineTop`) were not run here.
  - One output, no memories, no instances, no multi-output, reset held at 0: unchanged. Nothing about the optimised IR or the printed SV.
  - A circuit with many registers and several inputs is one `simp`/`omega` script; a local copy with two registers and three inputs (two Bool, one 8-bit) was refused at `[checker]` (deterministic heartbeat timeout at `whnf`, limit 200000). The limit was not raised; a smaller circuit of the same kind (two registers, a Bool and an 8-bit input) is accepted.
  - Nothing here is "327 supported" or strict-complete.
- **Fin literals.** Core simp turns a joined-context index into `(3 : Fin 4)` while the surrounding `Fin.val` keeps the bound `List.length (Γr ++ Γi)`; that term is not type-correct at instance transparency and simp then refuses to rewrite it. The script keeps the indices as `Fin.mk` (`-Fin.reduceFinMk`, `-Fin.isValue`, `-Fin.reduceSucc`, `-Fin.reduceOfNat`) and has one simproc for `Fin.val` of a numeral (`[8,8,8,8][↑3]`). A future generalisation (many registers, many inputs) should avoid expanding `natJoin`/`envOfC` through `List.finRange` and instead read each variable with `envOfC_names`, one lemma per slot.
