# U1 strict entry on main (PR-2)

This branch, `ved/u1-main`, is stacked on PR #147 (`ved/main-intro` `4845255b`). It brings the U1 entry from `par/ved-plan` `0a36bae0` to main.

## What U1 is

`#ved_u1 f` and `#ved_u1_deep f` synthesise `f` once, with `synthesizeCombinational`, the function `#synthesizeVerilog` calls. They return the module only after three steps succeed:

1. **The theorem.** A theorem `f.ved_u1 : U1Stmt f.ved_contract f.ved_mod f` is stated over the original constant `f` and the returned module. When `f` has leading implicit `DomainConfig` binders (`{dom : DomainConfig}` or auto-bound), `#ved_u1` states it over `@f defaultDomain` instead and the OK line says "specialised at defaultDomain": the theorem is about that specialisation, not about every domain. Any other non-explicit binder, or a fixed domain other than `defaultDomain`, is refused at [table].
2. **The kernel.** The kernel checks it synchronously, with exactly that type.
3. **The strict audit.** `#ved_strict_audit` accepts only `propext`, `Classical.choice` and `Quot.sound`, with no `native_decide`.

Otherwise the command refuses with `VED U1 REFUSED f [stage]`.

- `#ved_u1` uses a generated script. It covers register-free bodies built from not/and/or/xor/add/sub/mux/slice and two-field concatenation (lemmas in `Tools/VedU1Lemmas.lean`), and one-register delays. It is not complete for every circuit those operators can build; shifts and concatenation of more than two fields are not covered yet.
- `#ved_u1_deep` uses the standard-axiom facts that `#verify_elab_deep` generated (`_deep_trace`, `_deep_next`, `_deep_inits`, `_deep_out`). It covers one register whose current value is the output.

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
- **`Tests/Ved/U1MultiOutCheck.lean`:** multi-output (a `×`-tree of `Signal d _`, register-free).
  - Port rule: leaf = prefix, `out` at the root, product sides `_0`/`_1` (`splitReturnLeaves`); derived from the declaration and required to equal the returned module's output names, then widths and values per port.
  - The statement is `U1Stmt c m (fun xs => bundle2 (decl xs).1 (decl xs).2)`, so each projection is checked at its own port; `U1Stmt`/`OutputsStmt` are unchanged.
  - Accepted: 2 outputs of different widths, nested 3 outputs (right and left), same width.
  - Refused: a dropped output, swapped same-width outputs, one changed value, another declaration's module, a renamed port, wrong port-name lists.
  - Not supported, refused: `Signal d (A × B)` (ONE packed port `out`, `multi-output`), registers with several outputs (`multi-output`), structure results (`table`).
- **`Tests/Ved/U1DeepCheck.lean`:**
  - `accK9` and `natInit5` accepted on main, with a body that is not well-ordered in its own order;
  - the dependency closure contains no native replay;
  - other declarations' facts and proofs, and `native_decide` proofs, are refused.

## What it does not claim

- **The artifact.** The guarantee is about the module `synthesizeCombinational` returned. It is not about the printed Verilog (`toVerilog (optimizeModule m)`).
- **Scope.** One output, no memories or instances, and runs with reset held at 0.
- **Coverage.** Nothing here is "327 supported" or strict-complete; that belongs to the release gate (Issue `sparkle-ved-release-gate`).
- **The design document.** The design document named in the tool headers (`docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md`) is on `par/ved-plan`, not on main.
