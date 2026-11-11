# U1 strict entry on main (PR-2)

This branch, `ved/u1-main`, is stacked on PR #147 (`ved/main-intro` `4845255b`). It brings the U1 entry from `par/ved-plan` `0a36bae0` to main.

## What U1 is

`#ved_u1 f` and `#ved_u1_deep f` synthesise `f` once, with `synthesizeCombinational`, the function `#synthesizeVerilog` calls. They return the module only after three steps succeed:

1. **The theorem.** A theorem `f.ved_u1 : U1Stmt f.ved_contract f.ved_mod f` is stated over the original constant `f` and the returned module. When `f` has leading implicit `DomainConfig` binders (`{dom : DomainConfig}` or auto-bound), `#ved_u1` states it over `@f defaultDomain` instead and the OK line says "specialised at defaultDomain": the theorem is about that specialisation, not about every domain. Any other non-explicit binder, or a fixed domain other than `defaultDomain`, is refused at [table]. For a result that is a `×`-tree of `Signal d _` (register-free), the statement is over the bundled lambda `fun xs => bundle2 (f xs).1 (f xs).2` (nested by the tree), i.e. the projections of the original declaration's value; see the multi-output section below.
2. **The kernel.** The kernel checks it synchronously, with exactly that type.
3. **The strict audit.** `#ved_strict_audit` accepts only `propext`, `Classical.choice` and `Quot.sound`, with no `native_decide`.

Otherwise the command refuses with `VED U1 REFUSED f [stage]`.

- `#ved_u1` uses a generated script. It covers register-free bodies built from not/and/or/xor/add/sub/mux/slice, two-field concatenation, `==` (`Operator.eq`, 1-bit result), constants (`.const`, `Signal.pure`) and the constant mux chains `kLut!` expands to (lemmas in `Tools/VedU1Lemmas.lean`), and one-register delays. A body that uses `==` is closed over the finite input domain: every data input is generalised and the remaining goal `∀ x, x < 2^w → …` is decided by the kernel (`decide +kernel`; no `native_decide`, standard axioms only). The cost grows with the product of the input ranges and may hit resource limits; this suits table-shaped leaves (a 4-bit or 8-bit index). There is no width guard that refuses wide inputs, and no fixed stage at which they stop; `sboxHW` still stops at `maxRecDepth` in the checker and stays open. It is not complete for every circuit those operators can build; shifts and concatenation of more than two fields are not covered yet.
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
- **`Tests/Ved/U1MultiOutCheck.lean`:** multi-output (a `×`-tree of `Signal d _`, register-free).
  - Port rule: leaf = prefix, `out` at the root, product sides `_0`/`_1` (`splitReturnLeaves`); derived from the declaration and required to equal the returned module's output names, then widths and values per port.
  - The statement is `U1Stmt c m (fun xs => bundle2 (decl xs).1 (decl xs).2)`, so each projection is checked at its own port; `U1Stmt`/`OutputsStmt` are unchanged.
  - Scope (review of a3f25e5f): four small examples; no new strict row of the fixed 327 (the register-free multi-output rows there are packed `Signal d (A × B)`, still refused).
  - Accepted: 2 outputs of different widths, nested 3 outputs (right and left), same width.
  - Refused: a dropped output, swapped same-width outputs, one changed value, another declaration's module, a renamed port, wrong port-name lists.
  - Not supported, refused: `Signal d (A × B)` (ONE packed port `out`, `multi-output`), registers with several outputs (`multi-output`), structure results (`table`).
- **`Tests/Ved/U1PackedCheck.lean`:** `#ved_u1_packed`, a result `Signal d (A × B)` (ONE port `out`, first leaf in the high bits; docs/VED-U1-PACKED.md).
  - A separate mode and statement (`PackedStmt`); `#ved_u1` and `U1Stmt` are unchanged and `#ved_u1` still refuses such a result at `[multi-output]`.
  - Accepted: 2 components, a `Bool` leaf, nested right and left (3 leaves), auto-bound domain; the contract's slice map is compared with a hand-written one.
  - Refused (stage `packed` or `proof`, nothing left behind): slices swapped, exchanged, wrong offset, wrong width, overlap, gap, missing or extra slice, another port name, a changed field value, fields swapped inside the module, another declaration's module.
  - Fixed inventory rows: R296 `test_tuple` and R309 `test_decoder_fields` are strict in their own file context.
- **`Tests/Ved/U1EqLutCheck.lean`:**
  - 7 positives (`==` of two signals, `==` against a constant, a constant output, local 4-entry `kLut!` tables), each with the exact type and the standard axioms;
  - 13 refusals at `[proof]` with no `ved_*` left: 9 mutants and 4 modules of other declarations. Each mutant differs from the original in exactly one statement (two for the swap); the positions and the old and new statements are checked before the control runs, and a mutator whose target is absent fails.
- **`Tests/Ved/U1RconCheck.lean`:**
  - the real `Sparkle.IP.Crypto.AESHW.rconHW` (16-entry `kLut!`): exact type, standard axioms, `ved_mod` equal to a fresh synthesis. Its own lean_lib, not in the VED CI workflow (it imports the AES IP).
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

## `#ved_u1_deep`: where the deep facts are looked up

Issue `sparkle-ved-deep-name`. `#verify_elab_deep d` declares `{last component of d}_deep*` in the CURRENT namespace. `#ved_u1_deep d` used to look them up in the declaration's namespace, so it refused (`[proof]: …_deep missing`) whenever the two commands ran outside the declaration's namespace (after `end` with an `open`, or at the root).

- **Resolution rule** (`Tools.VedU1Deep.deepScope`). The facts are `{current namespace}.{last component of d}{suffix}`, the way DeepElab names them; a private declaration is taken by its user name, so its last component is used. If that `_deep` does not exist, the declaration's own namespace is used (the old spelling). If both exist and differ, the entry refuses at `[proof]` and names both constants; it never picks one.
- **Soundness.** Nothing was added to the trusted base: the kernel check and the exact comparison of the registered type are unchanged. Facts of another declaration with the same last component that sit in the current namespace are not detected by name; they are refused because the proof does not check (`[proof]`), never accepted.
- **Check.** `Tests/Ved/DeepNameCheck.lean` (`lake build Tests.Ved.DeepNameCheck`): accepted, std3, exact type: facts made and used after `end A.B` with `open A.B`, from another namespace through the full name, inside `A.B`, and for a private declaration. Refused at `[proof]`: facts in both namespaces, another declaration's facts with the same last component, no `#verify_elab_deep`.
- **Not claimed.** This note makes no statement about the strict count of the fixed 327-row inventory; that count comes from a separate measurement.

## `#ved_u1` with several registers built by `Signal.loop`

Issue `sparkle-ved-u1-multiloop`. Nothing in `Sparkle/`, in `Tools/DeepElab.lean` or in the statement (`U1Stmt`, `OutputsStmt`, `ShapeCore`, `regsOf`, `st0`) changed; no unsupplied hypothesis.

- **Why not the deep route.** `#verify_elab_deep` on a copy of `synth_uartTx` (`(uartTxHW …).txLine`, four registers) stops at its preparation stage ("could not locate the top-level runCircuitH"); making it succeed means changing DeepElab. The `#ved_u1` register path is extended instead.
- **The rule.** `circuit do` with `k` registers is one `Signal.loop` over the tuple of their values (a nested `circuit do` is a second loop). `loopScriptFor` (Tools/VedU1Entry.lean) proves by induction on the cycle that register `n` of the returned module is `toNat` of the loop-state component it implements (`ved_loop_R`; components are matched to the module's registers position by position when the widths agree, else by width in order, and the kernel checks the choice). The loop at `s+1` comes from the loop at `s` (`Tools.VedU1Loop.loop_val_unfold`, a theorem: it unfolds `loopGo`, no axiom); the state is generalised to variables (`ved_loop_gen`; `Bool` components are split) and the module's step is compared with the loop's step. Closing: `simp` with the BitVec/operator lemmas, the one-bit logic rewrite (`ved_bit_simp`), `c ||| x` as `c + x` (`ved_or_lit`), reading packed fields back (`ved_pack_simp`), bounds for `^^^`/`|||`/`&&&`/`*` atoms, then `omega` (`ved_loop_close`). Every tactic is untrusted: the kernel checks the result and the stored type is compared with `==`.
- **Budget.** The kernel `addDecl` now runs under the same `withProofBudget` as the script, and the script sees `exponentiation.threshold` 4096 (384-bit registers). These raise limits only; accepted statements are unchanged.
- **Checks.** `Tests/Ved/U1MultiLoopCheck.lean` (PR CI): the ORIGINAL private declarations `synth_uartTx`, `synth_uartRx`, `synth_envByte` are accepted, the stored type is `==` `U1Stmt <decl>.ved_contract <decl>.ved_mod <decl>`, axioms within std3; refused at `[proof]`, nothing left under the base: one register's next value changed and a wrong initial value (real `synth_uartTx`), two same-width registers swapped (real `synth_envByte`), a register read one cycle late (stand-ins `lateA`/`lateB`). The other 23 rows are in `U1MultiLoopFull1`/`Full2`/`Full3` (same checks), two more rows (`synth_fp381MontMulDone`, `synth_serverFsmTxReq`, previously refused) in `U1MultiLoopFull4`, and `U1MultiLoopAll` (full CI) checks all 28 rows together (stored type, std3, exactly these 28 rows, no duplicate). What made the two rows pass: a product by a 32-bit literal in a BitVec/Nat step is commuted to `lit * x` (`ved_mul_lit_bv` / `ved_mul_lit_nat`; the kernel unfolds `x * n#w` by recursion on the literal, a 14 GiB memory blow-up with `n = 0xfffcfffd`), and the closing `split` uses the case hypotheses on the same state register so FSM tests do not multiply. Split because the one-file check was ONE Lake module of about 15 minutes (26 strict proofs of 10 to 120 s each); shared commands in `U1MultiLoopRow`.
- **Rows** at c6371d6d (28 strict): R86 R95 R97 R98 R117 R118 R124 R134 R135 R136 R138 R145 R151 R155 R156 R157 R169 R170 R190 R191 R221 R222 R225 R226 R233 R241 R244 R245 (R145 `synth_fp381MontMulDone` and R241 `synth_serverFsmTxReq` were refused at cedd324d: `omega` on the Montgomery step and an FSM case split over 8M heartbeats; both pass since c6371d6d). Not strict at c6371d6d: R109 `pidTop` (the loop is found once the Circuit-monad helpers are unfolded; the closing is then killed by the 14 GiB RSS guard during the `ved_pack_simp` stage; the goal there repeats the large error term in nested clamps, which is the suspected but unconfirmed cause of the memory growth), R141 `synth_fp2MulC0` (simp reaches the maximum recursion depth in the first loop-normalising step with the full operator-lemma set, at both 20000 and 400000; raising the limit alone does not resolve it; root cause not determined).
- **Not claimed.** One output, no memories or instances, reset held at 0: unchanged. A module whose registers are not all loop-state components (plain `Signal.register` terms outside a loop) is refused at `[proof]`. Nothing here is "327 supported" or strict-complete.
