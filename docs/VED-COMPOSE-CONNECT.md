# VED-COMPOSE-CONNECT: the returned IR's cones connected to the open parent's deep cones (small examples)

Issue `sparkle-ved-compose-connect`, branch `ved/compose-connect1` (base 425119c7 = `ved/proof-compose` 6ff184d4 + the approved
research ca892a1f).  Option `ved.compose.connect` (default `false`).  New files: `Tools/VedComposeConnect.lean`,
`Tools/VedComposeConnectGen.lean`, `Tests/Ved/ComposeConnectCheck.lean`; edited: `lakefile.lean` (four stanzas), a one-field
addition to `DeepInfo` (`Tools/VedU2HierStateArgs.lean`) and one option-gated hunk in `Tools/VedU2HierRegEntry.lean`.

## Scope (do not read more into it)

Small-example result: `multiTwo` and `multiShared` of `Tests/Ved/U2HierMultiCheck.lean` (copied into the Check).  No real-IP row
was run; the coverage stays 244/327; this is not the completion of circuit composition in general.  The statement `U2HRStmt`
is unchanged (the stored type is compared with `==`), the guarantee is that of docs/VED-MAIN-INTRO.md ("What it guarantees, and
what it does not") and docs/VED-U1-MAIN.md ("What it does not claim").  The parent's loop is still tied to the declaration by the
existing knot; the child theorem is the child's own `ved_u1`.

## What the option changes

With the option on (and `ved.compose.step` on), `scriptTextR` returns, right after the prelude of the step (`intro E hasgF hEin
hEreg hEorc`, the register/input/oracle facts `hEr`, `hlS`, `hE_`, `hEo`, `hlto`), the lines of
`Tools.VedComposeConnectGen.hlocLines` and nothing else: the chain walk, the `bundle_slice_fact` reads and the per-cone `simp`
closers are NOT emitted, so there is no old fallback in that mode.  The hkid blocks (instance arguments, child theorems,
H2/H3 wiring) are the existing ones.  Every connection logs `VED COMPOSE CONNECT: ...` (tactic `ved_connect_log`).

## Supply table: `cone_connect_bnf` (the approved `cone_connect_bn` plus the flattening step)

| hypothesis | supplied by |
|---|---|
| `hwi hri hwr` | the three `hb0.*` facts the `refine step_local` already passes |
| `hW : WOKb (declWidth m) m b0 = true` | closed, `decide +kernel`, once per `hloc` (W, returned side) |
| `hasg hEin hEreg hEorc` | the binders of `hloc` (`step_local`) |
| `hl0 : leafOk (cutNames d m b0) (inl ..) = true` | closed, `decide +kernel`, per cone |
| `hrange` (needed leaves only) | `hrangeN : ∀ y ∈ needed, E y < 2 ^ declWidth m y` proved once from the prelude facts (register: `hEr`+`hlS`, i.e. `BitVec.isLt`; data input: `hok.1 t` (`InputsOk`), the clock is not in `needed`; instance output: `hlto` from the child's output `isLt`), and `neededOk needed (inl ..) = true` (closed) per cone (R) |
| `hc` | the cone `bn (declWidth m) n2 (flat n3 (inl (Atab m b0) n e))`, never written out |

## The new lemmas (`Tools/VedComposeConnect.lean`)

* `ren_eval` (W): `evalExpr we' E' (renE τ c) = evalExpr we E c ∧ widthOf we' (renE τ c) = widthOf we c` when every leaf `x` of `c`
  has `we' (τ x) = we x` and `E' (τ x) = E x` (the two-environment versions of the research file's `*_map` lemmas).
* `tauOf`, `tabW` (closed), `tabW_sound`, `cone_deep_eval`: the leaf table `tab : List (String × Nat)` (returned name ↦ slot of the deep
  context) gives the renaming into `nm`; `tabW` checks that every leaf of the returned cone is in the table and that
  `declWidth m x` is the width of the slot in the deep context `Γr ++ Γi`; `hV` (`VOk`) is the leaf-value obligation (registers by
  `hR`, data inputs by `InputsOk` + `bit_toNat`/`bv_toNat`, oracle inputs by the definition of `Ow`: ONE cone input serves every
  instance of the class).
* `flat`, `slc`, `flat_sound`, `refs_flat`, `cone_connect_bnf`: the right-nested register bundle of the synthesiser
  (`concat [r0, concat [r1, r2]]`) is flattened (`Tools.ConcatNorm.concat_pivot`) and a slice of a slice that stays inside is composed
  (`slice_slice_val`, by `Nat.testBit`); needed because the approved `bn` resolves slices of FLAT concatenations only (this is
  what stopped `multiShared`, three registers).
* `connect_value`, `reg_connect`, `out_connect` (F): `reg_connect` concludes `Cdo.irState deep nm inp (t+1) i = E x`, `out_connect` the
  `getD 0 (evalExpr .. (compile nm deep.out))` form of `_deep_trace`; the fidelity theorem `_deep_fidelity_*` enters as an argument
  and its TYPE supplies the literal (`renE (tauOf ..) (bn ..) = L` is closed, proved by `rfl`).

## Observations

* `multiTwo`: 2 registers + the port, `multiShared`: 3 registers + the port, all by the connection lemmas; proof elaboration ~4.4 s
  (the option-off compose script ~6 s for `multiTwo`; single runs, not a measurement of anything at scale).
* The connection equation is checked by `rfl` in the elaborator (Meta `isDefEq`); the kernel then re-evaluates it.  At R193 size
  this and the `String` scans in `asgOf` are the expected costs (research §M4); nothing is claimed.

## Commits

See `git log ved/compose-connect1`.

## Batched closed checks (unit 2)

`reg_connect` takes four closed facts per register. Proving them by four `decide +kernel` / `rfl` calls per register re-evaluated the
inlined cone from a cold cache every time (observed on the kMux toy, 13 registers: ~1 s each, 48 of 81 s of the parent proof; 24 registers: 368 s).
`RegsOk` is one Bool over all register slots, evaluated once by the kernel; `regs_spec` returns each slot's four facts
(`hren` through `eqE_sound` against `CExpr.compile nm (deep.next i)`, identified with the fidelity literal by `hfid`).
The approved lemma statements are unchanged. Observed (single runs): parent proof 8/12/24 registers 19.3 / 27.1 / 64.4 s (before: 42.9 / 80.7 / 368.4 s).
Scope: local-lemma result on toys; a real-IP row (R194) was run once and is NOT accepted (budget exhausted before the connection block, see the unit report).

## Parent prelude and instance blocks (unit 3, option `ved.compose.connect`; default path unchanged)

R194 (`synth_sha512Block_done`, 34 register slots, 25 data inputs, two `kMux` instances) was refused at the 8,000,000-heartbeat budget in OLD reused
code before the connection block (unit 2 report). Attribution (script ticks; observed, single run): (a) `simp [contractOf, dataInputs, declWidth, ..] at hin`
(the 25 input bounds), 162 s of script lines 45-74, generated four times; (b) the bundle-slice chain of the first instance's hkid block, ~77-86 s;
(c) one `simp` per hypothesis (`hstA` and all 34 `hRd_i`) in the instance port lines, 55 s and 85 s.

* (a) `Tools/VedComposePrelude.lean` (new lean_lib): `hin_bnd` takes the closed equation `c.dataInputs.map (fun p => (p.name, declWidth m p.name)) = L`
  (decided by the kernel; `L` is read off the declaration table by `Tools.VedComposeConnectGen.hinLines`, it is CHECKED, not assumed) and `hok.1 t`
  and returns `bndConj (ins t) L`; `simp only [bndConj, bndConjAux, Nat.reducePow]` gives the literal conjunction the old `simp` gave.
  `bit_obs` bridges the trace theorem of a one-bit output (`(bif b then 1 else 0 : BitVec 1).toNat`) to the `Bool.toNat` the entry's `simp` leaves
  (found by R194 run 1: the `done` port; toys had 64-bit outputs).
* (c) under `connect` the port-line unfolding simps run at the loop copies (`hL..`, the hypotheses `ved_rw_loops` reads) only, not at `hstA` and the 34 `hRd_i`
  (`Tools/VedU2HierStateArgs.lean`, `portLines`); the bundle-slice chain facts use `decide +kernel` (RegEntry hunk; measured gain small).
* Not changed: (b) the chain itself (one `concat_range` + one `bundle_slice_fact` per slice step; ~1.1-1.3 s per step at 34 slots, 25 inputs), `WOKb` and `RegsOk` (kernel
  evaluations; the largest remaining costs).
* Statements unchanged (`U2HRStmt` stored type is the entry's expected type). Controls: `ComposeConnectCheck` has kernel controls for the input-bound equation
  (real list accepted, a wrong width and swapped names refused).

## Unit 4: independent post-check of R194 (`Tests/Ved/ComposeConnectR194Check.lean`, not in CI)

Runs `#ved_u2_hier`'s entry once on `synth_sha512Block_done` (`ved.compose.step` + `ved.compose.connect`) through `checkRow`
(the same function as the toys' Check) and checks, independently of the entry: stored type `==` `U2HRStmt` of the original declaration,
module/design `==` a fresh synthesis, axioms within std3, 35 connect log lines (34 `reg_connect` + 1 `out_connect` sites), the child
theorem `kMux.ved_u1` in the proof. Run (one process, guarded, ~7 min, ~18 GB):
`VED_HIER_STATS=1 python3 -I rss_guard.py 23068672 timeout 890 kjob lake env lean <abs>/Tests/Ved/ComposeConnectR194Check.lean`
after `kjob lake build Tests.Ved.ComposeConnectCheck` and `kjob lake build IP.Crypto.SHA512BlockHW`. Observed, single run: passes.

## Unit 5: heartbeat measurement and map-based closed facts (option `ved.compose.connect`; default path unchanged)

* Measurement (`Tools/VedU2HierRegEntry.lean`, env `VED_HIER_HB=1`, off by default, no budget change): `ved_hb "<script line>"` before the block-opening lines
  and one line at the end of the proof elaboration, `VED-HB <label> used=<raw> limit=<raw> permille=<..>` on stderr, with `used = IO.getNumHeartbeats -
  Core.Context.initHeartbeats` and `limit = Core.Context.maxHeartbeats` (the 8,000,000 option x 1000 = 8.0e9 raw): what the elaborator's own check compares.
  It replaces `VED_HIER_TICK`'s `ved_tick` lines when both are set.
* `WOKb`, `RegsOk`, the port cone's four facts and the bundle-slice chain evaluated list scans with `String` comparisons (`declWidth m`, `Atab m b0`,
  `needed.contains`, `tab.lookup`, `asgOf`). `Tools/VedComposeConnect.lean` (end of file) now has a name map `VT` (binary search tree on `hsh (nameKey x)`,
  the idea of `NTree` in `VedComposeOrder`; a node keeps `(nameKey, value)` pairs), `smGet_smOf : smGet (smOf l) x = l.lookup x` (from `nameKey_inj` only: the
  hash is never trusted, a bad hash can only cost time), the pointwise equalities `weF_eq`, `atabF_eq`, `asgF_eq`, `memF_setOf`, and the closed Bools
  `WOKbF` (`wokbF_sound : WOKbF m b = true -> WOKb (declWidth m) m b = true`), `RegsOkF` (`regsOkF_sound`), `specOkLe` for the port (`outSpecF_sound`) and
  `ChainOkF` (one check over all slice steps / concat ranges / element widths of an instance block; `slice_fact_F`, `concat_range_F`, `wd_F` return one step's
  facts by its index). The generator (`Tools/VedComposeConnectGen.lean`: `batchChain` reads the steps back off the chain lines, a line of another shape is left
  as it is) uses them by default; `VED_COMPOSE_NOFASTWR=1` (`DeepInfo.noFastWR`) restores the list evaluations for measurement. The statements of
  `reg_connect`, `out_connect`, `regs_spec`, `WOKb`, `RegsOk`, `bundle_slice_fact` are unchanged.
* Controls (`Tests/Ved/ComposeConnectCheck.lean`, kernel evaluation): `WOKbF` real module true, one wrong width false; `RegsOkF` real true, swapped slots / exchanged
  input wires / one register of the wrong width false; `ChainOkF` real step true, wrong offset / element index / declared width / bundle names false.
* Measured (observed, single runs): see the unit report; R194 total 427.7 s -> 217.1 s, peak 17.68 -> 9.54 GB, heartbeats 1.98e9 of 8.0e9.

## Unit 6 (R193 and next rows; observed, single run)
R193 `synth_sha512Block_out0` is accepted through the connection path (post-check `Tests/Ved/ComposeConnectR193Check.lean`, not in CI): rc 0, total 213.5 s, parent proof 107.8 s, 1.957e9 of 8.0e9 heartbeats (24.4 %), peak 9.51 GB. R246 is refused before the connection path (`genOpenSt`: the declaration is not one call of the single child, VedU2HierStGen.lean:116). R231/R232 hit the 890 s timeout inside phase 1 / deep run without reaching proof generation. Coverage is not updated.

## Unit 7 (R231/R232 stage, R246 shape; observed, single runs)
* R232 (`synth_ipv4RxHeaderOk`), run with phase marks (`Tools/VedU2HierRegEntry.lean`, `VED_HIER_PHASE_FILE`, measurement only): synthesis and phase 1 up to the child checks take well under 1 s; the time goes into the child `ipv4HeaderChecksumSig` (register-free, 68 statements): the add-stage chain route (`VedH3ChildChainEntry.buildChain`) elaborates 5.6 s and is then refused (`omega` in the prelude's `PreFacts` discharge: `ttlProto` is `0x4000 ||| (0 ++ proto)`, a `|||` that `omega` does not read); `checkCombChild` falls back to the generated script, which does not finish in the remaining ~880 s. The parent's deep run / proof / connection path are never reached. The fix belongs in `Tools/VedH3ChildChainEntry.lean` (outside this unit). R231 (same file) is consistent with this (phase 1 started, no `open:` tick) but was run without the marks.
* R246 (`(usbWebServer ..).uartTx`): one instance of the combinational child `respByteMux` (reading the `phase` register of `txSequencer`), whose byte reaches the output through the registers of the SLIP framer and UART TX. `genOpenSt` needs the declaration to BE the child's call. With `ved.compose.connect` a single instance goes through `genOpenMulti` like several (`Tools/VedU2HierRegEntry.lean`, `multi`; default path unchanged); the toy `projTx` (struct projection of a circuit whose child output feeds its registers) is accepted (`Tests/Ved/ComposeConnectCheck.lean`, `checkRow`, controls: option off refused at `[open]`, other projection refused, initial value refused). The real row is then refused in `genOpenMulti`: `usbWebServer` is several `circuit do` blocks wired outside one another, so the declaration does not reduce to ONE `runCircuitH`. A toy of two such circuits (the registers of the first are not in the open parent: `[deep]: the parent has 2 registers, the open parent's circuit has 1`) reproduces the shape; supporting it needs an open parent over all circuits' registers (a new entry shape, not a small extension).

## Unit 8: the chain route's `PreFacts` discharge, R232 and R231 (observed, single runs)
* Cause of the unit-7 refusal (found by `trace_state` at the discharge, child alone): not `|||` itself. The prelude word `0x4000 ||| (0#8 ++ proto)` contains a `concat`, whose `evalOp` mask width is `max 16 (widthOf.go (declWidth M) [const 0 8, ref proto])`; the discharge's `simp` did not unfold `widthOf.go` / `evalList` / `evalExpr.go` and did not know `declWidth M "_gen_proto" = 8`, so the goal stayed a stuck `match` and `omega` saw only the four seeds. `Tools/VedH3ChildChainEntry.lean` (what `buildChain` proves is unchanged): those three definitions in the discharge and in the `at hpre` simp; per data input `declWidth M n = w` (`decide +kernel`) as a simp fact; and for the final equality `(16384 ||| p) % 65536` (prelude, masked) = `16384 ||| p` (signal side) a once-proved `or_mod_16` (`Nat.mod_eq_of_lt`, `Nat.or_lt_two_pow`) with `input < 65536` for inputs of width <= 16. No disjoint-bit lemma was needed.
* `Tests/Ved/H3ChildCheck.lean`: `ckOr` (prelude shape, 2 stages) accepted, exact type, 3 standard axioms; `0x40FF ||| p` and `0x4001 ||| p` in the module refused at `[proof]`, no `ved_*` constant left; `ckSum`, `ckSum2`, `ckParent` and their controls unchanged.
* Rows (harness cases from the unit-7 scratch, `ved.compose.step` + `ved.compose.connect`, guard 23068672, one run each): R232 `synth_ipv4RxHeaderOk` rc 0 in 51 s wall (phase clock 37.0 s: child chain route 8.1 s, deep run 13.2 s, parent proof 10.1 s, kernel 2.0 s), 9 `reg_connect` + 1 `out_connect`, `VED U2 HIER OK`, std3; R231 `synth_ipv4RxSrcIp` rc 0 in 47 s, the same shape (34.1 s on the phase clock). Wrapper copy of R232: `Tests/Ved/ComposeConnectR232Check.lean` (NOT in CI), rc 0, 46.7 s, `compose connect OK` (type `==` `U2HRStmt`, same artifact, std3, child theorem `ipv4HeaderChecksumSig.ved_u1`). These are local real-IP-content results on wrapper copies, not fixed ledger rows; coverage is not updated.

## Unit 9: multi-circuit open parent (R246 shape) — analysis, one lemma, NOT implemented (observed; no real row run)
* What the open parent is: `genOpenMulti` (`Tools/VedU2HierMultiGen.lean`) reduces the declaration (`findRun`) to ONE `runCircuitH inits body`, replaces the child calls in `body` by oracle variables and builds `decl.ved_open xs os = runCircuitH inits body_O`, with `F2`, `Os`, `Q = Signal.loop (loopFOf inits body)` and the knot `loop_knot` (one `Signal.loop` over one `HList αs`). Phase 2 then needs `#parent IR registers = #registers of the open parent's deep circuit`.
* Why `toyTwo` (two circuits, the first's output is the child call's argument in the second) fails: the first circuit's loop occurs only inside the child call's argument, which the oracle replaces; the open parent therefore has the registers of the second circuit only (`[deep]: the parent has 2 registers, the open parent's circuit has 1`, unit-7 run). `Tools/DeepNestedState.lean` exports state theorems of closed nested loops of the open parent, but the loop is no longer in it. R246 fails earlier (`findRun`, `[open]`): a projection of a wiring of 9 circuits.
* No existing lemma/inliner step turns two wired `runCircuitH` into one over the appended state (looked at: `loop_knot`/`loop_unique`, `DeepNestedState`, `packRegister`).
* Added (lemma only, not used by any generator): `Tools/VedComposeMultiLoop.lean`, `loop_pair`: for causal `FA`, `FB` the pair `(loop FA, loop (FB (loop FA)))` is `loop (fun p => (FA p.1, FB p.1 p.2))` pointwise (kernel-checked via `loop_unique`; `kjob lake build Tools.VedComposeMultiLoop`, own lean_lib stanza). Feedback between circuits cannot be written with `let` wiring (acyclic), so it only exists with an outer loop: out of scope.
* First unsupplied proposition (toy `toyTwo`, with `αA = [BitVec 7]`, `αB = [BitVec 8]`): `∀ go, toyTwoP go = runCircuitH (αs := αA ++ αB) (initsA ++ initsB) fusedBody`, i.e. the declaration equals ONE `runCircuitH` over the appended register list with the fused body (`writes = writesA ++ writesB(ph := the A registers)`); then the existing path applies to that value. `loop_pair` gives the loop-level content; missing are (a) `packRegister (αA ++ αB) (iA ++ iB) (wA ++ wB)` against the pair of the two packs (an HList-append isomorphism lemma) plus `HListWireable`/`Inhabited` for the appended list, (b) a generator that finds the K closed `runCircuitH` in the declaration's value (`collectRC`), builds `fusedBody` from the reduced `(output, writes)` pairs and proves the equation (hcF-style causality scripts per circuit), (c) the registration order against the parent IR (`permIdx`) and the deep run of the fused value.
* Work estimate (an estimate, not measured): (a) about 0.5 unit, (b) 1 to 1.5 units, (c) 0.5 unit, R246 itself (9 circuits, K = 9 product, heartbeats/RSS unknown) a further unit. More than the ~1 unit of lemmas + generator allowed for this unit, so stopped after analysis.

## Unit 10: survey of the remaining hierarchy rows with the connection path (observed, one run each; no source change)
* Rows run once each with `ved.compose.step` + `ved.compose.connect` (harness cases, guard 23068672): all 20 are refused in 12-28 s wall (peak 2.97-3.35 GB), before any parent proof, so no heartbeat line is reached.
* Groups by first cause: (A) child with more than one output, `[hier-shape]` `connsOkS` `c.outputs.length == 1` (R184, R185, R186, R126, R127, R187, R188, R247, R248, R065: 10 rows); (B) a memory at the top, `[hier-shape]` (R040, R291, R024: 3); (C) child not a leaf (`leafBody`, depth 1 only), `[hier-shape]` (R163, R164, R067, R068: 4); singletons: R230 `[conns]` (one instance's output feeds another instance's data port), R227 `[deep]` (the open parent's port `txByte` does not export its loop state), R220 `[open]` (no call of a child in the circuit body).
* No group is small: A needs the single-output assumption removed in `connsOkS`/`connsOkS_facts` (`Tools/VedU2HierProj.lean`), `outNameOf`/`leafOut`/`instEval_leaf` (`Tools/VedU1HierComp.lean`), the H3 child table (`Tools/VedH3ChildTblEntry.lean`: `m.outputs = [⟨_, .bitVector n⟩]`) and the per-output instance/cone generation (`outPort := k.c.outputs.headD`) in `VedU2HierRegEntry`/`VedU2HierEntry`; most of these files are outside the allowed edits. Nothing implemented. Toy (refused, `[hier-shape] ... child Toy2Out.child2 has 2 outputs (multi-output children: H3)`): a `@[hardware_module]` returning a 2-field structure (`s := x + y`, `d := x - y`) and a parent using both fields.

## Unit 11: multi-output combinational leaf children, part 1 (observed; local lemmas only, NO toy accepted, no real row run)

* New file `Tools/VedComposeMultiOut.lean` (own lean_lib): `leafOutAt`, `outWrites_multi`, `instEval_leaf_multi` (the k-output instance step: `instEval` of a
  combinational leaf child with `hout : conns.filter (outputs) = ps.map (fun q => (q.1, .ref q.2))` equals `some (ps.map (fun q => (q.2, leafOutAt cm (arr cm) q.1 (xs.map env))))`),
  `instEval_leaf_of_multi` (the existing single-output `instEval_leaf` statement as the k = 1 case, control, the old lemma is untouched), `child_rel_outAt` (per-output
  child theorem for any number of outputs, from `child_rel`). Built with `kjob lake build Tools.VedComposeMultiOut`, no sorry, no new axiom.
* Blocker for the end-to-end toy (and for every multi-output row): `HierShapeS d m = true` is a conjunct of the CONCLUSION of `U2HRStmt` (and `U2HStmt`), and
  `HierShapeS` calls `connsOkS`, which contains `c.outputs.length == 1`. On `Toy2Out.top2` (child `child2`, 2 outputs) `HierShapeS d m` evaluates to `false` on the
  returned `(m, d)` (observed, scratch check, 2.68 GB rss_guard peak), so `U2HRStmt` is false for that `(m, d)`: no generator or option can prove it, and the stored type
  must equal `U2HRStmt`. Relaxing it means changing the definition `connsOkS` inside the statement (not option-gatable: it is a kernel-side `def`), re-proving its users
  (`connsOkS_facts`, `instEvalS`, `kid_inst`, ...) without `length = 1`, and a reviewer decision that the statement's shape conjunct may be weakened. Not done (statement edit
  is excluded by the brief). Generator hunks and `ved.compose.multiOut` were therefore not added (nothing could be accepted behind it).

## Unit 12: the three remaining hierarchy rows R230, R227, R220 (observed, single runs; NO row accepted, no source change kept)

* `HierShapeS d m` (`Tools/VedU2HierProj.lean:76`) evaluated on the returned `(m, d)` (scratch files, `synthesizeCombinational` + `HierShapeS`, one run each): **true** for all three (R230: children `ipv4HeaderChecksumSig`, `ipv4HeaderByte`; R227: `icmpHeaderByte`; R220: `httpGetByte`; every child single-output), so all three are in scope of `U2HRStmt`.
* R230 (`[conns]`): the checksum child's output wire feeds `_gen_chksum` of the byte child (a chain of two combinational instances inside one `circuit do`), refused by `connDiagNet` (`Tools/VedU2HierRegEntry.lean`, the `pureNetB` leaf test). Toy `ToyChain` (`mkA`, `mkB`, `outR <~ mkB (mkA ph)`) reproduces the same text. An experiment (option-gated, `ved.compose.connect`, reverted, not kept): (1) `pureNetB` leaves also include instance outputs; (2) the instance classes (`netKeyOfInst`) are keyed through instance outputs (`mkB (mkA ph)` copies: the synthesiser emits the chain twice, once for the register input and once for the let-bound names); (3) `replaceCalls` (`Tools/VedU2HierMultiGen.lean`) also replaces calls inside call arguments (innermost first) and the oracle tuple/argument constants use the real calls instead of marker applications. With (1)-(3) the toy passes `[conns]`, `[open]` (pairing, `Os`, `F2`, knot, equation all added by the kernel) and fails in `[proof]`, at the hkid branch of the second instance: the goal `E "_tmp_arg0_6" = (mkA {val := fun t => ((Q ..).val t).1}).val t |>.toNat` for the data port of `mkB` (the wire is the OUTPUT of the `mkA` instance). First unsupplied proposition: the first instance's own kid fact at the same cycle, `∀ t < K, E y_A = (obs of kidOut A) (callA ins).val t` (`y_A` the `mkA` output wire), must be available inside the second instance's port proof; it exists only as `hEo` in the later hstep branch, not as a hypothesis of a hkid branch (hkid is the thing being proved). Supplying it needs the first instance's block (`kid_inst_net` + the port lines) to be emitted as a `have` inside the second's block, recursively for chain depth, in `Tools/VedU2HierRegEntry.lean` (instance-line generator) plus a pairing of the dead copies; and every U2HierMultiGen edit forces the ~17 min `Tests.Ved.U2HierMultiCheck` rebuild. Not small (about 1 to 1.5 units, estimate); nothing kept. Diff of the experiment: kept outside the tree.
* R227 (`[deep]`): `icmpEchoResponder` is `let parsed := icmpRxParser ..` (a closed `circuit do`, 5 registers) followed by a second `circuit do` (4 registers, the child call `icmpHeaderByte`) that reads `parsed.typ/ident/seq`. The open parent's deep run does not export `_txByte_deep_state` (`Tools/VedU2HierRegEntry.lean:1182`; the state-export proof lives in `Tools/DeepElab.lean`, not editable here; not isolated, no further row run). The same shape on a toy (`ToyNest`: `let p := parser b v; circuit do ... outR <~ mux go (mkA (ph + p)) oS`) is refused one stage later with `[deep]: the parent has 3 registers, the open parent's circuit has 2`: the parser's registers are in a nested closed loop, not in the open parent's loop. That is the unit-9 shape (multi-circuit open parent): first unsupplied proposition `declaration = ONE runCircuitH over the appended register list` (see unit 9); R227 is a member of that family, not a new small gap.
* R220 (`[open]`, `Tools/VedU2HierMultiGen.lean:252`): `hftStrategy` is `let parsed := httpRequestParser ..; let emitted := httpGetEmitter ..; circuit do ..` where only `emitCount` is a register of the declaration's own circuit; the child `httpGetByte` is passed unapplied to `burstEmit` (higher order, `byteFn cntSig` inside another closed `circuit do`), so there is no saturated child call in the body that `findRun` returns. Needs the multi-circuit open parent (unit 9) AND unfolding `burstEmit` first. Not small.
* Result: no new accepted row, no wrapper post-check, no Tools/Tests change kept; `ComposeConnectCheck`/`ComposeStepCheck`/`U2HierMultiCheck`/`H3ChildCheck` not re-run (nothing they depend on changed). Coverage not updated.

## Unit 13: chained combinational instances under `ved.compose.connect` (observed, single runs; local toys accepted; R230 refused at `[deep]`)

* Hunks (all behind `ved.compose.connect`; default path unchanged): `Tools/VedU2HierRegEntry.lean`: `connDiagNet (allowInstOut)` (another instance's output is a leaf of a net), `keyNetI` (instance-class key through instance outputs, so the synthesiser's two copies of a chain get equal keys), `genOpenMulti (chain := connOn)`, and in the instance-line generator the producer instance's kid fact `hkp{p} : E y_p = obs (call_p).val t` (+ range `hlkp{p}`) is proved as a `have` inside the consumer's hkid branch by re-running the producer's own lines (so longer chains nest), added to the consumer's port/chain simp facts, with `all_goals (try rfl)` for the argument-definition form. `Tools/VedU2HierMultiGen.lean`: `replaceCalls (nested)`, `substMarks`, and the loop-body constant is `_FL` instead of `_F2` in chain mode (the derived-call stream `_F{j}` of a third call clashed with `_F2`).
* Dead duplicate chain: the synthesiser emits the chain twice; the copy is paired with the same calls (equal keys) and gets its own hkid branches (each embeds its own producer). It adds no register and does not change the statement or the artifact.
* `ToyChain` (2-chain), a 3-chain `chain3Tx`, and `chainMixTx` (consumer with a register-derived net, the producer's output and a register port; struct output) are accepted with step+connect (`ComposeConnectCheck`: stored type `==` U2HRStmt, same artifact, std3, kernel, every child theorem occurs, only connection lemmas). Controls refused: wrong wiring (`[kernel]`), instance mix-up (`[proof]`), width mismatch on the chained port (`[hier-shape]`), option off (`[conns]`, "another instance's output").
* R230 wrapper-case copy, step+connect: passes `[conns]` and `[open]`, then is refused at `[deep]`: "the port headerByte of the open parent did not export its loop state" (43.7 s, rss_guard peak 4.09 GB; the second run, with `VED_HIER_DEBUG`, identical). The deep run itself reports `headerByte ... PROVEN via Cdo.elab_general (5 registers, 7 inputs)`, but `<open>_headerByte_deep_state` is absent. Cause (toys): the declaration's own port is directly a child's output (`headerByte := byteOut`), so its cone reads no register; the same `[deep]` refusal occurs for ONE non-chained instance (`ToyChainR3`), and not when the port reads a register (`ToyChainR2`). It is a limit of the deep route's state export (`ved_have_export` in `Tools/DeepElab.lean`, not editable here), independent of the chain.

## Unit 14: a declaration port that is directly a child's output (option `sparkle.deepExportState`; observed, single runs)

* Cause (`Tools/DeepElab.lean`, capstone of a port): the port is a bare input of the deep circuit, so `congr 1` closes the goal by `rfl`; and if it were split, the big `simp only [outFOf, ..]` removes the loop from the goal (the output ignores the state), so `topProof`'s `generalize` matches no loop and `ved_have_export` never runs (no `_deep_state`).
* Fix (option `sparkle.deepExportState`, default false, set by hand next to step+connect): `congr 1` becomes `first | refine congrArg BitVec.toNat ?_ | congr 1`; the tail is `first | (bigSimp; ved_has_loop; ..; topProof) | routeB`, routeB = state export (same `ved_have_export` of the top loop) BEFORE the simp, then the output side. A goal that keeps the loop takes the old route. Option off: the same tactic text as before. No statement changes.
* Toys with option on: ToyChainR3, ToyChainR, ToyChainR2 accepted; `ComposeConnectCheck` appends `direct1Tx`, `direct2Tx` (accepted: type `==`, same artifact, std3, kernel, child theorems, reg_connect/out_connect, no fallback) and 3 controls (option off: old `[deep]` text; wrong child output wiring: `[proof]`; wrong width: `[hier-shape]`).
* R230 wrapper copy (step+connect+option): accepted; local result `Tests/Ved/ComposeConnectR230Check.lean` (wrapper copy, not CI, not a ledger row): 5 reg_connect + 1 out_connect, both child theorems, std3, type `==`.

## Unit 15: `U2HRStmtK`, a separate statement for children with k >= 1 outputs (CANDIDATE, not reviewed; observed, single runs)

* User decision 2026-11-23 (option 3): `U2HRStmt` and everything it unfolds to are unchanged. New file `Tools/VedU2HierMultiOut.lean` (own stanza): `connsOkK` (= `connsOkS` with `1 <= c.outputs.length`, plus distinct output port names and distinct output parent wires; "every port connected" and "every connection a plain wire of the port's width" are the existing clauses, so no output is dropped), `HierShapeK` (= `HierShapeS` with `connsOkK`), `U2HRStmtK` (= `U2HRStmt` with `HierShapeK d m = true`; every other conjunct is the SAME definition: none of them mentions a child's output count, `instEvalS`/`outWrites`/`wrH` already write every connected output). Statement committed alone (0ffcc7d2), `Tests/Ved/MultiOutCheck.lean` prints it.
* Proved, no new axiom (`propext`, `Quot.sound` only): `HierShapeK_of_S`, `U2HRStmtK_of_U2HRStmt` (no hypothesis), `HierShapeS_of_K` and `U2HRStmtK_iff` (iff when every module of the design has exactly one output).
* Kernel chain for `HierShapeK`: the length-1 fact is destructured and never used in `stepHS_succ`, `runHS_exists`, `runHS_proj(_aux)`, `runHS_child_clkRst`, `kid_inst`, `kid_inst_net`, `kid_step`, `outputsOnHS_of_stepR(K)`, so they are textual copies with `HierShapeK` (names `*_multi`, `connsOkK_facts` has the same tuple with `1 <= length`). Built. Existing theorems untouched.
* Option `ved.compose.multiOut` (default false; registered in `Tools/VedU2HierMultiOut.lean`): one gated hunk in `Tools/VedU2HierRegEntry.lean`, the `[hier-shape]` stage uses `hierDiagK`/`HierShapeK`. Off = the previous code path and text.
* First unsupplied proposition for the end-to-end toy (observed): with the option on, a real 2-output child (`child2 : P2 dom`, a structure result; the synthesiser instantiates only structure-returning `@[hardware_module]`s, a tuple result is inlined, `[scope]: no child instance`) passes `[hier-shape]` and is refused at `[child]`: `ved_table%: P2 defaultDomain is not a Signal defaultDomain _ (v1: Signal binders only)` (`readTableOfType`, `Tools/VedU1Contract.lean:200`). So the CHILD's own theorem for a structure-valued declaration does not exist: a `DeclTable` has `Ty = InTy ins (Signal out.val)`, so `U1Stmt (contractOf tbl [s, d] ..) child2 g` with `g := child2` is not even well-typed; it needs a wrapper `g = fun xs => bundle2 (child2 xs).s (child2 xs).d` (as the product-result entry does with `.1/.2`) plus a struct-result U1/H3 entry (`Tools/VedU1Entry.lean`, `Tools/VedH3ChildEntry.lean`: not in this unit's edit list), then `Kid` with k outputs (`outPort := k.c.outputs.headD`, `contractOf .. ["out"]` in `Tools/VedU2HierRegEntry.lean`), the instance model of `genOpenMulti` (one call and one wire `y` per instance) and the parent's open elaboration of `(child2 a b).s`/`.d` projections. Not small; nothing of it attempted.
* Checks (`Tests/Ved/MultiOutCheck.lean`, `kjob lake build` rc 0): on the real designs of `top2` (child 2 outputs) and `top3` (child 3 outputs, parent reads two): `HierShapeS = false`, `HierShapeK = true`. Controls on an edited `(m, d)`: output not connected, two outputs on one wire, an unknown wire: `HierShapeK = false` and the entry refuses at `[hier-shape]` with the matching text under the option; option off: `[hier-shape] ... has 2 outputs (multi-output children: H3)` (previous text). Swapping two same-width outputs in the parent's use stays `HierShapeK = true`: that is not a shape property, only a proof can refuse it (no proof route exists yet, so this control is NOT run).
* Not done: accepted toy, 3-output toy acceptance, independent probe of an accepted theorem, R065 (not run, steps 5-6 not passed). No ledger row, coverage not updated.

## Unit 16: the 2-output STRUCT child end to end under `ved.compose.multiOut` (observed, single runs; `U2HRStmtK` is still an unreviewed candidate)

* Child theorem (struct route, nothing new trusted): with the option on, a child whose table the Signal reader refuses (a structure result) is read through `Tools.VedU1StructOut.stmtOfStruct` (the `#ved_u1_struct` reader: statement `fun xs => bundle2 (D xs).f1 (bundle2 (D xs).f2 ..)` over the ORIGINAL declaration, output ports = field names) and proved by `checkU1E cdecl base cstmt cm .generated names` on the design's own child module: the standard checker, the same call `vedU1EntryOn` makes. The bundle lambda is stored as `<child>.ved_bundle`; the parent's proof applies `kid_inst(_net)_multi` / `kid_step_multi` to it. The kernel chain already speaks per output port (`∀ q ∈ c.outputs, ∃ x, lookup q.name = ref x ∧ E x = srcOf ck g .. q.name t`); `child_rel_outAt` (0add884c/6320020b, unreviewed) is NOT used.
* Parent, hunks (all gated by the option; `Tools/VedU2HierRegEntry.lean`: child stage, `kON` output names, `ved_bundle`, `multi` forced for a multi-output child, per-output instance branches (`rcases` over `y = y1 ∨ y = y2`, oracle `if y = y_o then obs ((call).field_o).val t`), `_multi` lemma names, `HierShapeK`, expected statement `U2HRStmtK`; `Tools/VedU2HierMultiGen.lean`: `genOpenMulti (multiOutOn)`: a structure-valued call gets ONE free Signal oracle per field (the open parent keeps Signal parameters; the call in the body is the constructor applied to them, `reduceCtorProjs` removes `P2.s (P2.mk ..)`), `Os`/E/hcO over the leaves, `_FL` names; `Tools/VedU2HierEntry.lean`: `CallInfo.leaf/proj`; `Tools/VedU2HierStateArgs.lean`: `DeepInfo.multiOut`).
* Not supported (stated, not hidden): the `ved.compose.step` fast path is switched off for a design with a multi-output child (the old per-cone H3-open script proves it), `connect` producers that are multi-output are not generated, nested structure results, a 1-field structure.
* `Tests/Ved/MultiOutCheck.lean`: `top2` (outputs s, d, both read), `top3` (3 outputs, two read) and `top2m` accepted (stored type `==` `U2HRStmtK` of the original declaration, same artifact, std3, kernel, no `sorryAx`, child theorem constant occurs). Controls: the same-width swap passes the shape and is refused at `[proof]`; an output missing `[hier-shape]`; wrong wiring `[order]`; option off the old `[hier-shape]` text; nothing left behind. `Tests/Ved/MultiOutProbe.lean` (own stanza) is an independent probe (its own toy, the standard `#ved_u2_hier`, plain environment inspection).

## Unit 17: survey of the 10 group-A rows; the sequential struct child (observed, single runs; `U2HRStmtK` is still an unreviewed candidate)

* Survey (no `#ved_*` entry run; `synthesizeCombinational` of each case copy + a scratch evaluator, one lean process per row, rss_guard peak 1.7 to 3.1 GB): the returned `(m, d)` of R065 (`mesh2x2`): parent registers 0 (entry `checkU2H`, `U2HStmt`), 4 instances of ONE child `pe` (2 outputs, 2 registers), 4 chain edges (an instance output feeds another instance), `HierShapeS` false, `HierShapeK` true. R126 (`synth_signCore`) and R184 (`synth_p256SignCore`): parent registers 73 (`checkU2HR`), 8 instances of 6 children (`wSign` 15 outputs/13 registers, `wMul` 2/5, `wPointOp` 7/26, `wScalarMul` 12/14, `wInv` 5/6, `wMulN` 2/5, all leaf), 5 chain edges, `HierShapeS` false, `HierShapeK` true. R127, R185, R186, R187, R188, R247, R248: `d.modules` also holds NON-leaf modules (`wSignCore`; `wKeccakF`/`wSponge`; `wBlock`/`wSha256`), `HierShapeK` false (the nested group B, outside this unit).
* Chosen group: {R126, R184} (the only rows with a register parent and `HierShapeK` true, so no new statement is needed); R065 is the only register-free row and needs a statement for it (below, proposal only).
* Sequential struct child, child theorem: `Tests/Ved/MultiOutCheck.lean` (`kidr`, `{ s := reg, d := reg - y }`, one register): the entry's own call (`stmtOfStruct` of the declaration, `checkU1E ... .generated names` on the design's child module) yields a `U1Stmt` theorem over a module with a register, std3, no `sorryAx`; `Tests/Ved/MultiOutProbe.lean` does the same with the standard `#ved_u1 kidSeq` and plain environment inspection. So the struct entry's rule and the loop script for a bundled statement already cover a child with registers (no change was needed there).
* The PARENT over such a child is refused (pinned in the Check, nothing left behind, option on): (a) child input read from the parent's register (`topr0`): `[conns]`, `connDiagNet` allows a parent register leaf only for a combinational child (`allowRegs := (regsOf cm.body).isEmpty`, `Tools/VedU2HierRegEntry.lean`); (b) child input read from parent DATA inputs only (`topr`): with the gated hunk (`useState` also holds for a design with a multi-output child) the child stage and the open parent pass and the proof is refused at `[proof]`: `asgOnly <child>.ved_mod.body = true` is false, i.e. `kid_step_multi` (as `kid_step`) has `hcomb : asgOnly c.body = true`, a PER-CYCLE step for a combinational child.
* First unsupplied proposition (for R126/R184 and every sequential child under H3-open): a causality link between the open parent's oracle and the child's stream, e.g. `theorem srcOf_prefix (hU : U1Stmt ck c g) (I1 I2 : Nat → String → Nat) (hok1 : InputsOk ck c I1) (hok2 : InputsOk ck c I2) (t : Nat) (h : ∀ t' ≤ t, ∀ n, I1 t' n = I2 t' n) : ∀ q ∈ ck.outputs, srcOf ck g I1 q t = srcOf ck g I2 q t` (the child's output at `t` depends on its inputs up to `t`; from `hU`'s run theorem and the prefix property of `runModule`), then a strong induction over `t` in the generated parent script: the oracle of a sequential call at `t` is the IR instance output (`kid_inst_net_multi` gives it for the whole run, `hrunF` with `F t p = E_t(x_p)`), and the call `(child args).val t` equals it by `srcOf_prefix` once the loop-state arguments agree up to `t`. `connDiagNet` (register-fed sequential child) and a per-instance chain keyed by (instance, OUTPUT PORT) instead of `keyNetI` (reviewer note: `keyNetI` assumes single-output instances; control: two outputs of one instance feeding different consumers) come on top for the 5 chain edges. Not small; nothing of it attempted.
* Proposal only, NOT added (a new trusted statement needs its own review): for R065's register-free parent,
  `def U2HStmtK (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop := CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeK d m = true ∧ regsOf m.body = [] ∧ WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧ (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f`, i.e. `U2HStmt` (`Tools/VedU2HierStmt.lean:48`) with `HierShapeS` replaced by `HierShapeK`; with `U2HStmtK_of_U2HStmt` (no hypothesis) and `U2HStmtK_iff` (all modules single-output), proved like the `U2HRStmtK` ones. R065 would also need a sequential struct child (`pe`, 2 registers) fed through instance outputs, so the same proposition above applies in its closed-term form (no parent state, hence no induction, only `kid_inst_net_multi` with `F` the real stream).

## Unit 18: a parent with registers over SEQUENTIAL multi-output struct children (observed, single runs; `U2HRStmtK` is still an unreviewed candidate)

How the single-output path treats a sequential child (read, then lifted):

* An instance's proof block is one of three kinds (`Tools/VedU2HierRegEntry.lean`, instance-line generator): all data ports are parent data inputs (`kid_inst`, whole run, any child); a net over the data inputs only (`kid_inst_net`, a total stream `F`, `hrunF` over the whole run); a port that reads parent REGISTERS (`stateArg`, `kid_step`: one cycle, `hcomb`, a child of assignments only). Under `ved.compose.multiOut` every instance of a design with a multi-output child is `stateArg`.
* The composition `outputsOnHS_of_stepRK` (`VedU2HierState.lean`) is ONE induction over the cycles; `hkid` is asked at cycle `t` under the invariant at `t` only. There was no strong induction and no causality of a child: the three combinational-only places were `connDiagNet` (`allowRegs`), `kid_step` and the Signal-level `hOs` (the oracle read at the same cycle only, by unfolding the child).

What is added (all additive or gated by `ved.compose.multiOut`; the default path is textually unchanged, `U2HRStmtK`/`connsOkK`/`HierShapeK` untouched):

* `Tools/VedU2HierMultiOut.lean`:
  - `runModule_prefix`: the first `k` cycles of a successful `k + n`-cycle run are the `k`-cycle run under the shifted seed.
  - `srcOf_prefix (hU : U1Stmt ck c g) (I1 I2) (hok1 : InputsOk ck c I1) (hok2 : InputsOk ck c I2) (t) (h : ∀ t' ≤ t, ∀ n, I1 t' n = I2 t' n) : ∀ q ∈ ck.outputs, srcOf ck g I1 q.name t = srcOf ck g I2 q.name t` (causality of the child from its own theorem; `runModule_congr_seed` at `K = t + 1`, no new assumption).
  - `kid_seq_multi`: `kid_inst_net_multi` at ONE cycle `t0` for a sequential child; `hrunF` only for the cycles `s ≤ t0` (`F` a total stream in range); the child's run is cut at `t0 + 1` cycles (`runModule_prefix`) and the child's theorem is applied at `K0 = t0 + 1`.
  - `outputsOnHS_of_stepRKH_multi`: `outputsOnHS_of_stepRK_multi` whose `hkid` also receives the invariant at every earlier cycle (the `chain` induction strengthened to the history); same conclusion.
  - `call_causal`, `bundle_causal`, `bundle_causal_agree`, `ArgsAgree`: the same causality for a CALL on signals (reusing `ArgSigs`/`obsArgs`/`applyArgs`/`streamOf`/`applyIns_streamOf` of `Tools/VedU1HierComp.lean`): two argument tuples that agree at every cycle `k ≤ i` give the same result VALUE at `i`.
* `Tools/VedU2HierMultiGen.lean` (`hOs`): for a call of a sequential struct-valued child, each leaf is proved from the child's own theorem (`bundle_causal_agree`), the arguments' agreement at `k ≤ i` by the earlier chained leaf lemma or by evaluation at `k`; the old unfolding route stays for the other leaves.
* `Tools/VedU2HierRegEntry.lean`: `connDiagNet` allows register leaves for a multi-output child; `isSeqK` instances use `outputsOnHS_of_stepRKH_multi`, `hrunF0` (the port facts at a GENERAL cycle) and `hrunF` over `s ≤ t` from the history, then `kid_seq_multi`; chained producers (option `ved.compose.connect`) give ONE fact per output port (`hkp{instance}_{port}`), proved inside `hrunF0` for a sequential consumer; `keyNetI` takes `portKey := mo` so two outputs of one instance are two nets (the key names the output port; unchanged for single-output instances).

Checks (`Tests/Ved/MultiOutCheck.lean`, `MultiOutProbe.lean`): `topr0` (child input = the parent's register), `topr` (parent data inputs), `topb` (two instances, the second reads an output of the first), `topc` (one instance, its two outputs feed two different consumers) are accepted with the stored type `==` `U2HRStmtK c m d top`, the same artifact, std3, the kernel and the child theorem constant used; controls refused (same-width swap `[proof]`, output missing `[hier-shape]`, wrong wiring `[order]`, the producer's two outputs swapped between the consumers of `topc` `[proof]`, the consumer of `topb` reading the other output `[proof]`, option off the old `[hier-shape]` text). The unit-3 pinned refusals of `topr`/`topr0` are replaced by these acceptances. Probe: `PROBE SEQ PARENT OK`.

Not claimed: a real row is not a fixed ledger row; nested (non-leaf) children and the register-free parent (`U2HStmtK`, unit 17 proposal) are still outside; the `ved.compose.step` fast path is off for a multi-output design.

Real row R184 (`synth_p256SignCore`), case copy ONCE with `ved.compose.step`, `ved.compose.connect` and `ved.compose.multiOut` (observed, single run, not a ledger row, coverage not updated): refused at `[child]`: `child Sparkle.IP.Crypto.P256SignDemo.wMul: VED U1 REFUSED ... wMul [proof]: errors were logged while elaborating the proof; first: ved_ss_R: no invariant mvar ?R in the goal` (the CHILD theorem of the 5-register multiplier wrapper through the struct route `checkU1E ... .generated`; the parent's own steps of this unit were not reached). rc 1, wall 375 s, rss_guard TOTAL peak 10.0 GB (largest child maxrss not measured). Scratch toys of the same shape (a scaled and a full-width (258/256/9 bit) copy of `mulHW`, a wrapper over it, a parent over the wrapper with a 256-bit register) are accepted (child by `#ved_u1_struct`, parent by `checkU2HR` under the option), so the refusal is not the widths, the operators or the wrapper form; the first unsupplied proposition for R184/R126 is the struct-route child theorem (`U1Stmt`) of `wMul`, outside this unit's files (`Tools/VedU1StructSeq*.lean`).

## Unit 19: the child theorems of R184, one by one (observed, single runs; not a ledger row; coverage not updated)

Each child of `synth_p256SignCore` through the entry's own call (`stmtOfStruct` + `checkU1E ... .generated` on the design's child module), parent-free, guard 23068672 kB:

| child | registers | outputs | result | wall | rss_guard total peak |
|---|---|---|---|---|---|
| wMul | 5 | 2 | accepted | 52 s | 4.0 GB |
| wMulN | 5 | 2 | accepted | 53 s | 4.0 GB |
| wInv | 6 | 5 | accepted | 57 s | 4.2 GB |
| wSign | 13 | 15 | accepted | 344 s | 10.0 GB |
| wScalarMul | 14 | 12 | refused `[proof]`: 8,000,000-thousand heartbeats exhausted in the closing stage | 543 s | 11.4 GB |
| wPointOp | 26 | 7 | killed by the guard (23.1 GB) in the kernel `decide` of `OrderOk` (560 statements) | 85 s | > 23 GB |

The refusal of `wMul` in the R184 parent run (`ved_ss_R: no invariant mvar ?R`) was NOT a property of `wMul` (accepted alone, and after `wSign` in a separate command) and not the heartbeat budget (0.54M of 8M used): the parent's child loop is one `TermElabM`, the struct sequential script names its holes `?R ?h0 ?hstep`, and `?x` of an already used user name denotes the existing (assigned) mvar, so the second struct child with registers found no `?R`. Under `ved.compose.multiOut` each child is now checked in a fresh metavariable context (restored afterwards; statement term instantiated first; no budget change, no `VedU1StructSeq*` change). Check: `Tests/Ved/MultiOutCheck.lean` toy `topq` (two different sequential struct children) is accepted; the control pins the old refusal when the two checks share one context.

Still open for R126/R184: `wScalarMul` (closing stage over budget) and `wPointOp` (leaf `OrderOk` has no fast kernel check; `OrderOkFast` exists only for the parent's `OrderOkHS`). R184 was not re-run (not every child is accepted).
