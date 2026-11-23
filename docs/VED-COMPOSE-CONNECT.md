# VED-COMPOSE-CONNECT: the returned IR's cones connected to the open parent's deep cones (small examples)

Issue `sparkle-ved-compose-connect`, branch `ved/compose-connect1` (base 425119c7 = `ved/proof-compose` 6ff184d4 + the approved
research ca892a1f).  Option `ved.compose.connect` (default `false`).  New files: `Tools/VedComposeConnect.lean`,
`Tools/VedComposeConnectGen.lean`, `Tests/Ved/ComposeConnectCheck.lean`; edited: `lakefile.lean` (four stanzas), a one-field
addition to `DeepInfo` (`Tools/VedU2HierStateArgs.lean`) and one option-gated hunk in `Tools/VedU2HierRegEntry.lean`.

## Scope (do not read more into it)

Small-example result: `multiTwo` and `multiShared` of `Tests/Ved/U2HierMultiCheck.lean` (copied into the Check).  At the time of unit 1 no real-IP row
was run (later units: R194/R193 wrapper copies, see below); the coverage stays 244/327; this is not the completion of circuit composition in general.  The statement `U2HRStmt`
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
Scope: local-lemma result on toys; a real-IP row (R194) was run once and was NOT accepted at that time (unit 2; budget exhausted before the connection block, see the unit report; accepted in unit 3).

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
(the same function as the toys' Check) and checks, independently of the entry: stored type `==` `U2HRStmt` of the declaration in the Check (a copy of the test file's private wrapper, run as `_private._stdin.0.*`; not the fixed inventory constant itself),
module/design `==` a fresh synthesis of that copy, axioms within std3, 35 connect log lines (34 `reg_connect` + 1 `out_connect` sites), the child
theorem `kMux.ved_u1` in the proof. Run (one process, guarded; unit-4 measurement ~7 min, ~18 GB, unit 5: ~3.6 min, ~9.5 GB):
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

## Scope correction (review of 14129475)

The R193/R194 Checks run a COPY of the private wrapper of `Tests/IP/Crypto/SHA512BlockHWTest.lean` (wrapper text equal after whitespace normalisation, IP body imported); the executed names are `_private._stdin.0.*`, not the fixed inventory constants, and "same artifact" compares with a re-synthesis of that copy. They are local real-IP-content results, not success of the fixed ledger rows; row success needs the standard harness on the original source scope.

## Unit 7 (R231/R232 stage, R246 shape; observed, single runs)
* R232 (`synth_ipv4RxHeaderOk`), run with phase marks (`Tools/VedU2HierRegEntry.lean`, `VED_HIER_PHASE_FILE`, measurement only): synthesis and phase 1 up to the child checks take well under 1 s; the time goes into the child `ipv4HeaderChecksumSig` (register-free, 68 statements): the add-stage chain route (`VedH3ChildChainEntry.buildChain`) elaborates 5.6 s and is then refused (`omega` in the prelude's `PreFacts` discharge: `ttlProto` is `0x4000 ||| (0 ++ proto)`, a `|||` that `omega` does not read); `checkCombChild` falls back to the generated script, which does not finish in the remaining ~880 s. The parent's deep run / proof / connection path are never reached. The fix belongs in `Tools/VedH3ChildChainEntry.lean` (outside this unit). R231 (same file) is consistent with this (phase 1 started, no `open:` tick) but was run without the marks.
* R246 (`(usbWebServer ..).uartTx`): one instance of the combinational child `respByteMux` (reading the `phase` register of `txSequencer`), whose byte reaches the output through the registers of the SLIP framer and UART TX. `genOpenSt` needs the declaration to BE the child's call. With `ved.compose.connect` a single instance goes through `genOpenMulti` like several (`Tools/VedU2HierRegEntry.lean`, `multi`; default path unchanged); the toy `projTx` (struct projection of a circuit whose child output feeds its registers) is accepted (`Tests/Ved/ComposeConnectCheck.lean`, `checkRow`, controls: option off refused at `[open]`, the declaration of the other field (a different width) against `projTx`'s module refused at `[artifact]` (not a same-width wrong projection refused by the new path's proof), initial value refused). The real row is then refused in `genOpenMulti`: `usbWebServer` is several `circuit do` blocks wired outside one another, so the declaration does not reduce to ONE `runCircuitH`. A toy of two such circuits (the registers of the first are not in the open parent: `[deep]: the parent has 2 registers, the open parent's circuit has 1`) reproduces the shape; supporting it needs an open parent over all circuits' registers (a new entry shape, not a small extension).

## Unit 8: the chain route's `PreFacts` discharge, R232 and R231 (observed, single runs)
* Cause of the unit-7 refusal (found by `trace_state` at the discharge, child alone): not `|||` itself. The prelude word `0x4000 ||| (0#8 ++ proto)` contains a `concat`, whose `evalOp` mask width is `max 16 (widthOf.go (declWidth M) [const 0 8, ref proto])`; the discharge's `simp` did not unfold `widthOf.go` / `evalList` / `evalExpr.go` and did not know `declWidth M "_gen_proto" = 8`, so the goal stayed a stuck `match` and `omega` saw only the four seeds. `Tools/VedH3ChildChainEntry.lean` (what `buildChain` proves is unchanged): those three definitions in the discharge and in the `at hpre` simp; per data input `declWidth M n = w` (`decide +kernel`) as a simp fact; and for the final equality `(16384 ||| p) % 65536` (prelude, masked) = `16384 ||| p` (signal side) a once-proved `or_mod_16` (`Nat.mod_eq_of_lt`, `Nat.or_lt_two_pow`) with `input < 65536` for inputs of width <= 16. No disjoint-bit lemma was needed.
* `Tests/Ved/H3ChildCheck.lean`: `ckOr` (prelude shape, 2 stages) accepted, exact type, 3 standard axioms; `0x40FF ||| p` and `0x4001 ||| p` in the module refused at `[proof]`, no `ved_*` constant left; `ckSum`, `ckSum2`, `ckParent` and their controls unchanged.
* Rows (harness cases from the unit-7 scratch, `ved.compose.step` + `ved.compose.connect`, guard 23068672, one run each): R232 `synth_ipv4RxHeaderOk` rc 0 in 51 s wall (phase clock 37.0 s: child chain route 8.1 s, deep run 13.2 s, parent proof 10.1 s, kernel 2.0 s), 9 `reg_connect` + 1 `out_connect`, `VED U2 HIER OK`, std3; R231 `synth_ipv4RxSrcIp` rc 0 in 47 s, the same shape (34.1 s on the phase clock). Wrapper copy of R232: `Tests/Ved/ComposeConnectR232Check.lean` (NOT in CI), rc 0, 46.7 s, `compose connect OK` (type `==` `U2HRStmt`, same artifact, std3, child theorem `ipv4HeaderChecksumSig.ved_u1`). These are local real-IP-content results on wrapper copies, not fixed ledger rows; coverage is not updated.
