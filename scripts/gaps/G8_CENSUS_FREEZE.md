# G8 class-coverage census: frozen plan (measurement only)

Issue `sparkle-gaps-g8-measure` (milestone `sparkle-gaps`).
- **Base:** `poc/roundtrip-proof` eb5099faed3125636e9ba473a82f28288877379f.
- **Branch:** `par/g8-measure`.
- **Purpose:** the gap table's G8 row (docs/ShippingCompiler-Gaps-2026-10-28.md) reads "corpus coverage: UNMEASURED". This
  unit measures an UPPER BOUND on the number of constants of the 459 frozen corpus modules (universe `U`, Amendment 1) that can be the `top` of a member of
  `MemSharedLeafParent` (C4) or `QSharedLeafParent` (C5). It records why the others are excluded.
- **Changes:** no compiler, production or existing-test change. No new theorem.
- **In poc (sparkle-gaps-g8-int):** files 1, 2 and 4 below. The corpus chunks (file 3) stay on `par/g8-measure`
  0cf85531; result: scripts/gaps/G8_CENSUS_RESULT.md.

## What is measured, and why it is only an upper bound
A class member `P` has `P.top.decl = f`. The theorem's binder `entry : MachineDefines … P.top.decl P.top.d.shape`
(Tools.ShippingMachineEntry.MachineDefines) ties `P.top.d.shape` to the shape the compiler reads for `f`.
- **The test:** T0 evaluates, on the shape that `Tools.ShippingMachineCommand.readMachine` returns for `f` and for its
  callees, a list of conditions. Each condition is IMPLIED by a cited class field. That is the same reader the generators
  use to produce `f.machineData` (Tools/ShippingMachineCommand.lean:440; `generateCore` :2515-2522).
- **What a result means:**
  - **T0 FAIL** ⇒ `f` is not the top of any member, as long as the shape tie above holds.
  - **T0 PASS** ⇒ `f` is only a CANDIDATE. The remaining fields are not evaluated:
    - the data checks that need the full MachineData or chosen tables;
    - the GEN-SHAPE fields;
    - `group : QuadGroupFacts`, a structural Prop that is not decidable.
- **Reporting:** results are reported as "T0-eligible, member modulo the unevaluated fields", never as members.
- **Implementation review:** for each condition, the implementation review checks that it really is implied by the cited
  field.

## T0 conditions (frozen; evaluated in this order; the first failure is the reason)
Notation: `S` = `readMachine f` shape, `insts`/`instTagged`/`instFields`/`layout` its fields, `originAt` =
`Tools.ShippingInstTagged.originAt`.

**Common to both classes (the fields are identical in CDefTest.lean:81-92 and QDefTest.lean:132-143):**
- **R0:** `readMachine f` succeeds (the class's `top : GenPkg` with its MachineData comes from the generator on `f`).
- **P1:** `layout.slots ≠ []`. Field `slotsNe` (CDefTest:88, QDefTest:139).
- **P2:** `insts ≠ []` and `instFields ≠ []`. Field `pdata.insts_ne`, `pdata.fne` (Tools/ShippingNmEntry.lean:109-110).
- **P3:** every `x ∈ instTagged` has `x.2.child? = none` and `memChild? x.1 = none`. Field `noMem` (CDefTest:87,
  QDefTest:138) and `pdata.child` (NmEntry:112).
- **P4:** `instTagged.map (·.1)` has even length, and entries `2i` and `2i+1` are equal. The wrapper list `Ws` is the list of
  entries `2i`, in order. Field `pdata.names` (NmEntry:111): `= cs.flatMap (fun e => [e.c, e.c])`. `tieCs`
  (CDefTest:166, QDefTest:167) fixes the order of the wrapper declarations.
- **R1:** `readMachine w` succeeds for every `w ∈ Ws`. The wrappers are `GenPkg`s whose `.decl = w`, through `tieCs`/`tieCallee`.

**M (C4) only:**
- **M1:** every `w ∈ Ws` has `insts ≠ []`, and all call-entry names of all wrappers are ONE name `L`. Fields `tieLeaf`
  (CDefTest:108) and `wKids` (:140, `(w.insts[k]).1 = leaf.decl`).
- **M2:** every wrapper entry has `(originAt w k).child? = none`. Field `wAllOrd` (:142).
- **M3:** `readMachine L` succeeds, and every entry `k` of `L` has `(originAt L k).child?.isSome`. Fields `leaf` (a
  `GenPkg` on `L`) and `leafAllMem` (:123).

**Q (C5) only:**
- **Q1:** for every `w ∈ Ws`, every `x ∈ w.instTagged` has `x.1 = L` or `x.1 = memChildName cb aw dw`, for one non-memory
  name `L` shared by all wrappers and per-wrapper constants `(cb, aw, dw)`. Field `tags` (QDefTest:93) for each wrapper,
  whose `L` is the class's single `leaf` (`QWrapper leaf`, :152).
  - If no wrapper calls a non-memory name, `L` is unconstrained by the shape. The row then reads `Q1-noleafcall`, and Q2/Q3
    are skipped. It counts as T0-eligible only with that flag shown.
- **Q2:** `readMachine L` succeeds, and `L`'s `insts = []`. Fields `leafData.insts` (Tools/ShippingQuadLeafGeneric.lean:56).
- **Q3:** `memChild? L = none`. Field `leafNoMem` (QDefTest:149).

Every condition is a Bool computed in MetaM from `Read.shape`. No kernel evaluation, no `decide`.

## Candidates and corpus
- **Corpus files:** the files of `scripts/shipping-coverage/run.sh:25` (its synthesis-command grep over Tests, IP and
  Examples) at eb5099fa: 462 files.
- **Corpus modules:** frozen in `scripts/gaps/G8_CORPUS_MODULES.txt`, 459 lake modules, SHA-256
  `810c4b624b09c2dd2189a07262042d4cc047e3d4dda092f14934e80e5162ceb0`.
  - 312 of them are `Tests.Compiler.*`.
- **Not lake modules:** `scripts/gaps/G8_NOLIB_MODULES.txt` (3 `Examples.*` files, SHA-256 `8afb78e2…bd20`). They are reported as
  UNMEASURED.
- **Amendment 1 (review be6e7ea5): measurement universe.**
  - **Definition:** `U` = every constant `c` with `env.getModuleIdxFor? c` equal to one of the 459 frozen corpus modules.
    There is NO name filter: internal names, `match_`/`proof_`/`eq_`/`sizeOf`/`inst`, generated marks and `_regen`/`_gap`
    are all kept. `Tools.ShippingCorpusSweep.candidates` is NOT used, because the class fields do not exclude those names
    from `top.decl`.
  - **Constants of kind `defnInfo`** are evaluated (R0 onwards).
  - **Constants of any other kind** (theorem, opaque, axiom, inductive, constructor, recursor, quot) are counted in the bucket
    UNEVALUATED-KIND. They are listed per kind and treated as UNKNOWN, never as non-members.
  - **Name-category column:** every row also carries one value, `plain` or one of `internal`, `match_`, `proof_`, `eq_`,
    `sizeOf`, `inst`, `generated-mark`, `_regen`, `_gap`. The totals are therefore also reported for the filtered subset
    that `candidates()` would have kept. That subset is a secondary breakdown only; the bound below does not use it.
  - **The claim:** the number of tops of C4/C5 members among the constants of the 459 modules is at most
    `T0-eligible + UNEVALUATED-KIND + READ-TIMEOUT + UNMEASURED modules' constants`. That holds relative to the shape tie
    stated above. This number is reported, and so are the terms it is made of.
  - **The 3 non-lake modules** (G8_NOLIB_MODULES.txt) are OUTSIDE `U` and outside this bound. They are listed as
    UNMEASURED, and the bound is never stated for the 462-file set.
- **Row classes:**
  - **READ-FAIL:** R0 fails; the reason is the first line of the exception.
  - **LEAF:** `insts = []`, so it cannot be a top.
  - **PARENT:** M and Q T0 are evaluated on these, giving `M:PASS|FAIL(reason)` and `Q:PASS|FAIL(reason)`.
- **Budget:** each `readMachine` runs under the default `maxHeartbeats`. Nothing is raised. A heartbeat exception gives
  READ-TIMEOUT, counted as unmeasured and not as non-member.

## Files (new only)
1. **`Tools/ShippingSharedLeafCensus.lean`:** the T0 predicates, the candidate enumeration and the command
   `#shared_leaf_census "LABEL" [Mod, …]`.
   - It writes one `logInfo` row per candidate and records the totals as `String` constants
     `G8Census.<LABEL>.{rows,totals}` via `addDecl`, as durable evidence.
   - It imports `Tools.ShippingMachineCommand` and `Tools.ShippingCorpusSweep` only, and is not imported by the compiler.
   - Plus a `lean_lib` entry.
2. **`Tests/Compiler/SharedLeafCensusControlTest.lean`:** controls, each an assertion that throws on failure.
   - **Positive:** `topshareM` gives `M:PASS`, and `topshareQ` gives `Q:PASS`. Both are from
     Tests/Compiler/SharedLeafMemKidTest.lean, which is NOT in the corpus.
   - **Negative:** `topshareM` gives `Q:FAIL`, and `topshareQ` gives `M:FAIL`. The leaves `leafM` and `leafP` are LEAF,
     READ-FAIL, or FAIL on both.
   - **Wrappers, Amendment 2 (reviewer ruling after control job g8-ctl-1e4807b0):** the wrappers `wrapM`, `wrapM3`, `wrapP`
     and `wrapQ`, each taken as a top, must give `M:FAIL` and `Q` in {`FAIL`, `PASS-noleafcall`}.
     - T0 and Q1 are unchanged. Q1-noleafcall is candidate-only, because no class field requires a wrapper to call the
       shared leaf.
     - `wrapP` is a wrapper, not a leaf.
     - The totals report `PASS-noleafcall` separately: it is its own value in the `Q:` tally. The result doc splits
       T0-eligible into strict `PASS` and `PASS-noleafcall`.
   - **Coverage check:** each condition P1-P4, M1-M3 and Q1-Q3 is the first failure of at least one row in the controls
     plus the corpus. If a condition is never first, that is reported, not asserted.
   - Plus a `lean_lib` entry.
3. **Corpus chunks `Tests/Gaps/G8CensusNN.lean`, NN = 00..11:**
   - Chunk NN imports corpus modules `NN*40+1 … NN*40+40` of the frozen list and runs `#shared_leaf_census "cNN" […]`
     over exactly those modules.
   - **If a chunk fails to elaborate because of its imports** (for example a known global-constant clash between test
     modules): it is split in halves under new job names, recursively. A single module that still fails is UNMEASURED,
     with its error.
   - Plus a `lean_lib` entry per chunk.
   - **Amendment 3 (reviewer ruling after g8-c10-cbae5d3a was OOMKilled once its imports had built):**
     - The memory limit stays at 12Gi.
     - A census-process OOM (exit 137) is split by the same recursive halving as an import failure.
     - The OOM job stays a failed diagnostic and is never a pass.
     - Only successful, disjoint child chunks are counted.
     - A single-module census that still OOMs is UNMEASURED/unknown, never non-member. The result doc states whether
       that module's constant count can be included in the U-bound. If it cannot, the numeric bound is reported as
       incomplete (symbolic in that term).
     - Halving a chunk that failed for any of these reasons is recorded in the result doc as a deviation from the
       first-written rule, which named import failures only.
4. **`scripts/gaps/G8_CENSUS_RESULT.md`:** written after the builds. It contains:
   - the totals per row class and per first-failure reason, M and Q separately, also split by `Tests.Compiler.*` versus
     the rest;
   - the T0-eligible list;
   - the unmeasured list;
   - the job table;
   - the SHA-256 of each job log.

## Builds
- All builds are issue-linked, exact head (head = base, dirty false), and run with
  `kjob -N sparkle-dev run --issue sparkle-gaps-g8-measure --name g8-<target>-<sha8> -n <node> -m 12Gi -c 4 -- kjob lake build sparkle_barrier sparkle_jit <target>`.
- **Targets:** the control test, and the 12 chunks.
- **Placement:** at most one heavy build per node. Polling only; running jobs are never cancelled.
- **Failed runs:** recorded as diagnostics.

## Not claimed
- T0-eligible is not membership. The unevaluated fields include `group`.
- A T0 failure is a non-membership only relative to the shape tie stated above.
- No statement about constants outside `U`: the 3 non-lake files, or the whole compiler-accepted input space.
- No compiler change.
