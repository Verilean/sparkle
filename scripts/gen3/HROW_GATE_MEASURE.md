# HROW_GATE_MEASURE: how to measure the machineShape? final gate over the whole corpus (procedure only; NOT run)

Issue `sparkle-gen3-hrow-gate`. Gate: `Sparkle/Compiler/Elab.lean`, `machineShape?`, just before `unifiedGateRoot`
(commit 72fa2fad). Decision: `scripts/gen3/HROW_GATE_DECISION.md` (user decision G).
Ledger: FG 94 / T1 56 (this document changes nothing).

What is measured, and what it is not. Two measurements, both are MEASUREMENTS over the corpus, not proofs:
(M1) the generated Verilog of every corpus module equals the Verilog of base 43977202; (M2) the number of times the
gate returned `none` is 0. A corpus-external program can still fire the gate; it then takes the legacy route (it
does not fail). Read "0 firings" as "0 on this corpus".

Deviation from the issue text to note for the reviewer: the gate is
`instOrigins.all (·.child?.isNone) || (instStruct && !instFields.isEmpty)`, i.e. `instStruct` AND a non-empty
field list, because `OneOutNoMemRow` reads the OUTPUT `instFields` (`if instStruct then instFields else []`),
and `instStruct` alone does not give `instFields ≠ []` without a reader invariant. By reading, every
`insts.push` also pushes a field (Elab 4080 / 4123), so the extra conjunct should not change firing.

## 1. The counting mark (measurement copy ONLY; never committed)

Make a throw-away copy of the worktree (outside the source tree, e.g. under the Job's scratch dir) at the gate
commit. In the copy only, replace the gate line by

```lean
    if !(st.instOrigins.all (·.child?.isNone) || (st.instStruct && !st.instFields.isEmpty)) then
      dbg_trace "HROWGATE-FIRED {declName?}" none   -- or: unsafe IO mark, see below
    else
```

`machineShape?` is pure and has no declaration name; so use the plain mark `dbg_trace "HROWGATE-FIRED"` (the
compiler prints it to stderr of the elaborating `lean` process). To attribute a firing to a module, run ONE module
per `lean` process (section 2) so the file name is the key. Do not use `IO` marks (the function is pure). Count of
firings of a file = number of `HROWGATE-FIRED` lines in that file's stderr. A line count of 0 for every file is M2.
Caution: `dbg_trace` can be evaluated more than once per call (closed term extraction, re-elaboration); a count
> 0 is a signal to look at the files, not an exact number. Zero is zero.

## 2. Corpus, one build, no per-file Pod

Corpus = Tests / IP / Examples (every `.lean` file that has `#synthesizeVerilog` or `@[hardware_module]`;
list: `git grep -l -E "synthesizeVerilog|hardware_module" -- Tests IP Examples`). Precedent: S2's fuel
measurement used a temporary `lean_lib CorpusTE` that imports ALL modules in one build; use the same shape:

1. in the throw-away copy only, add to `lakefile.lean` a `lean_lib CorpusTE` whose `roots` are the corpus modules
   (a generated list), plus the marked `Elab.lean`;
2. `kjob lake build CorpusTE` once, with `-O0`-style args if the existing lib options allow; capture the whole log
   outside the source tree and `grep -c HROWGATE-FIRED`;
3. do the same on the base copy (43977202, no gate) — same list — for M1.

The measurement copy's lakefile and the mark are NEVER committed.

## 3. M1: Verilog comparison against base

Precedent `scripts/shipping-coverage/compare_outputs.py OLD_WORK/out NEW_WORK/out` (identical / renumbered /
different, exits 1 on `different`). Procedure: run pass 1 of `scripts/shipping-coverage` (kept `WORKDIR/out`)
on base and on the gate commit WITHOUT the mark (the mark prints extra stderr only; use the unmarked build for
the comparison to keep the outputs clean), then compare. Accept (rev2, 2026-11-02; the goal is the generated Verilog): every `module … endmodule` block is identical
between the two sides, on every output file that contains one. `compare_outputs.py` is run and its counts are
reported. Its `different` files are allowed only if none contains Verilog, and each is listed with its kind of
difference: timing / count lines, or the run-pass environment, e.g. a missing olean outside the corpus lib or a
timeout, re-checked by a direct `kjob lake build` at the exact head. `renumbered` is reported with its count, as in
the precedent (fresh-name numbering only). A module absent from one side is listed, not ignored.
(rev1 said "Accept: no `different`". That also counted profile / heartbeat lines and environment noise, which are
not compiler output.)

## 4. Reporting

Write the result to the Issue note: files compared, count identical / renumbered / different, files with
`HROWGATE-FIRED`, files not measured (timeout/OOM) listed separately as UNMEASURED. If any file fires, record the
file, do not remove the gate, and stop for the user (the narrowing of the machine route is then a measured fact,
decision document needed). The coder runs this with `kjob run`; this agent did not run it.

## 5. Results (coder, 2026-11-02)

| Measurement | Job(s) | Result |
|---|---|---|
| M2 firing count | hrowm2-877c1498 (marked copy, Tests / Examples / IP, 389 IP modules) | `HROWGATE-FIRED` 0. The 23 build failures are the same targets as the base (pre-existing) |
| M1 build | hrowcmp-base (43977202) / hrowcmp-new (877c1498, unmarked) | both exit 0, `CorpusCmp` 456 modules, 1953 jobs, 478 output files each, missing 0 |
| M1 compare_outputs | `compare_outputs.py HCMP-base/out HCMP-new/out` | identical 436, renumbered 0, **different 42** |
| Verilog in the 42 | `grep endmodule` on both sides | **0 files**: none of the 42 contains a Verilog module |
| What the 42 differ in (digits masked) | diff after masking numbers / build-dir hashes | 29: `[profile]` times, heartbeats, closure counts only. 13 differ in text, all tests (no Verilog), next rows |
| Exit status changed (6) | status.txt | ChildVertAuditTest 0→124 (timeout of the run pass under load), Gen2/PkgCompat 0→1 (`rfl` type mismatch), Gen3/PostFactsCheck 0→1 (missing olean), Gen2/LeafInstance, S3GroupCheck, SlotlessLeafInstance 1→0. Changes in both directions |
| Those 6 at the exact head | hrowst-877c1498: `kjob lake build` of the 6 modules at 877c1498 | **exit 0** (956 jobs): all 6 build, PkgCompat and ChildVertAuditTest included. So the run-pass statuses come from the measurement environment (olean set / load), not from the gate |
| Other 7 text diffs | — | files outside `CorpusCmp` that fail on both sides with `object file … does not exist`; only which missing olean is reported differs (and TopNCCheck reports unknown constants from its missing import) |

Conclusion under the §3 rule (rev2): **accepted**. Verilog blocks are identical on every file that contains one. The 42 `different` files are all **non-Verilog differences**: 29 timing / count lines, and 13 from the run-pass environment (6 exit-status changes, all building at the exact head, plus 7 missing-olean files outside `CorpusCmp`). The rev1 literal rule "no `different`" would have counted these 42. The generated Verilog is identical on all files that contain it. This is a measurement, not a proof. The gate did not fire on the corpus (M2).
