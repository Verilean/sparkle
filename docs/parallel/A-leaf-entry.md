# A / G1: a leaf machine as an ENTRY (round par/a-23)

Branch `par/a-23`, base poc `d0de8898`. **WRITTEN, NOT BUILT.** Nothing here
was built or run; nothing counts as removed until the integrator's build.
Marks: **[R]** read in the source at that commit (file:line), **[I]**
inferred.

Outcome in one line: the three check premises of `f.machine_ships_wired` are
**NOT all derivable** from what exists. Two compiler facts are missing
(§3). What is derivable is proved; the missing facts are hypotheses in the
form a fallback guard would prove, and are counted as NOT ALLOWED premises.

## 1. The endpoints and their three checks [R]

| what | where |
|---|---|
| `machine_ships_wired` (statement) | `Tools/ShippingMachineShipsW.lean` 41–74 |
| its generator (`f.machine_ships_wired`: data, the wired twin of `machine_sound`'s head, four decided premises) | `Tools/ShippingMachineCommand.lean` 2599–2642 |
| `_closed` (replaces the `MachineCloses` binder by `f.machine_closes`) | `Tools/ShippingMachineClosesGen.lean` 74–105, 115–124 |
| `machine_ships_comb` (slotless) and its generator | `Tools/ShippingMachineShipsComb.lean` 202–235; `ShippingMachineCommand.lean` 2643–2664 |
| the three checks, under `∃ raw`, `∀ wof` | `ShippingMachineShipsW.lean` 68–71: `simpleBody b = false`; `seqCheck wof (weOf wof) (checkedOptimize b).body = true`; `((seqNames (checkedOptimize b).body).all fun n => declWidth (checkedOptimize b) n == weOf wof n) = true` |
| `machine_ships_comb`'s | `ShippingMachineShipsComb.lean` 229–233: the same with `simpleBody b = true` |
| conclusion | `MachineShips declName d (dropZeroWidthModule raw) b (checkedOptimize b) wof dom src` (`ShippingMachineShipping.lean` 62–98): the IR run of ONE module and `runModuleSV wof` of its emitted statements |

`wof` is universally quantified; the statement is used at ONE `wof`. The
emitter's is `wofOf o = moduleWof o` (`Tools/ShippingDesignSVLeaf.lean` 21);
`weS o = weOf (wofOf o)` (22, an `abbrev`). At that `wof` the text clause of
`MachineShips` is `TextRun o …` (`ShippingDesignSVLeaf.lean` 25–31).

## 2. What exists for a leaf as a CHILD, and why it stops at `b` [R]

* `leaf_run_typedIn` (`Tools/ShippingLeafTyped.lean` 354–373): over a run of
  the full entry, `b = m0 ∨ b = mergeChecked m0`, `TypedIn m0`,
  `m0.body.all seqStmtOk`, `PortsIn b`, `b.body.all seqStmtOk`, and with a
  slot `m0.body.all isAssign = false`. It asks `hw : InvW mref cref w`
  (364), used once as `ChildBnd.of_invW mctx cctx hw` (377).
* `leaf_real_kidK_reg` (710–753): `kidCheck C n y.1` for the module the child
  cache SERVES — `y.1` is `b`, not `checkedOptimize b`. A design's children
  are the served modules (`DesignSV`'s `C mn = some (child, cwe)`,
  `Tools/ShippingDesignSV.lean` 79–95); no optimizer is applied to a child in
  that statement. So the child side never needed the text of
  `checkedOptimize` of an instance-free module.
* The PARENT chain (`core_runFacts`, `core_designCheck_run`,
  `core_text_shipped`) does not apply with no instance:
  `RunFacts.gate : hierGate b = true` (`Tools/ShippingGuardsSound.lean`
  303–311) gives an instance statement (`hasInst_of_hierGate`, 269);
  `core_text_shipped` (`Tools/ShippingTextShipped.lean` 86–112) asks
  `hins : insts ≠ []`, `hfne : instFields ≠ []`; and its key step
  `checkedOptimize_print` (47–59) is about the INSTANCE branch of
  `checkedOptimize` (`keepGuarded` asks `printOk`). All three fail for a
  module without calls. A leaf-specific version is needed, and it meets a
  different branch of the compiler.

## 3. The three checks: derived / missing

`checkedOptimize` (`Sparkle/IR/RefineCheck.lean` 381–396), for
`b.body.all seqStmtOk` and `simpleBody b = false`:

    if RefineCheck.refineCheck m o then o else m            -- o = optimizeModule m

| check | state | how / what is missing |
|---|---|---|
| `seqCheck` and the width agreement, at `b` (`wofOf b`) | **derived**, no module hypothesis: `leaf_entry_raw` | `leaf_run_typedIn` + `TypedIn.seqCheck`; merged case by `mergeChecked_print` (`RefineCheck.lean` 322) + `printOk_sound` |
| the same at `checkedOptimize b`, when `checkedOptimize b = b` | **derived** | rewriting |
| the same at an ACCEPTED candidate | **MISSING (G-opt)** | this branch has no print guard, and `refineCheck` has no name / declaredness / operand-width conjunct (`docs/parallel/G1-designCheck-text.md` §D). Exact statement: `simpleBody m = false → m.body.all seqStmtOk = true → checkedOptimize m = m ∨ printOk (checkedOptimize m) = true`. With `if refineCheck m o && PrintGuard.printOk o then o else m` it is `mergeChecked_print`'s six lines. A compiler edit: a decision for the user. The alternative is a preservation theorem for `optimizeModule` on typed statements (none exists for this branch) |
| `simpleBody b = false`, `b = m0` or the merge returned its input | **derived** | `m0` has a register → `simpleBody_false_of` |
| `simpleBody b = false`, merge accepted and changed | **MISSING (G-reg)** | `refineCheck m o` pairs each register of `o` with one of `m` (`RefineCheck.lean` 161–168), not conversely: it accepts an `o` without registers. That `mergeDuplicatesRaw` keeps one is not a theorem (`mergeDuplicatesParts`, `Sparkle/IR/RegDedup.lean` 231–294, an `Id.run do` over hash maps). Exact statement: `m.body.all isAssign = false → (mergeChecked m).body.all isAssign = false`. Either that theorem about the merge, or a guard (`… && !(r.body.all isAssign)` in `mergeChecked`'s last branch) |

Also not a check, but a premise: `InvW` at the run's start (from
`leaf_run_typedIn`). `ChildBnd` suffices; the change is one hypothesis and
one argument in `Tools/ShippingLeafTyped.lean` 364 / 377 (and the old
statement re-derived by `ChildBnd.of_invW`). An existing file: not edited.

## 4. New statements (`Tools/ShippingLeafEntry.lean`)

Abbreviating `o := checkedOptimize b`:

    theorem leaf_entry_raw (K : LeafKid mctx mref cctx cref c dk)
        (hw : InvW mref cref w)
        (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w') :
        b.body.all seqStmtOk = true ∧
          (seqCheck (wofOf b) (weS b) b.body = true ∧
            (seqNames b.body).all (fun x => declWidth b x == weS b x) = true) ∧
          ∃ m0, (b = m0 ∨ b = mergeChecked m0) ∧ m0.body.all isAssign = false

    theorem leaf_entry_textChecks (K : LeafKid mctx mref cctx cref c dk)
        (hw : InvW mref cref w) (hr : RunsTo (synthesizeCombinational c) …)
        (hmergeReg : ∀ m0, b = mergeChecked m0 → m0.body.all isAssign = false →
          b.body.all isAssign = false)
        (hoptPrint : o = b ∨ printOk o = true) :
        simpleBody b = false ∧
          seqCheck (wofOf o) (weOf (wofOf o)) o.body = true ∧
          ((seqNames o.body).all fun n => declWidth o n == weOf (wofOf o) n) = true

    theorem leaf_entry_textChecks_id … (hmergeId : ∀ m0, b = mergeChecked m0 → b = m0)
        (hsame : o = b) : (the same three)

    theorem leaf_entry_ships_of
        (hships : ∃ raw, (b = dropZW raw ∨ b = mergeChecked (dropZW raw)) ∧
          ∀ wof, simpleBody b = false → seqCheck wof (weOf wof) o.body = true →
            ((seqNames o.body).all fun n => declWidth o n == weOf wof n) = true →
            MachineShips declName d (dropZW raw) b o wof dom src)
        (hchk : (the three at wofOf o)) :
        ∃ raw, (b = dropZW raw ∨ b = mergeChecked (dropZW raw)) ∧
          MachineShips declName d (dropZW raw) b o (wofOf o) dom src

    theorem leaf_entry_ships (d) (soundL : … MachineTraceL …)
        (K : LeafKid mctx mref cctx cref declName d) (hw : InvW mref cref w)
        (hr : RunsTo (synthesizeCombinational declName) …) (hmergeReg) (hoptPrint) :
        ∃ raw, (…) ∧ MachineShips declName d (dropZW raw) b o (wofOf o) dom src

    theorem designSV0_of_leaf (C) (hs : o.body.all seqStmtOk = true)
        (h : TextRun o seed T s.st s.mems envs) : DesignSV C 0 o seed T s envs

Helpers: `simpleBody_false_of`, `text_post_reg`, `text_shipped_of_print`,
`checkedOptimize_seqBody`, `leaf_entry_shipped_seq`, `oracle_seq`.

`hoptPrint`, where the candidate is accepted, IS `printOk` of the shipped
module — the content of checks 2 and 3. For such a run the theorem removes
nothing of them; it locates the obligation in one guard-shaped statement.

## 5. `MachineShips` vs `DesignSV` for an entry without calls

At `wof = wofOf o` the text clause of `MachineShips` is `TextRun o seed …`.
`DesignSV C 0 o seed T s envs` is `TextRun o (oracle C o.body … seed) …`,
`Resolved`, `PortsMatch` and one clause per instance. For an instance-free
`o` the oracle seeding is `seed` (`oracle_seq`) and the other three are
vacuous: `designSV0_of_leaf`, for EVERY `C` and children's state. So
`DesignSV` adds no content; it adds only the uniform statement shape of the
29. `MachineShips` says more: the IR run of `o`, the equality of the two
runs, and that the outputs are the source's observations. A design-level
endpoint of a leaf entry would be `MachineShips` with its text clause
restated — a new definition, not written (task 2 is not complete).

Observed, not followed up: `toVerilogDesign` prints each module through
`optimizeModule` (`Sparkle/Backend/Verilog.lean` ~500), not
`checkedOptimize`; the endpoints are about `checkedOptimize b`.

## 6. The slotless case — NOT written

`machine_ships_comb` asks `simpleBody b = true`. Three things are missing,
none derived here: (i) `simpleBody b = true` itself — no theorem gives
`simpleRhs` of a closed machine's assignments (`grep`: `simpleBody_of` is the
scalar route's, `Tools/ShippingPostSoundness.lean` 685) [I: not read to
exhaustion]; (ii) the merge of an assignment-only body is
`mergeDuplicates`' own, not print-guarded (`ShippingLeafTyped.lean` 74–76:
`hmergePrint` stays a hypothesis); (iii) the simple branch keeps a candidate
under `optCheck`, whose print conjunct is `PrintCheck.moduleCheck` (the
uniform-width check), not `printOk`. And a slotless body that is not simple
goes to the `refineCheck` branch — outside `machine_ships_comb`.

## 7. `cnt` (`Tests/Compiler/LeafEntryCntTest.lean`)

| endpoint | premise | predicted state (pending build) |
|---|---|---|
| `cnt.machine_ships_leaf` vs `cnt.machine_ships_wired` | `simpleBody b = false` | absent from the statement; replaced by `hmergeReg` (NOT ALLOWED) |
| | `seqCheck wof … (checkedOptimize b).body` | absent; replaced by `hoptPrint` (NOT ALLOWED; equal in content when the candidate is accepted) |
| | the `declWidth` / `weOf` agreement | absent; the same `hoptPrint` |
| | `MachineCloses cnt` | absent (`cnt.machine_closes`) |
| | NEW `InvW mref cref w` | NOT ALLOWED (`ChildBnd` would be ALLOWED) |
| | run, `MachineDefines cnt` | ALLOWED |

The statement is the inferred type of the proof term (the endpoint's `dom`
and `src` are not written by hand) and is logged.

## 8. Coverage once a generator exists

`leaf_entry_ships` covers every declaration with `f.machine_ships_wired` and
`LeafKid`'s decided conditions: the REGISTER rows of census §2.2
(`A-census-2.md` 82–88; list source: `scripts/shipping-coverage`'s
`machine_decls.txt` for the corpus, the `#machine_endpoint` lines of the
nine test files for the tests) — about 80 leaf declarations less the
slotless ones (`pickByte*`, `httpGetByte`, `ipv4Header*`, …; kind not read
one by one). With the two NOT ALLOWED hypotheses, until G-opt / G-reg are
settled.

## 9. Integrator

`lakefile.lean`:

    lean_lib «Tools.ShippingLeafEntry» where
      roots := #[`Tools.ShippingLeafEntry]

`Tests/AllTests.lean`: `import Tests.Compiler.LeafEntryCntTest`.
Name added under `cnt`: `machine_ships_leaf` (no other file adds it, `grep`).

Build order: `Tools.ShippingLeafEntry`; `Tests.Compiler.LeafEntryCntTest`;
`Tests.AllTests`.

UNVERIFIED, highest risk first:

1. the test's second `run_cmd`: a `fun` with implicit binders in a syntax
   quotation under `hygiene false`, elaborated with no expected type, its
   inferred type taken as the statement; `cnt.machine_ships_wired`'s binder
   kinds (read from the generator, not from a built statement) and that it
   exists for `cnt` at all [I];
2. `leaf_entry_ships_of`: `hships` must unify with the generated endpoint's
   conclusion (copied from `machine_ships_wired`'s text, same `open`s);
3. `oracle_seq` (`show` of the unfolded `if`, then `rfl`; `simp` fallback)
   and `designSV0_of_leaf` (`refine ⟨…⟩` on `DesignSV C 0 …`);
4. `leaf_entry_ships`: `@soundL` passed to `machine_ships_wired`;
5. the test's assertions: three NOT ALLOWED binders; the base endpoint
   mentions `simpleBody`, `seqCheck`, `seqNames`;
6. `rw [e]` with `e : b = m0` on goals over a local `b`.

## Build record (integrator, 2026-10-13)

Built at the first attempt on poc 50daf208 + this round's files (worker files unchanged; the test is in
AllTests and asserts exactly three NOT-ALLOWED binders). NOT a check-free endpoint and not counted:
`cnt.machine_ships_leaf` has none of `simpleBody`, `seqCheck`, the width agreement, `MachineCloses`, but
carries `InvW` at the start world, `hmergeReg` and `hoptPrint` — the last two are the two missing compiler
facts in guard form (G-reg: the checked merge keeps a non-assignment statement; G-opt: the instance-free
branch of `checkedOptimize` ships `o` after `refineCheck` only, without `printOk`). Derived unconditionally:
`seqCheck` and the width agreement of the served module `b` (`leaf_entry_raw`).

```
20261013-075428-a23-tests: lake build Tools.ShippingLeafEntry Tests.Compiler.LeafEntryCntTest 
result=success
exit=0
memory_peak_file=814784512
Build completed successfully (536 jobs).
20261013-075519-a23-alltests: lake build Tests.AllTests 
result=success
exit=0
memory_peak_file=427450368
Build completed successfully (1246 jobs).
126:0: LEAFENTRY PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leaf: NOT ALLOWED binder hw : Tools.ShippingChildInv.InvW mref cref w
126:0: LEAFENTRY PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leaf: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
126:0: LEAFENTRY PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leaf: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
126:0: LEAFENTRY PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leaf: NOT ALLOWED binder hmergeReg : ∀ (m0 : Sparkle.IR.AST.Module),
126:0: LEAFENTRY PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leaf: NOT ALLOWED binder hoptPrint : Sparkle.IR.OptCheck.checkedOptimize b = b ∨ Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true
126:0: LEAFENTRY CNT: Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leaf — the conclusion of Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_wired at the emitter's own width map wofOf (checkedOptimize b), with NO occurrence of simpleBody, seqCheck or seqNames and no MachineCloses; standard axioms. NOT a check-free endpoint: three binders are NOT ALLOWED — InvW at the start world (ChildBnd would do: one hypothesis of leaf_run_typedIn), hmergeReg (the checked merge keeps a non-assignment statement: not a theorem about mergeChecked) and hoptPrint (checkedOptimize b = b or printOk of the shipped module: the instance-fre
```
