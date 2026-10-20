# B / the optimizer's print guard: what is needed to decide (round par/b-19)

Branch `par/b-19`, base poc `7a2039ec`. **WRITTEN, NOT BUILT, NOT RUN.**
Nothing here was elaborated, built or simulated by me. Marks: **[R]** read in
the source at that commit (file:line), **[P]** predicted by reading (a value
no one has computed), **[M]** measured — there is NO [M] of mine in this note;
the only measurements quoted are the integrator's build record of
`docs/parallel/A-leaf-entry-2.md` (the hand-written `optCex` / `mergeCex`).

The compiler is not changed. Both candidate guards are computed in test code
(`Tests/Compiler/OptPrintGuardDefs.lean`: `guardedOptimize`, `mergeGuarded`).

`printOk o = false` is NOT a wrong output. It says: the text of `o` is
outside the fragment for which "meaning of the emitted text = meaning of the
IR" is proved. Whether such a text differs from the source is what item 2
(the simulation) measures, on one stimulus.

## 1. What was read

| what | where | content |
|---|---|---|
| `checkedOptimize`, instance-free assign + register branch | `Sparkle/IR/RefineCheck.lean` 385–386 | `if refineCheck m o then o else m` — no `printOk` [R] |
| the same function's other branches | 383–384, 388–395 | `simple`: `optCheck && assignmentOrderCheck`; instances: `deinline` (= `keepGuarded`, which HAS `printOk`, `HierCheck.lean` 233–252) + `hierRefineCheck`; unbound instances: `m`; anything else (memories): `o` unchecked [R] |
| `mergeChecked` | 258–270 | `refineCheck m r && (masksKept m r && printOk r)` — the merge HAS the print guard; no "keeps a non-assignment" conjunct [R] |
| `printOk`, `seqText`, `sf4` | `Sparkle/IR/PrintGuard.lean` 141–268 | `notShl := !isShlLit a` (172) looks at the LEFT operand of a two-operand node only; `+ - *` and the unsigned comparisons need `perOp` (182–183); `& | ^` have the second route `shlSideOK` (181, 96–109); the `.shl` node itself is in the fragment when its own left operand is not a literal shift (187); a mux needs `sf4` of its arms (153–156) [R] |
| the optimizer | `Sparkle/IR/Optimize.lean` 836–1087; phase 3 `inlineSingleUseWires` 359–525, `substituteExpr` 325–355 | a wire used once (not an output, register output, clock / reset, memory wire, nor read directly by a register input, 470–477, 850–855) is replaced at its use by its definition; bare when the wire is 32 or 64 bits wide or the definition is a ref / const / low slice of the width, else wrapped `& (2^w − 1)` (335–346). Phase 0 puts constant wires back as literals (531–567); phase 1 resolves slices of concats (231–239) [R] |
| the machine route's closing | `Sparkle/IR/Machine.lean` 76–112 | `next<slot> = packed[hi:lo]`, `register slot <= next<slot>`, `out = packed[hi:lo]`: the register input reads ONLY the `next…` wire, so that wire is the protected one and every gate wire behind it is inlinable [R] |
| who prints through `checkedOptimize` | `Sparkle/Backend/VerilogDesign.lean` 25–32 (`designArtifact`: the module named `d.topModule` only; children as they are), `Sparkle/Compiler/Elab.lean` 8888–8889 (`verilogOf`) [R] |
| the full entry | `Elab.lean` 5515–5529 (`synthesizeCombinationalWith`: core, zero-width cleanup, `mergeChecked`), 8834–8837, 9032–9035 (`synthesizeHierarchical`: top appended when absent, name validation) [R] |
| the census idiom | `Tests/Compiler/MemoHitCensusTest.lean` 181–210 (enumeration, cap 400, legacy → machine → mixed, certified left out), 158–175 (isolated bounded run), 139–142 and 235–237 (digests) [R] |
| the simulation idiom | `scripts/shipping-coverage/nested_let_sim.{sh,lean}`, `Tests/Compiler/NestedLetCacheTest.lean` 186–199, 240–255 [R] |
| the route idiom | `Tests/Compiler/CallWidthHuntTest.lean` 455–510 (`resetRefs`, `gatesOf`, `routeOf`), 655–658 (`synthesizeCombinationalCore n [] false`, then `synthesizeCombinational n`) [R] |
| source idioms | `kCount` (`CallWidthHuntTest.lean` 331–336: enable mux, `Signal.pure k#w` literals); literal operands `quotientReg <<< 1#32` (`IP/RV32/Divider.lean` 151), `mtimeHiReg + 1#32` (`IP/RV32/CLINT.lean` 57) [R] |

Not read: the machine front end (`Elab.lean` 5056 `machineShape?` and the
translator). The SHAPE of the module the machine route emits for the
declarations below is therefore inferred from `closeMachine` and from
`A-leaf-entry-2.md` §3.2 ("the machine route allocates the literal as a
wire"), not seen. Every per-declaration line of §2 is a prediction.

## 2. Item 1 — the sources (`Tests/Compiler/OptPrintSourceTest.lean`)

Twelve `circuit do` register machines over `defaultDomain`, each with the
enable mux of `kCount`. `c k` = `(Signal.pure k#w : Signal defaultDomain (BitVec w))`.

Expected module of the machine route [P, shape not seen]: gate wires `_…`
for each operator and literal, a packed concat, `next<r> = packed[..]`,
`register r <= next<r>`, `out = packed[..]`. Expected optimizer result [P]:
phase 0 puts the literals back, phase 1 turns `next<r> = packed[..]` into
`next<r> = <mux wire>`, the packed wire dies, phase 3 inlines every
single-use gate wire into `next<r>` (protected: the register input reads it).
So `next<r>` carries the whole next-value expression, and `printOk` of the
candidate is `sf4` of that one expression.

| declaration | enable arm | expected `next<r>` after the optimizer [P] | `printOk (checkedOptimize b)` [P] | why [R of `sf4`] |
|---|---|---|---|---|
| `shlAdd32` | `(rs <<< c 2) + c 1` | `en ? ((r << 32'd2) + 32'd1) : r` | **F** | `add`: `perOp`, left operand is a literal shift → `notShl` false |
| `shlAddLet32` | `let t := rs <<< c 2`; `t + c 1` | the same (the `let` port is an alias; phase 0 removes it) | **F** | as above |
| `shlAdd8` | width 8 | `en ? ((((r << 2) & 255) + 1) & 255) : r` | T | the 8-bit wire is inlined WITH its mask; `and [shl …, 255]` passes by `shlSideOK` (second disjunct: `kw ≤ width x`, `width b = width x`) |
| `shlAdd16` | width 16 | the same with `65535` | T | as above |
| `shlAdd64` | width 64 | as `shlAdd32` | **F** | 64: no mask |
| `shlAddLit32` | `(rs <<< 2#32) + 1#32` | as `shlAdd32` | **F** | same IR if the literal instances lower to constants |
| `shlVar32` | `(rs <<< (x &&& c 7)) + c 1` | `… ((r << (x & 7)) + 1) …` | T | `isShlLit` is false for a non-literal amount |
| `shlSub32` | `(rs <<< c 2) - c 1` | `… ((r << 2) - 1) …` | **F** | `sub`: `perOp` |
| `shlAnd32` | `(rs <<< c 2) &&& x` | `… ((r << 2) & x) …` | T | `shlSideOK` |
| `shlMux32` | `rs <<< c 2` is the arm | `en ? (r << 2) : r` | T | the `.shl` node itself is in the fragment |
| `shlEq32` | condition `(rs <<< c 2) === x` | `… (((r << 2) == x) & 1'd1) ? … ` | **F** | `eq`: `perOp`; the 1-bit wire's mask does not rescue it |
| `addShlRight32` | `c 1 + (rs <<< c 2)` | `… (1 + (r << 2)) …` | T | `notShl` reads the LEFT operand only |

Predicted hits (branch `seq`, `printOk b = true`, candidate accepted,
`printOk` of the shipped module false): `shlAdd32`, `shlAddLet32`,
`shlAdd64`, `shlAddLit32`, `shlSub32`, `shlEq32` — 6 of 12 [P]. Each of
these predictions also assumes [P]: the declaration takes the machine route;
`refineCheck b (optimizeModule b) = true`; `printOk b = true`.

The test logs, per declaration: route, branch, `printOk b`, `opt != b`,
`refineCheck b (opt b)`, `printOk (opt b)`, `checkedOptimize b == b`,
`printOk (checkedOptimize b)`, whether the guard changes the shipped module,
the statements of `b` and of the shipped module, `emitModule` of the shipped
module (the text the design writer prints for the top), and the guarded text
when it differs. A `SUMMARY` line counts hits and right / wrong predictions.

Prediction about the TEXTS [P]: every one of the six predicted hits is a
text in which a 32- / 64-bit shift sits inside a 32- / 64-bit arithmetic or
comparison node whose operands all have that width. Under SystemVerilog's
context-determined sizing such an expression is evaluated at that width, as
the IR does (`Semantics.lean` 121: `mask w (a <<< b)`). I therefore expect
`command==source T` for all twelve — the texts unproved, not different. This
is an expectation about one stimulus, to be replaced by item 2's lines.

## 3. Item 2 — the simulation (`scripts/shipping-coverage/optprint_sim.{sh,lean}`)

Per declaration: `<tag>_cmd.sv` by the real `#writeVerilogDesign`;
`<tag>_guard.sv` = `guardedText` of the design (the text under the guard);
the testbench and the source trace with the stimulus and reset scheme of
`nested_let_sim.lean` (two reset phases, 64 + 24 run cycles). One line:

    OPTPRINTSIM <decl>: command==source <T/F/-> x-cycles=<n> cycles=<n> guarded==source <T/F/-> guard-changes-text=<T/F> printOk-shipped=<T/F>

and the first differing cycle when a comparison is not T; a `TOTAL` line.

Reading the result:

* `printOk-shipped=F` and `command==source T`: the shipped text is unproved
  and agrees with the source on this stimulus. The guard buys a proof, not a
  repair.
* `command==source F`: a real difference between the shipped text and the
  source — to be reported with the log line, whatever `printOk` says.
* `guarded==source` must be T wherever the row ran (the fallback text is the
  unoptimised module).

## 4. Item 3 — the census (`Tests/Compiler/OptPrintCensusTest.lean`)

Population: the enumeration of `MemoHitCensusTest`, the same expression over
the same imports (the file imports that test and `OptPrintGuardDefs`, which
has no Signal-valued definition); legacy, machine, mixed first, then the
certified-route candidates that test leaves out (reported separately, and
the digests are given for both sets).

For every module occurrence of every returned design: (a) instance-free, by
branch; (b) candidate differs; (c) of (b) `refineCheck` true; (d) of (c)
`printOk o` false, each listed with declaration, module, branch, whether it
is the design's top, `printOk m`; `fires` = (d) in branch `seq` on the
design's top = the modules whose PRINTED text the guard changes (children
are printed unoptimised today: `designArtifact`). Digest of the texts
shipped today, digest of the texts under the guard, the declarations whose
text changes. The merge guard: on each top before the merge, bodies not
assignment-only / merges that change / accepted today / `FIRES` (accepted
with an assignment-only result).

Predictions [P]:

* merge guard `FIRES` = 0 (`A-leaf-entry-2.md` §1.3: a register's class
  holds registers only when defined names are distinct);
* optimizer guard `fires` > 0 is LIKELY on the corpus: literal 32-bit shifts
  feeding arithmetic exist in sources of the population's roots
  (`IP/RV32/Divider.lean` 151, 32 bits; 135 is 33 bits, where the inliner masks; whether those declarations are among the
  400, take the `seq` branch as tops and are instance-free was not checked).
  No number is predicted;
* cost: `refineCheck` builds tree normal forms; modules over
  `SPARKLE_OPTPRINT_MAXSTMTS` (default 3000) statements are not evaluated and
  are counted. The run shares `MemoHitCensusTest`'s 360 s wall-clock budget
  for the entry runs but ADDS the optimizer and both checks per module: if
  `not run: time budget` is not 0, the counts are of a prefix.

## 5. The decision text

**Question.** Should the checked optimizer refuse a candidate that is
outside the print fragment, and should the checked merge refuse a candidate
that lost every non-assignment statement?

**Diff 1 (G-opt)** — `Sparkle/IR/RefineCheck.lean` 386:

      else if m.body.all seqStmtOk then
    -   if RefineCheck.refineCheck m o then o else m
    +   if RefineCheck.refineCheck m o && Sparkle.IR.PrintGuard.printOk o then o else m

**Diff 2 (G-reg)** — `Sparkle/IR/RefineCheck.lean` 270:

    - else if refineCheck m r && (masksKept m r && Sparkle.IR.PrintGuard.printOk r) then r else m
    + else if refineCheck m r && (masksKept m r && (Sparkle.IR.PrintGuard.printOk r &&
    +     !(r.body.all Sparkle.IR.RegDedup.isAssign))) then r else m

**Fallback.** In both: the input module is shipped (unoptimised / unmerged).
A fallback, never a rejection, exactly as `keepGuarded` and the present
conjuncts of `mergeChecked`. No declaration stops compiling.

**What it gives.** Diff 1: `simpleBody m = false → m.body.all seqStmtOk =
true → checkedOptimize m = m ∨ printOk (checkedOptimize m) = true` — the
binder `hoptPrint` of `cnt.machine_ships_leafB` becomes a theorem. Diff 2:
`m.body.all isAssign = false → (mergeChecked m).body.all isAssign = false` —
the binder `hmergeReg`. With both, the leaf register entry has no
NOT-ALLOWED binder left (to be built; not claimed).

**What it costs — emitted text.** For every instance-free register module
that is a design's top and whose optimised form is outside the fragment, the
unoptimised module is printed: more wires, the same IR function. The census
line `OPTPRINT DIGEST changed` is that list for the corpus; `OPTPRINT SRC`
shows the two texts side by side for the twelve sources. Diff 2 is predicted
to change no text (`OPTPRINT MERGE … FIRES 0`).

**What the three measurements will show.**

1. `OPTPRINT SRC` (item 1): whether a source a user could write reaches the
   `optCex` situation at all (`hit=T`), at which widths and operator
   positions, and what both texts look like. If no row is a hit, `optCex`
   stays a hand-written IR module and Diff 1 is a proof convenience with no
   known effect on emitted text.
2. `OPTPRINTSIM` (item 2): for those sources, whether the unproved text
   agrees with the source cycle by cycle. `T` everywhere: the guard closes a
   proof gap only. Any `F`: the guard (or a fix of the emitter) repairs an
   observed difference — a different, more urgent decision.
3. `OPTPRINT CENSUS` (item 3): how many texts of the corpus change under
   Diff 1 (`fires`, `DIGEST changed`), how many of the affected modules were
   inside the fragment before the optimizer (`printOk(m)=T`: the fallback
   makes the shipped text provable; `F`: it does not, the module's own check
   has to come from elsewhere), and that Diff 2 fires nowhere.

**What it costs — proofs** (by `grep` at `7a2039ec`; classification by
reading each site's lines, not by building):

* Diff 1. Sites that unfold `checkedOptimize`: 25 in 18 `Tools/` files + 1
  in `Sparkle/`.
  * needs a patch: `checkedOptimize_seqOk` (`Sparkle/IR/RefineCheck.lean`
    399–407): `exact Or.inl hc` → `exact Or.inl (and_left_true hc)`. Its
    users take the lemma, not the unfolding: `Tools/ShippingChecksDerived`,
    `ShippingMachineShipsW`, `ShippingChecksWidths`, `ShippingLeafEntry`,
    and through `checkedOptimize_seq` `ShippingMachineShipping`;
  * walk every branch with `repeat' split` and close each goal by the same
    alternatives (the new condition adds no new goal shape) — predicted to
    pass unchanged, to be rebuilt: `Tools/ShippingModuleNames.lean` 94,
    `Tools/ShippingOptSoundness.lean` 367, `Tools/ShippingOptimizePorts.lean` 58;
  * `simple` branch only (`simp only [hg, if_true]` / `simp [checkedOptimize,
    hg, …]`), not touched: `ShippingAssignmentOrder` 119, `ShippingOptSoundness`
    309, 328, `ShippingSVBridge` 386, 462, `ShippingPrintEntrySoundness` 52,
    `ShippingPrintSoundness` 465, 563, 571, `ShippingControlOptSoundness` 62,
    105, `ShippingMachineShipsComb` 135;
  * instance branches only (the `seq` test is rewritten away by
    `not_all_seqOk` first), not touched: `ShippingShipsNoOuts` 181,
    `ShippingShipsHierFree` 185, `ShippingMachineShipsHier` 298,
    `ShippingMachineShipsHierH` 188, `ShippingShipsFree` 201,
    `ShippingChecksDerived2` 79, `ShippingPortsMatchShipped` 49,
    `ShippingGuardsSound` 294, 306, `ShippingHierShipsSV` 40;
  * new, six lines (pattern of `mergeChecked_print`): `checkedOptimize_print`.
  Predicted patches in `Tools/`: 0; in `Sparkle/`: 1 line + 1 new lemma.
* Diff 2. Sites that unfold `mergeChecked`: 9 in `Tools/` + 4 in `Sparkle/`.
  * needs a patch: `mergeChecked_print` (`RefineCheck.lean` 322–330): one
    more `and_left_true`. `mergeChecked_nonAssign` (left projection) and
    `mergeChecked_masks` (left of right) are unchanged — the reason the
    conjunct is put innermost;
  * assignment-only branch only, not touched: `ShippingGateChildComb` 116,
    `ShippingMachineChildComb` 392, `ShippingMergeClosed` 152,
    `ShippingMachineShipsComb` 255, `ShippingCombKidText` 201;
  * enter the guarded branch and use `and_left_true hrc` only (unchanged
    projection), predicted to pass, to be rebuilt: `ShippingSeqChildIface`
    74, `ShippingMachineShipsHier` 70, `ShippingMachineDepthRun` 87, 254;
  * new, six lines: `mergeChecked_keepsNonAssign`.
  Predicted patches in `Tools/`: 0; in `Sparkle/`: 1 line + 1 new lemma.
* Both: `Tests.AllTests` to be rebuilt; tests that pin emitted text of an
  affected declaration would change (which ones: the census list).

**Not decided here / alternatives.** (i) Leave the compiler, keep the two
binders as premises (the endpoint stays not check-free). (ii) Instead of
Diff 1, widen the proved fragment (`sf4` + `emit_sem`) to a literal shift
on the left of `+ - *` and comparisons at equal operand widths — no text
change, a proof in `Tools/SVParser/EmitSem.lean` of unknown size; item 2's
result says whether that statement is even plausible. (iii) Instead of
Diff 2, the theorem `mergeRaw_keeps_nonAssign` of `A-leaf-entry-2.md` §1.3.

## 6. Integrator

No `lakefile.lean` / `AllTests` change: the three Lean files are under the
`Tests` library and are built by target; none is for `Tests.AllTests`.

Order (each in the protected queue, never beside another build):

1. `lake build Tests.Compiler.OptPrintGuardDefs` (cheap; imports
   `Sparkle.IR.RefineCheck`, `Sparkle.IR.ZeroWidth`,
   `Sparkle.Backend.VerilogDesign`);
2. `lake build Tests.Compiler.OptPrintSourceTest` — read `OPTPRINT SRC` lines;
3. `scripts/shipping-coverage/optprint_sim.sh` (under `cgrun.sh`, after 2) —
   read `OPTPRINTSIM` lines;
4. `lake build Tests.Compiler.OptPrintCensusTest` — read `OPTPRINT CENSUS`,
   `OPTPRINT D`, `OPTPRINT DIGEST`, `OPTPRINT MERGE`.

UNVERIFIED, highest risk first:

1. `OptPrintSourceTest`: the twelve declarations' elaboration — `shlAddLit32`
   (`(rs <<< 2#32) + 1#32`: literal operands inside a `Signal.mux` argument;
   the idiom exists in `IP/` but under a typed `let`), `shlEq32` (a `Bool`
   `let` in a `circuit do`). If one fails, the file has an error (the
   `run_cmd` still logs the others: names are single-backtick) but its olean
   is not produced and step 3 cannot import it: delete the declaration and
   its rows in `decls`, `optprint_sim.lean` (`src…`, `rows`, the command).
2. The routes: a declaration may not take the machine route (then its row
   says so and its prediction is void).
3. `optprint_sim.lean`: the input order assumption (parameter order = input
   order; logged), source evaluation of `Signal.reg` at 64 bits.
4. `OptPrintCensusTest`: wall-clock and memory (the optimizer and
   `refineCheck` on every instance-free module up to 3000 statements; lower
   `SPARKLE_OPTPRINT_MAXSTMTS` if it does not return); mixed comma / newline
   separators in two structure instances; `validateDesignNames` inside
   `try`.
5. `OptPrintGuardDefs`: `Stmt.inst ..` / `Stmt.register ..` patterns, BEq on
   `Module`.

## Run records (integrator, 2026-10-13) — measurements for the decision; log-only, nothing claimed about the compiler's correctness

Tree: poc 7a2039ec + this round's files (worker files unchanged; none in AllTests). cgrun 3 GiB, swap 0.

1. REAL SOURCES (`OptPrintSourceTest`): all 12 declarations take the machine route with an instance-free
   register module; predictions right 12 / wrong 0. In 6 of them (`shlAdd32`, `shlAddLet32`, `shlAdd64`,
   `shlAddLit32`, `shlSub32`, `shlEq32`) `printOk b = true`, the optimizer's candidate is accepted by
   `refineCheck`, and `printOk (checkedOptimize b) = false`: a source a user can write (a 32-bit register
   with `(r <<< 2) + 1`) is shipped as text outside the proved print fragment.
2. SIMULATION (`optprint_sim.sh`, 94 cycles, one stimulus): `command==source T` for all 12, x-cycles 0 —
   also for the 6 with `printOk` false. No wrong output observed. The guarded choice also equals the source;
   the guard changes the text of exactly those 6.
3. CENSUS (`OptPrintCensusTest`, 362 returned declarations, the MemoHitCensusTest population + 1): 362
   instance-free module occurrences (348 simple, 14 seq); candidate differs 355; `refineCheck` true 314;
   of those `printOk` of the candidate false: 0. Texts as shipped today vs under the guard: combined
   digests identical (361: 1444467916182415447; 362: 8149634735370364912), 0 declarations changed.
   Merge guard: 13 tops not assignment-only, the merge changes 6, all 6 accepted today, FIRES 0.

So on the measured corpus neither guard changes any text, and the constructed 32/64-bit shift sources are
the only known sources whose text would change (to the unoptimised module, which simulates equal).

```
20261013-091651-b19-src: lake build Tests.Compiler.OptPrintGuardDefs Tests.Compiler.OptPrintSourceTest 
result=success
exit=0
memory_peak_file=1588879360
20261013-091711-optprintsim: scripts/shipping-coverage/optprint_sim.sh 
result=success
exit=0
memory_peak_file=398331904
20261013-091722-b19-census: lake build Tests.Compiler.OptPrintCensusTest 
result=success
exit=0
memory_peak_file=308150272
shlAdd32: route=machine branch=seq instFree=T stmts=9 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=F checkedOptimize(b)==b=F printOk(checkedOptimize b)=F guard-changes-shipped=T printOk(guarded)=T hit=T
shlAddLet32: route=machine branch=seq instFree=T stmts=11 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=F checkedOptimize(b)==b=F printOk(checkedOptimize b)=F guard-changes-shipped=T printOk(guarded)=T hit=T
shlAdd8: route=machine branch=seq instFree=T stmts=9 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=T checkedOptimize(b)==b=F printOk(checkedOptimize b)=T guard-changes-shipped=F printOk(guarded)=T hit=F
shlAdd16: route=machine branch=seq instFree=T stmts=9 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=T checkedOptimize(b)==b=F printOk(checkedOptimize b)=T guard-changes-shipped=F printOk(guarded)=T hit=F
shlAdd64: route=machine branch=seq instFree=T stmts=9 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=F checkedOptimize(b)==b=F printOk(checkedOptimize b)=F guard-changes-shipped=T printOk(guarded)=T hit=T
shlAddLit32: route=machine branch=seq instFree=T stmts=9 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=F checkedOptimize(b)==b=F printOk(checkedOptimize b)=F guard-changes-shipped=T printOk(guarded)=T hit=T
shlVar32: route=machine branch=seq instFree=T stmts=10 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=T checkedOptimize(b)==b=F printOk(checkedOptimize b)=T guard-changes-shipped=F printOk(guarded)=T hit=F
shlSub32: route=machine branch=seq instFree=T stmts=9 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=F checkedOptimize(b)==b=F printOk(checkedOptimize b)=F guard-changes-shipped=T printOk(guarded)=T hit=T
shlAnd32: route=machine branch=seq instFree=T stmts=8 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=T checkedOptimize(b)==b=F printOk(checkedOptimize b)=T guard-changes-shipped=F printOk(guarded)=T hit=F
shlMux32: route=machine branch=seq instFree=T stmts=7 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=T checkedOptimize(b)==b=F printOk(checkedOptimize b)=T guard-changes-shipped=F printOk(guarded)=T hit=F
shlEq32: route=machine branch=seq instFree=T stmts=17 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=F checkedOptimize(b)==b=F printOk(checkedOptimize b)=F guard-changes-shipped=T printOk(guarded)=T hit=T
addShlRight32: route=machine branch=seq instFree=T stmts=9 printOk(b)=T opt!=b=T refineCheck(b,opt b)=T printOk(opt b)=T checkedOptimize(b)==b=F printOk(checkedOptimize b)=T guard-changes-shipped=F printOk(guarded)=T hit=F
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlAdd32: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=T printOk-shipped=F
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlAddLet32: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=T printOk-shipped=F
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlAdd8: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=F printOk-shipped=T
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlAdd16: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=F printOk-shipped=T
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlAdd64: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=T printOk-shipped=F
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlAddLit32: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=T printOk-shipped=F
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlVar32: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=F printOk-shipped=T
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlSub32: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=T printOk-shipped=F
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlAnd32: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=F printOk-shipped=T
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlMux32: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=F printOk-shipped=T
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.shlEq32: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=T printOk-shipped=F
OPTPRINTSIM Tests.Compiler.OptPrintSourceTest.addShlRight32: command==source T x-cycles=0 cycles=94 guarded==source T guard-changes-text=F printOk-shipped=T
OPTPRINTSIM TOTAL: 12 declarations; command==source T=12 F=0 not-compared=0; shipped top with printOk false: 6; text changes under the guard: 6 (one stimulus; not a proof)
n:157:0: OPTPRINT CENSUS: 400 candidates (128 legacy-route, 59 machine-route, 212 mixed-route, 1 certified-route, 0 of unknown route: not run); 400 runs of the shipping entry, 362 returned, 0 not run: time budget; 7014 ms; left out: name validation fails 0 [], top over 3000 statements 0 []; measured declarations 362, of them without a module named by the design's topModule field (the writer optimizes nothing) 0. ALL ROUTES: module occurrences 362; (a) instance-free 362 (evaluated 362: simple 348, seq 14, other 0; not evaluated, too large 0); (b) candidate differs 355 (seq 10); (c) of (b) refineCheck true 314 (seq 8); (d) of (c) printOk of the candidate false 0 (seq 0; of (d) with printOk of the module itself
n:157:0: OPTPRINT CENSUS BY ROUTE legacy: declarations 90; module occurrences 90; (a) instance-free 90 (evaluated 90: simple 88, seq 2, other 0; not evaluated, too large 0); (b) candidate differs 89 (seq 2); (c) of (b) refineCheck true 48 (seq 0); (d) of (c) printOk of the candidate false 0 (seq 0; of (d) with printOk of the module itself true 0); fires = (d) in seq on the design's top, i.e. printed text changes under the guard 0
n:157:0: OPTPRINT CENSUS BY ROUTE machine: declarations 59; module occurrences 59; (a) instance-free 59 (evaluated 59: simple 52, seq 7, other 0; not evaluated, too large 0); (b) candidate differs 59 (seq 7); (c) of (b) refineCheck true 59 (seq 7); (d) of (c) printOk of the candidate false 0 (seq 0; of (d) with printOk of the module itself true 0); fires = (d) in seq on the design's top, i.e. printed text changes under the guard 0
n:157:0: OPTPRINT CENSUS BY ROUTE mixed: declarations 212; module occurrences 212; (a) instance-free 212 (evaluated 212: simple 207, seq 5, other 0; not evaluated, too large 0); (b) candidate differs 207 (seq 1); (c) of (b) refineCheck true 207 (seq 1); (d) of (c) printOk of the candidate false 0 (seq 0; of (d) with printOk of the module itself true 0); fires = (d) in seq on the design's top, i.e. printed text changes under the guard 0
n:157:0: OPTPRINT CENSUS BY ROUTE certified: declarations 1; module occurrences 1; (a) instance-free 1 (evaluated 1: simple 1, seq 0, other 0; not evaluated, too large 0); (b) candidate differs 0 (seq 0); (c) of (b) refineCheck true 0 (seq 0); (d) of (c) printOk of the candidate false 0 (seq 0; of (d) with printOk of the module itself true 0); fires = (d) in seq on the design's top, i.e. printed text changes under the guard 0
n:157:0: OPTPRINT D TOTAL: 0 occurrences, 0 distinct module names
n:157:0: OPTPRINT DIGEST today [legacy+machine+mixed (the MemoHitCensusTest population)]: 361 declarations, combined digest 1444467916182415447
n:157:0: OPTPRINT DIGEST guarded [legacy+machine+mixed (the MemoHitCensusTest population)]: 361 declarations, combined digest 1444467916182415447
n:157:0: OPTPRINT DIGEST changed [legacy+machine+mixed (the MemoHitCensusTest population)]: 0 declarations []
n:157:0: OPTPRINT DIGEST today [all four routes]: 362 declarations, combined digest 8149634735370364912
n:157:0: OPTPRINT DIGEST guarded [all four routes]: 362 declarations, combined digest 8149634735370364912
n:157:0: OPTPRINT DIGEST changed [all four routes]: 0 declarations []
n:157:0: OPTPRINT MERGE: tops measured 362 (before the merge, after the zero-width cleanup); body not assignment-only 13; of them the merge changes the module 6; of them accepted today (refineCheck && masksKept && printOk) 6; FIRES (accepted today and the merged body is assignment-only: the candidate conjunct would refuse it) 0 []
```
