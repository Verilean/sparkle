# A / G1: the leaf entry's three NOT-ALLOWED binders (round par/a-24)

Branch `par/a-24`, base poc `7ae29e5c`. **WRITTEN, NOT BUILT.** Nothing here
was built or run; nothing counts as removed until the integrator's build.
Marks: **[R]** read in the source at that commit (file:line), **[P]**
predicted by reading (a value no one has computed), **[I]** inferred.

Outcome in one line: of the three NOT-ALLOWED binders of
`cnt.machine_ships_leaf`, ONE is replaced by an allowed premise (`InvW` →
`ChildBnd`, task 2). The other two are **not theorems**: `hmergeReg` as a
statement about `mergeChecked` on all modules is FALSE [P], and `hoptPrint`
is FALSE for the optimizer [P]. Both predictions have a log-only probe.
Neither can be closed without a user decision (a guard in `Sparkle/`) or, for
`hmergeReg` only, a proof about `mergeDuplicatesParts` that was not written.

## 1. G-reg — `m.body.all isAssign = false → (mergeChecked m).body.all isAssign = false`: FALSE [P]

### 1.1 What the guard asks [R]

`mergeChecked m` (`Sparkle/IR/RefineCheck.lean` 258–270), body not
assignments only: `r := mergeDuplicates m` (`= mergeDuplicatesRaw m`,
`Sparkle/IR/RegDedup.lean` 305–311) is kept iff
`refineCheck m r && (masksKept m r && printOk r)`.

Does an accepted `r` have to keep a register? No conjunct says so:

| conjunct | file:line | what it says about registers |
|---|---|---|
| `rO.all (fun ro => match regOf rM ro.1 with \| some rm => … \| none => false)` | `RefineCheck.lean` 161–167 | every register of `o` is one of `m` (by name; clock, reset, init, width). Vacuous when `o` has none |
| `rM.all (fun rm => rm.2.2.1.1 == "rst" && decide (0 < wm rm.1))` | 168 | about `m` only |
| `rO.all (… next values agree …)` | 176–183 | vacuous when `o` has none |
| `rM.all (fun rm => (rNormE wm insM dm rm.2.2.2.1).isSome)` | 185 | about `m` only ("the dropped ones too") |
| outputs: `decide (em = eo) && (refsOf eo).all (insO.contains ·)` | 171–175 | forces a register of `o` ONLY when an output's normal form reads one: `insO = (inputs…) ++ rO.map (·.1)` (149) and a register name is not an input (153). No output reads it → nothing |
| `masksKept` | 239–242 | output assignments only |
| `printOk` | `PrintGuard.lean` 266–268 | `seqText` / `seqNames` of `o` only |

There is NO count conjunct (contrast `seqOptCheck`, `OptCheck.lean` 259:
`rM.length == rO.length`) and no surjectivity. The file comment says it: "a
register of `m` that `o` does not have was dead" (12–13). So the guard
accepts a register-free `o` for an `m` with a register whenever no output's
normal form reads a register.

### 1.2 Can the merge produce one? Yes, on a multiply-driven name [P]

`mergeDuplicatesParts` (`RegDedup.lean` 231–294) [R]:

* `nodes` = `(name, stmt)` of every assign / register / single-port memory;
* `cls : HashMap String Nat` is keyed by NAME; in each refinement round
  `next := next.insert n k` — for a name defined twice the LAST statement
  wins;
* `rep[k]` = the first node name in body order with class `k`; `subst n := rep`
  for every non-representative name;
* the rewrite (285–290): a statement with `definedNode st = some n` and
  `subst.get? n = some r` becomes `.assign n (.ref r)` — WHATEVER its kind.

Probe module `mergeCex` (`Tests/Compiler/LeafEntryCexProbe.lean`), wires
`a, n : 8`, no outputs:

    assign a = 8'd5
    register n (clk, rst) <= 8'd0, init 0
    assign n = 8'd5

Round 1: signatures `a ↦ "0|A|…5"`, register `n ↦ "0|R|…"`, assign
`n ↦ "0|A|…5"`; `next = {a ↦ 0, n ↦ 0}` (the register's `n ↦ 1` is
overwritten); 2 classes ≠ 1. Round 2: 2 classes = 2, stop. 2 ≠ 3 nodes.
`rep[0] = a`, `subst = {n ↦ a}`. Body: `a = 5; n = a; n = a` — no register.
Guard: `refineCheck` — `rO = []`, every `rO.all` vacuous, `rM = [n]` passes
168 and 185, no outputs; `masksKept` vacuous; `printOk` — three typed
assignments at width 8. So `mergeChecked mergeCex` is assignments only while
`mergeCex.body.all isAssign = false`.

`mergeCex` is not a module the elaborator emits (`n` has two drivers). It
refutes the UNRESTRICTED statement; it says nothing against the merge of a
well-formed module.

### 1.3 The true statement, and why it is not written

For a body whose defined names are distinct the merge keeps a register [I]:
a class is split by the signature's kind marker (`|A|` / `|R|` / `|M|`,
`sigOf` 77–89) in the first round, so a register's class contains registers
only; its representative is a register and is never in `subst`. The exact
statement that is missing:

    theorem mergeRaw_keeps_nonAssign {m : Module}
        (hnd : (m.body.filterMap definedNode).Nodup)
        (h : m.body.all isAssign = false) :
        (mergeDuplicatesRaw m).body.all isAssign = false

Its proof is a proof ABOUT `mergeDuplicatesParts`: an `Id.run do` with two
nested `for` loops, a `break`, five `HashMap`s, and string signatures
(`canonExpr` is `partial`, so only the literal marker after `{self}|` is
usable — it suffices, but needs `String` append reasoning). No lemma about
this function exists (`grep mergeDuplicatesParts Tools/`: mentions in
comments only). I did not write it: unbuilt, a proof over the `do`-notation's
elaborated term cannot be written reliably without seeing the term. And the
leaf chain would in addition need `hnd` of `m0` (the cleaned
`closeMachine lay t'`): `TypedIn m0` has no such field
(`Tools/ShippingTextTyped.lean` 171–193) — a second missing fact
(`closeMachine_typed` would have to give it) [R: field list; I: derivable].

### 1.4 What the leaf chain needs, weakest form

`hmergeReg` is used once: `simpleBody b = false`
(`leaf_entry_textChecks`), i.e. `machine_ships_wired`'s premise, which
selects the `refineCheck` branch of `checkedOptimize`
(`checkedOptimize_seqOk`). It is needed only in the case
`b = mergeChecked m0`, merge kept. Three ways, none free:

1. **A guard in the compiler (user decision).** In `mergeChecked`'s last
   branch:

       - else if refineCheck m r && (masksKept m r && Sparkle.IR.PrintGuard.printOk r) then r else m
       + else if refineCheck m r && (masksKept m r && (Sparkle.IR.PrintGuard.printOk r &&
       +     !(r.body.all Sparkle.IR.RegDedup.isAssign))) then r else m

   Fallback: the module unmerged (as for the other conjuncts). Then
   `m.body.all isAssign = false → (mergeChecked m).body.all isAssign = false`
   is six lines (the pattern of `mergeChecked_print`). When does it fire? On
   an accepted merge that left no register / memory / instance: by §1.3 only
   for a non-assignment node sharing its name with an assignment, or a
   signature collision — not for any module the elaborator emits [I]. The
   conjunct is put INNERMOST so `mergeChecked_nonAssign`, `_masks`, `_print`
   (which take `and_left_true` / `and_right_true` projections) need one more
   projection only in `_print`. To measure: the corpus digests before/after
   (expected identical) and the count of modules on which the new conjunct is
   the one that fails (expected 0).
2. **The theorem of §1.3** plus distinct defined names of `m0` from the run.
3. **A hypothesis on `m0` that makes `refineCheck` force a register**: "an
   output's `m0`-normal form reads a register name" (§1.1, outputs row). True
   for `cnt`, but `m0` is the run's module, not a decided datum; no theorem
   gives its normal forms. Not pursued.

No `Tools/ShippingMergeKeeps.lean` was written: the requested theorem is
false, and nothing true about the merge is provable from what exists.

## 2. `InvW` → `ChildBnd` (`Tools/ShippingLeafEntryBnd.lean`) — written

`leaf_run_typedIn` uses `hw` once (`Tools/ShippingLeafTyped.lean` 377) [R].
New, in namespace `Tools.ShippingLeafEntryBnd`:

    theorem leaf_run_typedIn_bnd {c : Name} (d : MachineData) (ok : d.ok = true)
        (hbody : …) {nDecl : Nat} (hC : d.callsOk nDecl = true) (hdomB : …)
        (hno : d.shape.insts = []) (hSS : …) (outTy : …)
        {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
        (hbnd : ChildBnd mref cref w)
        (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
        (entry : MachineDefines mctx mref cctx cref c d.shape)
        (closesM : MachineCloses mctx mref cctx cref c d.shape) (hon : …) (hoty : …) :
        ∃ m0 : Sparkle.IR.AST.Module, (b = m0 ∨ b = mergeChecked m0) ∧
          Tools.ShippingTextTyped.TypedIn m0 ∧ m0.body.all seqStmtOk = true ∧
          Tools.ShippingLeafTyped.PortsIn b ∧ b.body.all seqStmtOk = true ∧
          (d.shape.layout.slots ≠ [] → m0.body.all Sparkle.IR.RegDedup.isAssign = false)

    theorem leaf_run_typedIn_again … (hw : InvW mref cref w) … : (the old statement) :=
      leaf_run_typedIn_bnd d ok hbody hC hdomB hno hSS outTy (ChildBnd.of_invW mctx cctx hw) hr
        entry closesM hon hoty

    theorem leaf_entry_raw_bnd (K : LeafKid mctx mref cctx cref c dk)
        (hbnd : ChildBnd mref cref w) (hr : RunsTo (synthesizeCombinational c) …) :
        (the conclusion of leaf_entry_raw)
    theorem leaf_entry_raw_again (K) (hw : InvW mref cref w) (hr) : (the same)
    theorem leaf_entry_textChecks_bnd (K) (hbnd : ChildBnd mref cref w) (hr)
        (hmergeReg) (hoptPrint) : (the three checks at wofOf (checkedOptimize b))
    theorem leaf_entry_shipped_seq_bnd (K) (hbnd) (hr) (hmergeReg) :
        (checkedOptimize b).body.all seqStmtOk = true
    theorem leaf_entry_ships_bnd (d) (soundL) (K) (hbnd : ChildBnd mref cref w) (hr)
        (hmergeReg) (hoptPrint) :
        ∃ raw, (b = dropZW raw ∨ b = mergeChecked (dropZW raw)) ∧
          MachineShips declName d (dropZW raw) b (checkedOptimize b)
            (wofOf (checkedOptimize b)) dom src

**Repeated proof text: 215 lines** (old 374–588). The old proof is not
factored — everything follows the `obtain` on `machine_run_of_core`, whose
third argument is the only use of `hw` — and the old file may not be edited.
The body was EXTRACTED from the old file (not retyped); the differences are
exactly: theorem name; `(hw : InvW …)` → `(hbnd : ChildBnd …)`;
`(ChildBnd.of_invW mctx cctx hw)` → `hbnd`; `PortsIn` namespace-qualified
(3 occurrences, one `have` split over two lines). The `open` lines are the
old file's. Once built, `leaf_run_typedIn`'s own body can be replaced by the
one line of `leaf_run_typedIn_again` (an edit of an existing file — the
integrator's). The four entry theorems' proofs are the old ones (6 / 8 / 7 /
4 lines) over the generalisation; the pure lemmas of
`Tools/ShippingLeafEntry.lean` are used as built.

## 3. G-opt — `checkedOptimize b = b ∨ printOk (checkedOptimize b) = true`: (ii) FALSE [P]

### 3.1 What was read [R]

`printOk` (`Sparkle/IR/PrintGuard.lean` 141–268): per assignment / register
input, `sf4` at the declared width; sanitize-stable declared names; width
tables on `seqNames`. Relevant refusals of `sf4`: a literal-amount left shift
(`isShlLit`, 88–90) is in the fragment only as the WHOLE operand list of the
`.shl` arm (187) or as the left operand of `&`/`|`/`^` under `shlSideOK`
(181); as an operand of `+ - *`, a comparison, `>>` it fails `notShl` (172,
182–188). A concat element that is an `.op` needs
`exprWidthT == some (widthOf …)` (198–206), and `exprWidthT` is `none` for
`mul`, `shl`, `shr`, `neg` (30–48).

`optimizeModule` (`Sparkle/IR/Optimize.lean` 836–1087), all phases read:
−1 `eliminateZeroBits`; 0 `propagateConstants` (531–567: constants and
aliases substituted into every reference); 0.5 duplicate / identity assigns;
0.6 `cseAndMergeInstances`; 1 `optimizeStmt` (`optimizeExpr` 231–239:
slice-of-concat resolution, `foldConstants` 136–224); 2 DCE; 3
`inlineSingleUseWires` (359–524) with `substituteExpr` (325–354); 4 DCE; 4.5
register reachability; 5 `eliminateZeroBits`.

Phase 3 is the one that leaves the fragment: a wire used exactly once (not an
output, register output, reset / clock, memory wire, nor referenced directly
by a register input) is replaced at its use by its definition — bare when the
wire's declared width is 32 or 64, or when the definition is a ref / const /
low slice of the width; otherwise wrapped `& (2^w − 1)` (336–349). Phase 0
does the same for constants (a literal amount held in a wire becomes a
literal amount in the shift). `refineCheck` normalises wires away
(`rNormE` 96–99) and knows `e & (2^w−1)` (`rBin` 64–71): it accepts these
rewrites — that is its purpose.

`optimizeExpr`, `substituteExpr`, `inferWidth`, `eliminateZeroBitInExpr`,
`resolveSlice` are `partial` (opaque in the logic): NO preservation theorem
about `optimizeModule`'s expressions can be proved from its definition. A
proof of (i) could only come from `refineCheck` itself, and `refineCheck` has
no conjunct about the form of `o`'s expressions.

### 3.2 The smallest module found [P]

`optCex` (`Tests/Compiler/LeafEntryCexProbe.lean`), wires `r, t, u : 32`,
output `out : 32`, inputs `clk`, `rst`:

    assign t = r << 32'd2
    assign u = t + 32'd1
    register r (clk, rst) <= u, init 0
    assign out = r

* `printOk optCex = true`: `t`'s right side is the `.shl` arm
  (`wb ≤ wa`, `notShl` of `r`); `u` is `perOp`.
* `optimizeModule`: `u` is protected (a register-input wire), `t` is used
  once → `u = (r << 32'd2) + 32'd1` (width 32: no mask); `t` and its wire go.
* `refineCheck optCex o = true`: both bodies normalise `u` to
  `add [shl [r, 2], 1]`; one register `r`, same on both sides; `out ↦ r`.
* `printOk o = false`: `sf4 (add [shl [r, const 2 32], const 1 32])` →
  `perOp` contains `notShl = !isShlLit (shl [r, const 2 32]) = false`.
* `simpleBody optCex = false` (a register), `seqStmtOk` all: `checkedOptimize
  optCex = o ≠ optCex`. The disjunction is false.

A source of that shape [I, not elaborated]: a 32-bit `Signal.loop` register
with next value `(r <<< 2) + 1` (the machine route allocates the literal `2`
as a wire; Phase 0 puts it back). At widths other than 32 / 64 the mask
rescues this particular shape (`(r << 2) & 255` is the `shlSideOK` route
[P]); other shapes may still fail there (a single-use `mul` wire inlined into
a concat: `exprWidthT (and [mul …, mask]) = none`) — NOT worked through: Phase
1's slice-of-concat resolution interferes, no module constructed.

Consequence for the built endpoints [I]: for a declaration of that shape the
`seqCheck` premise of `f.machine_ships_wired` at the emitter's width map is
false — the endpoint is vacuous there, not wrong.

### 3.3 The guard (user decision) — not written into `Sparkle/`

`Sparkle/IR/RefineCheck.lean` 385–386:

      else if m.body.all seqStmtOk then
    -   if RefineCheck.refineCheck m o then o else m
    +   if RefineCheck.refineCheck m o && Sparkle.IR.PrintGuard.printOk o then o else m

(`PrintGuard` is already imported: `mergeChecked` uses it.) Fallback: the
input module `m`, unoptimised — a fallback, never a rejection, as in
`keepGuarded` and `mergeChecked`. `refineCheck` stays the LEFT conjunct.

What it gives: `simpleBody m = false → m.body.all seqStmtOk = true →
checkedOptimize m = m ∨ printOk (checkedOptimize m) = true` (six lines, the
pattern of `mergeChecked_print`) — `hoptPrint` for every leaf register entry.
Together with `printOk b` / `TypedIn` of the served module (`leaf_entry_raw`)
the two text checks of the SHIPPED module follow in both cases
(`text_shipped_of_print`, built).

What it costs:

* proofs: `checkedOptimize_seqOk` (`RefineCheck.lean` 399–407) needs
  `and_left_true hc`; its five users in `Tools/` (`ShippingChecksDerived`,
  `ShippingMachineShipsW`, `ShippingChecksWidths`, `ShippingLeafEntry`,
  `ShippingMachineShipping`) use the lemma, not the unfolding [R: `grep`, not
  each proof]; the ~20 `Tools/` files that `unfold checkedOptimize` for OTHER
  branches must be rebuilt (the `simp only [hs, …, hok, if_true]` step in
  `checkedOptimize_seqOk` is the one known to touch this branch);
* emitted text: for every instance-free register module whose optimised form
  is outside the fragment (`optCex`'s shape: at least every 32- / 64-bit
  single-use literal shift feeding arithmetic), the UNOPTIMISED module is
  printed — more wires, same function. This is a change of emitted text, not
  "digests identical" by default. `Sparkle/Backend/VerilogDesign.lean` 27 / 38
  and `Sparkle/Compiler/Elab.lean` 8889 print through `checkedOptimize`.

To measure before deciding: (a) over the corpus machine declarations
(`scripts/shipping-coverage`, `machine_decls.txt`) and the test endpoints, the
count of modules with `simpleBody = false`, `seqStmtOk` all,
`refineCheck m o = true` and `printOk o = false` — the modules whose text
would change; (b) for those, `printOk m` (if also false, the fallback does
not make the text check hold either — `hoptPrint` holds by its left
disjunct but the served module's own check must come from `TypedIn`); (c) the
combined digest before / after; (d) `simx` on the changed ones only.

## 4. `cnt` (`Tests/Compiler/LeafEntryCntBndTest.lean`) — written; task 4's condition (1 complete) is NOT met

`cnt.machine_ships_leafB`: `cnt.machine_ships_leaf` with `ChildBnd`.

| endpoint | premise | predicted state (pending build) |
|---|---|---|
| `cnt.machine_ships_leafB` vs `cnt.machine_ships_leaf` | `InvW mref cref w` | absent; `ChildBnd mref cref w` in its place — ALLOWED |
| | `hmergeReg` | STAYS, NOT ALLOWED (§1) |
| | `hoptPrint` | STAYS, NOT ALLOWED (§3) |
| | run, `MachineDefines cnt` | ALLOWED |
| | `simpleBody`, `seqCheck`, `seqNames`, `MachineCloses` | absent (as in `machine_ships_leaf`) |

The test asserts exactly 2 NOT ALLOWED binders, 1 `ChildBnd` binder, no
`InvW`. Not a check-free endpoint; not counted.

## 5. Integrator

`lakefile.lean`:

    lean_lib «Tools.ShippingLeafEntryBnd» where
      roots := #[`Tools.ShippingLeafEntryBnd]

`Tests/AllTests.lean`: `import Tests.Compiler.LeafEntryCntBndTest`.
NOT for `AllTests` (log only, read its two `VERDICT` lines):
`Tests.Compiler.LeafEntryCexProbe` (imports `Sparkle.IR.RefineCheck` only).
Name added under `cnt`: `machine_ships_leafB`.

Build order: `Tests.Compiler.LeafEntryCexProbe` (cheap, independent — settles
the two predictions); `Tools.ShippingLeafEntryBnd`;
`Tests.Compiler.LeafEntryCntBndTest`; `Tests.AllTests`.

UNVERIFIED, highest risk first:

1. the two predictions (§1.2, §3.2): values of `HashMap`-based passes computed
   by hand. If a `VERDICT` line says REFUTED, the corresponding section's
   conclusion falls (the conjunct table of §1.1 and the pass reading of §3.1
   stand as read);
2. `Tools/ShippingLeafEntryBnd.lean`, section `Typed`: the extracted proof in
   ANOTHER namespace — every short name must resolve through the copied
   `open`s exactly as in `Tools.ShippingLeafTyped` (only `PortsIn` was found
   to be local there, by listing the file's declarations against the body);
   `maxHeartbeats 4000000` as the old;
3. the probe: structure-instance syntax of `Module` / `Port`, `.register`'s
   reset pair, `repr` of a `List Stmt` inside `s!`;
4. the test's second `run_cmd` (the built test's, with one binder and one
   constant changed) and the triple `(lines, bad, bnd)` projections;
5. `leaf_entry_ships_bnd`: `@soundL` passed on (as built).

## Build record (integrator, 2026-10-13)

Built on poc 50f058d8 + this round's files; `LeafEntryCntBndTest` in AllTests, `LeafEntryCexProbe`
target-only. Integrator change: `import Lean.Elab.Command` added to the probe (it did not elaborate without).

- `cnt.machine_ships_leafB`: `InvW` is gone, `ChildBnd` (ALLOWED) in its place; exactly two NOT-ALLOWED
  binders remain, `hmergeReg` and `hoptPrint`. Not a check-free endpoint, not counted.
- Both counterexamples CONFIRMED by evaluation (probe log below): on `mergeCex` the checked merge returns
  an assignment-only body from a module with a register; on `optCex` (`printOk optCex = true`)
  `checkedOptimize` returns a module whose `printOk` is false. So neither `hmergeReg` nor `hoptPrint` is a
  theorem of the present compiler. Both modules are hand-written IR: no Signal source producing them is
  known, and no wrong emitted text is shown — `printOk` false means the shipped text is outside the fragment
  for which text meaning = IR meaning is proved, not that it differs.

```
20261013-090312-a24-tests: lake build Tests.Compiler.LeafEntryCexProbe Tools.ShippingLeafEntryBnd Tests.Compiler.LeafEntryCntBndTest 
result=exit-code
exit=1
memory_peak_file=842477568
error: build failed
20261013-090354-a24-cex: lake build Tests.Compiler.LeafEntryCexProbe 
result=success
exit=0
memory_peak_file=222638080
Build completed successfully (208 jobs).
20261013-090414-a24-alltests: lake build Tests.AllTests 
result=success
exit=0
memory_peak_file=646197248
Build completed successfully (1248 jobs).
:78:0: LEAFCEX MERGE mergeCex: isAssign-all of m = false; mergeDuplicates body = [Sparkle.IR.AST.Stmt.assign "a" (Sparkle.IR.AST.Expr.const 5 8),
:78:0: LEAFCEX MERGE VERDICT: PREDICTION CONFIRMED — 'm.body.all isAssign = false → (mergeChecked m).body.all isAssign = false' is FALSE on mergeCex
:93:0: LEAFCEX OPT optCex: simpleBody m = false; seqStmtOk-all = true; printOk m = true; optimizeModule body = [Sparkle.IR.AST.Stmt.assign
:93:0: LEAFCEX OPT VERDICT: PREDICTION CONFIRMED — 'checkedOptimize m = m ∨ printOk (checkedOptimize m) = true' is FALSE on optCex although printOk optCex = true
```
