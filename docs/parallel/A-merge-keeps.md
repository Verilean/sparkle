# A / G-reg: the merge keeps a non-assignment statement (round par/a-30)

Branch `par/a-30`, base poc `edd9496c`. **WRITTEN, NOT BUILT.** Nothing here
was built or run; nothing counts as removed until the integrator's build.
Marks: **[R]** read in the source at that commit (file:line), **[P]**
predicted by reading / hand evaluation, **[I]** inferred.

Outcome in one line: the true form of G-reg is stated and its proof is
WRITTEN in full (no lemma left out), the leaf's module is shown to satisfy
its hypothesis from facts already built, and `hmergeReg` is discharged for
leaf register machines without touching `Sparkle/` — IF the files build. The
part that speaks about the compiler's `do` block (file 2 below) is the part
most likely not to.

## 1. The statement

    def LastNonAssign (body : List Stmt) : Prop :=
      ∃ pre st post, body = pre ++ st :: post ∧ isAssign st = false ∧
        ∀ l r, Stmt.assign l r ∈ post → definedNode st ≠ some l

    theorem mergeRaw_keeps_nonAssign {m} (hL : LastNonAssign m.body) :
        (mergeDuplicatesRaw m).body.all isAssign = false
    theorem mergeChecked_keeps {m} (hL : LastNonAssign m.body) :
        (mergeChecked m).body.all isAssign = false
    theorem lastNonAssign_of_nodup {body}
        (hnd : (body.filterMap definedNode).Nodup) (h : body.all isAssign = false) :
        LastNonAssign body

"Some non-assignment statement is not FOLLOWED by an assignment to the name
it defines." The candidate hypothesis (distinct defined names) implies it;
it is NOT what was used, because the leaf chain cannot supply it (§3).

### Why this hypothesis — the merge, as read [R] (`Sparkle/IR/RegDedup.lean`)

| line | what it does | consequence |
|---|---|---|
| 235–236 | `nodes` = `(name, stmt)` of every statement with `definedNode = some name` (assign, register, single-port memory, 64–74) | an instance / multi-port memory is not a node |
| 246, 257 | `cls : HashMap String Nat`, `next := next.insert n k` per node | keyed by NAME: for a name defined twice the LAST statement decides |
| 252–256 | `k` = id of the signature `sigOf alias cls (cls.getD n 0) st` | same class ⇔ same signature |
| 81–88 | signatures `"{self}|A|…"`, `"{self}|R|…"`, `"{self}|M|…"`, `"{self}|?"` | the character after the first `|` is `A` exactly for an assignment (`self : Nat` has no `|`) |
| 248, 259–260 | `for _ in [0:nodes.length + 1]`, `cls := next` BEFORE `if n' == nClasses then break` | the final `cls` is the result of one round |
| 273–275 | `rep[k]` = first node of class `k` in body order | |
| 281–283 | `subst := subst.insert n r` only if `r = rep[cls n] ≠ n` | a representative is never in `subst` |
| 287–290 | `definedNode st = some n`, `subst.get? n = some r` ⇒ `.assign n (.ref r)` — WHATEVER the kind of `st` | where a register is lost |
| 291–292 | otherwise `mapStmtExprs rename st` | the kind is kept |

So a REGISTER statement is replaced by an assignment exactly when its name
is in `subst`, i.e. its name's class has another representative. Two ways:

1. a legitimate merge: an EARLIER node has the same signature id — a
   duplicate register. Then that representative is a register, and stays;
2. the name's class is not the register's own: a LATER statement defines the
   same name (the last `next.insert` wins). If that later statement is an
   assignment, the class is an assignment's and the representative may be an
   assignment: every statement defining the name — the register too — becomes
   an alias. This is `mergeCex`.

`LastNonAssign` excludes exactly case 2 for ONE statement: the last
statement defining `st`'s name is a non-assignment, its class's signature is
a non-assignment's, so is the last statement defining the representative's
name, and that statement is kept.

A memory statement: a single-port memory is a node with marker `M` and is
treated like a register; a multi-port memory and an instance define no node
and are kept by 291–292 — the theorem covers them without the class argument
(`classes_keep`, case `definedNode st = none`).

### The two modules, by hand

* `mergeCex` = `a = 5; register n; n = 5` (`Tests/Compiler/LeafEntryCexProbe.lean`):
  the only non-assignment is `register n`, `post = [n = 5]`,
  `definedNode (register n) = some "n"`: the hypothesis FAILS — excluded.
  (`lastNonAssignB mergeCex.body = false`, asserted by evaluation in the
  test.)
* `dupReg` = `a = 5; register n1 <= a; register n2 <= a`: take
  `st = register n1`, `post = [register n2]` — no assignment in `post`: the
  hypothesis HOLDS. The merge [P]: round 1 `a ↦ 0, n1 ↦ 1, n2 ↦ 1` (the two
  register signatures are equal: `"0|R|clk|rst|…|0|ref #0"`), round 2 the
  same, 2 classes ≠ 3 nodes; `rep = {0 ↦ a, 1 ↦ n1}`; `subst = {n2 ↦ n1}`;
  body `a = 5; register n1 <= a; n2 = n1`. A register is kept — the
  representative.

## 2. What is written (all with proofs; no `sorry`, no lemma left out)

### File 1 — `Tools/ShippingMergeKeeps.lean` (pure; does not look at the `do` block)

* §1 signatures: `afterBar`, `isA`, `no_bar_nat`, `isA_form`,
  **`isA_sig : isA (sigOf alias cls self st) = isAssign st`**.
* §2 hash-map facts in `get?` form (`hm_get?_insert`, `hm_contains`,
  `hm_getD`, `hm_size_insert_new`, …) over `Std.HashMap.get?_insert`,
  `contains_eq_isSome_getElem?`, `getD_eq_getD_getElem?`, `size_insert`,
  `size_le_size_insert` (names and statements read in the toolchain source,
  `Std/Data/HashMap/Lemmas.lean`).
* §3 a round: `innerRec` (the inner loop as a recursion), the INVARIANT

      structure RoundInv (ids next) (kd : String → Bool) : Prop where
        bound : ∀ s k, ids.get? s = some k → k < ids.size
        inj   : ∀ s s' k, ids.get? s = some k → ids.get? s' = some k → s = s'
        kind  : ∀ n k, next.get? n = some k → ∃ s, ids.get? s = some k ∧ isA s = kd n

  with `kd` = the kind of the statement that LAST defined each name
  (`lastKind`), `RoundInv.step`, `innerRec_inv`, `innerRec_dom`,
  **`round_sep`** (same class ⇒ same last kind), `outerRec`,
  **`outerRec_round`** (a non-empty index list ⇒ the class map is a round's).
* §4 `repRec`, `substRec`; `repRec_keep` (an entry is never overwritten),
  `repRec_ok` (an entry is a node name of its class), `repRec_cover`,
  **`substRec_none`** (a name that is its own representative is not in
  `subst`).
* §5 `nodeOf`, `rewriteStmt`, `finish`, `finish_keeps`.
* §6 `LastNonAssign`, `classes_keep`, `partsRec`, **`partsRec_keeps`**.
* §7 `lastNonAssign_of_nodup`.

### File 2 — `Tools/ShippingMergeKeepsBridge.lean` (the compiler's `do` block)

The `do` elaborator of this toolchain (4.32.1) is the NEW one
(`backward.do.legacy` defaults to `false`, `Lean/Elab/Do/Switch.lean` 17–20
[R]); the shape of its output is not known to me, and no proof here
pattern-matches on it. Route:

1. the loops REPEATED as `Id.run do` functions of their list and start state
   (`innerLoop`, `outerLoop`, `outerLoopR`, `repLoop`, `substLoop`), text
   copied from 248–283;
2. **`parts_eq_model : mergeDuplicatesParts m = partsModel m`** — by `rfl`:
   `partsModel` is `if`s around calls of those helpers; unfolding the helpers
   gives the compiler's loops back (same text, same elaborator), and in `Id`
   `bind`/`pure`/`Id.run` are definitional;
3. `*_nil` by `rfl`; `innerLoop_cons` by `rfl`; `outerLoop_cons`,
   `repLoop_cons`, `substLoop_cons` (an `if` in the body) by a case split on
   the condition, `simp only [<helper>, List.forIn_cons, <the split's
   equation>, ↓reduceIte]`, then `rfl`;
4. `*_eq`: each helper is its recursion (induction; `outerLoopR_eq` through
   `Std.Legacy.Range.forIn_eq_forIn_range'`, the lemma
   `Tools/ShippingChildVC.lean` 163 uses on elaborator loops);
5. `model_eq_rec`, `idxOf_ne_nil`, `parts_keeps`,
   **`mergeRaw_keeps_nonAssign`**, `mergeRaw_keeps_nonAssign_of_nodup`,
   `mergeDuplicates_keeps`, **`mergeChecked_keeps`**.

Every shape-dependent step is `first | … | …` over several routes. If one
fails, only that lemma's PROOF changes: the later lemmas use its statement.

### File 3 — `Tools/ShippingMergeKeepsCheck.lean`

`lastNonAssignB` with `lastNonAssignB_of` / `not_lastNonAssign`
(completeness) and `lastNonAssignB_sound`. Used by the tests only.

### File 4 — `Tools/ShippingMergeKeepsLeaf.lean` (supply side and endpoints, §3)

## 3. The supply side

### What the built facts do NOT give [R]

`TypedIn m0` (`Tools/ShippingTextTyped.lean` 171–193): `wn`, `ow`, `oi`,
`ostable`, `ond` (distinct OUTPUT names), `oty`, `kinds`, `asg`, `reg`. No
distinctness of defined names, no "written once". `PortsIn` is about ports.
`closedTransition_of_run` (`Tools/ShippingClosedTransitionTyped.lean` 61–84)
returns `t'.body = B ++ [out := core]`, typedness, allocated assignment
targets of `B`, allocated wire names, inputs ⊆ wires, distinct input / wire
names, the slot ports' widths. It does NOT return "no statement of `B`
drives a slot port". (The fact exists one level down — `transition_spine`,
`Tools/ShippingCloseLetsRun.lean` 176: `∀ port ∈ m.inputs, port.name ∉
writesOf m.body` for the transition BEFORE `closeLets` — but it is not
carried through `closeLets` to `t'` by any built theorem.) So neither
`Nodup` of defined names nor "no register's name is an assignment target" is
available for `m0`.

### What they DO give — and it is enough

`closeMachine` (`Sparkle/IR/Machine.lean` 112–114):

    body := t.body.dropLast ++ nextAssigns w slotPorts lay.slots ++
      registers lay.resetKind slotPorts lay.slots ++ outAssigns w lay.outs

The registers come AFTER `B` and the next-value assignments; only other
registers and `outAssigns` follow. `LastNonAssign` asks about what FOLLOWS:

    theorem closeMachine_lastNonAssign (hbody : t.body = B ++ [.assign "out" (.ref w)])
        (names : ∀ p ∈ t.wires, Allocated p.name) (inWires : ∀ p ∈ t.inputs, p ∈ t.wires)
        (slots : Zip₂ (SlotOk (weOf t)) (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots)
        (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
        (hsl : lay.slots ≠ []) : LastNonAssign (closeMachine lay t).body

`st` = the first register `register p.name …`; `post` = the other registers
(`registers_mem`: none is an assignment) ++ `outAssigns` (targets `o.name`,
not allocated by `outNameOk_facts`; `p.name` is allocated: a slot port is an
input, an input is a wire). All five premises are conjuncts of
`closedTransition_of_run` / `MachineData.ok`.

    theorem leaf_run_lastNonAssign … (hbnd : ChildBnd mref cref w) (hr : RunsTo …) (entry) (closesM) :
        ∃ m0, (b = m0 ∨ b = mergeChecked m0) ∧
          (d.shape.layout.slots ≠ [] → LastNonAssign m0.body)

Its proof REPEATS the prefix of `leaf_run_typedIn_bnd` (`Tools/ShippingLeafEntryBnd.lean`
89–146 and 178: the run taken apart, to `M = closeMachine lay t'` and
`(dropZeroWidthModule M).body = M.body`): **58 lines, extracted, not
retyped**. Reason: `leaf_run_typedIn_bnd`'s statement hides `M` behind
`∃ m0`, so a second existential cannot be tied to the first; and the file may
not be edited. Once built, the clean form is ONE theorem with both conjuncts
(an edit of an existing file — the integrator's).

Because the two existentials are separate, `hmergeReg` is discharged through
its CONCLUSION, not through its `m0`:

    theorem leaf_nonAssign_bnd (K : LeafKid …) (hbnd) (hr) : b.body.all isAssign = false
    theorem leaf_mergeReg (K) (hbnd) (hr) :
        ∀ m0, b = mergeChecked m0 → m0.body.all isAssign = false → b.body.all isAssign = false :=
      fun _ _ _ => leaf_nonAssign_bnd K hbnd hr
    theorem leaf_entry_textChecks_bndR (K) (hbnd) (hr) (hoptPrint) : (the three checks)
    theorem leaf_entry_shipped_seq_bndR (K) (hbnd) (hr) : (checkedOptimize b).body.all seqStmtOk = true
    theorem leaf_entry_ships_bndR (d) (soundL) (K) (hbnd) (hr) (hoptPrint) : ∃ raw, … ∧ MachineShips …

## 4. `cnt` (`Tests/Compiler/MergeKeepsCntTest.lean`)

`cnt.machine_ships_leafR`: `cnt.machine_ships_leafB` without `hmergeReg`.

| endpoint | premise | predicted state (pending build) |
|---|---|---|
| `cnt.machine_ships_leafR` vs `cnt.machine_ships_leafB` | `hmergeReg` | ABSENT (proved; 0 binders mention `isAssign` — asserted) |
| | `hoptPrint` | STAYS, NOT ALLOWED — the one such binder (asserted: exactly 1) |
| | `ChildBnd mref cref w` | ALLOWED (asserted: 1) |
| | run, `MachineDefines cnt` | ALLOWED |
| | `simpleBody`, `seqCheck`, `seqNames`, `MachineCloses`, `InvW` | absent (asserted) |

Not a check-free endpoint; not counted. Section 4 of the test EVALUATES
(compiled evaluation, an error otherwise): `lastNonAssignB mergeCex.body =
false`, `mergeChecked mergeCex` assignments only, `lastNonAssignB dupReg.body
= true`, raw and checked merge of `dupReg` not assignments only; and LOGS
whether the raw merge of `dupReg` is the predicted `a = 5; register n1; n2 =
n1`.

`Tests/Compiler/MergeKeepsCexTest.lean` (TARGET-ONLY): the kernel-level
`mergeCex_outside : ¬ LastNonAssign mergeCex.body` and `okReg_inside` by
`decide` — the kernel compares `String`s there; not tried.

## 5. Consequence for the decision text (`docs/parallel/B-optprint.md`)

"Diff 2" (the guard `!(r.body.all isAssign)` in `mergeChecked`) is NOT
needed for the leaf chain once files 1, 2 and 4 are built: its alternative
("prove `mergeRaw_keeps_nonAssign` instead of Diff 2") is what this round
wrote. The guard would still be the only way to have
`m.body.all isAssign = false → (mergeChecked m).body.all isAssign = false`
for EVERY module (it is false without it: `mergeCex`). `hoptPrint` (Diff 1)
is untouched.

## 6. Integrator

`lakefile.lean`:

    lean_lib «Tools.ShippingMergeKeeps» where
      roots := #[`Tools.ShippingMergeKeeps]

    lean_lib «Tools.ShippingMergeKeepsBridge» where
      roots := #[`Tools.ShippingMergeKeepsBridge]

    lean_lib «Tools.ShippingMergeKeepsCheck» where
      roots := #[`Tools.ShippingMergeKeepsCheck]

    lean_lib «Tools.ShippingMergeKeepsLeaf» where
      roots := #[`Tools.ShippingMergeKeepsLeaf]

`Tests/AllTests.lean`: `import Tests.Compiler.MergeKeepsCntTest`.
NOT for `AllTests`: `Tests.Compiler.MergeKeepsCexTest` (target-only).
Name added under `cnt`: `machine_ships_leafR`.

Build order (each step is a separate verdict):

1. `Tools.ShippingMergeKeeps` — pure; imports `Sparkle.IR.RefineCheck` and
   `Std.Data.HashMap.Lemmas` only. Cheap.
2. `Tools.ShippingMergeKeepsBridge` — the `do` block.
3. `Tools.ShippingMergeKeepsCheck` — independent of 2.
4. `Tools.ShippingMergeKeepsLeaf` — needs 2 and `Tools.ShippingLeafEntryBnd`.
5. `Tests.Compiler.MergeKeepsCntTest`; then `Tests.AllTests`.
6. `Tests.Compiler.MergeKeepsCexTest` (target-only; needs 2 and 3).

UNVERIFIED, highest risk first:

1. **`parts_eq_model` (`rfl`)** — the claim that the compiler's `do` block
   and `partsModel` unfold to definitionally equal terms. It holds if the
   elaborator turns `if c then return x` at the top level into an `ite`
   whose branches are the return value and the rest, and a `for` into a
   `forIn` whose result the rest is applied to. If the new elaborator
   threads early returns differently, `rfl` fails and the lemma needs the
   goal in view. Everything about the compiler's own function hangs on this
   one lemma.
2. **`outerLoop_cons`, `repLoop_cons`, `substLoop_cons`** — `simp only` must
   expose the `if` of the first iteration with its condition in the form of
   the split's equation (`rep.contains (cls.getD n 0)`, …) after beta / zeta
   / tuple-projection reduction; then `rfl`. Four routes each.
   `innerLoop_cons` and the `*_nil` are plain `rfl`.
3. `outerLoopR_eq` — that the range loop is a `forIn` (or `forIn'`) over
   `Std.Legacy.Range`, as `Tools/ShippingChildVC.lean` assumes for the
   elaborator's loops.
4. `isA_sig` — the `s!` signatures re-associated by
   `simp only [sigOf, String.append_assoc]` to `toString self ++ ("|R|" ++ X)`
   (the literal is `toString "|R|"` in the macro's output: unified by `rfl`);
   `litA`…`litQ` by `simp` (the `String.reduceToList` simproc).
5. `Tools/ShippingMergeKeeps.lean` §2–§6: ordinary proofs, but ~800 lines
   unbuilt — `rw … at` directions, `split` on an `if` inside an argument,
   `cases h : e` generalisation. The hash-map lemma NAMES were read in the
   toolchain; their use through `get?` relies on `get?_eq_getElem?` being
   `rfl`.
6. `closeMachine_lastNonAssign` — `simp [closeMachine, hpw, hdrop, hps]`
   (copied from `closeMachine_typed`'s `hMb`), the final
   `simp [List.append_assoc]`.
7. `leaf_run_lastNonAssign` — an extracted prefix of a BUILT proof in a third
   namespace, with the same `open`s.
8. the test's `run_cmd`s (the built test's, with one binder removed and one
   counter added); `dupReg`'s structure-instance syntax (the probe's).
9. `MergeKeepsCexTest`'s two `decide`s (target-only by design).

If step 2 of the build fails beyond a local repair, what stands is file 1:
the theorem about the recursions, and with it the exact remaining
obligation — ONE equation,

    mergeDuplicatesParts m =
      partsRec m (aliasMap m) (initCls (nodesOf m)) (idxOf m)

(`parts_eq_model` followed by `model_eq_rec`).

## Build record (integrator, 2026-10-13)

Built on poc 0d6e46a0 (the two compiler guards ARE integrated there) + this round's files. Integrator
changes to worker files: `[DecidableEq α]` added to three hash-map helper lemmas of
`Tools/ShippingMergeKeeps.lean` (`hm_get?_insert`, `_self`, `_ne`: the statement uses `if k = a`); and the
counterexample assertion of `Tests/Compiler/MergeKeepsCntTest.lean` — VERSION DIFFERENCE: the note and the
test were written against the unguarded compiler, where `mergeChecked mergeCex` is assignments-only; with the
guard the CHECKED merge keeps the statement, so the test now asserts the RAW merge
(`mergeDuplicatesRaw mergeCex`) is assignments-only and the checked merge is not. No theorem statement changed.

Established: the four Tools files build, including the bridge between the compiler's `do`-block merge and
the recursive model (`parts_eq_model` by `rfl`). `mergeRaw_keeps_nonAssign : LastNonAssign m.body →
(mergeDuplicatesRaw m).body.all isAssign = false`, `mergeChecked_keeps`, and for the leaf shape
`leaf_mergeReg` (the cleaned closed machine of a leaf run has `LastNonAssign`: registers after the body).
`cnt.machine_ships_leafR` (in AllTests): `hmergeReg` gone by the THEOREM; exactly one NOT-ALLOWED binder,
`hoptPrint`; standard axioms.

Position (user ruling): this is a conditional proof for the leaf's trailing-register shape, NOT a
replacement of the compiler's non-assignment guard for arbitrary modules. The guard stays. On the guarded
tree the check-free leaf endpoint is `cnt.machine_ships_leafC` (both binders discharged by the guards);
`…leafR` shows that for leaves the merge half does not depend on the guard.

```
20261013-152203-a30-tests: result=exit-code memory_peak_file=716726272 
20261013-152249-a30b-tests: result=exit-code memory_peak_file=232538112 
20261013-152302-a30c-tests: result=exit-code memory_peak_file=344780800 
20261013-152328-a30d-tests: result=success memory_peak_file=304758784 Build completed successfully (542 jobs).
20261013-152349-a30-alltests: result=success memory_peak_file=425291776 Build completed successfully (1272 jobs).
:131:0: MERGEKEEPS PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafR: ALLOWED     binder hbnd : Tools.ShippingChildInv.ChildBnd mref cref w
:131:0: MERGEKEEPS PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafR: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
:131:0: MERGEKEEPS PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafR: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
:131:0: MERGEKEEPS PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafR: NOT ALLOWED binder hoptPrint : Sparkle.IR.OptCheck.checkedOptimize b = b ∨ Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true
:218:0: MERGEKEEPS CEX mergeCex: lastNonAssignB = false; isAssign-all of m = false; mergeChecked body = [Sparkle.IR.AST.Stmt.assign "a" (Sparkle.IR.AST.Expr.const 5 8),
:218:0: MERGEKEEPS CEX mergeCex (raw merge): isAssign-all of mergeDuplicatesRaw m = true
:218:0: MERGEKEEPS POS VERDICT: PREDICTION CONFIRMED — the raw merge is a = 5; register n1; n2 = n1 (one register became an alias, the representative stayed a register)
```
