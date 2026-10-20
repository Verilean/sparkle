# Worker R (`par/r-1`): the remaining `partial` functions, and one general reader invariant

Base poc `3b7fc95d`. **WRITTEN, NOT BUILT.** Nothing here was compiled or
run. READ means read in this tree. PREDICTED means worked out by reading.
BUILT or MEASURED is used only where an integrator record says so (cited).

## 0. Files and commits

| file | content |
|---|---|
| `Tools/ShippingReaderOutsInv.lean` (new) | `outs_of_reader`, `outTy_of_reader`, `outScalar_of_reader`, `reader_of_core`, `outTy_of_core`, `outScalar_of_core` (+ `bitWidth_machHWType`, `scalarTy_machHWType`, `machOutFields_ty`, `reader_defn`) |
| `Tools/ShippingReaderOutsMemOnly.lean` (new, leaf) | `MemOnlyDataR`, `MemOnlyDataR.toData`, `memOnlyData_of_reader`, `memOnly_{runFacts,outsCheck,kidsMem,designCheck}_of_reader` |
| `lakefile.lean` | two `lean_lib` lines, appended at the END |
| this file | the record |

Nothing under `Sparkle/` is changed. No existing statement is changed. ALLOWED is not changed. The generator is not changed.

Build order (serial):
1. `lake build Tools.ShippingReaderOutsInv`. Its imports are `ShippingShapeDecomp` (target-built, `b624a6ac`/`ff8f4565`), `ShippingMachineEntry` and `ShippingTextTyped` (both built).
2. `lake build Tools.ShippingReaderOutsMemOnly`. It needs step 1 and `ShippingMemOnly` (built).

```
lean_lib «Tools.ShippingReaderOutsInv» where
  roots := #[`Tools.ShippingReaderOutsInv]

lean_lib «Tools.ShippingReaderOutsMemOnly» where
  roots := #[`Tools.ShippingReaderOutsMemOnly]
```

## 1. Every `partial def` under `Sparkle/Compiler` and `Sparkle/IR`, and the machine route

`grep -rn "partial def" Sparkle/Compiler Sparkle/IR` gives 43 lines. Two of them are comment lines in `IR/Semantics.lean` (11, 13), so there are **41** `partial` definitions. The table also lists the two reader functions that are no longer `partial` (rows 1 and 2), which makes 43 rows.

Path column:
* **R**: the machine READER, `machineShape?` and what it calls.
* **E**: the ENTRY constant the reader is given (`entryConst`, which calls `userInliner`).
* **P**: the post-pipeline on the reader's output module (optimizer, printer).
* **L**: the legacy route.
* **—**: not on the machine route.

Counterpart column: is there a total definition under `Tools/` with a kernel proof that it solves the old source equation?

The two totalised functions (rows 1 and 2) follow this rule:
* That the new compiled function agrees with the OLD compiled `partial` one is **MEASURED**. These are the shadows: projChain grid; `PRODOLD`/`PRODARITY` grid 79 calls and a sweep of about 260k constants, 0 differences (`verification-p-reader-unit1.md`).
* That the new function is the unique solution of the old SOURCE equation is **PROVED** (`tail_unique`, `real_go_unique`).

That the old compiled code satisfied its own source equation is the one step outside the kernel. It is not assumed.

| # | function (file:line) | path, reader step | switched (total in the compiler)? | `Tools/` counterpart |
|---|---|---|---|---|
| 1 | `MachRawSurface.projChain` (MachRawSurface 56) | R: `rawNode` pair-matcher arm, under `machNorm` | **yes** (`def`; `tail` → `MachProjChain.tailAt`) | real-function theorems `ShippingReaderProjChainReal/Result` |
| 2 | `MachRawSurface.prodMatcherArity?` (`go`) (MachRawSurface 30) | R: `senv.prodMatch` → `rawNode` | **yes** (`def`; `go` → `MachProdMatcher.goS`) | `ShippingReaderMatcherArityReal`, `…RawNodeCanon` |
| 3 | `MachRawSurface.rootFloat` (198) | R: wrapper 5075; `machConv` 3986; `machChain` 4144 | no | none (recursion through `liftLooseBVars`, (O)) |
| 4 | `MachRawSurface.zetaAll` (219) | R: `machReserve` 3701, 3703 (slot kinds, reset values) | no | none ((O), `instantiate1`) |
| 5 | `MachTupleIn.packTupleInputs` (MachTupleIn 79) | R: wrapper 5065 (declaration binders `bs`) | no | none ((O)) |
| 6 | `machNorm` (Elab 4957) | R: wrapper 5077 (the whole body); calls `rawNode` 4971 | no | none (recurses on `rawNode`'s OUTPUT) |
| 7 | `machLiftScalarN` (4641) | R: via `machNormNode`, `machBoolMap` | no | partial: `ShippingReaderBoolMap*` uses it as a parameter (`lift`) |
| 8 | `machBoolMap` (4820) | R: `machNormMap` | no | `machBoolMapT` (`ShippingReaderBoolMap`, `…Leaf`), shadow `…BoolMapShadow` |
| 9 | `machConv` (3884) | R: mutual block, builds `MachRead` | no | none. `ShippingReaderLenOk` has frame lemmas for its 23 record updates |
| 10 | `machNested` (4016) | R: mutual | no | none |
| 11 | `machInstance` (4045) | R: mutual, pushes `insts` | no | none |
| 12 | `machInstanceS` (4079, local `inst`) | R: mutual, pushes `insts` | no | `inst` only: `instT` (`ShippingReaderInstTy`), shadow `…InstTyShadow` |
| 13 | `machChain` (4124) | R: mutual, the body | no | none |
| 14 | `machLoopBody` (4171) | R: mutual | no | none |
| 15 | `machLoopRoot` (4193) | R: mutual, pushes `kinds`/`inits`/`names` | no | none (`loopRoot_inits_length` covers the two `mapM`s, a `def` part) |
| 16 | `MachRecUnfold.headBetaM` (MachRecUnfold 54) | E: `userInliner` → `pass` | no | none |
| 17 | `MachRecUnfold.iota` (62) | E | no | none |
| 18 | `MachRecUnfold.reduceHead` (127) | E | no | none |
| 19 | `MachRecUnfold.betaAll` (142) | E | no | none |
| 20 | `MachRecUnfold.listLit?` (172) | E | no | none |
| 21 | `MachRecUnfold.passM` (243) | E | no | none |
| 22 | `MachRecUnfold.relevantClosure` (283) | E: the gate of `userInliner` 3403 | no (already structural on `fuel`; deleting `partial` only is the change, `F-reader-unit.md`) | none |
| 23 | `stripMemoizeWrappers` (Elab 2078) | L: `synthesizeCombinational` 5328 | no | used in `ShippingLegacySem*` statements (G2), no total twin |
| 24 | `Optimize.inferWidth` (IR/Optimize 45) | P: `optimizeModule` under `checkedOptimize` (result-checked by `OptCheck`) | no | the result checker (OptCheck) |
| 25–33 | `Optimize.resolveSliceOfConcatAux` 73, `resolveSlice` 103, `optimizeExpr` 231, `collectExprRefsAux` 247, `countExprUses` 258, `substituteExpr` 325, `eliminateZeroBitInExpr` 596, `resolveSubst` 668, `renameRefs` 674 | P: same | no | the checker; `renameRefsT` (OptCheck 176) is the structural twin of `renameRefs` |
| 34 | `RegDedup.canonExpr` (IR/RegDedup 47) | P: `checkedOptimize` / print guard | no | the checker |
| 35 | `AST.Expr.toString` (IR/AST 222) | P: debug printing | no | — |
| 36 | `DimExpr.evaluate` (IR/Type 68) | —: `Specialize` (the machine reader refuses `parameters ≠ []`) | no | — |
| 37 | `DimExpr.toString` (IR/Type 101) | — | no | — |
| 38 | `Specialize.specializeType` (IR/Specialize 56) | —: `specializeDesign` (parameterised designs), CUDA sim | no | — |
| 39 | `Specialize.specializeExpr` (75) | — | no | — |
| 40 | `PatternDetect.collectRefs` (IR/PatternDetect 43) | —: TimerOracle, Backend.Partition | no | — |
| 41 | `PatternDetect.exprContains` (53) | — | no | — |
| 42 | `PatternDetect.findCountdownCore` (65) | — | no | — |
| 43 | `SynthesizableLint.scanExpr` (Compiler/SynthesizableLint 97) | —: test lint | no | — |

The R rows are 15 functions: 2 switched and 13 still `partial`. The open ones are rows 3–15, and seven of them (rows 9–15) form ONE mutual block. E has 7. P has 12, which sit behind a result checker or are printers. L has 1. Eight are off the route (rows 36–43). Total of `partial` functions: 13 + 7 + 12 + 1 + 8 = 41.

### What the two switches reach, and what they do not reach (READ)

`projChain` and `prodMatcherArity?` are called only by `rawNode`. `rawNode` is called only by `machNorm` (row 6, `partial`), and `machNorm` recurses on `rawNode`'s output. Every path from the two switched functions to the returned `MachineShape` therefore goes through `machNorm` and then through the mutual block.

So the switches give theorems about `rawNode` (`rawNode_canon`, `rawNode_pairArm_some`). They give **no** theorem about any field of the returned shape. In particular they do not give R5: R5 is `MachRead.LenOk` of the state the mutual block returns (`B-readerinv.md` §8.2–8.3).

## 2. The unit: output-port data checks for EVERY reader result

### Why this unit

Three facts decide the choice:

* **R5, the shortest route.** R5 needs equations for rows 9–15 (one mutual block, about 360 lines) plus `machNorm` (row 6), in the COMPILER. All 23 record updates already preserve `LenOk` (`ShippingReaderLenOk`, written). The only missing piece is the unfolding equations, and providing them is a compiler change. That is a user decision and is NOT taken here: the ruling allows compiler changes only "if strictly needed for a total-function switch-over".
* **What can be shown for ALL inputs today.** Every shape field that the wrapper `machineShape?` (a `def`) computes WITHOUT reading `MachRead`. `ShapeDecomp` (built) pins these down. Of them, `layout.outs = machOutFields _ outs` depends only on `declOuts? senv d.type`, and `machOutFields` writes `ty := machHWType k` and `width := machWidth k` for EVERY kind `k`.
* **The data checks this matches.** Two checks that generated endpoints decide per declaration are exactly properties of `layout.outs` that hold for every `k`:
  * `outTy` — `∀ o ∈ outs, o.ty.bitWidth = o.width`. It is decided by `#machine_no_ports_mem`, `…_seq`, `#oneout_gen`, `#oneout_any_gen`, and it is a hypothesis of about 30 run lemmas.
  * `outScalar` — `∀ o ∈ outs, scalarTy o.ty = true`. It is decided by `#machine_no_ports_mem`.

This is the G3b item, "data checks hold of every reader output" (`ShippingCompiler-FinalGoal.md`). It is the first such check proved for every input rather than one declaration at a time.

### Statements (`Tools/ShippingReaderOutsInv.lean`)

```lean
theorem outs_of_reader (h : machineShape? sym params ci senv allow = some sp) :
    ∀ o ∈ sp.layout.outs, o.ty.bitWidth = o.width ∧ scalarTy o.ty = true
theorem outTy_of_reader    (h : machineShape? … = some sp) : ∀ o ∈ sp.layout.outs, o.ty.bitWidth = o.width
theorem outScalar_of_reader (h : machineShape? … = some sp) : ∀ o ∈ sp.layout.outs, scalarTy o.ty = true
theorem reader_of_core (hcore : RunsTo (synthesizeCombinationalCore c [] false) … (M, D) w1)
    (entry : MachineDefines … c shape) : ∃ ci senv, machineShape? false [] ci senv = some shape
theorem outTy_of_core     (hcore) (entry) : ∀ o ∈ shape.layout.outs, o.ty.bitWidth = o.width
theorem outScalar_of_core (hcore) (entry) : ∀ o ∈ shape.layout.outs, scalarTy o.ty = true
```

`reader_of_core` gets the three run facts that `MachineDefines` quantifies over from `synthesizeCombinationalCore_reads hcore`, the same steps `synthesizeCombinationalCore_machine_sound` uses. So `MachineDefines` stays a hypothesis and is never assumed to be satisfiable.

### The discharged premise (`Tools/ShippingReaderOutsMemOnly.lean`)

`MemOnlyDataR` is `MemOnlyData` without `outTy` and `outScalar`. The theorems `memOnly_runFacts_of_reader`, `…_outsCheck_of_reader`, `…_kidsMem_of_reader` and `…_designCheck_of_reader` have the conclusions and run hypotheses of the four theorems behind `#machine_no_ports_mem`'s `f.noPortsMem_runFacts / _outsG0 / _kidsMemG / _designP0`. With them, the generated `decide`s `f.noPortsMem_outTy` and `f.noPortsMem_outScalar` are no longer needed, and no per-declaration computation replaces them.

The generator still emits both `decide`s. Switching it to `MemOnlyDataR` is a separate change and a follow-up. The same `outTy_of_core` applies wherever a lemma has `outTy` beside `hcore` and `entry`: `ShippingChecksCore`, `…Raw`, `…Masked`, `…Outs`, `…Derived`, `ShippingCallSelf`, `ShippingCallsChildPorts`.

### What this does NOT give

* No conjunct of `d.ok`. The output NAME conjuncts (`outNameOk`, `Nodup`, non-empty) also come from the wrapper alone: the `if outs.isEmpty || …` test at 5069. They need one more inversion step that `machineShape?_decomp` drops (its `ite_none_inv` discards the condition). That is the next unit, and it is still not a whole premise, because `d.ok` is decided as one Bool. Output WIDTH positivity is not derivable: `senv.fields` can carry any kind.
* Nothing about `insts`, slots, `let`s, R1, R5, or NIN. These are results of rows 5, 9–15.

## 3. Predicted axioms, risks

Predicted axioms:
* `outs_of_reader`, `outTy_of_reader`, `outScalar_of_reader`, `outTy_of_core`, `outScalar_of_core`, `memOnly_*_of_reader`: `[propext, Classical.choice, Quot.sound]`, inherited from `machineShape?_decomp`, which is built with standard axioms.
* `bitWidth_machHWType`, `scalarTy_machHWType`: none, or `propext` if the `simp` fallback is taken.
* `machOutFields_ty`: `[propext]` at most.

Risks (PREDICTED):
1. `machOutFields_ty`, the cons case. `List.mem_cons.mp h` must see through `machOutFields` (structural, so `whnf` should do it). Two fallbacks are provided: `simp only [machOutFields, List.mem_cons]` and `rw`. If all three fail, the stated `lo` term may not match the elaborated one syntactically up to defeq.
2. `reader_defn`, the non-definition constructors. `cases h` is tried first, with `unfold`/`simp` as fallbacks. The same statement is `machineShape?_defn` in `ShippingCallWidthsEntry` (it is repeated here because I could not confirm that file was built).
3. `reader_of_core` pattern counts. `synthesizeCombinationalCore_reads` returns 9 witnesses before the three facts. `MachineDefines` takes 9 explicit arguments before the three facts. Both counts were READ.
4. `MemOnlyDataR`'s field types are copied as text from `MemOnlyData` (`ShippingMemOnly` 115–132), with the same `open`s. `toData` relies on the field ORDER of `MemOnlyData`.

## Integration (integrator, 2026-10-15) — BUILT with one fix
Applied on poc 877e5280 (lakefile conflict: both rounds appended lean_libs at the end — kept both). Run `r1`
(cgrun, 3 GiB, swap 0, `-j 1`): as written `ShippingReaderOutsInv` failed in `machOutFields_ty`'s cons case
(a hand-written structure literal for the head did not parse); integrator fix: `simp only [machOutFields,
List.mem_cons] at h` then the two cases (no statement changed). Then `Tools.ShippingReaderOutsInv`,
`Tools.ShippingReaderOutsMemOnly`: exit 0. Axioms: `outs_of_reader`, `outTy_of_core`, `outScalar_of_core`,
`reader_of_core`, `memOnly_{runFacts,outsCheck,kidsMem,designCheck}_of_reader`
[propext, Classical.choice, Quot.sound].
Status: the output-port invariant holds for EVERY `machineShape?` result (general, no per-declaration
computation); the memory-only theorems no longer need the per-declaration `outTy` / `outScalar` decides. The
generator `#machine_no_ports_mem` is NOT switched to them yet. NOT reached: R5 and the other reader-derived
data (`insts`, slots, `let`s, R1, NIN) — they come from `machNorm` and the 7-function mutual block, still
`partial`; making them total is a compiler change (needs a ruling). Partial count (compiler side, §1): 41
`partial def` in Sparkle/Compiler + Sparkle/IR (13 on the reader path), 2 switched.
