# `RefLawsCore` re-audit and a minimal pure heap model

Round par/heap, base 87874a82. New Lean file `Tools/ShippingHeapModel.lean` (registered in
`lakefile.lean`): **BUILT** (hm1 exit 0; ax2: no axioms; writing-time guesses G1-G6 accepted). Nothing
added to `RefLaws`, `RefLawsCore`, `ChildLaws`, any trust/allowed list or `Sparkle/`; no axiom.
**`ChildBnd` is not discharged; nothing here removes a premise.**

Abbreviations: `CI` = `Tools/ShippingChildInv.lean`, `CC` = `Tools/ShippingChildBndCore.lean`,
`HM` = `Tools/ShippingHeapModel.lean`, `LEAN` = `~/.elan/toolchains/leanprover--lean4---v4.32.1/src/lean`.

## 0. Background facts used by the audit

* `ST.Prim.Ref.get/set/mkRef` are `@[extern] opaque` (`LEAN/Init/System/ST.lean:186-191`); the
  world is `Void σ := (Void.nonemptyType σ).type`, an opaque NONEMPTY type (`ST.lean:15-19`).
  So in the logic every law relating two worlds is about uninterpreted functions: a
  set-theoretic model may interpret `Void IO.RealWorld` as a heap and `Prim.Ref.*` as heap
  functions. This is why the laws CAN be consistent even where they are false of the real
  runtime (see "fit" below). Consistency and fit are different questions.
* `ST.Ref σ α` is a structure `{ ref : RefPointed.type, h : Nonempty α }` (`ST.lean:172-173`):
  the cell pointer is UNTYPED. In the logic one can form `⟨sparkleChildCache.ref, ⟨∅⟩⟩ :
  IO.Ref (Lean.ExprStructMap String)` — a ref of another type aliasing the cache cell.
* `Meta.Context.canUnfold? : Option (Config → ConstantInfo → CoreM Bool)`
  (`LEAN/Lean/Meta/Basic.lean:504`) is a CALLBACK stored in the context; `getUnfoldableConst?`
  runs it (`LEAN/Lean/Meta/GetUnfoldableConst.lean:33`), so `whnf`/`unfoldDefinition?`/… run
  caller-supplied code when the context carries one.
* `whnfImp` calls `reduceNative?` (`LEAN/Lean/Meta/WHNF.lean:1008`, `:1116`), which for
  `Lean.reduceBool c` / `reduceNat c` runs `evalConstCheck` (`WHNF.lean:1003-1006`): COMPILED
  code of a constant of the current environment.
* `Meta.whnf` / `Meta.inferType` are `@[extern] opaque` (`Basic.lean:777`, `:832`): no
  statement about them can be refuted in the logic, so the problems above are FIT problems,
  not inconsistencies.
* Compiler refs with the SAME type as a tracked ref: `sparkleSubModuleCache` (same type as
  `sparkleChildCache`, `Sparkle/Compiler/Elab.lean:1024` vs `:1032`) and the `IO.Ref Nat`
  side refs (`Elab.lean:759-760, 952-953, 1095-1108`) like `sparkleSynthDepth` (`:963`).

## 1. Re-audit of the 14 `RefLawsCore` fields (`CC:102-160`, from `RefLaws` `CI:333-442`)

Common to every field except `quiet`: **∀ `mctx : Meta.Context`, ∀ `cctx : Core.Context`**
(implicit binders; every context, including contexts with a `canUnfold?` callback, any
options, any heartbeat limits), over FIXED `mref`/`cref` (the structure's parameters).
"Pure model" = could a model with world := heap and refs := cells satisfy it.
"Fit" = is it true of Lean's real runtime.

| # | Field (CC line / CI line) | Worlds | Operations / refs quantified | Callback / caller-supplied action quantified? | Pure model consistent? | Fit to runtime / flag |
|---|---|---|---|---|---|---|
| 1 | `quiet` (CC:104 / CI:351) | predicate on worlds, witness-chosen | — | — | yes (any predicate; HM uses `Q h.reg`) | content only through 2-6, 7, 8. Taking `True` turns `diag` into an all-worlds printer frame (`childbnd-residual.md` row C). |
| 2 | `diag` (CC:105 / CI:354) | every **quiet** `w` | `Diag p` (CI:264): `profLog b msg` (any `b`, `msg`), `ppExpr e` (any `e`), `IO.eprintln s`, `msgToString m` for `OkMsg m` (CI:137), `getStderr`, `flushStderr` (named action), `Handle.mk p m` (**any path, any mode**), `h.putStrLn s` / `h.flush` (**any handle `h`**) | no closure argument (the `ioFlush` of any `IO.FS.Stream` was removed, `docs/ShippingCompiler-TrustBase.md:920-927`); BUT `msgToString` runs the printers of `c.env` for each `withContext c` leaf — gated by `OkEnv c.env` (CI:122) inside `OkMsg`; `ppExpr` runs the current env's delaborators — gated only by `quiet w` | yes if `quiet` constrains the registry and the stderr writer (not modelled in HM) | **SUSPICIOUS (fit)**: `Handle.mk p m` + `h.putStrLn` for ANY path: e.g. `/proc/self/mem` opened for writing can overwrite the cache in the real process; `quiet` (a world predicate) cannot depend on the caller's path. Contrived, but the law is false of the runtime for such paths. Not modelled. |
| 3 | `frameT` (CC:109 / CI:359) | **every** `w` (values); quiet kept | `Throws p` (CI:281): `throwError msg`, lifted Core `throwError msg`, for **any** `msg : MessageData` (lazy thunks included) | `msg` may carry code (`ofLazy`), but `throwError` does not render it: `addMessageContext` only reads env / mctx / lctx / opts | yes (HM `frameT`, trivially: a throw does not touch the heap) | plausible; relies on `addMessageContextFull` running no callback (true in v4.32.1 by reading, unproved). |
| 4 | `excOk` (CC:113 / CI:370) | every **quiet** `w` | `Op p` (CI:288) = all `Framed` (incl. Meta primitives), all `Diag`, `throwError msg` with `OkMsg msg` | indirectly: the exception of `whnf`/`inferType`/`mkAppM`/… in ANY context (incl. `canUnfold?` callbacks, whose own exceptions propagate unchanged!) must be `OkExc` | ref-only part yes (HM `excOk`: framed ref ops never throw; a throw of `okE e` is `okE`) | **SUSPICIOUS (fit)**: a `canUnfold?` callback (`Basic.lean:504`) can `throw` an arbitrary `Exception` (an `ofLazy`/`.trace`/`.ofWidget` message, not `OkMsg`) and `whnf` propagates it; `reduceNative?` runs compiled code that can throw anything; T3 (Lean's own messages are in `OkMsg`) is unaudited — `OkMsg` (CI:137) has no `.trace`, `.ofWidget`, `ofGoal` (an `ofLazy` with another closure), `hint` constructors. Also needs `OkEnv` of the CURRENT env at every quiet world (`throwError` wraps `withContext {env := current}`), so `quiet` must imply `OkEnv` of the env in `cref` — witness-choosable, but then `frameQ` must preserve it. |
| 5 | `frameQ` (CC:115 / CI:375) | every quiet `w` | every `Framed p` (CI:189) | same as row 7 | ref-only part yes (HM `frameQ`: ref ops leave `reg`) | Meta-primitive part: see row 7 (a `canUnfold?` callback can register a printer / replace stderr). Not modelled. |
| 6 | `cacheSetQ` / `depthSetQ` (CC:117, 119 / CI:377, 382) | every quiet `w` | the set of the tracked cache (any `v`) / depth (any `v`) | no | yes (HM; `set_reg`) | plausible: a ref write does not touch the registry (fit OPEN). |
| 7 | `frame` (CC:122 / CI:388) | **every** `w` (NOT quiet-gated) | `Framed p` (CI:189-262): (a) reads of the 3 refs; (b) get/set/modify/modifyGet (plain and `liftM`-IO forms) of the 24 `SideRef`s (CI:69-96), any value, any pure `f`; (c) `IO.mkRef v` / get / set / modify of **ANY ref** `r : IO.Ref σ` with `LocalRefType σ` (only `ExprStructMap String`, CI:98) incl. `exprCache*` constructors; (d) `getEnv`, `getConstInfo n`, `IO.getEnv n`, `monoMsNow`, `mkFreshFVarId`, `throwUnknown`, Meta `get`, Meta `modify f` (any pure `f`), trace modify; (e) Meta primitives `whnf`, `inferType`, `isClass?`, `whnfUntil`, `instantiateForall`, `mkLambdaFVars`, `mkAppM`, `unfoldDefinition?`, `reduce`, any arguments | (c): the ref `r` is CALLER-SUPPLIED; (e): in every `mctx`, which may carry the `canUnfold?` callback; `whnf`/`reduce` may run compiled constants (`reduceNative?`) of the world's env; no closure appears as a constructor argument | (a),(b),(c),(d-ref part) yes — HM `frame` (`FramedR`: tracked reads, other-cell get/set/modify/modifyGet, alloc) | **SUSPICIOUS (fit), three ways**: (i) (c) for `r := ⟨sparkleChildCache.ref, _⟩` re-typed to `ExprStructMap String` (ST.lean:172) — a write through it changes the cache in the runtime (and is memory-unsafe); consistent in the logic only because the model can key cells by type. (ii) (e) under a context whose `canUnfold?` writes the cache: false of the runtime for all worlds. (iii) (e) `whnf (reduceBool c)` in an environment whose `c` is implemented by side-effecting compiled code: false for such worlds — and `frame` is NOT quiet-gated, so `quiet` cannot exclude them. (b) also needs the 24 side refs to be cells distinct from the 3 tracked ones, incl. the SAME-TYPED `sparkleSubModuleCache` and the `Nat` side refs (§0): true by `initialize` allocating fresh cells — a fit fact (row (d) of the ledger). |
| 8 | `cacheSet` (CC:125 / CI:393) | every `w` | set of the cache, any `v` | no | yes (HM `cacheSet`, from `get_set_same`, `get_set_other`) | get-after-set + non-aliasing of the 3 cells: fit OPEN (row b). |
| 9 | `depthSet` (CC:128 / CI:404) | every `w` | set of the depth, any `v` | no | yes (HM `depthSet`) | as row 8. |
| 10 | `telescope` (CC:131 / CI:413) | every `w` with `I w` | `forallTelescopeReducing ty k`, **any** `ty`, **any** continuation `k`, **any** `I` closed under value- and quiet-preserving steps | **YES: `k` is a caller-supplied action**, guarded by the hypothesis `∀ mctx' cctx' xs b, Keeps mctx' … I (k xs b)` (every context — a STRONG hypothesis, which weakens the law); the combinator itself runs `whnf` in `mctx` (row 7 (ii)/(iii)) | the guard makes it look consistent: a model in which the combinator's own steps frame the 3 cells satisfies it (Keeps of `k` by hypothesis, Keeps of the rest by frame and closure of `I`). NOT modelled (needs a model of Meta's combinator) | **SUSPICIOUS (fit)** only through `whnf` under a `canUnfold?` callback / native reduction (row 7 (ii),(iii)); the continuation is correctly guarded. |
| 11 | `lamTelescope` (CC:139 / CI:421) | same | `lambdaTelescope e k cleanup` | YES, `k`, guarded as row 10 | as row 10 | as row 10 (`lambdaTelescope` does not reduce, so less exposed; still `instantiateMVars`/local-context code). |
| 12 | `localDecl` (CC:147 / CI:429) | same | `withLocalDeclD n ty k` | YES, `k : Expr → MetaM α`, guarded `∀ mctx' cctx' x` | as row 10 | plausible (extends `lctx`, runs `k`); fit OPEN. |
| 13 | `letDecl` (CC:154 / CI:436) | same | `withLetDecl n ty v k` | YES, `k`, guarded | as row 10 | as row 12. |

Definitions inside the fields (CI): `endW` (300), `ErrOk` (306), `Keeps` (315) — definitions,
quantify `∀ w` (Keeps) over the given contexts. `Inert x` (108): `∀ w` (all worlds) for a
`BaseIO` action — used only inside `OkEnv` (122: `∀ ctx : PPContext` with `ctx.env = env`,
both printer entry points, any expr / name). `OkMsg` (137) / `OkExc` (154): message class.

Not a field but load-bearing for consistency: there is NO `Framed`/`Diag` constructor taking
a closure, stream or `IO`/`MetaM` action argument any more (TrustBase.md:925-927 test). The
remaining caller-supplied things are: refs of a LocalRefType (row 7 c), file paths / handles
(row 2), messages (rows 2-4, gated by `OkMsg` except in `frameT`), continuations (rows 10-13,
guarded), and the CONTEXTS themselves (every field: `canUnfold?`).

### 1a. Suspicious fields (summary)

1. **`frame` / `frameQ` / `excOk` for Meta primitives, and `telescope`/`lamTelescope` via
   `whnf`, quantified over EVERY `Meta.Context`**: `canUnfold?` (Basic.lean:504) is a
   caller-supplied `CoreM` callback run by unfolding (GetUnfoldableConst.lean:33). This is the
   same shape as the removed `Framed.ioFlush`, but not a logical inconsistency because
   `whnf`/`inferType` are `@[extern] opaque` (no proof can run the callback). It IS false of
   the runtime. Candidate repair (not done; a law change, needs a decision): restrict the
   context quantifier to `mctx.canUnfold? = none` (or to contexts the compile builds).
2. **`frame` for `whnf`/`reduce`, NOT quiet-gated**: `reduceNative?` (WHNF.lean:1008/1116)
   runs compiled code of constants of the world's environment; false of the runtime for
   environments containing a side-effecting `reduceBool` target. Candidate repair: gate the
   Meta-primitive constructors on `quiet` (and let `quiet` constrain the environment).
3. **`frame` for `localGet/Set/Modify`, `exprCache*` over ANY caller-supplied ref of type
   `ExprStructMap String`**: `ST.Ref` has an untyped pointer (ST.lean:172), so a re-typed alias
   of a tracked cell exists in the logic; the law is false of the runtime for it. Candidate
   repair: quantify over refs created by the run (a provenance predicate), not over all refs
   of a type.
4. **`diag` for `Handle.mk` / `putStrLn` / `flush` of any path/handle**: false of the runtime
   for handles onto the process's own memory (`/proc/self/mem`). Low practical risk; the law
   could name the profile log path (`profLogIO`, CI:60) instead.
5. **`excOk` content (T3)**: `OkMsg` lacks `.trace`, `.ofWidget`, `ofGoal`/other `ofLazy`
   closures and hint/note constructors; that Lean's primitives never throw such messages is
   unaudited, and with a `canUnfold?` callback (item 1) false.
6. **Concurrency** (all fields): the world-passing reading is sequential; a concurrent task
   (Lean's async elaboration, `Task.spawn`) writing the three refs between two steps falsifies
   every frame law. Not stated anywhere; a fit premise.

No field was found LOGICALLY unsatisfiable: every suspicious item rests on an `@[extern]`
opaque or on an untyped-pointer alias that an interpretation of the opaques can separate.
That is an argument, not a proof: joint satisfiability of the full `RefLawsCore` is not
proved (ledger row e).

## 2. The pure heap model (`HM`, written, not built)

* `Sig` (HM:77): the contents' types `C` (cache), `S` (synthesis ref), `O` (every other cell),
  `P` (printer registry), `E` (exceptions); generic, so no import beyond `Init`.
* `Heap σ` (HM:86): `cache`, `synth`, `depth : Nat`, `other : Nat → O`, `next`, `reg`.
* `Ref σ : Type → Type` (HM:98): `cache`, `synth`, `depth`, `other n` — typed refs; `Ref.id`.
* `hget` / `hset` / `alloc` (HM:121-135) pure; actions `M σ α := Heap σ → Out σ α` (the shape of
  `EST`), `getM`, `setM`, `modifyM := bindM getM (setM ∘ f)`, `modifyGetM`, `allocM`, `throwM`;
  `endW`, `RunsTo`, `readOf`, `cv`/`sv`/`dv` mirroring CI:300, `ShippingEntrySoundness.lean:937`,
  CI:102, CC:43-47.
* `FramedR` / `ThrowsR` / `OpR` (HM:283-300): the ref-only constructors of `Framed`, `Throws`,
  `Op` (no `Diag`, no Meta primitives).
* `HeapLaws σ okE` (HM:328): fields `quiet, frameT, excOk, frameQ, cacheSetQ, depthSetQ, frame,
  cacheSet, depthSet` — the SAME shapes as the `RefLawsCore` fields of the same names.

Theorems (all in HM; statements abbreviated):

* `get_set_same : hget r (hset r v h) = v`
* `get_set_other : r.id ≠ r'.id → hget r' (hset r v h) = hget r' h`
* `set_reg : (hset r v h).reg = h.reg`
* `alloc_spec`: the new cell reads `v`; cells `< next`, the three tracked cells and `reg` kept
* `runsTo_getM : RunsTo (getM r) h a h' → a = readOf r h ∧ h' = h` (read-frame)
* `runsTo_setM : RunsTo (setM r v) h u h' → h' = hset r v h`
* `modify_split` (modify = get; set), `endW_modifyM`
* `allocM_runs`, `FramedR.runs` (never throws), `FramedR.keeps`
* `HeapLaws.model Q okE : HeapLaws σ okE` with `quiet h := Q h.reg` — **the consistency proof
  of the ref-only fragment, in the model**
* `heapLaws_sat : Q p0 → ∃ (L : HeapLaws σ okE) (h : Heap σ), L.quiet h ∧ readOf synth h = s0 ∧
  readOf depth h = 0 ∧ readOf cache h = c0` (model analogue of the RHS of `childBnd_iff_core`,
  CC:285)
* `heapLaws_nonempty : Nonempty (HeapLaws σ okE)`
* `frame_all_false : c ≠ h.cache → ¬ ∀ {α} (p : M σ α) h, cv (endW p h) = cv h` — a frame law
  over all (caller-supplied) actions is false even in the model (the `ioFlush` shape).

Not covered by the model (stay open): `diag` (printers, stderr, file handles, `profLog`);
`excOk` for Lean's elaborator exceptions (`OkExc`/`OkEnv`); the `frame`/`frameQ`
constructors for `getEnv`, `getConstInfo`, `whnf`, `inferType`, `isClass?`, `whnfUntil`,
`instantiateForall`, `mkLambdaFVars`, `mkAppM`, `unfoldDefinition?`, `reduce`, Meta
`get`/`modify`, trace modify, fresh fvar, clock, env-var read, `throwUnknown`; `telescope`,
`lamTelescope`, `localDecl`, `letDecl`.

## 3. Ledger

| row | item | status |
|---|---|---|
| (a) | pure model laws | **PROVED in HM (written, not built)**: get-after-set, set-frame for distinct ids, read-frame, modify = get;set, alloc spec; model analogues of `frame` (ref-only constructors), `frameQ`, `cacheSet`, `depthSet`, `cacheSetQ`, `depthSetQ`, `frameT`, `excOk` (model's own throws only); instantiated by `HeapLaws.model`; `heapLaws_sat`, `heapLaws_nonempty`, `frame_all_false`. |
| (b) | fit of the pure model to Lean's extern ST refs (`ST.Prim.Ref.get/set/mkRef`, `Void IO.RealWorld`) | **OPEN** — not stated, not proved. Includes: the three tracked refs are distinct cells; the side refs (incl. same-typed `sparkleSubModuleCache` and the `Nat` refs) are distinct cells; no re-typed alias is ever used (§1a item 3); no concurrent writer (item 6). |
| (c) | fit for MetaM primitives / printers / exceptions | **OPEN** — and per §1a items 1, 2, 4, 5 the CURRENT statements are false of the runtime for adversarial contexts / environments / paths; repairing them is a law change (needs a decision). |
| (d) | initial contents (`initialize`, `IO.mkRef`) | **OPEN** (`childbnd-residual.md` R13/R14). |
| (e) | joint satisfiability of the full `RefLawsCore` | **OPEN** — only the ref-only fragment is satisfied, by the model. Every `ChildBnd`-premised theorem may still be vacuous. |
