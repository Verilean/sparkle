# `ChildBnd` fully unfolded: what the one nested antecedent of `<p>_designClosedB` asks

Round par/cbnd, base 5e8f8b7a. Status of the new Lean files: **BUILT** by the integrator (cb1/cb2 exit 0; one fix: explicit `C` binder in `cacheModify'`/`depthModify'`; axioms standard, ax1). Guess G3 (`modify` unfolds) was ACCEPTED by cb2, so the D* rows are derived
(`Tools/ShippingChildBndInit.lean`, `Tools/ShippingChildBndCore.lean`; writing-time guesses
marked in the files and listed in §5). Nothing added to `RefLaws`, `ChildLaws`, any trust /
allowed list, or `Sparkle/`. No new law: every new statement is a theorem or a definition whose
both directions are stated (`childBnd_iff`, `childBnd_iff_core`).

All line numbers are of this worktree at 5e8f8b7a. `CI` = `Tools/ShippingChildInv.lean`.

## 0. The statement

`<p>_designClosedB` (`Tests/Compiler/MemNameCollisionGateBoundTest.lean`, e.g. `:41`, `:69`,
`:97`, `:125` for the `_names` lemmas they use) carries

    hB : Tools.ShippingChildInv.ChildBnd mref cref w        -- w = the start world of the core run

    ChildBnd mref cref w := ∃ L : RefLaws mref cref, StartV L w ∧ L.quiet w        (CI:674)
    StartV L w := L.sval w = some synthesizeChild ∧ (L.dval w = 0 ∨ CacheInv mref cref (L.val w))  (CI:582)
    RefLaws mref cref : structure, 26 fields                                        (CI:333-442)

So `ChildBnd` = (A) existence of a 26-field law witness, (B) a start condition by that witness's
value functions, (C) the witness's `quiet` at `w`.

## 1. The table

Status: **D** derived in the repo (theorem cited) — **D\*** derived by the new files of this round
(built cb2) — **I** derivable from the initial state by a lemma that does not exist yet —
**R** needs a runtime model of IO/ST primitives (or of Lean's own compiled primitives), stays a
premise — **O** other/open.

### 1a. The outer shape

| # | Lean | About | Status |
|---|---|---|---|
| A0 | `∃ L : RefLaws mref cref` (`ChildLaws = Nonempty RefLaws`, CI:667) | that the 26 laws are jointly satisfiable at all | **O/R**: no model exhibited (`docs/ShippingCompiler-TrustBase.md:928` "A model of the laws is not exhibited"); the laws were inconsistent until `dc50653e` (TrustBase.md:920-926: `Framed.ioFlush` of any stream + `cacheSet` ⊢ `RefLaws → False`). A model needs a semantics of `ST.Prim.Ref.get/set` (opaque, `@[extern]`, `Init/System/ST.lean:188-191` of the v4.32.1 toolchain). Consistency of the CURRENT field list is not proved. |
| A1 | the split itself | — | **D\***: `childBnd_iff` (`ShippingChildBndInit.lean:191`): `ChildBnd w ↔ StartW w ∧ QuietAt w` (StartW law-free, CI:486; QuietAt = `∃ L, L.quiet w`, CI:473). `childBnd_iff_core` (`ShippingChildBndCore.lean:285`): `ChildBnd w ↔ (∃ C : RefLawsCore, C.quiet w) ∧ readOf sparkleChildSynth w = some synthesizeChild ∧ (readOf sparkleSynthDepth w = 0 ∨ CacheInv (readOf sparkleChildCache w))`. |

### 1b. `StartV L w` (CI:582)

| # | Lean | About | Status |
|---|---|---|---|
| B1 | `L.sval w = some synthesizeChild` | contents of the IO.Ref `sparkleChildSynth` in `w` | **D\*** reduction: `refLaws_sval_eq` (`ShippingChildBndInit.lean:82`): every witness has `L.sval w = readOf sparkleChildSynth w` (from the field `synthGet` and the lift's definition). Residual `readOf sparkleChildSynth w = some synthesizeChild`: **R**. The ref is created `IO.mkRef none` (`Sparkle/Compiler/Elab.lean:1040`) and set once by `initialize sparkleChildSynth.set (some synthesizeChild)` (`Elab.lean:8934`; the only write in `Sparkle/`). That this leaves `some synthesizeChild` readable at `w` needs the semantics of `initialize`, of `Prim.Ref.set`/`get`, and that nothing between initialisation and `w` writes the ref. The repo has NO lemma about what a fresh / initialised ref contains (`readOf` (CI:102) is used nowhere else). |
| B2 | `L.dval w = 0` (left disjunct) | contents of `sparkleSynthDepth` in `w` | **D\*** reduction: `refLaws_dval_eq` (`ShippingChildBndInit.lean:89`). Residual `readOf sparkleSynthDepth w = 0`: **R** (created `IO.mkRef 0`, `Elab.lean:963`; same missing fresh-ref semantics). Balance across EARLIER completed entry runs is **D relative to the laws** for runs that start in `J L D` (`entry_keeps_all`, `ShippingChildKeeps.lean:498`: `J` carries `L.dval = D` to the end world, every outcome); for an OUTERMOST earlier run (start condition `StartV`, not `J`) the corresponding lemmas are **I, BUILT (bl1 exit 0, ax2 standard)** (round par/bal, `Tools/ShippingChildBalance.lean`): `core_balance` / `full_balance` (`StartV L w → L.quiet w → L.dval w = 0 → Out0 L (endW … entry w) ∧ ErrOk … entry w`, every outcome; `Out0 L w := L.sval w = some synthesizeChild ∧ L.quiet w ∧ L.dval w = 0`), `core_bnd0` / `full_bnd0` (`ChildBnd0 w → ChildBnd0 (endW … entry w)`, `ChildBnd0 w := ∃ L, StartV L w ∧ L.quiet w ∧ L.dval w = 0`; `childBnd0_iff : ChildBnd0 w ↔ ChildBnd w ∧ readOf sparkleSynthDepth w = 0`), `core_bnd_readOf`, `core_then_core` (two consecutive core runs), `endSeq_bnd` / `seq_start_bnd` (n entries). Route: the prefix under `Out0` (frame laws; the guard throw before the bump included), the clear establishes `J L 0` (`tripleO_clear`), body at depth 1 by `bodyRel`+`childKeeps`, `finally` by `fin_triple`.  The chain from initialisation through the session also needs frames of every non-Sparkle command run in between: **R**. |
| B3 | `CacheInv mref cref (L.val w)` (right disjunct) | the cache's contents: each entry a `RealChild` | Not needed for an outermost run: `core_reads_inv` (`ShippingChildRun.lean:134`) uses only B1 and C in the depth-0 branch (the entry clears the cache, `Elab.lean:5541`). If used: `refLaws_val_eq` (`ShippingChildBndInit.lean:75`) reduces it to `CacheInv (readOf sparkleChildCache w)`; for the initial empty cache `CacheInv {}` is **D** (`cacheInv_empty`, CI:808) and `readOf sparkleChildCache w = {}` is **R** (`IO.mkRef {}`, `Elab.lean:1032`). |
| B3a | `RealChild c r` (CI:453), inside `CacheInv` | a run of `synthesizeCombinational c` from a world with `CacheAt`, `SynthAt`, `∃ L, L.quiet` | **D** for entries the compile inserts (`synthesizeChild_inv`, `ShippingChildRun.lean:203`; `RealChild.of_inv` CI:825). Only reached on a nested start. |
| B-init | B1 ∧ B2 from the initial contents | — | **D\*** (the connection asked for): `startV_of_init` (`ShippingChildBndInit.lean:172`): `readOf sparkleChildSynth w = some synthesizeChild → readOf sparkleSynthDepth w = 0 → StartV L w` for EVERY witness `L`; `startV_of_init_empty` (`:179`) with `readOf sparkleChildCache w = {}` instead of depth 0; law-free `startW_of_readOf` (`:113`) and its converse `readOf_of_startW` (`:124`); `startV_of_startW` / `startW_of_startV` (`:151`, `:162`). The premises are the refs' contents (`readOf`), strictly below `StartV` (which is about a witness's fields). The premises themselves: **R** (B1, B2). |

### 1c. `L.quiet w`

| # | Lean | About | Status |
|---|---|---|---|
| C | `L.quiet w` (field CI:351) | the diagnostic environment of the start world: no registered pretty-printer and not the installed stderr writes the three refs (trusted condition T1, `docs/ShippingCompiler-GeneralTheorem-Audit.md:366`) | **R**. `quiet` is a field chosen by the witness; it has content only through `diag`, `excOk`, `frameQ`, `*SetQ`, `frameT`. Choosing `quiet := fun _ => True` would turn `diag` into an all-worlds frame law for printers — the very law the T1 split removed. A proof needs a model of what the environment's registered delaborators/unexpanders and the stderr stream do to the heap. `ChildBnd.plain` / `childBnd_iff` isolate it as `QuietAt w`; `childBnd_iff_core` as `∃ C : RefLawsCore, C.quiet w`. |

### 1d. The 26 fields of `RefLaws` (CI:333-442)

"values" = `val`/`sval`/`dval`; "contents" = `readOf` of the cache / synthesis ref / depth ref.

| # | Field (line) | Statement, short | About | Status |
|---|---|---|---|---|
| F1 | `val` (334) | world → cache map | value function | **D\***: `refLaws_val_eq` (`ShippingChildBndInit.lean:75`): `L.val w = readOf sparkleChildCache w` for every witness. In `RefLawsCore` it is DEFINED as `cv` (`ShippingChildBndCore.lean:43`). |
| F2 | `sval` (335) | world → synthesis-ref value | value function | **D\***: `refLaws_sval_eq` (`:82`); `sv` (`ShippingChildBndCore.lean:45`). |
| F3 | `dval` (336) | world → depth | value function | **D\***: `refLaws_dval_eq` (`:89`); `dv` (`ShippingChildBndCore.lean:47`). |
| F4 | `aux` (343) | auxiliary predicate of the map | proof parameter, no runtime content | **D**: `RefLaws.plain` (CI:597), `withAux_val/sval/dval/quiet` by `rfl` (`Tools/ShippingCallsSame.lean:87-90`); **D\*** `ChildBnd.plain` (`ShippingChildBndInit.lean:216`): any `ChildBnd` witness can be taken with `aux = True`. |
| F5 | `auxInsert` (344) | closure of `aux` under a miss insert | proof parameter | **D** (as F4; trivial for `True`). |
| F6 | `quiet` (351) | world predicate | see row C | **R** (row C). |
| F7 | `diag` (354) | `Diag p` (CI:264: `profLog`, `ppExpr`, `IO.eprintln`, `msgToString` of an `OkMsg` message, `getStderr`, `flushStderr`, `Handle.mk/putStrLn/flush`) from a quiet world: values kept on every outcome, end world quiet | printers, stderr, file handles, the entry's logger — IO effects + environment printers | **R** (T1). `OkMsg` (CI:137) / `OkEnv` (CI:122) / `Inert` (CI:108) appear here as a HYPOTHESIS restricting the law (`Diag.msgToString m : OkMsg m → …`), not as an assumption. That the compiler's own messages are `OkMsg` is **D** (closure tactic `okmsg`, CI:167, called by `vc` at every throw site, Audit.md:243-246). |
| F8 | `frameT` (359) | `throwError msg` (any `msg`): values kept on every outcome; quiet kept | `throwError` runs `addMessageContext` (reads Meta/Core state through `mref`/`cref`) | **R** (reads of `mref`/`cref` return an opaque world; "the three refs' contents unchanged" needs `Prim.Ref.get` frame semantics). |
| F9 | `excOk` (370) | an exception an `Op` (CI:288) throws from a quiet world is `OkExc` (= `OkMsg e.toMessageData`), INCLUDING `OkEnv` of the context it captures | messages of Lean's own primitives (`whnf`, `inferType`, `getConstInfo`, …) and the printers of the environments the compile runs in | **R** — trusted T3 (`docs/ShippingCompiler-GeneralTheorem-Audit.md:238-242`). Beyond ST semantics: needs a model of Lean's compiled elaborator primitives (many are `@[extern]`/`opaque`, e.g. `Meta.whnf`) and of the registered delaborators (`OkEnv`). |
| F10 | `frameQ` (375) | `Framed` ops keep quiet | the compile registers no printer / does not replace stderr | **R** (T2, Audit.md:300). |
| F11 | `cacheSetQ` (377) | cache `set` keeps quiet | same | **R** (T2). |
| F12 | `cacheModifyQ` (379) | cache `modify` keeps quiet | same | **D\*** (guess G3): `RefLawsCore.cacheModifyQ'` (`ShippingChildBndCore.lean:176`) from `frameQ` (`.cacheGet`) + `cacheSetQ`, via `modify_split` (`:54`: `ST.Prim.Ref.modify` is DEFINED as get-then-set). |
| F13 | `depthSetQ` (382) | depth `set` keeps quiet | same | **R** (T2). |
| F14 | `depthModifyQ` (385) | depth `modify` keeps quiet | same | **D\*** (G3): `depthModifyQ'` (`:195`). |
| F15 | `frame` (388) | `Framed` ops (CI:189: reads of the three refs; get/set/modify of the 8 `SideRef`s CI:69 and of run-local refs; `getEnv`, `getConstInfo`, `whnf`, `inferType`, `isClass?`, `whnfUntil`, `instantiateForall`, `mkLambdaFVars`, `mkAppM`, `unfoldDefinition?`, `reduce`, Meta `get`/`modify`, trace modify, fresh fvar, clock, env-var read, expr caches) leave the values on every outcome | (i) a READ leaves the world's contents; (ii) a write to ANOTHER ref leaves these three (non-aliasing of distinct `IO.Ref`s); (iii) Lean's compiled primitives touch only `mref`/`cref` | **R**. (i),(ii) need `Prim.Ref.get/set` semantics and ref distinctness; (iii) a model of Lean's `@[extern]`/`partial` Meta code. |
| F16 | `cacheGet` (391) | a returning cache read returns `val w` | the read returns the contents | **D\*** once `val := readOf …`: `runsTo_get_readOf` (`ShippingChildBndInit.lean:56`, by the lift's definition), used in `RefLawsCore.toRefLaws` (`ShippingChildBndCore.lean:204`). For an ARBITRARY `val` it is what pins `val` to the contents (F1). |
| F17 | `cacheSet` (393) | after `set v`: cache = `v`, the other two unchanged | get-after-set; non-aliasing | **R**. |
| F18 | `cacheModify` (396) | after `modify f`: cache = `f` of before, others unchanged | — | **D\*** (G3): `RefLawsCore.cacheModify'` (`:166`) from `frame` (`.cacheGet`) + `cacheSet` via `modify_split`. |
| F19 | `synthGet` (400) | a returning synthesis-ref read returns `sval w` | — | **D\*** as F16. |
| F20 | `depthGet` (402) | a returning depth read returns `dval w` | — | **D\*** as F16. |
| F21 | `depthSet` (404) | after `set v`: depth = `v`, others unchanged | get-after-set; non-aliasing | **R**. |
| F22 | `depthModify` (407) | after `modify f`: depth = `f` of before | — | **D\*** (G3): `depthModify'` (`:186`). |
| F23 | `telescope` (413) | `forallTelescopeReducing ty k` keeps any value-invariant `I` if every continuation run does (in any contexts) | Lean's combinator runs `whnf`, creates fvars, extends the local context (writes `mref`) | **R** (model of Lean's Meta implementation + ST frame). |
| F24 | `lamTelescope` (421) | same for `lambdaTelescope` | same | **R**. |
| F25 | `localDecl` (429) | same for `withLocalDeclD` | same | **R**. |
| F26 | `letDecl` (436) | same for `withLetDecl` | same | **R**. |

### 1e. Definitions inside the fields (no assumption of their own)

| Lean | About | Status |
|---|---|---|
| `endW` (CI:300), `ErrOk` (CI:306), `Keeps` (CI:315), `RunsTo` (`ShippingEntrySoundness.lean:937`) | the end world of a run on any outcome; "an exception is OkExc"; invariant kept; one run in fixed contexts | definitions — **D** (nothing assumed). |
| `Framed` (CI:189), `Diag` (CI:264), `Throws` (CI:281), `Op` (CI:288), `SideRef` (CI:69), `LocalRefType` (CI:98) | the SCOPE of each law (which operations a law speaks of) | definitions; their size is the size of the R rows F7-F15. A test rejects `Framed` constructors over caller-supplied streams/actions (TrustBase.md:925-927). |
| `OkMsg` (CI:137), `OkExc` (CI:154), `OkEnv` (CI:122), `Inert` (CI:108) | message class; inert printers (`Inert` is stated by `readOf` at two worlds) | definitions; they enter as hypotheses of `diag` (restricting it) and as the conclusion of `excOk` (row F9, R). `OkEnv` of a concrete environment would itself be an R statement (printers' frame on the heap). |

### 1f. Variants (not in `<p>_designClosedB`)

* `ChildBndM` (`Tools/ShippingMemoLaws.lean:262`) = `∃ L : RefLawsM, StartV L.toRefLaws w ∧ L.quiet w`; `RefLawsM` (`:90`) adds `mval`, `memoGet`/`memoSet`/`memoModify` (R, same kind as F16-F18; `memoModify` would follow from get/set as F18), `distinct` (ASSUMED non-aliasing, R), `memoFrame` (R). Implies `ChildBnd` (`ChildBndM.toChildBnd`, `:270`).
* `ChildBndC` (`Tools/ShippingCacheCoherent.lean:159`) adds `Coherent (L.val w)` on the nested branch only; at depth 0 it equals `ChildBnd`'s depth-0 case (`childBndC_of_zero`, `:224`; `ChildBndC.bnd`, `:218`).

## 2. What was proved this round (built cb2)

`Tools/ShippingChildBndInit.lean` (imports `Tools.ShippingChildInv` only):

* `runsTo_get_readOf : RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w a w' → a = readOf r w`
* `refLaws_val_eq / refLaws_sval_eq / refLaws_dval_eq (L) (mctx cctx) w : L.val w = readOf sparkleChildCache w` (resp. synth, depth)
* `synthAt_of_readOf`, `cacheAt_of_readOf`, `startW_of_readOf`, `readOf_of_startW`
* `startV_of_startW (L) (mctx cctx) : StartW mref cref w → StartV L w`; `startW_of_startV (L) : StartV L w → StartW mref cref w`
* **`startV_of_init (L) (mctx cctx) : readOf sparkleChildSynth w = some synthesizeChild → readOf sparkleSynthDepth w = 0 → StartV L w`**; `startV_of_init_empty` (cache `= {}` instead of depth 0)
* **`childBnd_iff (mctx cctx) : ChildBnd mref cref w ↔ StartW mref cref w ∧ QuietAt mref cref w`**
* `childBnd_of_init (mctx cctx) : QuietAt w → readOf synth w = some synthesizeChild → readOf depth w = 0 → ChildBnd w`; `childBnd_of_init_empty`
* `ChildBnd.plain : ChildBnd w → ∃ L, StartV L w ∧ L.quiet w ∧ ∀ m, L.aux m`

`Tools/ShippingChildBndCore.lean` (imports the above):

* `cv / sv / dv` := `readOf` of the three refs
* `modify_split : RunsTo (ST.Ref.modify r f) … w u w' → ∃ w1, RunsTo (ST.Ref.get r) … w (readOf r w) w1 ∧ RunsTo (ST.Ref.set r (f (readOf r w))) … w1 u w'`
* `structure RefLawsCore mref cref` — 14 fields: `quiet, diag, frameT, excOk, frameQ, cacheSetQ, depthSetQ, frame, cacheSet, depthSet, telescope, lamTelescope, localDecl, letDecl`, each the `RefLaws` field with `val/sval/dval := cv/sv/dv`
* `RefLawsCore.cacheModify' / cacheModifyQ' / depthModify' / depthModifyQ'`
* `RefLawsCore.toRefLaws : RefLawsCore → RefLaws` and `RefLawsCore.ofRefLaws (mctx0 cctx0) : RefLaws → RefLawsCore` (quiet preserved by `rfl` both ways) — so `RefLawsCore` is NOT a strengthening and NOT a new law: it is the same assumption with 12 fields discharged
* **`childBnd_of_core (C) : C.quiet w → readOf synth w = some synthesizeChild → (readOf depth w = 0 ∨ CacheInv (readOf cache w)) → ChildBnd w`** (no contexts needed); `childBnd_of_core_init`
* **`childBnd_iff_core (mctx0 cctx0)`** (statement in row A1).

Proved vs premise: all of the above are theorems/definitions without new hypotheses; their
hypotheses are the residual rows below. None of the R rows is discharged.

## 3. What remains after this round (precise list), and why it needs runtime semantics

Reading of `ChildBnd w` after the new files (`childBnd_iff_core`):

    (∃ C : RefLawsCore mref cref, C.quiet w)                                  -- R1-R12 + R0
    ∧ readOf sparkleChildSynth w = some synthesizeChild                        -- R13
    ∧ (readOf sparkleSynthDepth w = 0 ∨ CacheInv (readOf sparkleChildCache w))  -- R14 (outermost: depth 0)

| id | residual | why it needs a runtime model |
|---|---|---|
| R0 | joint satisfiability of `RefLawsCore` (A0) | no model of `ST.Prim.Ref.get/set` (opaque `@[extern]`) exists in the logic; consistency not proved. |
| R1 | `quiet w` (C) + `diag` (F7) | effect of printers / stderr / file handles / logger on the heap. |
| R2 | `frameT` (F8) | `throwError` reads `mref`/`cref`; a read's effect on the world is opaque. |
| R3 | `excOk` (F9, T3) | content of Lean's own primitives' exceptions and `OkEnv` of the captured environments: compiled Lean code, not definable in the logic. |
| R4 | `frameQ`, `cacheSetQ`, `depthSetQ` (F10, F11, F13, T2) | quietness preserved by the compile's own operations. |
| R5 | `frame` (F15) | reads leave the world; writes to other refs do not alias these three; Lean primitives (`whnf`, … opaque/`partial`) touch only `mref`/`cref`. |
| R6 | `cacheSet`, `depthSet` (F17, F21) | get-after-set and non-aliasing for the opaque `Prim.Ref.set`. |
| R7 | `telescope`, `lamTelescope`, `localDecl`, `letDecl` (F23-F26) | Lean's Meta combinators' implementation. |
| R13 | `readOf sparkleChildSynth w = some synthesizeChild` (B1) | semantics of `initialize` (`Elab.lean:8934`) and `IO.mkRef` (`:1040`); no write in between. No repo lemma about what a fresh ref contains. |
| R14 | `readOf sparkleSynthDepth w = 0` (B2) | `IO.mkRef 0` (`Elab.lean:963`) semantics at the FIRST entry; the balance across consecutive Sparkle entries is the (I) lemmas of row B2 (BUILT (bl1 exit 0, ax2 standard), `Tools/ShippingChildBalance.lean`); frames of everything run between commands: R. |

Discharged this round (built cb2): F1-F3, F16, F19, F20 (values are the contents),
F4-F5 (auxiliary, already D), F12, F14, F18, F22 (modify = get then set).

Row B2's (I) — the outermost-run depth balance — is BUILT by bl1 (exit 0; axioms standard, ax2) (round par/bal,
`Tools/ShippingChildBalance.lean`, theorems listed in row B2). What it gives for R14: the
session-level balance ACROSS Sparkle entries, i.e. `ChildBnd0` (= `ChildBnd` ∧ `readOf
sparkleSynthDepth = 0`) at the start of the first outermost entry implies it at the start
of every later one, when each entry starts in the previous one's end world (any outcome;
`endSeq`). What stays open in R14: (a) the contents at the FIRST entry (`IO.mkRef 0`, R14
proper, and R13, and `QuietAt` = R1) — premises; (b) frames of every non-Sparkle command
run between entries (`endSeq` assumes none) — R; (c) R0, so the balance may be vacuous.


## 4. Over-claim check

* Nothing here removes a premise of `<p>_designClosedB`; it re-reads `ChildBnd` as an equivalent
  conjunction whose non-runtime parts are now theorems. The R rows are still assumed by every
  `ChildBnd`-premised theorem, and their joint consistency (R0) is not shown, so those theorems
  could still be vacuous.
* `readOf` facts at the start world are NOT derived; the "initialisation → StartV" lemma moves
  the premise from a witness's field to the refs' contents, nothing more.

## 5. Writing-time guesses (all accepted by build cb2)

* G1 `runsTo_get_readOf`: the `change` to `match (ST.Ref.get r : ST IO.RealWorld σ) w with …` on a
  hypothesis (as `refGet_runs` CI:690 does on a goal); `rw [hg]` inside `readOf`'s match.
* G2 `ChildBnd.plain`, `childBnd_of_core`, `toRefLaws.cacheGet`: definitional unfolding of
  `RefLaws.plain` / `toRefLaws` projections and of `cv/sv/dv` accepted by `exact` / anonymous
  constructor.
* G3 `modify_split`: `ST.Ref.modify` → `ST.Prim.Ref.modify` (a `def`, `@[implemented_by]`, in the
  `module` `Init/System/ST.lean`) and `ST.bind` unfold by `change` from a non-module file. If the
  module system hides the body, `modify_split` fails; then F12, F14, F18, F22 must move back into
  `RefLawsCore` (four more R-shaped fields, but get-after-set + read-frame suffice in content).
  `ShippingChildBndInit.lean` does not depend on G3.
* G4 `RefLawsCore.ofRefLaws`: `rw [← hv, ← hs, ← hd]` rewrites the constants `cv/sv/dv` under the
  fields' binders.

Modules to list in the lakefile (not edited): `Tools.ShippingChildBndInit`, `Tools.ShippingChildBndCore`.
