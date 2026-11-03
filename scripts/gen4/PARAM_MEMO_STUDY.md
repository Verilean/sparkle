# PARAM_MEMO_STUDY: RefLawsM against the ledgers, and whether option B (no memo hit below the parametric top) can be shown

Status: study only. No Lean source in the tree is edited; nothing is proved. Base 014e4dc9 (par/param-memo).
Ledger: FG 92 / T1 57 (this unit: FG -0 +0 / T1 -0 +0).
Vocabulary: **counted** = printed by a command in this unit; **read** = my reading of code, not checked by Lean;
**observed** = a scratch run of the real compiler (an observation, not a proof). This study did not find a supply path or
a ledger row where one is said to be missing; that is not a claim of impossibility. Scratch files (a Lean-level file and a
runtime probe) were built once each (`kjob lake build`, exit 0) and removed; they are not in the tree.
Ledger sources: `par/fg-ledger-sync:scripts/gen2/PREMISE_LEDGER.md` + `premise_ledger/*.md`, `par/t1-ledger-sync:scripts/gen3/PREMISE_LEDGER.md`.

## 0. Result in short

1. **No field of `RefLawsM` that is about the memo is in any ledger row, in `Laws` (`L.O`/`L.T`), or in the parametric
   chain's existing premises.** The only memo-related ledger item found is T1L-25 / G-MEMO (an unassigned *obligation*,
   "`CacheShips` does not cover the memo"), which names no law. The base `RefLaws` (26 fields) is the premise of B.P-7
   (I3c, `Tools/ShippingGen4ParamKeeps.lean`); `Laws` is a *different, restricted* structure (T1L-01) and the bridge
   between them is itself open (T1L-22). So `RefLawsM` = B.P-7's `RefLaws` (existing) + 6 memo fields (not in any ledger).
2. In `readOf` normal form (§1.3) the memo content of those 6 fields is small: a *set law* and a *frame law*. But the
   existing `RefLawsM.memoFrame` covers only **3** operations (the stretch between the depth-0 reset and the first memo
   read), whereas the translator walk uses the **40**-constructor framed class and the four telescope combinators. So
   **option A as the tree has it is not enough for the whole walk**; it needs an extension (new premise candidates
   C-M1..C-M3, §2, elaborated in scratch).
3. **Option B** (memo hits do not occur below the parametric top): the reading (§3) gives a concrete invariant
   `memo keys ⊆ child-cache keys` that makes every memo read miss, because every in-translator child run goes through
   `synthesizeChild`, which tests the child cache first, and memo and child cache are reset together. Observed on 3
   fixtures: no miss-with-memo-entry. But **B does not remove the memo laws**: stating and carrying that invariant
   through the walk needs the same set/frame/telescope facts about the memo. B only avoids a *content* invariant.
4. No route found in this study avoids new memo-cell laws other than a production guard (option C, out of scope and not
   allowed here). Recommendation in §5.

## 1. Field-by-field table

Definitions read from `Tools/ShippingMemoLaws.lean` (RefLawsM) and `Tools/ShippingChildInv.lean:333` (RefLaws).
Counted by the scratch (`getStructureFields`): `RefLaws` 26 fields; `RefLawsM` own 6 + `toRefLaws`; `RefLawsAOps` 10;
`RefLawsATele` 4; `Laws` = {O, T}. Constructors: `SideRef` 24, `Framed` 40, `FramedA` 40, `MemoOther` 9, `MemoFrameOp` 3.
Constant closure (counted, scratch, `Tools.`/`Sparkle.` constants of types/defs/ctor types): `Laws` 69 consts, `RefLawsAOps` 63,
`RefLawsATele` 31, `RefLaws` 58, `RefLawsM` 61. The memo cell `sparkleSubModuleCache` occurs in the closure of `Laws`/`RefLawsAOps`/`RefLaws`
**only as a `SideRef` constructor** (a ref whose operations are "framed": they leave `cv/sv/dv`). `RefLawsM` and `MemoFrameOp`
occur in no closure of `Laws`, `RefLawsAOps`, `RefLawsATele`, `RefLaws`.

### 1.1 The 6 memo fields

| field (Tools/ShippingMemoLaws.lean) | FG row | T1 row | `Laws` (L.O/L.T) | N1 TRUSTED | parametric existing (I3b/I3c, RefLaws) | verdict |
|---|---|---|---|---|---|---|
| `mval : World → HashMap Name Res` | none | none (T1L-25 names the memo as an obligation only) | no field; the analogous child-cache view `cv` is *defined* (`readOf`, `ShippingChildBndCore.lean:43`) | none | none | not a premise as such if replaced by `readOf` (§1.3); as written it is data of the structure |
| `memoGet` (read returns `mval`, leaves it) | none | none | the child-cache analogue is not a field of `RefLawsAOps` (it is `runsTo_get_readOf`, a theorem) | none | `RefLaws.cacheGet` is a field of the old `RefLaws` (B.P-7) | first half derivable by the generic `runsTo_get_readOf` (read, built); "leaves it" is the *read-frame* |
| `memoSet` (after `set v`, `mval = v`) | none | none | analogue `RefLawsAOps.cacheSet` (T1L-01) exists for the child cache only | none | `RefLaws.cacheSet` (B.P-7), child cache only | **new content**: needs a memo analogue |
| `memoModify` | none | none | analogue absent (derived by `modify_split`) | none | `RefLaws.cacheModify` (B.P-7) | derivable from get+set by the generic `modify_split` (read, built); not a premise in normal form |
| `distinct` (9 refs ≠ memo, `¬HEq`) | none | none | none; local fresh refs get non-alias from `RefLawsAOps.frame` at the *tracked* refs, not the memo | none | none | **new**; header says not provable in the logic; side-condition of the frame law in normal form |
| `memoFrame` (3 ops leave `mval`) | none | none | none | none | none | **new**, and too narrow (§2) |

"none" for FG/T1 means: no row of the ledger texts above mentions it (greps for `memo`, `subModule`, `RefLawsM`, `MemoFrame` found only
T1L-25, the G-MEMO lines in `GENERAL_SPEC.md:173,255,377` and `PREMISE_LEDGER` T1 §"G-MEMO"). I did not read every row of the 1500-line A_M2
file line by line; the search was by those strings.

### 1.2 The inherited `RefLaws` fields (the `toRefLaws` part)

They are exactly B.P-7's premise (FG ledger, unassigned, "RefLaws 系 (I3c, ParamKeeps.lean)"). They are not `Laws`: `Laws.O : RefLawsAOps`
has 10 fields (restricted by `AdmCtx`, quiet worlds, `FramedA Fresh`) and `Laws.T : RefLawsATele` 4; the source of `RefLawsAOps` says it is
"NOT derived from the old `RefLawsCore` fields (a different assumption)". T1L-22 lists "a `RefLaws` ↔ `Laws`/`JQC` bridge" as open. So
"RefLaws is already a trusted premise" holds for the parametric chain only through B.P-7, and it is *a different TRUSTED object* than T1L-01.
Definitional identity was not tested with `isDefEq`: the two structures have different fields, so they are not defeq; a field-wise
correspondence is the open bridge, not something this unit establishes.

### 1.3 What the memo premises reduce to (read, by analogy with a built result)

`Tools/ShippingChildBndCore.lean` (header, "BUILT cb2") shows `RefLaws`' 26 fields are equivalent to a 14-field `RefLawsCore` once the value
functions are `readOf` of the refs: `val/sval/dval`, `cacheGet/synthGet/depthGet`, `aux/auxInsert`, the `*Modify*` fields carry no runtime content
(generic lemmas `runsTo_get_readOf`, `modify_split`, quantified over *any* `IO.Ref`). The same applies to the memo: with `mv w := readOf sparkleSubModuleCache w`
(a definition, elaborated in scratch) only the *set law* and the *frame law(s)* remain. I did not prove this equivalence for the memo.

## 2. New premise candidates (complete types; elaborated in scratch, exit 0; NOT used; decision belongs to review)

Scratch file `Tests/Gen4/ParamMemoScratch.lean` (built: `kjob lake build Tests.Gen4.ParamMemoScratch`, 705 jobs, exit 0, no sorry; file and
lakefile entry removed). Context: `Fresh`, `mref`, `cref`, `O : RefLawsAOps Fresh mref cref`; `mv w := readOf sparkleSubModuleCache w`.

```lean
def mv (w : Void IO.RealWorld) : Std.HashMap Name Res := readOf Sparkle.Compiler.Elab.sparkleSubModuleCache w

inductive MemoOpA : {α : Type} → MetaM α → Prop   -- the 8 access shapes of the memo cell
  | get : MemoOpA (ST.Ref.get sparkleSubModuleCache : MetaM _)
  | set (v) : MemoOpA (ST.Ref.set sparkleSubModuleCache v : MetaM Unit)
  | modify (f) : MemoOpA (ST.Ref.modify sparkleSubModuleCache f : MetaM Unit)
  | modifyGet {β} (f : _ → β × _) : MemoOpA (ST.Ref.modifyGet sparkleSubModuleCache f : MetaM β)
  | modifyGetIO {β} (f : _ → β × _) : MemoOpA (liftM (ST.Ref.modifyGet sparkleSubModuleCache f : IO β) : MetaM β)
  | getIO : MemoOpA (liftM (ST.Ref.get sparkleSubModuleCache : IO _) : MetaM _)
  | setIO (v) : MemoOpA (liftM (ST.Ref.set sparkleSubModuleCache v : IO Unit) : MetaM Unit)
  | modifyIO (f) : MemoOpA (liftM (ST.Ref.modify sparkleSubModuleCache f : IO Unit) : MetaM Unit)

-- C-M1 memoFrame over the whole framed class (40 ctors, not 3)
def MemoFrameAll (O : RefLawsAOps Fresh mref cref) : Prop :=
  ∀ {mctx cctx}, AdmCtx O.quiet mctx cctx → ∀ {α} (p : MetaM α) (_hp : FramedA Fresh p), ¬ MemoOpA p →
    ∀ w, O.quiet w → mv (endW mctx mref cctx cref p w) = mv w

-- C-M2 memoSet (and modify, which is derivable in normal form; kept to mirror RefLawsM)
def MemoSetLaw (O : RefLawsAOps Fresh mref cref) : Prop :=
  (∀ {mctx cctx}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
     RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = v) ∧
  (∀ {mctx cctx}, AdmCtx O.quiet mctx cctx → ∀ f w u w',
     RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = f (mv w))

-- C-M3 memoTele: the four fields of RefLawsATele with `mv w' = mv w` added to the combinator's "leaves" list
structure MemoTele (O : RefLawsAOps Fresh mref cref) : Prop where
  telescope lamTelescope localDecl letDecl   -- same statements as RefLawsATele, premise
    -- `∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (quiet w → quiet w') → I w → I w'`
```
(`MemoTele` is written out in full in the scratch; the four fields are those of `RefLawsATele` with that one extra conjunct.)
Why each is needed: the existing `Keeps`-style walk (`telescope`/`lamTelescope`/`localDecl`/`letDecl`) pushes an invariant `I` through a combinator only
if `I` depends on `cv, sv, dv` (+quiet); an invariant that reads the memo cannot be pushed through them without C-M3. C-M1 is needed at every one of the
40 framed constructors that is not a memo access. C-M2 at the 5 writer sites and the reset. `RefLawsM.distinct`'s 9-ref class covers 9 of the 23 other `SideRef`s
and none of the run-local fresh refs; in this form the side condition is carried by `¬ MemoOpA p`, which is *syntactic*: it says an op whose term is a memo
access is excluded, and relies on the law being true of the other refs; whether the runtime guarantees that is exactly the `distinct` assumption.
These are *candidates*, not decisions. They are TRUSTED-boundary statements (new law fields) and require the reviewer / user.

## 3. Option B: can memo hits be excluded below the parametric top?

Read from `Sparkle/Compiler/Elab.lean` (lines as at base).

* **Where the memo is read**: only at 5335, inside `synthesizeFromConst`, guarded by `!symbolicMode`, on the legacy arm (after gates and the machine arm decline).
* **Where it is written**: 5297, 5304, 5323, 5388 (the gate, mixed, machine and legacy arms) — each is the *last effect* of the arm (`modify (insert declName result)`, then `return result`); and
  `set {}` at 5540 (depth 0). `grep` finds no other `sparkleSubModuleCache` use in `Sparkle/` (counted: 9 lines incl. the `initialize` and 2 comments).
* **Reset**: depth 0 resets memo *and* child cache together (5540-5541); nested runs reset neither (5545-5553 reset the per-module maps only).
* **Children are non-symbolic**: the symbolic mode is entered only by `synthesizeCombinationalWithParameters` (commands, depth 0); children are reached through
  `childSynthEntry` / `closeInsts*` → `sparkleChildSynth` → `synthesizeChild` (8929), which calls `synthesizeCombinational n` (parameters `[]`, `symbolicMode = false`).
  (PARAMETRIC_FREEZE §1.4 says the same; `Elab.lean:6326-6334`.)
* **Key fact**: `synthesizeChild n` checks the *child cache* first (8930) and only on a miss runs the entry, which can read the memo. The memo holds `n` only after a run of `n`
  returned through its last effect; then `synthesizeChild` inserts `n` into the child cache after only pure post-processing (`synthesizeCombinationalWith`: zero-width, `mergeChecked`; `IO.getEnv`).
  So the invariant **K: every memo key is a child-cache key** holds at every point where translator code runs, except inside that window.
* **Consequence**: at a miss in `synthesizeChild n` (so `n ∉ child cache`, law `cacheGet` / `readOf`), K gives `n ∉ memo`, so the memo read at 5335 misses for the run of `n`.
  The scratch has `MemoKeysInChild` and `memo_miss_of_child_miss` (proved, 3 lines, from the statement of K only).
* **Differences that matter for F-kids**: the memo stores the *raw* `result` (before `synthesizeCombinationalWith` post-processing) while the child cache stores the post-processed pair. So *if* a memo hit
  could happen, it would hand back a pair that is not what F-post has treated. This is a second reason the hit must be excluded rather than carried.
* **What B needs, as proof obligations (none done)**: (a) K at the start of every depth ≥ 1 run; K at depth 0 after the reset is `{}`, trivially. (b) K preserved by every translator step: the steps do
  not write the memo, so this is the frame law C-M1 at the 40 constructors and C-M3 at the 4 combinators, plus C-M2 at the 5 writer sites (a writer inserts `n` while `n` is the in-flight name; K is
  restored by the child-cache insert right after, so K must be stated with an "in-flight name" exception, i.e. `K_n` during the run of `n` and `K` outside). (c) the window between memo write and
  child-cache insert is exception-free (post-processing is pure; `IO.getEnv` cannot throw in the model — this is a claim about `MetaM` semantics that must be written as a lemma). (d) every depth ≥ 1 call of the
  entry in the translator is through `synthesizeChild` (read: `Rec.synthesizeCombinational := childSynthEntry`, `closeInstsM/GM` use `synth`; `StartV` pins `sval = some synthesizeChild`, existing).
* **Existing items**: `outer_miss` (`Tools/ShippingLegacySemMemoWalk.lean:495`) is the depth-0 miss from the reset (premises `RefLawsM`, `EntryConstIs`, gate declines); it does not speak about depth ≥ 1.
  `Tools/ShippingMemoInv.lean` states a *content* invariant (`MemoInv`, `ArmObligations`, `MemoSound`) "statements only; no theorem uses them" — option A's material. G-MEMO (`GENERAL_SPEC.md:255`):
  "needs its own invariant, or a proof that machine-route parents never read it for their children" — the second branch is option B's M3 analogue; T1L-25 is unassigned.
* **Possible counterexamples**: (i) a depth ≥ 1 call of the entry not through `synthesizeChild` — none found (`grep` over `Sparkle/`: the callers of `synthesizeCombinational` are the commands at depth 0 and `Rec.synthesizeCombinational`); recursion on the same name is excluded only
  as "no memo/child entry exists before the run ends" (re-entry runs until the depth limit 1024 and throws). (ii) an exception between the memo write and the child-cache insert followed by a retry in a `try … catch` (6586/6598): none found, since the window is pure; this is the case a proof must exclude.
  (iii) a memo entry that is not in the child cache because it was written by the *top* of a non-symbolic depth-0 run: not relevant to a symbolic top, whose own writes happen last.
* **Observed** (scratch probe `Tests/Gen4/ParamMemoProbe.lean`, built once, exit 0, removed): a counted copy of `synthesizeChild` was installed in `sparkleChildSynth`; at every child-cache miss it recorded whether the memo already held the name. Three symbolic tops (`W := 8`),
  fixed-width `@[hardware_module]` children: `tNested` (c(c y)), `tDiamond` (d, e, c with d,e calling c), `tTwoOut` (a register child `pe2` instantiated twice, four record projections). Result: child-cache hits/misses 1/1, 2/3, 4/1;
  **miss-with-memo-entry = [] in all three**; memo keys = child keys in all three. A repeated child is served by the child cache, never by the memo. Limits: the tops themselves ended with `Native symbolic-width synthesis currently supports combinational modules only`
  (the children had been synthesized before that throw; these are not successful top runs); 3 fixtures, no `circuit do` parent with a memory, no fixture where a child is itself the second use after an exception. This is an observation of 3 runs and proves nothing for other designs.

## 4. Conclusions per option

| | needs (premises) | proof size | ledger prospect |
|---|---|---|---|
| **A** use `RefLawsM` as it stands | the 6 fields — **not** in FG/T1/Laws; and they are **insufficient** (memoFrame covers 3 ops) → C-M1, C-M2, C-M3 as new premises; also the content invariant `MemoPF` (`WorldPF`) carried by the walk (that is `ShippingMemoInv`'s unproved `MemoSound`) | the PARAM_INV_ESTIMATE figure (3500–5000 lines, estimated) **plus** the memo content walk at 5 writer sites and the C-M3 combinator cases; not counted | new premises ≥ 3 candidates (grouped, 1 law family) vs B.P-8 −1 / B.P-1 −1 (conditional); **net not shown negative** — may be ≥ 0 |
| **B** exclude hits (K) | the same C-M1/C-M2/C-M3 (the memo cell must still be observed), **no** content invariant, no `MemoPF`; plus (a)–(d) of §3 | PARAM_INV_ESTIMATE figure plus K's walk (the frame cases are shared with the walk's other cases); K's own proof is small relative to the translator walk, not counted | same as A for the premises; saves the content walk |
| **C** production guard (F-kids §5(c)) | production edit | out of scope; not allowed in this unit | n/a |
| **D** shared law family with M3's G-MEMO (T1L-25) | one memo law family serving both T1L-25 and M4 | shared; not counted | one new family instead of two; needs user decision on law scope |

R0 lines (conditional, unchanged from the approved estimate): B.P-8 −1, B.P-1 −1 only if F-θ, F-top, F-post, shape, assembly, F-kids are all proved; **F-kids alone: 0**. A or B add a memo law
family (C-M1..C-M3, count of ledger rows undetermined: could be 1 row or 3), so the *net* can be 0 or negative. This study does not assign row IDs.

## 5. What is needed from review / user (not decided here)

1. Whether memo-cell laws C-M1..C-M3 may be introduced as a TRUSTED family (new law: needs the user). Until then F-kids stays a statement and the ledger does not move.
2. Whether to treat them together with M3's G-MEMO (T1L-25) as one family (option D) rather than a parametric-only family.
3. If the family is not wanted: the only route found is the production guard (C), which is outside this unit and outside the current permission.
My lean (not a decision): B on top of one shared family (D) — it keeps the memo's *content* out of the trust base (only where the cell is written/framed), and K is the invariant the existing source structure supports.
Reversibility: all of it is before any proof exists; nothing is committed beyond this document.

`台帳: FG 92 / T1 57（今回 FG -0 +0 / T1 -0 +0）`
`条件付き台帳: B.P-8 -1 / B.P-1 -1（全項目揃った場合のみ。F-kids 単独は 0。A/B とも memo 法則の新前提 1〜3 行を伴い得て、相殺の可能性あり）`

## 6. Limits

* The ledger search was by string over the sync'd ledger files, not a row-by-row reading of all of A_M2 (1551 lines).
* §1.3 (memo reduces to set + frame in `readOf` normal form) is by analogy; not proved for the memo.
* K and its obligations (a)–(d) are read, not proved; `memo_miss_of_child_miss` is the only theorem (it assumes K).
* The probe's tops did not complete as successful top runs; fixtures are 3; no memory parents; the probe does not exercise the legacy arm's memo read (which arm each child took was not recorded).
* Not read to the end: the arm bodies of `synthesizeMachineCertified`, `closeInsts*` beyond the `synth` calls; `translateExprToWire` handlers other than the instance arms.
