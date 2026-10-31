# BOUNDARY-AUDIT freeze U2 (docs only; Lean follows after approval)

Issue: `sparkle-gen5-boundary-audit` (M5, N1 / G5 / G7 audit). Branch `kjob/g5ba-r4`, base `284595a4` (U1 five lemmas and the
R1/R2 audit fixes approved). This file ADDS to `scripts/gen5/BOUNDARY_AUDIT_FREEZE.md` (r1); nothing there is withdrawn
except where §2 below says a row is updated.
Sources read for this unit: `Tools/ShippingSrm3Callee.lean` (`MemCalleeData`, `memCallee_closesA`), `Tools/ShippingCallsMemPinned.lean`
(`machineClosesAtA_of_memKids'`), `Tools/ShippingSrm12Corr.lean` (`kidTA_name`, `instTagged_mem_idx`), `Tools/ShippingSrm7Rank.lean`
(`rkOf_edge`, `declRank_self`), `Tools/ShippingKid.lean` (`TagsAgree`, `agree_at`), `Tools/ShippingReaderFuelShapeProv.lean`
(`machineShapeF_tag_mem`), `Sparkle/Compiler/Elab.lean` (reader, read only), `Tools/ShippingHeapModel.lean` / `ShippingStartAtLoad.lean`
(headers), `scripts/gen2/GENERAL_SPEC.md` §1, §5, §6, `scripts/gen2/GEN2_DEFS.lean.txt`, `scripts/gen5/DG_CLOSINGRUN_FREEZE_R6.md`, and the
Issue notes recorded in `managerctl` (for the SHAs in §2; those SHAs are copied from the recorded approvals, not re-verified here).
"Not found" means only that this survey did not find a supplier or route; it does not say the row is impossible or underivable.
Nothing here claims N1, G5, M5, FG or Issue completion. No new TRUSTED boundary, law, compiler/shared-definition edit, FG narrowing
or GenWF strengthening is proposed.

## 1. N1 remainder: `hn`, `hmemSame`, `hself`

### 1.1 Where they are used (real names)
FG has no name binder. The chain that reaches names is `T1Hyp.closes` (`MachineClosesAtA`) ← `Tools.ShippingSrm3Callee.memCallee_closesA`
(Srm3Callee.lean:91) ← `Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids'` (CallsMemPinned.lean:330). In
`memCallee_closesA` the two fields `MemCalleeData.sepK` (Srm3Callee.lean:61) and `MemCalleeData.parent` (:64) are passed as the binders
`hsep` (CallsMemPinned.lean:248) and `hparent` (:252) of `machineClosesAtA_of_memKids'`. U1 (`hsep_of_kidNames`, `hparent_of_kidNames`,
approved) turns those two binders into the three premises below; this unit examines the three premises. `nameK` is a FREE function
parameter of `MemCalleeData`; it is related to the world only through `memT` (memory kids) and `hord`'s `ChildIfaceP (nameK k) …` (ordinary kids).

| premise | binder of the FG chain where it is needed | derivable from existing theorems / compiler text? | status after U2 |
|---|---|---|---|
| `hn : ∀ k hk, nameK k = kidModName (insts[k].1, org k)` | `hn` of `hsep_of_kidNames` and `hparent_of_kidNames` (feeding `MemCalleeData.sepK`/`.parent`) | `nameK` is chosen by the caller of `memCallee_closesA`. If the caller chooses `nameK := kidNameAt shape` (new def, §3), `hn` holds BY DEFINITION (`hn_kidNameAt`, a restatement of the choice, not a fact about the compiler). The content moves to: (a) `memT` first conjunct for memory kids — derivable (`kidNameAt_eq_memModule_name`, via `child?_eq_memModule` + `memModule_name`); (b) for ordinary kids `hord`'s `ChildIfaceP (nameK k) …` has the field `.name : y.1.name = nameK k`, so one needs `y.1.name = ofDecl c` for `RealChildA O c y` (B7, the premise `hn` of `kidTA_name`, Srm12Corr.lean:96). An unconditional theorem for every `RealChildA` was not found (the nearest are `hname_of_iface`, Srm15Graph.lean:58, which takes `ChildIfaceP (ofDecl c)` as a premise, and `machine_all`, CacheCoherentCert.lean:~410, which has the harness fact `hout` as a premise). | by choice of `nameK`: closed (definitional). B7 for ordinary kids: 未供給 / この調査で経路未発見 |
| `hmemSame : ∀ k k', memKey (org k) ≠ none → memKey (org k) = memKey (org k') → insts[k].1 = insts[k'].1` | `hmemSame` of `hsep_of_kidNames` (the callee-equality conjunct of `sepK` for two memory kids) | YES from `MemTagsNamed shape` (new Prop, §3): a memory-origin entry's callee name is `memChildName cb aw dw`, so equal memory keys give equal names. `MemTagsNamed` is implied by `TagsAgree` (`memTagsNamed_of_tagsAgree`; `TagsAgree` is the existing decidable check, ShippingKid.lean:~80, `decide`d per declaration at ShippingNoPortsMemCommand.lean:429). `TagsAgree` itself is stronger (it also says an ordinary entry's name is not a memory placeholder) and is NOT needed here: the compiler comment (MachInstOrigin.lean:5-10) says a declaration may carry a placeholder name, so `TagsAgree` can fail for such a declaration while `MemTagsNamed` stays meaningful. Supply of `MemTagsNamed` for the reader: the only place the reader creates a `.mem` origin is `Elab.lean:3959` with the name `memChildName combo aw dw` (a source reading, not a theorem; the reader is `partial`). For the fuel candidate `machineShapeF` the fact IS a theorem: `machineShapeF_tag_mem` (ReaderFuelShapeProv.lean:~320). The link from `T1Hyp.defines` (`MachineDefines`, whose reader is the production `machineShape?`) to `machineShapeF` is the reader-bridge item (`OldEq` is a hypothesis there, ReaderFuelOldEq.lean header): not found in this survey. | derivation from `MemTagsNamed`: closed. `MemTagsNamed` of the actual shape: 条件付き (PROVED for `machineShapeF`'s output; link to `MachineDefines`' shape 未供給 / 経路未発見) |
| `hself : ∀ k hk, memKey (org k) = none → insts[k].1 ≠ declName` | `hself` of `hparent_of_kidNames` (the non-memory kid is not the declaration itself) | YES from a rank: `Tools.ShippingSrm7Rank.rkOf_edge` (Srm7Rank.lean:212) gives every edge of a ranked declaration a module rank strictly below it; `declRank_self` (:248) is the `.ord` instance. A kid with `memKey = none` has `kidModName = ofDecl callee` (`rkOf_decl`), so `callee = declName` would give `r' < r` with `r' = r`. Premises: `callees g declName = some shape.instTagged` (the premise `hgraph` of `ran_designCorr`, Srm12Corr.lean) and `declRank g F declName = some r` (for the top: `inClass_rank`, Srm7Rank.lean:270; for a callee: `rkOf_edge` applied to its caller). `InstOrigin.field` is covered (`kidModName (c, .field i) = ofDecl c`), which `declRank_self` (stated for `.ord` only) does not state. | derivation from graph + rank: closed. The graph `g` and the rank premise are not binders of FG: their supply (InClass for the top, graph = the generated call graph) 未供給 / FG 最終型への接続は経路未発見 |

Additional rows examined in the same pass (both appear in `MemCalleeData`):

| field | exact Prop (Srm3Callee.lean:71,77) | derivable? | status |
|---|---|---|---|
| `memT`, name conjunct | `(originAt shape k).child? = some y → nameK k = y.1.name` | YES for `nameK := kidNameAt shape` (`kidNameAt_eq_memModule_name`). The conjuncts `nk k = 4`, `outsK k = ["out"]`, `namesK k = [y.1.name]` are not name facts and are NOT addressed. | name conjunct: closed for the chosen `nameK` |
| `memNames`, second conjunct | `y.1.name ≠ ofDecl C` for the memory kid's built module | YES, `memModule_name_ne_ofDecl` (`ofDecl_ne_ofMem`). The first conjunct `y.1.name ∈ names` depends on the supplied list `names`: not addressed. | second conjunct: closed |

Rows NOT closed by this unit (unchanged from r1 §1.2/§1.4): B3 `hparentD`, B4 `hdisjD`, B5 `hfresh`/`outHead` (G-CLOSES-FRESH), B6 `nameIn`
and `memNames` first conjunct, B7 for ordinary kids. The statement "B1/B2 are reduced to premises" does not say B1/B2 are supplied for FG.

### 1.2 Why this is not a restatement, and what it does not show
`hn_kidNameAt` is a restatement of a definition and is recorded as such. `memTagsNamed_of_tagsAgree`, `hmemSame_of_memTagsNamed`,
`hself_of_rank`, `kidNameAt_eq_memModule_name`, `memModule_name_ne_ofDecl` need case splits on `InstOrigin`, `agree_at`-style access
to `instTagged` (`instTagged_mem_idx`) and, for `hself_of_rank`, `rkOf_edge`. `sepK_parent_of_supply` composes them with the U1
theorems and has, for `nameK := kidNameAt shape`, exactly the shapes of `MemCalleeData.sepK` and `.parent`. It does not show that
the compiler's call graph is acyclic, that a given declaration has a rank, or that `MachineDefines`' shape satisfies `MemTagsNamed`.

## 2. FG final-type binder supply table (updated from the r1 skeleton)

State vocabulary: 証明済み = a theorem in tree for exactly that binder; 条件付き = an approved theorem whose premises are not themselves supplied (or
whose clean build is still pending, said in the row); 未供給 = no approved theorem for the binder (the supplier Issue is named where one exists; "route not found" = this survey
found none); 契約 = a Prop FG assumes by the approved boundary; TRUSTED = trusted by design. "SHA" is the SHA recorded in the Issue's approval or note
(manager record, not re-checked by this unit). A scoped approval is not a completion of the Issue.

| # | binder / field | supplier Issue / unit | state | evidence (recorded SHA; what remains) |
|---|---|---|---|---|
| 1 | `L : Laws mref cref` (`O`: 10 fields `quiet diag frameT excOk frameQ cacheSetQ depthSetQ frame cacheSet depthSet`; `T`: 4 fields) | G5 (this Issue, audit) | 契約 | no `Laws` value in tree. `Tools/ShippingHeapModel.lean` proves the ref-only fragment RESTATED over a pure `Heap σ` (header: not connected to `IO.Ref`/`MetaM`; `diag`, `excOk` for Lean exceptions, `frameQ`/`frame` constructors for Meta primitives, and the four telescope fields stay open) |
| 2 | `Start.1` `AdmCtx L.O.quiet mctx cctx` | G5 | 契約 | PROVED only for `Command.mkMetaContext` (`mkMetaContext_canUnfold`); "entry runs there" is a reading. sparkle-gen5-dg-env: `AdmCtx`/`InertUnfold` 経路未発見 (note) |
| 3 | `Start.2` `JQC L.O 0 w` | G5 | 契約 | `cacheInvA_empty` 証明済み for the empty cache; `StartAtLoad` (ShippingStartAtLoad.lean header) reduced to named correspondence premises, not discharged |
| 4 | `RunsTo (synthesizeCombinational…)` ∨ `…WithParameters` | — | hypothesis (not a supply) | — |
| 5 | `ReflectsAll L declName parameters` | sparkle-gen5-package-coverage, -decl-bridge, -reader-bridge (all `todo`; recorded as consultation requests, nothing approved) | 未供給 | — |
| 6 | `T1Hyp.pkg` (G3-GEN) | sparkle-gen5-dg-dataof (row 6b dims projection), sparkle-gen5-dg-cover, sparkle-gen5-gencall-proof (`todo`) | 条件付き (parts) / 未供給 (whole) | dataof: U-D/U-E + freeze rev2 `62ea2479`, audit fix `945fbe9a`; row 6b projection lemmas implemented at `2bdc9324`/`063056d6`, clean build is the coder's (not yet). Unsupplied per its note: `dataOfAt` is `some`, real-reader match, `s = sp`, row 6a, C-CMP/C-QWIT, S-OK, S-COV-FLOAT |
| 7 | `GeneratedAt` / `hGen` (DG-COVER) | sparkle-gen5-dg-cover → residue to sparkle-gen5-dg-readertrace (`doing`) | 条件付き | `a54446a1` (U-C1-C5 pure core), `93a7c331` (freeze rev2), `3eb663df` (Cover2 preservation), `8e852666` (rev4), `72752f4c` (Cover3), `8e01a9cf` (U-E1), `9b9cdd55` (U-E2), `44d72eaf` (U-E3a). Remaining per note: R-trace/R-in/R-nl/R-dom/readF⇒FReachC/U-E3b (readertrace), row 6b/nDecl (dataof), `hbr` (reader-bridge), SigTy (dg-env), B3 (src-argw), Read LetOk (readkinds) |
| 8 | `T1Hyp.defines` (G3-SHAPE) | sparkle-gen5-dg-readkinds; sparkle-gen5-dg-runreads; sparkle-gen5-dg-env | 条件付き | readkinds: U1-U4 `3f79600f`/`069c7556`; U5 `4ac00d24` (exists/unique); U6 `36318286` (three theorems, conditional); U7 `f02837ed` freeze, `8bed2e00` mutant sync; U8 `f86cbdd7` (four theorems, same-witness join and conditional `MachineDefines`); U9 type freeze `e1d12867`, U9c skeleton `3fa1d1de` is a SKELETON with one intended `sorry` hole (not a proof). runreads RR1-RR3 `88771739`+`144c3f1e` (done, scoped; g5rr3 clean exit 0). env U1 `a14f2479` (clean `env5vb` exit 0). env class D 13 rows, telescope/Diag/AdmCtx/InertUnfold: 経路未発見 |
| 9 | `T1Hyp.closes` (G-CLOSES) | `memCallee_closesA` + N1 (this Issue) | 条件付き | `memCallee_closesA` 証明済み over `MemCalleeData`. N1: U1 `d68b0f47`/`284595a4` (B1/B2 to premises `hn`,`hmemSame`,`hself`), U2 (this freeze) to `MemTagsNamed` + graph + rank + B7. B3, B4, B5, B6 (`nameIn`), B7: 未供給. Route evidence side: sparkle-gen5-dg-acc `5aab73de` (A3/A4 audit), `802381fe` (`AccReads` conditional + A5 design), `a88c3e9c` (A5a/A5b); remaining per note: hcl/route/read/link (or cover+shape), off-route/GenSFacts |
| 10 | `T1Hyp.dec` (G-CALLDEC) | sparkle-gen5-gencall-proof (`todo`); sparkle-gen5-t2-tie provides dec-free roots | 未供給 (dec); 条件付き (dec-free roots) | t2-tie: T1HypND and five dec-free roots `5f0b2a69`/`f80cc94c`+`da510573`. Route from `T1HypND` to `dec` not found (R6 §2) |
| 11 | `T1Hyp.closed` | — | 未供給 | no supplier Issue |
| 12 | `StepStmt L P DataOk` (M2-b) | sparkle-gen2-step (`doing`) | 未供給 | LS-1 freeze `e8bc3012` approved; hW/coverage/G-SERVED/S5/StepStmt open per note |
| 13 | semantic hypothesis `hDG_SEM` and extension-at-call rows | sparkle-gen5-dg-sem | 条件付き | P4 freeze rev1 `6d596308`; U4A-F `1258f07e`; P4e rev2 + U5A-D/SemExt `1c300db6`. U5E `genExtAtCall_of_genSem` built in agent build only, the S1 `T2Tie` fix `7c06a80f` build is pending (not approved). `hp`/`hq`/`GenIn` from a real run: 未供給 |
| 14 | default-entry post-processing relation `b ↔ raw` | sparkle-gen5-dc-connect | 条件付き | U1-U6 abstract + check rev3 `08e97dba`; freeze rev5 `c07b5f66`; R1/R2 `6bd33fd7`; U-POST `e5ecf802` freeze, `db171c2e` implementation; U-POSTD freeze `3e5b5add`, Lean `4523f2e9` (agent build only, coder's clean build pending). Not supplied: TopShips D→D′ transport (a2), (a3), (b1)/(b2) O3 raw, real `EntryWitness`, parametric/ReflectsAll |
| 15 | `hrow` / `hrows` of `closingRun_of_run` | sparkle-gen5-dg-closingrun; sparkle-gen5-t2-tie (rows owned by dependencies) | 未供給 | R6 §2. Conditional assembly: CR0-CR4 + `closingRun_of_run` `6f3c8ee5` (freeze `25be9f8c`), r4 freeze `962626dd`, r5 depth-0 shared-block `f2e763d0`, r6 audit `f3a29dbb`. t2-tie `456699fc`/`632f365d`: U-A/B/C1/C2 scoped; `hOW`/`hkidW`/`hrows` = data-supply; `hs/hd0/hIH/hKI/hGen/hrun` statement-level |
| 16 | `hIH`, `hKI` at depth 1 | via `ih_allPF` | 未供給 | needs rows 7, 12, 15 |
| 17 | depth-0 `stop` (`InvAt 0 w'`) | sparkle-gen5-dg-closingrun | 条件付き / route 未供給 | r5 `f2e763d0` shared-block (scoped); the depth-0 `stop` route for FG: not found (R6 §2) |
| 18 | non-vacuity witness (a concrete package + run satisfying `T1Hyp`/`Start`) | sparkle-gen2-top-contract (`doing`: U1 `18125e5c`; concrete `ran`, joint non-vacuity not yet); sparkle-gen5-dg-closingrun | 未供給 | none in tree |
| 19 | G7-a artifact = optimized top + children | `writer_prints_endpoint_artifact` | 証明済み with binders `hno`,`htop` | DesignWriterRun.lean:119; `hno`/`htop` for every successful run: not covered |
| 20 | G7-b `runModuleTG` ⇒ `DesignSV` for `TopShips` designs | — | 未供給 (route not found); `_sat` endpoints 証明済み for their class | TrustBase.md:1635-1659 |
| 21 | G7-c printed bytes | printer | TRUSTED (by design) | Gaps row 129 |

Counting rule for §2: each of the 21 rows is counted once, under the FIRST state named in its state column ("primary state"). Primary states: 契約 3 (rows 1-3), hypothesis 1 (row 4), 条件付き 7 (rows 6, 7, 8, 9, 13, 14, 17), 未供給 8 (rows 5, 10, 11, 12, 15, 16, 18, 20), 証明済み 1 (row 19, with binders), TRUSTED 1 (row 21); 3+1+7+8+1+1 = 21. Rows whose state column names two states (6, 10, 17, 19, 20) also carry the second state in the text. This is an inventory of what the Issue notes record, not a completion measure. The "residual is only an allowed boundary" check
that the Issue goal asks for is NOT satisfied by this table: rows 5-18 and 20 are 未供給 or 条件付き.

## 3. Lean statements for the rows that close (new file; frozen types)

File (new): `Tools/ShippingGen5NameKids2.lean`; check file (new): `Tests/Gen5/NameKids2Check.lean`; two `lean_lib` entries in `lakefile.lean`
(`Tools.ShippingGen5NameKids2`, `Tests.Gen5.NameKids2Check`). Imports: `Tools.ShippingGen5NameKids`, `Tools.ShippingSrm12Corr`
(`instTagged_mem_idx`), `Tools.ShippingKid` (`TagsAgree`, `originAt`), `Tools.ShippingSrm7Rank`, `Tools.ShippingMemOnlyNames`
(`memModule_name`). Namespace `Tools.ShippingGen5NameKids2`. `set_option autoImplicit false`. Opens:
`Lean (Name)`, `Sparkle.Compiler.Elab (MachineShape)`, `Sparkle.IR.ModuleName (ofDecl)`, `Sparkle.Compiler.MachInstOrigin (InstOrigin)`,
`Sparkle.Compiler.MachMemory (memChildName memModule)`, `Tools.ShippingSrm7Rank (kidModName CallGraph callees declRank)`,
`Tools.ShippingMemCloses (memKey)`, `Tools.ShippingInstTagged (originAt TagsAgree)`. Props about names only; no `Laws`, no runtime, no compiler definition.

```
def kidNameAt (shape : MachineShape) (k : Nat) : String :=
  kidModName (((shape.insts[k]?).map Prod.fst).getD Name.anonymous, originAt shape k)

def MemTagsNamed (shape : MachineShape) : Prop :=
  ∀ (k : Nat) (hk : k < shape.insts.length) (cb : Bool) (aw dw : Nat),
    originAt shape k = InstOrigin.mem cb aw dw → (shape.insts[k]'hk).1 = memChildName cb aw dw

theorem hn_kidNameAt (shape : MachineShape) :
    ∀ (k : Nat) (hk : k < shape.insts.length),
      kidNameAt shape k = kidModName ((shape.insts[k]'hk).1, originAt shape k)

theorem memTagsNamed_of_tagsAgree (shape : MachineShape) (h : TagsAgree shape) : MemTagsNamed shape

theorem hmemSame_of_memTagsNamed (shape : MachineShape) (h : MemTagsNamed shape) :
    ∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      memKey (originAt shape k) ≠ none → memKey (originAt shape k) = memKey (originAt shape k') →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1

theorem hself_of_rank {g : CallGraph} {F r : Nat} {declName : Name} (shape : MachineShape)
    (hgraph : callees g declName = some shape.instTagged) (hr : declRank g F declName = some r) :
    ∀ (k : Nat) (hk : k < shape.insts.length), memKey (originAt shape k) = none →
      (shape.insts[k]'hk).1 ≠ declName

theorem kidNameAt_eq_memModule_name (shape : MachineShape) :
    ∀ (k : Nat) (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design),
      (originAt shape k).child? = some y → kidNameAt shape k = y.1.name

theorem memModule_name_ne_ofDecl (shape : MachineShape) :
    ∀ (k : Nat) (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design),
      (originAt shape k).child? = some y → ∀ (C : Name), y.1.name ≠ ofDecl C

theorem sepK_parent_of_supply {g : CallGraph} {F r : Nat} (shape : MachineShape) (declName : Name)
    (hmem : MemTagsNamed shape) (hgraph : callees g declName = some shape.instTagged)
    (hr : declRank g F declName = some r) :
    (∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      kidNameAt shape k = kidNameAt shape k' →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1 ∧ memKey (originAt shape k) = memKey (originAt shape k')) ∧
    (∀ (k : Nat), k < shape.insts.length → kidNameAt shape k ≠ ofDecl declName)
```
Proof plan (not part of the frozen statements): `hn_kidNameAt` by `simp [kidNameAt, List.getElem?_eq_getElem hk]`; `memTagsNamed_of_tagsAgree`
by `instTagged_mem_idx` + `TagsAgree` at that element + `of_decide_eq_true` on the `.mem` arm; `hmemSame_of_memTagsNamed` by `cases` on both origins
(a `none` memKey of `.ord`/`.field` contradicts `≠ none`); `hself_of_rank` by `instTagged_mem_idx` + `rkOf_edge` + `rkOf_decl`; `kidNameAt_eq_memModule_name`
by `child?_eq_memModule` and `memModule_name`; `sepK_parent_of_supply` by `hsep_of_kidNames` (U1) with `hn_kidNameAt`, `hmemSame_of_memTagsNamed`, and
`hparent_of_kidNames` with `hself_of_rank`. If a statement needs a change when proved, the change is recorded as an amendment to this file before the Lean commit is offered.

## 4. G5 joint satisfiability: still OPEN, and what is needed

The exact Prop whose proof would show that the `Laws` / `Start` fields are jointly satisfiable at all (the weakest form; it is not the runtime fit) is
```
∃ (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
  (L : Laws mref cref) (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld), Start L mctx cctx w
```
It is not in tree and this unit does not claim it. What it asks, field by field (Gen2Defs.lean:46-53, ChildInvA.lean:263-325):
(1) a predicate `quiet` with `quiet w` at the start (since `Start.2` includes `quiet w`, a `quiet` that is false everywhere satisfies the nine implication-shaped `O` fields vacuously but makes `Start` false, so
the trivial model is excluded); (2) `frameQ`, `cacheSetQ`, `depthSetQ`: quietness preserved by every `FramedA`/cache/depth operation; (3) `diag`, `frameT`, `excOk`, `frame`: the `cv/sv/dv`
frame and the exception class for the `Diag`/`Throws`/`Op`/`FramedA` program classes, which include Lean's own `MetaM` primitives; (4) `cacheSet`, `depthSet`: the post-state values after
`sparkleChildCache.set` / `sparkleSynthDepth.set`; (5) the four telescope fields of `T` for every admissible invariant `I`; (6) for `Start.1`, `InertUnfold` of the context's `canUnfold?` callback;
(7) for `Start.2`, `sv w = some synthesizeChild` (a world after the `initialize`d refs are set) and `CacheInvA` of `cv w` (`cacheInvA_empty` covers the empty cache).
Recorded state: `ShippingHeapModel.lean` shows the ref-only fragment restated over a pure model is satisfiable (`heapLaws_sat`), and says it is not connected to the opaque
`ST.Prim.Ref`/`Void IO.RealWorld`; `ShippingStartAtLoad.lean` reduces `StartAtLoad` to named per-primitive correspondence premises and states `QuietWitness` stays open. So
what is still missing is (a) the fit between the pure model and the extern refs (a premise-level link; whether it can be a theorem or has to be a TRUSTED statement is a user decision, NOT taken here),
(b) the fields about Lean's own code (`diag`, `excOk` for elaborator exceptions, `frameQ`/`frame` for Meta primitives, the four telescope fields), (c) a quiet start world satisfying (7).
If it turns out that a stated field is unsatisfiable together with `Start`, the exact field and the program that refutes it are to be written and the work stopped for a user decision; no such field was found by this unit.

## 5. U2 checks (written from §3, not from the implementation)

* **Expected TYPEs** (`Tests/Gen5/NameKids2Check.lean`): each of the 7 theorems and 2 definitions (bodies) in §3 re-stated as an independent `def Exp… : Prop` from the §3 text; the Expected props may name the constants `kidNameAt`, `MemTagsNamed`,
  `kidModName`, `memKey`, `originAt`, `callees`, `declRank` (their BODIES are checked separately, below). Comparator: the one reducible comparator of `Tests.Gen5.NameKidsCheck` (`cmpTeleR`,
  `checkExpectedR`, `checkMutantR`), imported, for positives and mutants.
* **Definition bodies**: `kidNameAt` and `MemTagsNamed` are compared (the same reducible comparator) with independently written `ExpKidNameAt`, `ExpMemTagsNamed` bodies (from §3).
* **Mutants** (single change, well-typed; rejection is by signature/defeq, NOT a semantic counterexample): (1) `hn_kidNameAt`: `originAt shape k` → `InstOrigin.ord` on the right; (2) `hmemSame_of_memTagsNamed`: `≠ none` → `= none`;
  (3) same: drop the `memKey` equality hypothesis; (4) `hself_of_rank`: `= none` → `≠ none` on the `memKey` hypothesis; (5) same: `declRank … = some r` → `= none`; (6) same: `callees … = some …` → `= none`;
  (7) `kidNameAt_eq_memModule_name`: `=` → `≠`; (8) `memTagsNamed_of_tagsAgree`: conclusion `MemTagsNamed shape` → `TagsAgree shape`; (9) `sepK_parent_of_supply`: drop the second conjunct;
  (10) same: drop `hmem`; (11) same: `ofDecl declName` → `ofMem true 0 0`. Plus 2 cross-statement controls (`sepK_parent_of_supply` against `ExpHmemSame`, `hself_of_rank` against `ExpHn`).
  Reported as MUTANT n, each distinct mutant def counted once; an accepted mutant fails the run.
* **Use-site `example`s**: `sepK_parent_of_supply` applied at `d.shape` of a `MachineData d` yields propositions identical (by `exact`) to the types of `MemCalleeData.sepK` and `.parent` with `nameK := kidNameAt d.shape`
  (a type check, not a semantic claim).
* **Closure** (reusing the U1 walker `reachWith`/`auditRoot` of `Tests.Gen5.NameKidsCheck`, as improved in R1/R2): roots are the 7 theorems; root-self judgement (a forbidden constant as the root itself), unknown name fails,
  and a synthesized root reaching an unknown name only through a helper's TYPE is checked with the intended path asserted; the same fixtures `Tests.Gen5.NameKidsFixture` are reused. Counts reported as controls: negative n, clean 1,
  REACH n (one per root), with the aggregation rule stated in the file header.
* **AXIOMS**: `#print axioms` of each of the 7 theorems ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`, no `axiom`.
* Numbers in the report are actual counts per category with the rule next to them; no total is quoted without categories.
* Build: `kjob lake build Tools.ShippingGen5NameKids2` then `kjob lake build Tests.Gen5.NameKids2Check`, one at a time. After the Lean commit the Issue stays `doing` (the coder runs the clean issue-linked build).

## 6. What this freeze does not do
No change to any compiler, production or shared-definition file (`Tools/ShippingGen2Defs.lean`, T1Hyp, T1HypND, `Elab*.lean`) and no change to any built file. No new TRUSTED boundary/law, no FG/guarantee change, no GenWF
strengthening, no `sorry`/`axiom`/`native_decide`. `nameK := kidNameAt shape` is a CHOICE a consumer may make; this unit does not change `MemCalleeData`. B3-B7 and the G5 joint satisfiability stay OPEN.

## 7. Amendments after approval (wording only; no re-freeze; no theorem added)
Recorded with the implementation commit. They add to or correct the wording above; no statement in §3 changes.
1. **Count.** §3 states 7 theorems (`hn_kidNameAt`, `memTagsNamed_of_tagsAgree`, `hmemSame_of_memTagsNamed`, `hself_of_rank`, `kidNameAt_eq_memModule_name`,
   `memModule_name_ne_ofDecl`, `sepK_parent_of_supply`) and 2 definitions (`kidNameAt`, `MemTagsNamed`). Every earlier "eight theorems" in §5 reads "7 theorems and 2 definitions".
2. **`rkOf_edge` and fields.** `rkOf_edge` applies to every call entry of a ranked declaration, so `hself_of_rank` covers a kid with origin `.field i` as well as `.ord`
   (`kidModName (c, .field i) = ofDecl c`). `hmemSame_of_memTagsNamed` still takes `MemTagsNamed` of the actual shape as a premise; its supply for the reader's shape is as in §1.1.
3. **§2 distinguishes history from actual supply.** The "evidence" column of §2 is the history at the time each SHA was recorded in the Issue (the state when that SHA was approved or noted), not a
   re-check of the present tree. The "state" column is the survey's reading of what is actually supplied. Where the two differ, the actual supply is the one in the state column; the SHAs
   are not evidence that later work did not change a row. Row 13: the S1 `T2Tie` fix `7c06a80f` is recorded as approved (DG-SEM); the table text "build is pending (not approved)" is the history at the
   earlier note. That approval is a scoped approval of that unit, not a supply of `hp`/`hq`/`GenIn` from a real run (still 未供給).
4. **`T1Hyp.closed` (row 11).** Its Prop (GEN2_DEFS `T1Hyp.closed`): `∀ c, Reach c → ∀ q, P c = some q → ∀ k (hk : k < q.d.shape.insts.length), (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1`.
   Besides "no supplier Issue", the obligation is a CONNECTION: each non-memory kid of a reached declaration must be reached, from the static closure of `Reach` / the ACC route evidence
   (sparkle-gen5-dg-acc `AccReads`, the call-closure side of `Reach`; the match of `Reach` with the translator's actual child calls is G-REACH). This survey did not find that connection stated as a theorem. It is 未供給, and
   the same static closure is the place where G3 closed / no-owner rows would connect.
