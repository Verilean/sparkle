# T2-TIE next unit — supplier survey of the remaining inputs + freeze r0 (docs only; no Lean yet)

Issue `sparkle-gen5-t2-tie`, branch `kjob/g5tt-cr5`, base `171fea73` (one-output C1-C4 connection, reviewer approved; headers synced in the
first commit of this branch). Nothing here claims T1, FG, M5 or Issue completion. "未供給 / この調査で経路未発見" means only that this survey
did not find a supplier or route in the trees listed in §0; it does not say the row is impossible or underivable. A conditional wrapper
is NOT counted as a supply. No new law/TRUSTED boundary, no shared-definition or compiler change, no FG narrowing, no `GenWF` change,
`stop_of_run` untouched. Not elaborated: types below were read off the cited sources; they are checked only when implemented.

## 0. What was searched

* Tree at `171fea73` (`Tools/ShippingGen5*`, `Tools/ShippingGen2*`, `Tools/Shipping{CallWidths,ChildServe,MachineInstG,MachineEntry,Srm4Core6}`).
* Approved/under-review files of other Issues, read from their branch tips: DG-SEM `kjob/g5sm-u3` (SemGen/SemPkg/SemRef) and
  `kjob/g5sm-p4r` (`DG_SEM_FREEZE_P4.md`), DG-ACC `kjob/g5ac-r3` (`ShippingGen5Acc*`, A3 `AccGenP`), DG-DATAOF `kjob/g5do-r4`,
  DG-READKINDS `kjob/g5rk-r8`, DG-COVER `kjob/g5cv-r7`, DG-DECLCONNECT/FG `kjob/g5dc-r6`, DG-CLOSINGRUN `kjob/g5cr-r6` (+ `DG_CLOSINGRUN_FREEZE_R6.md`),
  M3 `kjob/g3ds-ds8` (`Tools/ShippingGen3*`).
* Query used for the width rows: `OneOutWidth|callWidthsStrict|callWidthsOk|hkidW|OneOutNoMemRow|GenExtAtCall|CallOutRange|FieldRowAt` over
  `Tools/ShippingGen5*`, `Tests/Gen5`, `scripts/gen5` on each branch above. Besides the T2 files (`T2Tie/T2Range/T2Conn/T2OutTy/T1ND`, already in the tree) and
  their Checks, no gen5 branch mentions them; `Tools/ShippingGen3*` at `kjob/g3ds-ds8` does not mention `callWidthsStrict`, `OneOutWidth`, `callWidthsOk` or `hkidW`.

## 1. Survey table — every remaining input of `callTie_of_closingShared_one` / `callTie_of_served`

"Built" = in the tree at `171fea73` or approved at the cited branch. Owner = the Issue that must supply the row.

| # | Row (full type, as a premise) | Existing candidate (real name, file) | Needs | Status of the row | Owner |
|---|---|---|---|---|---|
| 1 | `hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q` | `T1HypND.pkg : ∀ c, Reach c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q` and `T1HypND.closed X hR p hP k hk hnone : Reach (insts[k]).1` (`Tools/ShippingGen5T1ND.lean:35`) | `hT : T1HypND`, `hR`, `hP`, `hnone` (all already premises of the built theorems) | **Existence route found** in the tree: `∃ q, P (insts[k]).1 = some q ∧ q.decl = … ∧ DataOk q`. The existential form is what is supplied; the field `pkg` itself is a T1 hypothesis whose own supply is DG-ACC `genP_pkg` (A3, `kjob/g5ac-r3`, CONDITIONAL on `GenSFacts K`, `hacc`, `hcl`, `ReachCover`, `hOk`: not supplied by this Issue). | this Issue (existence step, §3 U-A); `pkg` supply: `sparkle-gen5-dg-acc` |
| 2 | `hDG_SEM : GenExtAtCall p q k hk` (def `T2Tie.lean:238`) | `Tools/ShippingGen5SemGen.lean` (`genSemGenE_writes/result/source`, built U3 `kjob/g5sm-u3`) and the `callOut`/`ExtStage` family frozen in `DG_SEM_FREEZE_P4.md` §2-§5 (U4A-F, under review). The statement that would give it is `genExtAtCall_of_genSem` = roadmap **P4e** (`DG_SEM_FREEZE_P4.md` §8), "under S1-S3", **not frozen and not built**. | S1 (`Q c = some q`), S2 (`CallField`, T2-FIELD), S3 (range), callee output-name `Nodup`, `GenIn`/`GenWF` coverage | **未供給 / この調査で経路未発見** (no built or frozen theorem of the form `GenExtAtCall p q k hk`). | `sparkle-gen5-dg-sem` (P4e). Not implemented here. |
| 3 | `hDG_SEM_range : CallOutRange p q k hk` (def `T2Tie.lean:250`) | `callOutRange_of_widths p q k hk houtTy hW` (`T2Range.lean:162`, built) with `houtTy := houtTy_of_closingND …` (`T1ND.lean:77`, built; from `hT.defines` via `RealChildA.run`) and `hW := callOutWidthAt_of_oneOut P p q k hk hGENP h1 hOW` (`T2Range.lean:188`) | `hOW : OneOutWidth P p k` (row 5) | **Composition route found for one-output parents**: `CallOutRange` follows from `hT`, the closing witness (row 4), row 1 and `hOW`; `hDG_SEM_range` is then not a separate premise. It is conditional on `hOW`. | this Issue (composition, §3 U-C1); `hOW`: row 5 |
| 4 | `hDG_CLOSINGRUN` group parent (`instFields ≠ []`): C1-C4 with `FieldRowAt p k r.1 = (instFields.getD k "" ∈ r.1.outputs.map (·.name))` | **Route found in the tree** (the r0/r1 documents said "not found"; this survey found it): `ClosingShared` right branch gives `CloseCalls` right = `instFields ≠ [] ∧ closeInstsG … shape.instFields children (m₀,d₀) = some (raw,D) ∧ MemChildren …` (`MachineEntry.lean:948`). `closeInstsG_calls` (`MachineInstG.lean:307`): for `k < insts.length`, `∃ st ∈ raw.body, args outs child mc, CallStmtG … mc st ∧ moduleByName D.modules child.1.name = some mc ∧ (k, instFields.getD k "") ∈ outs ∧ insts[k]? = some args ∧ (children[k]?).map (·.1.name) = some child.1.name`; `CallStmtG` (`MachineInstG.lean:19`) contains `(outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) = true`. `closeInstsG_names` (`MachineInstG.lean:369`): `∀ c ∈ children, moduleByName D.modules c.1.name = some c.1 ∧ ∀ m ∈ c.2.modules, moduleByName D.modules m.name = some m` (C3 and C2). C1: `ChildrenShipsI.2 k hk` + `hT.closed`, exactly as in the one-output unit. | `hsh : ClosingShared`, `hG : instFields ≠ []`, `hT`, `hR`, `hP`, `hnone` | **Closable from existing parts by this survey's reading; NOT yet elaborated.** Planned as U-B. | this Issue (§3 U-B) |
| 5 | `hOW : OneOutWidth P p k` (def `FitChain.lean:893`) | `Tools.ShippingGen2DataBridge.oneOutWidth_of_strictP P p (hcw : callWidthsStrict p.d p.kD (kidOutsP P p) = true) (hsimple : instFields = []) : ∀ k, OneOutWidth P p k` (`DataBridge.lean:143`, built) | the Bool row `callWidthsStrict p.d p.kD (kidOutsP P p) = true` for every reached `p` | The theorem is built; the **row is 未供給 / この調査で経路未発見**: `DataOk` is an abstract Prop in `T1HypND`, and no file in §0 derives `callWidthsStrict …` (or `callWidthsOk`) from `DataOk` or from a run. M3 `kjob/g3ds-ds8` has no mention. | `sparkle-gen3-data-supply` (G-ONEOUT-WID / G-DATA) |
| 6 | `hkidW` (group, `T1ND.lean`, premise of `callTie_of_served_kidW_closing_t1ND`): `∀ k hk (y : Res), RealChildA L.O (insts[k]).1 y → ∀ pt ∈ y.1.outputs, pt.name = instFields.getD k "" → binders[kD+k].map (kindTy ·.2).bitWidth = some pt.ty.bitWidth` | `hkidW_of_data` (`CallWidths.lean:62`, `RealChild` form) and `hkidW_of_dataAM` (`Srm4Core6.lean:115`, **`KidTA` form** = `o.child? = some y ∨ (o.child? = none ∧ RealChildA O c y)`), `hkidW_of_memOrigin` (`Gen2MemFacts.lean:20`, memory-origin children only) | `hcw : callWidthsOk d nDecl kidOuts = true`; `hkidT : ChildOutTys (kidOuts k) y.1` for the served child; for the `RealChildA`-form premise: a bridge from `RealChildA` to `KidTA` which needs `origin.child? = none` at every `k` (not true for memory-origin entries) | **未供給 / この調査で経路未発見.** Same `callWidthsOk` row as row 5 is missing; `hkidT` has a route from `childRunN_outputs` of the closing witness (used in `callOutRange_of_closing_kidW`) but only for the served child of one `k`; the `∀ k, RealChildA` form is not covered by `hkidW_of_dataAM`. | `sparkle-gen3-data-supply` |
| 7 | `closingRun0_of_run` binder `hord` | `hord_of_row` from `hrow : ∀ q, DataOk q → OneOutNoMemRow q = true` (`DataBridge.lean:57`; r6 §2) | `hrow` | Unchanged since `DG_CLOSINGRUN_FREEZE_R6.md`: `hrow` **未供給 / この調査で経路未発見** in §0's trees (DG-DATAOF `kjob/g5do-r4`, DG-READKINDS, DG-COVER contain no `OneOutNoMemRow`). | `sparkle-gen3-data-supply` / DG-WFCOVER |
| 8 | binders `hs : Start L mctx cctx w`, `hd0 : dv w = 0` | `Start` = `AdmCtx ∧ JQC L.O 0 w` (`Gen2Defs.lean:52`) — start conditions of an outermost compilation | — | Premises of the whole theorem, not rows another file derives. Not a gap this unit can close. | statement-level (T1 start) |
| 9 | binders `hIH : IHAt L P Reach 1`, `hKI : ChildKeepsInv L P Reach 1` | `ih_allPF … 1` (`Gen2T1.lean:198`); parts `keepChild_proved`, `limitStmt_proved` proved; `servedShips0_proved` needs `hrow`; `postFacts_proved` needs `hrows`, `hrow`; `StepStmt`; `T1Hyp.dec` | as r6 | Unchanged from r6: `StepStmt` and a route `T1HypND → T1Hyp.dec` **この調査で供給元・経路が見つからなかった**. | `sparkle-gen3-data-supply` / G-CALLDEC |
| 10 | binder `hGen : ∀ b ci envR envR' w5 w6, RunReadsAt … → Gen ci envR envR'` | DG-ACC A3: `GeneratedAtK K P X E p` and the statement `GenPGeneratedStmt K` / theorem `genP_generated` (`kjob/g5ac-r3`, `AccGenP.lean:36,96`), CONDITIONAL on `GenSFacts K`; DG-ENV `ReadsAt` lemmas (`Tools/ShippingGen5Env*.lean`) are one ingredient | DG-COVER + DG-WFCOVER + `GenSFacts` + DG-ENV, and identifying `Gen` with `GeneratedAtK` | **未供給 / この調査で経路未発見** as a `Gen ci envR envR'` consequence of `RunReadsAt` (no theorem connects `RunReadsAt` to `GeneratedAtK`). | `sparkle-gen5-dg-acc`, `-dg-cover`, `-dg-env` |
| 11 | binder `hrun : RunsTo (synthesizeCombinationalCore X [] false) …` | the run itself; DG-RUNREADS supplies facts *about* a given run | an actual run | Premise (the run), not supplied by a file. | statement-level |
| 12 | §3'(d) non-vacuity of `ClosingRun0`/`ClosingShared` | none in §0's trees | a concrete `Laws`, `Pkgs`, `Reach`, `DataOk`, a run, rows 1-11 | **未供給 / この調査で経路未発見** (unchanged). | `sparkle-gen5-dg-closingrun` |
| 13 | §3'(e) depth-0 `stop` | `stop_of_run` needs `1 ≤ dv w` (r6) | — | **この調査で経路未発見**; forbidden root in the Check; unchanged. | `sparkle-gen5-dg-closingrun` |
| 14 | `OneOutNoMemRow`/`hrows : DataRows` for `hrows` (PostFacts/IH) | as row 9 | — | unchanged from r6 | `sparkle-gen3-data-supply` |

Net of this survey: the closable rows owned by this Issue are row 1 (existence), row 4 (group C1-C4) and the composition of row 3 (one-output range from
`hOW`). Rows 2, 5, 6, 7, 9-14 are not supplied by anything found; they are owned by the Issues named in the last column and are not reimplemented here.

## 2. Ambient context of the new file (unchanged from `T2TIE_CR_FREEZE_R1.md` §4')

New file `Tools/ShippingGen5T2TieCR2.lean`, namespace `Tools.ShippingGen5T2TieCR2`, `set_option autoImplicit false`. Imports: `Tools.ShippingGen5T2TieCR`,
`Tools.ShippingGen5T1ND`, `Tools.ShippingMachineInstG`, `Tools.ShippingChildServe`. Header `open`s: exactly those of `Tools/ShippingGen5T2TieCR.lean` (which are lines 14-23 of
`ClosingRun2.lean` plus `Tools.ShippingGen2`). Ambient variable line, verbatim:

```
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
```
Every theorem lists ALL binders. `T1HypND`, `ShipsRes`, `FieldRowAt`, `CallTie`, `GenExtAtCall`, `OneOutWidth` resolve in `Tools.ShippingGen2`. `Res := Tools.ShippingChildInv.Res`.

## 3. Frozen statements

### U-A — callee package existence (row 1)
```
theorem calleePkg_of_t1ND
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) :
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ q.decl = (p.d.shape.insts[k]'hk).1 ∧ DataOk q
```
Proof plan: `hT.pkg _ (hT.closed X hR p hP k hk hnone)`; then `obtain ⟨q, hq, hd, hok⟩` and repackage. Uses `T1HypND.pkg`, `T1HypND.closed` only.

### U-B — group parents: C1-C4 from `ClosingShared` (row 4)
```
theorem servedCall_of_closingShared_group
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) :
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1
```
Proof plan: unpack `hsh`; `insts = []` branch contradicts `hk`; the `CloseCalls` left branch (`instFields = []`) contradicts `hG`; right branch gives `closeInstsG …`.
`closeInstsG_calls` at `k` (with `insts := shape.insts.map (·.2.1)`, `List.length_map`) gives `child`, `mc`, `outs`, `CallStmtG`, `moduleByName D.modules child.1.name = some mc`,
`(k, instFields.getD k "") ∈ outs`, `(children[k]?).map (·.1.name) = some child.1.name`; `ChildrenShipsI.2 k hk` gives `y` with `children[k]? = some y`, so `y.1.name = child.1.name`;
`closeInstsG_names` (at `y ∈ children`) gives `moduleByName D.modules y.1.name = some y.1` and `∀ m ∈ y.2.modules, moduleByName D.modules m.name = some m` (C3, C2), hence `mc = y.1`;
C4: unfold `FieldRowAt`, `if_neg hG`, and the clause `(outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) = true` of `CallStmtG` at `(k, instFields.getD k "") ∈ outs`
(`List.all_eq_true`, `List.any_eq_true`, `List.mem_map`); C1: `child? = some y` excluded by `hnone`; `Reach (insts[k]).1` by `hT.closed X hR p hP k hk hnone`. Witnesses `r := y`, `dsn := D`.
Risk (stated, not hidden): the exact shape of `closeInstsG_calls`' `child` vs `children[k]?` and the `MemChildren` conjunct are read from source, not elaborated; if the proof needs a premise beyond the above, it will be reported as a type change request, not added silently.

### U-C1 — one-output composed form (rows 1, 3, 4-one)
```
theorem callTie_of_closingShared_one_ex
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k) :
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk
```
Proof plan: `calleePkg_of_t1ND` gives `q`; `servedCall_of_closingShared_one` (built, `T2TieCR.lean`) gives the closing witness; `houtTy_of_closingND L P hT p q k hk (hT.closed X hR p hP k hk hnone) hq hclosing`;
`callTie_of_served_oneOut L P p q k hk hq hclosing (hDG_SEM q hq) houtTy h1 hOW`.

### U-C2 — group composed form (rows 1, 4-group)
```
theorem callTie_of_closingShared_group_kidW
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) :
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk
```
Proof plan: as U-C1 with `servedCall_of_closingShared_group` and `callTie_of_served_kidW_closing L P p q k hk hq hclosing (hDG_SEM q hq) houtTy hG hkidW` (`T2Conn.lean`).

`ClosingRun0` forms are `h.shared` applied to the same statements; they are not separate theorems.

### What each theorem does and does not claim
They are CONDITIONAL compositions. They remove from the premise list: `hDG_GENP` (U-A existence), the group `hDG_CLOSINGRUN` (U-B), and `hDG_SEM_range` (replaced by `hOW` /
`hkidW`). They keep as premises, named: `hT`, `hsh`, `hDG_SEM` (row 2, DG-SEM P4e), `hOW` (row 5) / `hkidW` (row 6). The `∀ q` form of `hDG_SEM` is the form a P4e
theorem would have; it is a restatement of the same premise, not a supply of it. Rows 2, 5, 6 and everything in §1 marked 未供給 stay unsupplied.

## 4. Check (`Tests/Gen5/T2TieCR2Check.lean`, written from §3, not from the implementation's signature)

* **TYPE**: `ExpA`, `ExpB`, `ExpC1`, `ExpC2` written independently from the Lean text above (accessor/unfolded forms where possible) and compared with the SAME reducible comparator used by
  `Tests/Gen5/ClosingRun2Check.lean` (`checkExpectedR`, `checkMutantR`, `reachWith`). Positive controls: the built `callTie_of_served_oneOut_t1ND` and `servedCall_of_closingShared_one` pass the same comparator.
* **MUTANT** (signature/defeq rejection of well-typed one-place differences; **not** semantic counterexamples):
  | id | theorem | exact difference |
  |---|---|---|
  | N1 | A | delete binder `hnone` |
  | N2 | A | conclusion `q.decl = (p.d.shape.insts[k]'hk).1` → `q.decl = X` |
  | N3 | A | drop the conjunct `DataOk q` |
  | N4 | B | `hG : instFields ≠ []` → `instFields = []` |
  | N5 | B | last conjunct `FieldRowAt p k r.1` → `FieldRowAt p (k + 1) r.1` |
  | N6 | B | conclusion binder order `∃ r dsn` → `∃ dsn r` |
  | N7 | C1 | delete binder `hOW` |
  | N8 | C1,C2 | conclusion `CallTie p q k hk` → `CallTie p p k hk` |
  | N9 | C1,C2 | `hDG_SEM : ∀ q, P … = some q → GenExtAtCall p q k hk` → `GenExtAtCall p p k hk` |
  | N10 | C2 | `hkidW` binder `p.kD + k` → `p.kD + k + 1` |
  | N11 | C2 | in `hkidW`, `RealChildA L.O (p.d.shape.insts[k]).1 y` → `RealChildA L.O p.decl y` |
  | N12 | C1 | `h1 : instFields = []` → `instFields ≠ []` |
* **CLOSURE** (explicit `thmInfo/defnInfo/opaqueInfo` walk; unknown name = FAIL; with the r6 negative control): the closure of each of A, B, C1, C2 must not contain `T1Hyp.dec`,
  `Tools.ShippingGen5ClosingRun.stop_of_run`, `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`; REACH: A reaches `T1HypND.pkg`, `T1HypND.closed`; B reaches `closeInstsG_calls`,
  `closeInstsG_names`, `ChildrenShipsI`; C1 reaches `calleePkg_of_t1ND`, `servedCall_of_closingShared_one`, `houtTy_of_closingND`, `callTie_of_served_oneOut`; C2 reaches `servedCall_of_closingShared_group`, `callTie_of_served_kidW_closing`.
* **AXIOMS**: standard only. No `sorry`/`axiom`/`native_decide`.
* Counts in the report are the actual numbers of TYPE/MUTANT/REACH/AXIOMS lines, summary lines excluded.

## 5. Not claimed
* Not a supply of `hDG_SEM` (`GenExtAtCall`, DG-SEM P4e), `OneOutWidth`, `hkidW`, `hrow`/`hord`, `hIH`/`hKI`, `hGen`/`GeneratedAt`, non-vacuity, depth-0 `stop`, or the general FG / T1.
* Row 4 (group) is a reading of existing statements, not yet elaborated; it is part of this freeze so the reviewer can reject it before any Lean exists.
* No new law/TRUSTED, no shared-definition or compiler change, no FG narrowing, no `GenWF` change; `stop_of_run` unchanged and unreachable from the new theorems (checked by CLOSURE).
* The clean exact-head build is the coder's; this freeze is docs only and elaborates nothing.
