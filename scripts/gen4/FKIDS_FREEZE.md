# FKIDS_FREEZE: F-kids (children of the parametric top declare no parameters), the `StatePF` walk

Status: FREEZE of the statements (rev1), written BEFORE any proof. Base `par/ftheta` 9562f44c (contains kjob/rt180 7c836d8a:
K walk `topEntry_K_of_family3`, MemoFamily rev3, `MsgMvK`; F-θ with the `LamTelescopeN` route).
Nothing is accepted by this document. Ledger: FG 81 / T1 57 (this unit: FG -0 +0 / T1 -0 +0).
"Read" = my reading of code, not checked by Lean. "Counted" = produced by grep/wc in this unit.

## 1. What `LegalBinding` needs from F-kids (read from the tree)

`LegalBinding D θ := specValidateBindings D.modules θ = .ok ()` (Tools/ShippingGen4ParamIface.lean:91). Of the five
`validateBindings` clauses, (a) (no module declares a duplicate parameter name) and (e) (every declared parameter name of
every module of `D` has a θ binding) range over ALL modules of `D`; (c) (every θ name is declared by some module) is met by the
top. For the modules other than the top, F-kids says they declare nothing, so (a) and (e) hold for them vacuously
(`List.Forall` over `[]`). This is `PARAM_LEGAL_STUDY.md` §4 item 3 (F-kids), in the guard form:

    ∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = []        (D' the entry design, M' the post-processed top)

The guard is NOT vacuous: `ModuleNameCheck.check` (Sparkle/IR/ModuleNameCheck.lean:21) deduplicates repeated uses of one raw name
(`checkNames (namesOf modules).eraseDups`), so a child module named like the top is not refused by `finishSynth`; `designTop`
(Tools/ShippingGen4ParamIface.lean:27) gives `D'.modules = D.modules` only under `∀ x ∈ D.modules, x.name ≠ M.name`. The
route below does not need the collision refusal: the core statement (§2 `fKids_statePF`) has no guard, and the guard form
follows from it by the post-processing facts `(dropZeroWidthModule m).name = m.name`, `(mergeChecked m).name = m.name`,
`.parameters` likewise (small, new, theorems about existing definitions; they are also the F-post lemmas, so they are shared,
not counted twice).

## 2. The frozen statements

New files (names fixed here): `Tools/ShippingGen4FKidsDefs.lean` (definitions), `Tools/ShippingGen4FKidsState*.lean`
(the `StatePF` walk, split into modules), `Tools/ShippingGen4FKids.lean` (the theorems below),
`Tests/Gen4/FKidsCheck.lean` (the Check). Namespace `Tools.ShippingGen4FKids`.

```lean
/-- the invariant "parameters = []" -/
def ParamFree (m : Sparkle.IR.AST.Module) : Prop := m.parameters = []
def DesignPF (D : Design) : Prop := ∀ x ∈ D.modules, ParamFree x
def StatePF (cs : CircuitState) : Prop := DesignPF cs.design           -- StatePF of PARAM_INV_ESTIMATE §1
def PairPF (r : Sparkle.IR.AST.Module × Design) : Prop := ParamFree r.1 ∧ DesignPF r.2
/-- every entry of a cache map is a PairPF pair (the memo and the child cache hand pairs back) -/
def CachePF (m : Std.HashMap Name Res) : Prop := ∀ n r, m.get? n = some r → PairPF r
/-- the world half of the invariant: the K-walk invariant at depth D, and both caches PairPF -/
def WorldPF (O : RefLawsAOps MkRefd mref cref) (D : Nat) (w : Void IO.RealWorld) : Prop :=
  KWD O MemoKeysInChild D w ∧ CachePF (cv w) ∧ CachePF (mv w)
```

Three theorems, VERIFIED SEPARATELY (separate TYPE checks):

```lean
/-- (1) memo-hit / child-result part. A returning memoised child entry from a `WorldPF` world at depth `D ≠ 0` returns a
PairPF pair and gives a `WorldPF` world at the same depth; so a cache hit (child cache or memo) can only hand back a PairPF pair,
and a child-cache miss is a memo miss (`childMiss_memoMiss`, K walk, reused). -/
theorem fKids_memoHit {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) (D : Nat) (hD : D ≠ 0) (c : Name) :
    Triple mctx mref cctx cref (WorldPF O D) (synthesizeChild c)
      (fun r => WorldPF O D ∧ PairPF r)  (fun e w => WorldPF O D w ∧ OkExc e)
    -- (written with the usual `fun r w => WorldPF O D w ∧ PairPF r`)

/-- (2) the StatePF walk, as seen from the symbolic top: a returning run of the symbolic core from the K start world
yields a design whose modules declare no parameter. (the top module `M` is not constrained: it is the one allowed to declare) -/
theorem fKids_statePF {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {θ : List (String × Nat)}
    {w w' : Void IO.RealWorld} {M0 : Sparkle.IR.AST.Module} {D0 : Design}
    (hw : KWD O (fun _ _ => True) 0 w)
    (h : RunsTo (synthesizeCombinationalCoreWith Tsyn declName θ true true) mctx mref cctx cref w (M0, D0) w') :
    DesignPF D0

/-- (3) F-kids, in the form the `LegalBinding` assembly consumes (guard form of §1). -/
theorem fKids {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {θ : List (String × Nat)}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Design}
    (hw : KWD O (fun _ _ => True) 0 w)
    (h : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w') :
    ∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = []
```

`Tsyn` is `Tools.ShippingGen4ParamEntry.Tsyn`; `Triple`, `KWD`, `MemoKeysInChild`, `MsgMvK`, `MemoFamily`, `AdmCtx`, `RefLawsAOps`
are existing (Tools/ShippingGen4KWalk*.lean, Tools/Assume/MemoFamily.lean, Tools/ShippingChildInvA.lean). If a binder or a
`variable` of the final file has a different shape (a universe, an implicit), the Check compares the ELABORATED type of the
final text to this text, and any difference is recorded in §6 as a revision (rev2), with the cause.

## 3. The StatePF walk (how the statements are proved; not part of the statements)

* Invariant over a CompilerM run: `KeepsCS I S c` := from every compiler context with provenance (`CtxOk`) and every state `st` with
  `S st`, the MetaM run `c ctx st` from a world with `I` returns in `I` with the final state satisfying `S`, and throws in `I` with
  the exception in the class (`OkExc`). `S := StatePF`. This is `KeepsCP` with the state tracked (same `Triple`; the postcondition
  reads `p.2`). Rules: bind, ite, dite, pure, throw, `liftMetaM` (a lifted MetaM leaves the state: the leaf is a plain `Keeps`
  goal, closed by the EXISTING `kwalkM`/`FramedNM`/`MemoFamily` rules of the K walk), get, set/modify (with a one-line
  `S`-preservation side goal), `withReader`, try/catch (the handler runs from the state at the `try`: `StateT` over `MetaM`),
  `forIn`, `withLocalDecl`/`withLetDecl` (the result of `withLocalDeclD` is the result of the continuation: derived from the Lean
  definitions as `localDecl_of_O` does for `Keeps`, `Tools/ShippingChildTeleLocalA.lean`, no new law).
* The world half `I := WorldPF O D` is stable (it depends on the child cache and the memo contents, and on K's fields), so every
  K-walk leaf lemma (generic in a `StableK` invariant) applies unchanged. Cache writes: the child-cache write `insert n r` and the
  memo write `insert declName result` write a PairPF pair, which the walk has just established for the entry's own result.
* `design` changes only at `CompilerM.addModuleToDesign` (4 call sites, counted/read in PARAM_INV_ESTIMATE §2.1): there the argument
  is a module of a child pair, so ParamFree by `PairPF`; `addParameter` writes `module`, not `design` (`rfl`).
* The pair `PairPF` of a child entry result is proved by the same depth induction as the K walk (`child_budget`), for the three
  front ends (certified / mixed / machine) and the legacy tail; for a non-symbolic entry `parameters = []` is the empty list
  given to `bindInputsLegacy`, so `module.parameters = []`.
* The symbolic top (`symbolicMode = true`, `parameters = θ`) reaches only the legacy tail (`certifiedShape_off`,
  `mixedCertifiedShape_off`, `machineShape_off`, `entryConst_off`, Tools/ShippingGen4ParamEntry.lean:27-62, exist), `finishSynth_symbolic`
  (same file :112, exists) gives `D = fcs.design`, hence `StatePF fcs`.

## 4. Premises (only these, besides the run)

| premise | kind | where it enters | counted |
|---|---|---|---|
| `M : MemoFamily O` (rev3, approved) | existing approved row (M4.MEMO-01) | leaves of the world half (frames, telescope laws) | reused, NOT counted again |
| `hmsg : MsgMvK O` | existing named conditional leaf | exception rendering in the legacy arm (K walk) | stays conditional; never a reduction basis |
| `LamTelescopeN` (Tools/ShippingLegacySemTelescopeN.lean) | the shared N4-a Meta-library fact | ONLY if a `lambdaTelescope` result law is needed beyond `MemoTele.lamTelescopeT` (Triple form, in `M`); expected NOT needed. If it becomes a binder of `fKids` it is one shared +1 candidate row (F-θ / F-top / F-kids do not stack it) | shared |
| the run `h` | the run | — | — |
| `hA : AdmCtx O.quiet mctx cctx`, `hw : KWD O (fun _ _ => True) 0 w` | the start world / context of the K top entry (the hypotheses of `topEntry_K_of_family3`, nothing new) | — | already-counted rows |

No new law, no TRUSTED, no `RefLawsM`, no compiler or shared-definition edit, no `sorry`/axiom/`native_decide`.

## 5. Subtraction table

| item | before | after F-kids proved | note |
|---|---|---|---|
| F-kids (this unit) alone | 0 | 0 | one of six parts (F-θ, F-top, F-kids, F-post, shape, assembly) |
| B.P-8 `LegalBinding D θ` | UN-C | UN-C | -1 only when all six parts are proved |
| B.P-1 `AllPos θ` | UN-C | UN-C | -1 only when all six parts are proved (`legalBinding_allPos`) |
| M4.MEMO-01 `MemoFamily` | 1 row | 1 row | reused; no second row |
| `MsgMvK` | conditional leaf | conditional leaf | not a reduction basis |
| `LamTelescopeN` | in neither ledger | shared +1 candidate (one row for F-θ / F-top / F-kids together) | not stacked here |
| new rows | | +0 | |

`台帳: FG 81 / T1 57（今回 FG -0 +0 / T1 -0 +0）`

## 6. Checks (Tests/Gen4/FKidsCheck.lean, to be written with the proofs)

(a) the TYPE of each frozen statement by structural `Expr ==` (one telescope walk, not strings); (b) ASSUMPTION check: every Prop binder
of the F-kids root is one of: `MemoFamily`, `MsgMvK`, `LamTelescopeN`, the run (`RunsTo`), or a listed existing row (`AdmCtx`, `KWD`),
by head constants of the binder types; negative control: a theorem with an extra hypothesis fails; (c) `fKids_memoHit` and
`fKids_statePF` verified separately; mutants (a changed conclusion, a dropped guard, a weakened invariant); `#print axioms`
(propext, Classical.choice, Quot.sound).

## 7. Failed attempts / notes (filled as the work goes)

Status at the end of the second agent (lakefile entries for ALL remaining modules were registered once, commit 2f34bbc4; not edited since).
Nothing here is a reduction: the two frozen theorems (`fKids_memoHit`, `fKids_statePF`) and the three F-top/shape obligations are NOT yet proved.
"BUILT" = `kjob lake build <module>` exit 0 in this worktree, no `sorry`, axioms propext/Classical.choice/Quot.sound only.

### 7.1 BUILT (the KeepsCS port of the K walk, state tracked)
* walk calculus and leaves (agent 1): Defs, Calc, Prims, Tac, Tele, Translate, Emit, Inst; (agent 2) ProjField, Canon (adds `KeepsCS.fuelFixM`), Fallback (`ChildEntryKS` now in the `PairPF` Triple form).
* Entry: the certified / mixed / machine entry arms now RETURN a `PairPF` pair (`finishSynthPS`, `certRest_keepsKS`, `certified_keepsKS`, `mixed_keepsKS`, `machineCert_keepsKS`); new pure facts about the machine closing (`closeMachine_params`, `closeLets_params`, `closeInsts_pf`, `closeInstsG_pf`, `designWith_pf`, `memModule_pf`); the PF world `KPF`/`KPFX` and the memo / child-cache writes of a `PairPF` result (`triple_memoInsertPS`, `triple_childInsertPS`, `CachePF`).
* EntryArms, EntryCore (not on the depth path: written before it was clear that the depth-pinned copies are what the induction uses).
* Depth: `PPF`, `WPF O D = KWD O PPF D`, `WPFX`, and the frozen `WorldPF` with `worldPF_iff : WorldPF O D w ↔ WPF O D w`; `triple_memoInsertDP`, `triple_childInsertDP`.
* DepthArms: `fromConst_*_windowD` at a pinned depth, results `PairPF`.
* DepthEntry: `entryNested_windowDP`, `combWith_nestedDP` (the post-processing `dropZeroWidthModule` / `mergeChecked` keep `ParamFree`: `dropZero_pf`, `mergeChecked_pf`, `designPF_top`), `tripleK_cacheGetD`, and **`synthesizeChild_windowDP`**: from `hcomb` (the entry at depth D, still a HYPOTHESIS here) a returning `synthesizeChild n` from `WPF O D` gives `WPF O D ∧ PairPF r`; a child-cache hit hands back the cache entry (`CachePF (cv w)`), a miss records the `PairPF` entry result. This is the content of `fKids_memoHit` once `hcomb` is discharged by the depth induction.
* Helpers, Diag (a STUB: `MsgMvK`, `logMvK_of`, `ppMvK_of` are the K walk's own, so there is exactly ONE `MsgMvK`; a regenerated copy was removed because it declared a second `MsgMvK` that would have hidden the named assumption from the Check), LegacyH1-H7 (with `TripleCS` / `KeepsCS.bindCaught` in H7), LegacyH8a, H8d, Rules, Cached.

### 7.2 NOT done, and why (the next agent starts here)
1. LegacyH8 (`handleDefinitionUnfold`) fails: after `kwAll2` the goal `OkMsg ex.toMessageData` (the caught `lastFail`) is left, because the hypothesis `OkOpt (…).2` that the K walk gets from `KeepsCP.bindCaught` is never introduced. What was done: `KCS.bindCaught` (pointed, 4 binders `a s (OkOpt a.2) (GoodS st s)`) is now proved in LegacyH7 (next to `TripleCS`, `KeepsCS.bindCaught`), and `swalkN` (Tools/ShippingGen4FKidsTac.lean, rt174 branch) now refers to it. A direct `refine Tools.ShippingGen4FKidsLegacyH7.KCS.bindCaught (by assumption) (fun _ _ _ _ => ?_)` on `KCS I st (Rec.tryInlineUnfold tr e hint named >>= f)` with `htri : TripleCS …` in the context WORKS (checked in a scratch file), but `swalkN` on the same goal does NOT take that branch: it unfolds `tryInlineUnfold` (`get` side goals). So the walker reaches the `Bind.bind` case through another route before the rt174 check (the KeepsCS->KCS `intro`, or a given-rule head match on `Bind.bind`). Debug with `KWALK_DEBUG=1` (the `kwalk step: head …` trace is in Tac.lean ~l.160) on exactly that goal; a fallback is to cut the proof of `handleDefinitionUnfoldKS` by hand at that bind.
2. `GoodS` demands `module.parameters` unchanged, and that is FALSE for the symbolic top: `bindInputsLegacy θ …` calls `CompilerM.addParameter` for every binder named in θ (Elab.lean:2127), independent of `symbolicMode`. For a child `θ = []`, so `find?` is `none` and `addParameter` is not reached. So the K-walk copy of `bindInputsLegacy` (LegacyTail, generated, FAILS at line 118, removed from the tree) cannot be proved for a general `parameters`. Resolution (design finding): (a) make the walk relation design-only (`StatePF` both sides; `addParameter` writes `module`, not `design`, so this holds at the top as well), and (b) prove the child's `module.parameters = []` as a separate state invariant that is only broken by `addParameter`, whose reach is excluded by `parameters = []` literally in the child's program. The `View` lemmas of Defs already give both halves.
3. Not generated/ported yet: LegacyH9, H10a, H10b, H11 (depend on H8), LegacyTail (see 2), LegacyArm, LegacyInduct, LegacyInduct2, LegacyFinal, DepthInduct, DepthTop, then the root `Tools/ShippingGen4FKids.lean` and `Tests/Gen4/FKidsCheck.lean`. `scripts/gen4/fkids_port.py` regenerates a K-walk module as a `KeepsCS` module (renames, `kwalk`->`swalkN`, `fuelFixM_keepsCP`->`KeepsCS.fuelFixM`); what it cannot do is listed in this section (TripleCP forms, `withVarMapping`-style `A`-suffixed rules in the `kwAll` list (patched by hand in Rules), result-carrying posts (`PairPF`), the bindCaught rule). Modules with no `KeepsCP` (Diag, LegacyArm, LegacyInduct, LegacyInduct2, LegacyFinal) should NOT be regenerated: re-use the K ones (the Diag lesson above); `DepthInduct`/`DepthTop` need the hand rewrite of `child_step`/`entryTop_windowD` with `PairPF` posts and `WPF`, following `synthesizeChild_windowDP`.
4. `LegacyImplKS` / `LegacyCachedKS` / `ChildEntryKS` are still the three hypotheses of `translateFallbackKS`/`translate_keepsKS`; they are discharged by H8-H11 / Final / the induction exactly as in the K walk (`legacyImplK_of_entry`), with `MsgMvK` as the only named assumption.

### 7.3 The three obligations from F-top / shape (owed by this walk): not reachable yet, exactly why
* (1) no collision `∀ x ∈ D.modules, x.name ≠ M.name`: needs a walk invariant on the NAMES of the modules added to `design` (they are `ModuleName.ofDecl c` of child declarations `c`, and `ofDecl` is injective: Tools.ShippingModuleName) together with `c ≠ declName` for every child synthesized under `declName`; the second fact is not given by any invariant of the K walk (a declaration that instantiates itself is only stopped by the depth limit, not by a name check). It is a NEW invariant (module names of the design differ from the current top), to be carried by the same walk as a second conjunct of `GoodS`/`StatePF`; `ModuleNameCheck.check` does not give it (it deduplicates raw names).
* (2) clause (e) for the top: every name in `M.parameters` is bound by θ: needs the invariant `∀ p ∈ module.parameters, p.name ∈ θ.map (·.1)` through the legacy walk (only `addParameter` at Elab.lean:2127 extends it, with `parameterDefault?` found by `find?` in θ, i.e. the name IS in θ). Provable in the SAME walk as a design-only-relation companion (see 7.2 item 2); not reachable before the legacy walk is complete.
* (3) clause (a), no duplicate parameter declaration at the top: `synthesizeCombinationalCoreWith` throws on `hasDuplicate` θ names (Elab.lean ~5429) and `bindInputsLegacy` calls `addParameter` once per binder (each binder has its own `userName`, so a duplicate declaration needs two binders with the same user name AND the name in θ; this is possible for a declaration with two same-named binders, so the check is NOT automatic): the claim `(module.parameters.map (·.name)).Nodup` therefore also needs an argument about the binder names of the declaration, or a hypothesis. Not a consequence of the run alone as far as I read it; record as OPEN, to be decided with F-top (it may be a genuine extra premise).
For children (a) is vacuous (`parameters = []`).

### 7.4 Failed attempts
* A copy of `Diag` produced by the porter declared a second `MsgMvK` in namespace `FKidsDiag`; elaboration reported `Ambiguous term MsgMvK`. Fixed by making `FKidsDiag` an empty stub (7.1).
* LegacyH1 `handleErrorPatternsKS` timed out at 1M heartbeats (`whnf`) with the `swalkN` walker; it closes at 4M. All generated Legacy files now set `maxHeartbeats 4000000`.
* EntryArms / EntryCore (non-pinned K world) turned out not to be on the depth-induction path; the pinned-depth copies (Depth*) are. They are built and kept (small), not used by the induction.

### 7.5 fkids3 (third agent) progress notes
* 7.2-1 cause found: the walker's rt174 branch (`KCS.bindCaught`) never ran because the quotation in Tac.lean named `Tools.ShippingGen4FKidsLegacyH7.KCS.bindCaught`, a lemma declared LATER than Tac; hygiene made the identifier "Unknown identifier" (seen with `KWALK_DEBUG=1`: `kwalk runTac failed ... Unknown identifier`). Fixed by `mkIdent` in Tac. With that, H8 gets past `OkMsg` and the next goals are `ParamFree` of the child pair (`subModule`, members of `subDesign.modules`), which the K walk never needed.
* For those: Calc gets `OptPFc`, `NoRetS`/`NoRetSA` (a run that never returns), `KCS.bindTryChild` (`try (some <$> liftMetaM (childSynthEntry n)) catch h >>= f`, `h` never returns, `f` is asked only for `some r` with `PairPF r`), `KCS.forIn_list_mem`; Tac gets: join-point facts with an `OptPFc` premise for Option (Module x Design) parameters, the `bindTryChild` step, `NoRetS` steps, closers for `ParamFree`/`OptPFc` side goals. All gated on `hchild` / a PairPF hypothesis in scope, so other modules' walks are unchanged. H8's `hchild` is the `PairPF` Triple form (`ChildEntryKS`).
* Failed attempt: the first ungated version of these Tac changes made LegacyH3 (`handleBitVecOps`/`kwAll`) run away at `whnf` (4M and 8M heartbeats both exhausted), so the rules were gated.
* RESULT (end of fkids3): Calc, Tac (gated) and H3 build again (H3 at 4M); the regenerated LegacyH8 with `hchild` in PairPF Triple form does NOT yet build: at maxHeartbeats 4M it stops at `whnf` (error at the theorem), and at 20M the build was still running after 580 s (killed, not a result). The file was removed from the tree (regenerate: `python3 scripts/gen4/fkids_port.py LegacyH8`, then replace the `hchild` binder by `∀ c, Triple mctx mref cctx cref I (childSynthEntry c) (fun r w => I w ∧ PairPF r) (fun e w => I w ∧ OkExc e)`). Not yet known which new step runs away (candidates: the `OptPFc`-premise join point, `bindTryChild` unification of `some <$> liftMetaM (synthesizeCombinational n)` against `childSynthEntry`, the NoRetS handler walk). Next: run with `KWALK_DEBUG=1` in one `lake build` and read the last `kwalk step` lines.
* Not started: 7.2-2 (design-only GoodS; planned edit: `GoodS a b := StatePF a ∧ StatePF b`, fix the `hg.2.1` -> `hg.2` uses in Calc/H7 and the `⟨h,h,rfl⟩`), LegacyTail, H9-H11 reuse, DepthInduct/DepthTop, root, FKidsCheck, obligations (1)-(3).

### 7.6 fkids4 (fourth agent)
* 7.2-2 done: `GoodS a b := StatePF a ∧ StatePF b ∧ (a.module.parameters = [] ↔ b.module.parameters = [])` (commit 08462d5e). The design part (`GoodS.design`) is the walk relation the symbolic top can use; the third conjunct is the child's separate invariant (an iff, not an equality, and it must be symmetric: `instCallKey` restores an earlier builder state, and the one-way implication failed there). It is broken only by `addParameter`; `bindInputsLegacyKPS` (LegacyTail, BUILT, f1bb8525) takes `hθ : parameters = []` and closes the `addParameter` branch because `find? _ [] = some _` is absurd. For the symbolic top (θ ≠ []) a design-only walk through `bindInputsLegacy` is still to be written (obligation 2); it is not needed by fKids for children.
* H1..H7, H8a, H8d, Rules, Cached, Entry, LegacyTail all rebuilt and BUILT with the new `GoodS`.
* 7.5 runaway of LegacyH8: cause found WITHOUT further hand cutting. `KWALK_DEBUG=1`: only ~190 steps, the last logged `kwalk step: head @bind` (after `Rec.handleDefinitionUnfold.match_1`, `jp_39`), then `whnf` timeout at 4M. That bind is `try (some <$> liftMetaM (getConstInfoInduct structName)) catch _ => pure none`, an UNRELATED try/catch: the gated `bindTryChild` step (Tac, fkids3) fired on every `tryCatch` once `hchild` was in scope, and unifying `childSynthEntry ?n` against `getConstInfoInduct _` ran away. Fix (Tac): the step applies only if the try body mentions `childSynthEntry` or `Rec.synthesizeCombinational`. LegacyH8 (hchild in `PairPF` Triple form) then builds.
* LegacyH9, LegacyH10a BUILT (ported, `hchild` in `PairPF` Triple form). LegacyH10b (`toIRK_boundS`, line 86) does NOT build: `whnf` timeout at 4M after 13m48s (first attempt, no KWALK_DEBUG yet); the generated H10b/H11 were removed from the tree (regenerate: `python3 scripts/gen4/fkids_port.py LegacyH10b`; H11 likewise; for both, only the `hchild` binder is replaced by the Triple form). Next: `KWALK_DEBUG=1 kjob lake env lean` once on H10b, read the last `kwalk step`.
* H10b under `KWALK_DEBUG=1` (one run, ~13 min, log not kept in the tree): 3140 `kwalk step`s, then the theorem dies with `whnf` timeout; the last logged events are the walker's recursive-call attempts at the end of the `toIR` unfold: `exact ih _ _ _ _ _ :: Type mismatch` (several arities, 12k-1.4M hb each) and finally `exact ih _ _ (by assumption) _ _ _ :: internal exception #5` after 18.6M raw hb = a runtime heartbeat exception that `runTac` does not catch (`runTac` catches only ordinary exceptions; `runTacLim` is the variant with `tryCatchRuntimeEx`). Suspect: with `KCS` the recursive hypothesis `ih : ∀ … e' (h' : sizeOf e' < n), KeepsCS … (toIR … e')` is pointed at a state after `intro st`, and the `exact ih …` arities that do not match unfold the whole do-block. Next steps for the next agent: (a) make the `ih` attempt in Tac go through `runTacLim` (a runaway try is reported, the step goes on) and/or try `exact ih _ _ _ _ _ st`-style with the pointed state; (b) then H11 (same `hchild` binder replacement), Arm, Induct, Induct2, Final, DepthInduct, DepthTop, root, FKidsCheck.
* Not started this session: obligations (1) NameNoTop, (3) Nodup (the 7.3 evidence stands unchanged), and the child `parameters=[]` iff for the symbolic top.
