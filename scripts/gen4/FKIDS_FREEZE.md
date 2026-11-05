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
* (none yet)
