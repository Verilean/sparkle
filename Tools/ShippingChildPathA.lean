import Tools.ShippingChildVertA
-- NOT YET BUILT (worker par/path, base 37dc265f). Isolated: no existing file uses it.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx` only (no `RefLaws`, no
-- `RefLawsCore`, no `RefLawsCore.toAOps`/`toA`, no `RefLawsATele`).
-- Reused law-free lemmas (each checked: its statement and proof mention no law bundle):
--   Tools/ShippingChildKeeps.lean: `Triple`, `keeps_iff`, `Triple.bind`, `Triple.pure`, `Triple.ite`;
--   Tools/ShippingChildHarness.lean (all stated BEFORE its `variable (L : RefLaws …)`):
--     `TripleC`, `keepsC_iff`, `Triple.throw`, `TripleC.pure`, `TripleC.bind`, `TripleC.lift`,
--     `TripleC.get`, `TripleC.set`, `TripleC.getCompilerState`, `TripleC.withReader`,
--     `TripleC.throw`, `TripleC.ite`;
--   Tools/ShippingChildVC.lean: `Keeps.bind`, `Keeps.pure`;
--   the `okmsg` tactic (ShippingChildInv.lean: constructors of `OkMsg` only).
-- The bodies of `makeWireA`, `addInputA`, `addOutputA`, `emitAssignA`, `bindInputPortA`,
-- `finishSynthA` and the leaf walk of `emitLeavesA` copy the BUILT old proofs
-- (ShippingChildHarness.lean:117-303) with `J L D`/`JE L D` replaced by a stable `I` and each
-- `Triple.frame L X D` / `Triple.diag L X D` replaced by `keepsA_framed` / `keepsA_diag`.
-- Writing-time guesses (marked `-- guess: Pn` below):
--  P1 `emitLeavesA`: after the 9 binds, `dsimp only` zeta-reduces the two `do` join points
--     (`__do_jp`), so the goal is `if (!le.isFVar) = true then lift (r.modify _) >>= _ else _`
--     and BOTH branches, after `try dsimp only`, are the same tail `get >>= fun cs => …` (the
--     old proof stated that tail explicitly; here it is walked twice by `all_goals`);
--  P2 `FramedA.exprCacheModify r _ hr` unifies with `ST.Ref.modify r (·.insert ⟨le⟩ lw)`;
--  P3 `certRest_keepsA`: after `unfold certRest`, `try dsimp only` zeta-reduces `compiler`, and
--     `Triple.bind` unifies `bindCertifiedInputs k l ctx st` with `(compiler.run ctx).run st`
--     (as `harnessRel_of` does), `rintro ⟨_, fs⟩` then `exact` closes the `let (_, s) ←` match;
--  P4 `fromConst_certified_keepsA`: after `delta synthesizeFromConst` (fallback `unfold`) the
--     discriminant is
--     `if true = true then certifiedShape? false [] constInfo else none`; `hd` closes by
--     `(if_pos rfl).trans hshape` (fallbacks inside), `rw [hd]` rewrites it;
--  P5 then `refine Keeps.bind (keepsA_diag … (Diag.profLog b _))` unifies with the matcher applied
--     to `some (bs, body)` by whnfCore (matcher iota) — NO `dsimp`/`simp` over the unfolded entry
--     (it holds the whole legacy branch); the fallback `dsimp only` (only if that fails) does
--     traverse it;
--  P6 the logger `logProf s!"…"` elaborates to `liftM (profLogIO b _)` (as in `core_tripleA`) and
--     `sparkleSubModuleCache.modify f` to `ST.Ref.modify sparkleSubModuleCache f : MetaM Unit`;
--  P7 `fromConst_certified_hbody`: `htr` for `translateExprToWire tenv` is accepted for the
--     eta-expanded translator `fun e h t n => translateExprToWire tenv e h t n` (beta defeq).

/-! # The certified branch of the body, under the admissible boundary

Extends the ONE vertical path of `Tools/ShippingChildVertA.lean` (witness `O :
RefLawsAOps MkRefd mref cref`, `hA : AdmCtx O.quiet mctx cctx`) from
`certified_keepsA` down through the certified sub-path:

  `synthesizeFromConst` (certified branch, Elab.lean:5296: `certifiedShape? =
  some (bs, body)` → logger → `synthesizeCertified` → `sparkleSubModuleCache`
  update → `return`) → `certified_keepsA` → `certRest` = `bindCertifiedInputs`
  (one `bindInputPort` per signal binder) ∘ `emitLeaves` (one leaf `"out"`) ∘
  the `CircuitM` run ∘ `finishSynth`.

Proved, for any STABLE invariant `I` (`StableA O.quiet I`; in particular
`JQ O.quiet D`):
* `certRest_keepsA` — `hrest` of `certified_keepsA` DISCHARGED: every op is a
  law of `O` (clock `FramedA.monoMs`, counters `FramedA.sideGet
  .callCounter/.cacheHits`, logger `Diag.profLog`, wire-width cache
  `FramedA.sideModify .wireWidth`, the translation-cache update
  `FramedA.exprCacheModify r _ hr` with the provenance `hr : MkRefd _ r`
  THREADED from `certified_keepsA` — not `True`) or pure circuit-state /
  reader work, the port-name check and `finishSynth` throw only messages of the
  class (`okmsg`). The ONLY hypothesis is the translator, at its one call in
  `emitLeaves`: `htr : ∀ e hint top named, KeepsC … I (translate e hint top
  named)`.
* `fromConst_certified_keepsA` — the whole certified branch of
  `synthesizeFromConst` for a constant whose certified shape matches
  (`certifiedShape? false [] constInfo = some (bs, body)`), from `htr` only.
* `fromConst_certified_hbody` — the instance at `JQ O.quiet 1` and the
  entry's translator `translateExprToWire tenv`: the shape of `core_tripleA`'s
  premise `hbody`, for the matching constants.

What of `hbody` (core_tripleA) this covers: ONLY the constants `ci` handed to
the body whose certified shape matches (`certifiedShape? false [] ci = some _`,
the `ci` being the entry's `entryConst …`), and only RELATIVE to the
translator. Ledger — the minimal calls NOT migrated to the new boundary:
1. the translator call at `emitLeaves` (`translate leafExpr portName false
   true`; for the entry, `translateExprToWire` with its child recursion
   `synthesizeChild` and its own telescopes) — hypothesis `htr`;
2. the mixed branch: `synthesizeMixedCertified` (harness walk analogous, open);
3. the machine branch: `machineShape?` read + `synthesizeMachineCertified`;
4. the legacy tail: the memo read `sparkleSubModuleCache.get`,
   `openRecordInputs`, `lambdaTelescope` (needs `RefLawsATele`, a separate
   assumption), `splitReturnLeaves`, `bindInputsLegacy`, and its own
   translation / `finishSynth`. -/

namespace Tools.ShippingChildPathA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildVertA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The circuit-state primitives (copies of the old harness, law-free but the wire-width cache) -/

/-- The wire-width cache's update, lifted: `FramedA.sideModify .wireWidth`. -/
theorem wireWidthA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (f : Std.HashMap String Nat → Std.HashMap String Nat) :
    TripleC mctx mref cctx cref I
      (CompilerM.liftMetaM (ST.Ref.modify sparkleWireWidthCache f)) (fun _ => I)
      (fun e w => I w ∧ OkExc e) :=
  TripleC.lift (keeps_iff.mp (keepsA_framed O hA hS (FramedA.sideModify _ .wireWidth)))

theorem makeWireA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    TripleC mctx mref cctx cref I (CompilerM.makeWire hint ty named)
      (fun _ => I) (fun e w => I w ∧ OkExc e) := by
  unfold CompilerM.makeWire
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  dsimp only
  split
  · refine TripleC.bind (wireWidthA O hA hS _) ?_
    intro _
    exact TripleC.pure fun _ hw => hw
  · exact TripleC.pure fun _ hw => hw

theorem addInputA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (name : String) (ty : Sparkle.IR.Type.HWType) :
    TripleC mctx mref cctx cref I (CompilerM.addInput name ty)
      (fun _ => I) (fun e w => I w ∧ OkExc e) := by
  unfold CompilerM.addInput
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  split
  · exact wireWidthA O hA hS _
  · exact TripleC.pure fun _ hw => hw

theorem addOutputA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (name : String) (ty : Sparkle.IR.Type.HWType) :
    TripleC mctx mref cctx cref I (CompilerM.addOutput name ty)
      (fun _ => I) (fun e w => I w ∧ OkExc e) := by
  unfold CompilerM.addOutput
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  split
  · exact wireWidthA O hA hS _
  · exact TripleC.pure fun _ hw => hw

theorem emitAssignA {I : Void IO.RealWorld → Prop} (lhs : String) (rhs : Sparkle.IR.AST.Expr) :
    TripleC mctx mref cctx cref I (CompilerM.emitAssign lhs rhs)
      (fun _ => I) (fun e w => I w ∧ OkExc e) := by
  unfold CompilerM.emitAssign
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  exact TripleC.set _

/-! ## The binder walk -/

theorem bindInputPortA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) {α : Type}
    (fv : FVarId) (bn : String) (ty : Sparkle.IR.Type.HWType) (k : CompilerM α)
    (hk : TripleC mctx mref cctx cref I k (fun _ => I) (fun e w => I w ∧ OkExc e)) :
    TripleC mctx mref cctx cref I (bindInputPort fv bn ty k)
      (fun _ => I) (fun e w => I w ∧ OkExc e) := by
  unfold bindInputPort CompilerM.withVarMapping
  refine TripleC.bind (makeWireA O hA hS _ _ _) ?_
  intro w
  refine TripleC.bind (addInputA O hA hS _ _) ?_
  intro _
  refine TripleC.bind TripleC.getCompilerState ?_
  intro old
  exact TripleC.withReader _ hk

/-- `bindCertifiedInputs`: a domain binder is skipped, a signal binder is one
`bindInputPort`. -/
theorem bindCertifiedInputsA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) {α : Type} (k : CompilerM α)
    (hk : TripleC mctx mref cctx cref I k (fun _ => I) (fun e w => I w ∧ OkExc e)) :
    ∀ l : List ((Name × GateBinder) × FVarId),
      TripleC mctx mref cctx cref I (bindCertifiedInputs k l)
        (fun _ => I) (fun e w => I w ∧ OkExc e)
  | [] => by unfold bindCertifiedInputs; exact hk
  | ((_, .domain), _) :: rest => by
    unfold bindCertifiedInputs
    exact bindCertifiedInputsA O hA hS k hk rest
  | ((_, .signal _), _) :: rest => by
    unfold bindCertifiedInputs
    exact bindInputPortA O hA hS _ _ _ _ (bindCertifiedInputsA O hA hS k hk rest)

/-! ## The leaf emission, the translator its only hypothesis -/

/-- **`emitLeaves` under the admissible boundary.** Every op but the
translator is discharged; the translation-cache update uses the provenance
`hr` of the cache ref. -/
theorem emitLeavesA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (b : Bool) (r : IO.Ref (Lean.ExprStructMap String))
    (hr : MkRefd _ r)
    (htr : ∀ e hint top named, KeepsC mctx mref cctx cref I (translate e hint top named)) :
    ∀ (leaves : List (String × Lean.Expr)) (fw : Option String) (idx : Nat),
      TripleC mctx mref cctx cref I (emitLeaves translate r (profLogIO b) leaves fw idx)
        (fun _ => I) (fun e w => I w ∧ OkExc e)
  | [], fw, idx => by
    unfold emitLeaves
    exact TripleC.pure fun _ hw => hw
  | (pn, le) :: rest, fw, idx => by
    unfold emitLeaves
    have clock : TripleC mctx mref cctx cref I (CompilerM.liftMetaM (liftM IO.monoMsNow))
        (fun _ => I) (fun e w => I w ∧ OkExc e) :=
      TripleC.lift (keeps_iff.mp (keepsA_framed O hA hS FramedA.monoMs))
    have calls : TripleC mctx mref cctx cref I
        (CompilerM.liftMetaM (ST.Ref.get sparkleCallCounter)) (fun _ => I)
        (fun e w => I w ∧ OkExc e) :=
      TripleC.lift (keeps_iff.mp (keepsA_framed O hA hS (FramedA.sideGet .callCounter)))
    have hits : TripleC mctx mref cctx cref I
        (CompilerM.liftMetaM (ST.Ref.get sparkleCacheHits)) (fun _ => I)
        (fun e w => I w ∧ OkExc e) :=
      TripleC.lift (keeps_iff.mp (keepsA_framed O hA hS (FramedA.sideGet .cacheHits)))
    have log : ∀ msg, TripleC mctx mref cctx cref I
        (CompilerM.liftMetaM (liftM (profLogIO b msg))) (fun _ => I)
        (fun e w => I w ∧ OkExc e) :=
      fun msg => TripleC.lift (keeps_iff.mp (keepsA_diag O hA hS (Diag.profLog b msg)))
    refine TripleC.bind clock ?_; intro t0
    refine TripleC.bind calls ?_; intro c0
    refine TripleC.bind hits ?_; intro h0
    refine TripleC.bind (log _) ?_; intro _
    refine TripleC.bind (keepsC_iff.mp (htr le pn false true)) ?_; intro lw
    refine TripleC.bind clock ?_; intro t1
    refine TripleC.bind calls ?_; intro c1
    refine TripleC.bind hits ?_; intro h1
    refine TripleC.bind (log _) ?_; intro _
    dsimp only  -- guess: P1
    refine TripleC.ite
      (fun _ => TripleC.bind (TripleC.lift (keeps_iff.mp
        (keepsA_framed O hA hS (FramedA.exprCacheModify r _ hr)))) (fun _ => ?_))  -- guess: P2
      (fun _ => ?_)
    all_goals
      try dsimp only
      refine TripleC.bind TripleC.get ?_
      intro cs
      try dsimp only
      refine TripleC.ite (fun _ => ?_) (fun _ => ?_)
      · refine TripleC.bind (Q := fun _ _ => False)
          (TripleC.throw _ fun _ hw => ⟨hw, by okmsg⟩) ?_
        intro _ _ _ w hf
        exact hf.elim
      · try dsimp only
        refine TripleC.bind (addOutputA O hA hS _ _) ?_
        intro _
        refine TripleC.bind (emitAssignA _ _) ?_
        intro _
        exact emitLeavesA O hA hS translate b r hr htr rest _ _

/-! ## `finishSynth` and the rest of the certified sub-path -/

theorem finishSynthA {I : Void IO.RealWorld → Prop} (declName : Name)
    (st : Sparkle.IR.Builder.CircuitState) :
    Triple mctx mref cctx cref I (finishSynth declName [] false st)
      (fun _ => I) (fun e w => I w ∧ OkExc e) := by
  unfold finishSynth
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact Triple.ite (fun _ => Triple.pure fun _ hw => hw)
    (fun _ => Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩)

/-- **`hrest` of `certified_keepsA`, discharged**: the binder walk, the one
leaf, the `CircuitM` run and `finishSynth` keep a stable invariant for a
cache ref with provenance, given only the translator. -/
theorem certRest_keepsA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsC mctx mref cctx cref I (translate e hint top named))
    (ids : List FVarId) (r : IO.Ref (Lean.ExprStructMap String)) (hr : MkRefd _ r) :
    Keeps mctx mref cctx cref I (certRest translate (profLogIO b) declName bs body ids r) := by
  unfold certRest
  refine keeps_iff.mpr ?_
  try dsimp only  -- guess: P3
  refine Triple.bind
    (bindCertifiedInputsA O hA hS _ (emitLeavesA O hA hS translate b r hr htr _ _ _) _ _ _) ?_
  rintro ⟨_, fs⟩
  exact finishSynthA declName fs

/-- `synthesizeCertified` from the translator only (`certified_keepsA` with
`certRest_keepsA`). -/
theorem certified_keepsA_of_translate (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsC mctx mref cctx cref I (translate e hint top named)) :
    Keeps mctx mref cctx cref I (synthesizeCertified translate (profLogIO b) declName bs body) :=
  certified_keepsA O hA hS translate (profLogIO b) declName bs body
    (fun ids r hr => certRest_keepsA O hA hS translate b declName bs body htr ids r hr)

/-! ## The certified branch of `synthesizeFromConst` -/

/-- **The certified branch of the body, from the translator only.** For a
constant whose certified shape matches, `synthesizeFromConst` (certified
front end, concrete widths) keeps a stable invariant: the logger
(`Diag.profLog`), `synthesizeCertified`, the sub-module cache update
(`FramedA.sideModify .subModule`), the `return`. -/
theorem fromConst_certified_keepsA (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)} {body : Lean.Expr}
    (hshape : certifiedShape? false [] constInfo = some (bs, body))
    (htr : ∀ e hint top named, KeepsC mctx mref cctx cref I (translate e hint top named)) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst) := by
  have hd : (if true = true then certifiedShape? false [] constInfo else none) = some (bs, body) := by
    first  -- guess: P4
      | exact (if_pos rfl).trans hshape
      | (rw [if_pos rfl]; exact hshape)
      | simpa using hshape
  -- `delta` (no simp traversal of the unfolded entry, which holds the legacy branch)
  first | delta synthesizeFromConst | unfold synthesizeFromConst  -- guess: P4
  rw [hd]  -- guess: P4
  first  -- guess: P5, P6
    | refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_
    | (dsimp only; refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_)
  intro _
  refine Keeps.bind (certified_keepsA_of_translate O hA hS translate b declName bs body htr) ?_
  intro result
  refine Keeps.bind (keepsA_framed O hA hS (FramedA.sideModify _ .subModule)) ?_  -- guess: P6
  intro _
  exact Keeps.pure _

/-- The same at `JQ O.quiet D`. -/
theorem fromConst_certified_keepsJQ (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (D : Nat)
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)} {body : Lean.Expr}
    (hshape : certifiedShape? false [] constInfo = some (bs, body))
    (htr : ∀ e hint top named,
      KeepsC mctx mref cctx cref (JQ O.quiet D) (translate e hint top named)) :
    Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst) :=
  fromConst_certified_keepsA O hA (stableA_JQ _ D) translate b declName constInfo isInst hshape htr

/-- **The part of `core_tripleA`'s `hbody` this file covers**: the body at
depth 1 with the entry's translator, for a handed-over constant `ci` whose
certified shape matches, from the translator's own keeping only. (The other
constants — mixed, machine, legacy — and the translator stay open; see the
ledger in the header.) -/
theorem fromConst_certified_hbody (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) {tenv : Lean.Environment} (b : Bool)
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)}
    {body : Lean.Expr} (hshape : certifiedShape? false [] ci = some (bs, body))
    (htr : ∀ e hint top named,
      KeepsC mctx mref cctx cref (JQ O.quiet 1) (translateExprToWire tenv e hint top named)) :
    Keeps mctx mref cctx cref (JQ O.quiet 1)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst) :=
  fromConst_certified_keepsJQ O hA 1 _ b declName ci isInst hshape htr  -- guess: P7

end Tools.ShippingChildPathA
