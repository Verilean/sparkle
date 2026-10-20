import Tools.ShippingChildPathA
-- BUILT by the integrator: fa1 exit 1 (do-notation pushes the continuation into the shape-read `if`: binds misaligned; guess M5 failed), fa2/fa3 exit 1 (`pure_bind` did not fire), fa4 exit 1 (lemma placed after a docstring), fa5 exit 0 (integrator rewrote `fromConst_machine_keepsA`: `simp only` reduction of the `if`s, `generalize` of the shape, `keeps_pure_bind_of`), audit fa6 exit 0 (worker par/mm, base 6a231b89). Isolated.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx` only (no `RefLaws`, no
-- `RefLawsCore`, no `RefLawsCore.toAOps`/`toA`, no `RefLawsATele`, no `J L D`/`JE L D`, no
-- `Triple.frame L`/`Triple.diag L`, no `CacheInv`/`RealChild`/`ChildKeeps`/`HarnessRel`/`BodyRel`).
-- Reused law-free lemmas (each statement checked to mention no law bundle):
--   Tools/ShippingChildKeeps.lean: `Triple`, `keeps_iff`, `Triple.bind`, `Triple.bindQ`,
--     `Triple.pure`, `Triple.mapM` (stated after `variable (L …)` but its statement does not
--     mention `L`, so `L` is not a binder of it);
--   Tools/ShippingChildHarness.lean: `Triple.throw`, `TripleC`;
--   Tools/ShippingChildVC.lean: `Keeps.bind`, `Keeps.pure`, `Keeps.ite`;
--   Tools/ShippingChildBndInit.lean: `runsTo_get_readOf`;
--   Tools/ShippingChildPathA.lean (built, law-free but `O`): `bindInputPortA`, `emitLeavesA`,
--     `finishSynthA`, `fromConst_certified_keepsA`;
--   the `okmsg` tactic (constructors of `OkMsg` only).
-- The mixed harness walk copies the BUILT old `harnessRel_of` (ShippingChildHarness.lean:309-324)
-- and the machine walk the old `machine_keeps` / `closeInstsM_keeps` / `closeInstsGM_keeps`
-- (ShippingChildKeeps.lean:552-612), with every `Triple.frame L X D` replaced by `keepsA_framed`
-- and the synthesis-ref read `Triple.synthRead L` (law `L.synthGet`) replaced by
-- `tripleA_synthGet` (law `O.frame` at `FramedA.synthGet`, plus `sv w = some synthesizeChild`
-- carried BY THE INVARIANT, premise `hsv`; for `JQ` it is the second conjunct).
-- Writing-time guesses (marked `-- guess: Mn` below):
--  M1 `mixed_keepsA`: after `unfold synthesizeMixedCertified`, `split` splits the `dite`, and
--     `dsimp only` zeta-reduces `innerBody`/`compiler` (as in `harnessRel_of`); `Triple.bindQ
--     (φ := MkRefd _)` unifies with `IO.mkRef {} >>= fun cacheRef => …`;
--  M2 `tripleA_synthGet`: `cases hm : (sparkleChildSynth.get : MetaM _) …` and
--     `runsTo_get_readOf _ hm` (the `tripleA_depthGet` pattern, VCA V1/V3); `sv w` unfolds to
--     `readOf sparkleChildSynth w` by `exact`;
--  M3 `closeInstsM_keepsA`/`closeInstsGM_keepsA`: after `subst hs`, `dsimp only` reduces the
--     `let some synth ← … | return none` match on `some synthesizeChild` (as the old proofs);
--  M4 `keeps_of_pure_bind`: `Keeps I (pure a >>= f)` gives `Keeps I (f a)` by definitional
--     unfolding of the `MetaM` bind (first `exact h`, fallbacks via `keeps_iff` + `change` to the
--     `EST.bind` form used by `Triple.bind`);
--  M5 `fromConst_machine_keepsA`: after `delta synthesizeFromConst` and `rw [hd1, hd2]`,
--     `refine Keeps.bind ?_ (fun machine? => ?_)` unifies with the two matchers on `none` by
--     whnfCore (matcher iota, as PathA P5) and splits off the `machine?` computation
--     `if (true && !false && [].isEmpty) = true then do let env ← getEnv; pure … else pure none`;
--  M6 the legacy goal (the `none` alternative of `match machineResult?`) is closed from
--     `hlegacy` (the entry with the certified front end OFF): `delta … at h`, the two
--     `if false = true` discriminants rewritten by `if_neg`, then `keeps_of_bind_ite_neg` (its
--     `c` found by unification through the two matchers on `none`; `by decide` closes
--     `¬ ((false && !false && [].isEmpty) = true)`) and twice `keeps_of_pure_bind`; the
--     remaining `match none with | some result => … | none => TAIL` is the goal's term
--     (TAIL does not mention `certifiedFrontEnd`), closed by `exact`;
--  M7 the hbody instances: `htr` for `translateExprToWire tenv` accepted for the eta-expanded
--     translator (as PathA P7); `fun _ h => h.2.1` is `hsv` for `JQ`.

/-! # The other two front-end branches of the body, under the admissible boundary

Extends `Tools/ShippingChildPathA.lean` (the certified branch) to the two other
front ends of `synthesizeFromConst` (Sparkle/Compiler/Elab.lean:5288-):

* the MIXED certified branch (`mixedCertifiedShape? = some (bs, body)`, the first
  gate missing): logger → `synthesizeMixedCertified` (fresh fvars, distinctness
  `dite`, translation-cache allocation `FramedA.mkExprCache` with provenance
  `MkRefd` threaded to `emitLeaves`, `bindMixedCertifiedInputs`, the `CircuitM`
  run, `finishSynth`) → `sparkleSubModuleCache` update → `return`;
* the MACHINE branch (both gates missing): the environment read
  (`FramedA.env`) for `machineShape?`, `synthesizeMachineCertified` = the mixed
  harness, the pure `closeLets`/`closeMachine`, and the instance closing
  `closeInstsM` / `closeInstsGM` (the synthesis-ref read `FramedA.synthGet`,
  then ONE call of the child entry `synthesizeChild` per non-memory call entry;
  a memory-origin entry's child is built, pure), the logger, the cache update.

Proved, for any STABLE invariant `I` (`StableA O.quiet I`):
* `mixed_keepsA` — `synthesizeMixedCertified` from the translator `htr` only.
* `machineCert_keepsA` — `synthesizeMachineCertified` from `htr`, the child entry
  `hchild : ∀ c, Keeps … I (synthesizeChild c)` (a SEPARATE named premise, used at
  its calls in `closeInstsM`/`closeInstsGM` only), and `hsv : ∀ w, I w → sv w =
  some synthesizeChild` (what the invariant says of the synthesis ref).
* `fromConst_mixed_keepsA` — the mixed branch of `synthesizeFromConst`
  (`certifiedShape? false [] ci = none`, `mixedCertifiedShape? false [] ci isInst =
  some _`), from `htr` only.
* `fromConst_machine_keepsA` — `synthesizeFromConst` when both gates miss, from
  `htr`, `hchild`, `hsv` and `hlegacy`: the machine branch is covered, but the
  run FALLS THROUGH to the legacy tail when `machineShape?` (at the environment
  read there) is `none` or `synthesizeMachineCertified` returns `none` (`closeLets`
  fails, or `closeInsts`/`closeInstsG` fails); that fall-through is exactly the
  premise `hlegacy`, stated as "the entry with the certified front end OFF keeps
  `I`" (`synthesizeFromConst … [] false false ci isInst`, whose three gate
  discriminants are `none` and which then runs the same tail).
* `fromConst_frontends_keepsA` / `fromConst_hbody_frontends` — the three
  front-end branches together, premises `htr`, `hchild` (and `hsv`), and the
  legacy tail `hlegacy` ONLY for constants on which both gates miss.
* `core_tripleA_frontends` — `core_tripleA` with its `hbody` discharged from
  these premises (the translator, the child entry, the legacy tail).

LEDGER — for each branch of `synthesizeFromConst` (entry: `ci = entryConst true false
[] ci0 (instancePredicate env) (userInliner env) (structEnv env)`), the calls NOT
migrated to the new boundary, and the existing tests that reach it:
1. CERTIFIED (`certifiedShape? false [] ci = some _`; PathA): unmigrated: the
   translator call in `emitLeaves` (`htr`). Reached by: `fragA`, `fragB`, `fragC`,
   `fragD`, `fragS` — Tests/Compiler/ShippingEntrySoundnessTest.lean:225-260
   asserts `(certifiedShape? false [] ci).isSome` on `getConstInfo` (equal to the
   entry constant: `entryConst` changes `ci0` only when `certifiedShape? ci0` is
   `none`).
2. MIXED (`certifiedShape? … = none`, `mixedCertifiedShape? … = some _`; here):
   unmigrated: the translator call in `emitLeaves` (`htr`). Reached by: `pick`,
   `pickD` (Tests/Compiler/ShippingMachineInstTest.lean:170-171) and
   `Sparkle.IP.Crypto.Keccak256HW.keccakRcHW`
   (Tests/Compiler/OneOutWKeccakFTest.lean:156): `#gate_child`, whose `gateDefs`
   (Tools/ShippingGateChildCommand.lean:26-35) throws unless, on the entry
   constant, `certifiedShape?` is `none` and `mixedCertifiedShape?` is `some`.
3. MACHINE (both gates `none`, `machineShape?` `some` at the environment read,
   `synthesizeMachineCertified` `some`; here): unmigrated: the translator (`htr`,
   inside the mixed harness) and the child entry `synthesizeChild` at each
   non-memory call (`hchild`). Reached by (`#machine_endpoint f` →
   `generateCore` → `readMachine`, Tools/ShippingMachineCommand.lean:440-453,
   throws unless both gates miss on the entry constant and `machineShape?` is
   `some`; with `checkCloses` (2502-2505) it also evaluates
   `synthesizeMachineCertified … |>.isSome`, so the run does NOT fall through):
   `dead7` (Tests/Compiler/LeafDeadInitTest.lean:54), `toggleL`
   (Tests/Compiler/ShippingMachineSeqLoopTest.lean:35), `twoHW`, `toggle`
   (Tests/Compiler/ShippingMachineCommandTest.lean:52,57), `loopPair`
   (Tests/Compiler/ShippingMachineLoopTest.lean:109), `pe`
   (Tests/Compiler/ShippingMachineSeqLinkedTest.lean:25). `acc` and `cnt`: the
   machine SHAPE is read (Tests/Compiler/LeafEntryFamilyTest.lean:121,149,
   `#machine_leaf_entry_try` GENERATED/REBUILT, whose `scan` refuses unless
   `readMachine` succeeds, Tools/ShippingLeafEntryCommand.lean:163-175); whether
   `synthesizeMachineCertified` returns `some` for them: not determined from these
   files.
4. LEGACY TAIL (both gates `none`, and `machineShape?` `none` at the environment
   read OR `synthesizeMachineCertified` `none`): NOT migrated (premise
   `hlegacy`): the memo read `sparkleSubModuleCache.get`, the logger and clock,
   `openRecordInputs`, `stripMemoizeWrappers`, `lambdaTelescope` (needs
   `RefLawsATele`, a separate assumption), `splitReturnLeaves`, `IO.mkRef` of its
   cache, `bindInputsLegacy`, its translation (`emitLeaves`/translator),
   `finishSynth`, the cache update, and the non-`defnInfo` throw. Reached by:
   not determined from the tests (`notCertified`,
   Tests/Compiler/ShippingEntrySoundnessTest.lean:286-289, asserts only that the
   FIRST gate misses). -/

namespace Tools.ShippingChildFrontA
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
open Tools.ShippingChildPathA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## Law-free `Keeps` conversions (no law, no boundary) -/

/-- The converse: `pure a >>= f` keeps what `f a` keeps (integrator, after fa3). -/
theorem keeps_pure_bind_of {α β : Type} {I : Void IO.RealWorld → Prop} {a : α}
    {f : α → MetaM β} (h : Keeps mctx mref cctx cref I (f a)) :
    Keeps mctx mref cctx cref I (Pure.pure a >>= f) := by
  first
    | exact h
    | (intro w hw; exact h w hw)

/-- A `pure` first step is no step (definitional unfolding of the `MetaM`
bind). -/
theorem keeps_of_pure_bind {α β : Type} {I : Void IO.RealWorld → Prop} {a : α}
    {f : α → MetaM β} (h : Keeps mctx mref cctx cref I (Pure.pure a >>= f)) :
    Keeps mctx mref cctx cref I (f a) := by
  first  -- guess: M4
    | exact h
    | (intro w hw; exact h w hw)
    | (rw [keeps_iff] at h ⊢
       intro w hw
       have h1 := h w hw
       change match (EST.bind ((Pure.pure a : MetaM α) mctx mref cctx cref)
           fun x => f x mctx mref cctx cref) w with
         | .ok b w' => I w' | .error e w' => I w' ∧ OkExc e at h1
       exact h1)

/-- The `else` branch of a first step whose condition is false. -/
theorem keeps_of_bind_ite_neg {α β : Type} {I : Void IO.RealWorld → Prop} {c : Prop}
    [Decidable c] (hc : ¬c) {a b : MetaM α} {f : α → MetaM β}
    (h : Keeps mctx mref cctx cref I ((if c then a else b) >>= f)) :
    Keeps mctx mref cctx cref I (b >>= f) := by
  rw [if_neg hc] at h
  exact h

/-! ## The mixed harness -/

/-- `bindMixedCertifiedInputs`: a domain binder is skipped, a `Bool` / `bits n`
binder is one `bindInputPort`. -/
theorem bindMixedCertifiedInputsA (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    {α : Type} (k : CompilerM α)
    (hk : TripleC mctx mref cctx cref I k (fun _ => I) (fun e w => I w ∧ OkExc e)) :
    ∀ l : List ((Name × MixedGateBinder) × FVarId),
      TripleC mctx mref cctx cref I (bindMixedCertifiedInputs k l)
        (fun _ => I) (fun e w => I w ∧ OkExc e)
  | [] => by unfold bindMixedCertifiedInputs; exact hk
  | ((_, .domain), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindMixedCertifiedInputsA O hA hS k hk rest
  | ((_, .bool), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindInputPortA O hA hS _ _ _ _ (bindMixedCertifiedInputsA O hA hS k hk rest)
  | ((_, .bits _), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindInputPortA O hA hS _ _ _ _ (bindMixedCertifiedInputsA O hA hS k hk rest)

/-- **`synthesizeMixedCertified` from the translator only.** Fresh fvars
(`FramedA.freshFVar`), the distinctness branch, the translation cache
allocated with provenance (`tripleA_mkExprCache`, `MkRefd` threaded to the
cache update in `emitLeavesA`), the binder walk, the one leaf, the run, and
`finishSynth`. -/
theorem mixed_keepsA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsC mctx mref cctx cref I (translate e hint top named)) :
    Keeps mctx mref cctx cref I
      (synthesizeMixedCertified translate (profLogIO b) declName bs body) := by
  rw [keeps_iff]
  unfold synthesizeMixedCertified
  refine Triple.bind
    (Triple.mapM _ (fun _ => keeps_iff.mp (keepsA_framed O hA hS FramedA.freshFVar)) _) ?_
  intro ids
  split  -- guess: M1
  · dsimp only
    refine Triple.bindQ (φ := MkRefd _) (tripleA_mkExprCache O hA hS _) ?_
    intro cacheRef hr
    refine Triple.bind
      (bindMixedCertifiedInputsA O hA hS _
        (emitLeavesA O hA hS translate b cacheRef hr htr _ _ _) _ _ _) ?_
    rintro ⟨_, fs⟩
    exact finishSynthA declName fs
  · exact Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩

/-! ## The machine synthesis -/

/-- The synthesis-ref read under a stable invariant that fixes the ref's
value (`hsv`): the value read is `some synthesizeChild` (law: `O.frame` at
`FramedA.synthGet`; the value from the definition of the lifted read). -/
theorem tripleA_synthGet (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (hsv : ∀ w, I w → sv w = some synthesizeChild) :
    Triple mctx mref cctx cref I (sparkleChildSynth.get : MetaM _)
      (fun s w => I w ∧ s = some synthesizeChild) (fun e w => I w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsA_framed O hA hS FramedA.synthGet) w hw
  cases hm : (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w with  -- guess: M2
  | ok a w1 =>
    rw [hm] at hK
    exact ⟨hK, (runsTo_get_readOf _ hm).trans (hsv w hw)⟩
  | error e w1 => rw [hm] at hK; exact hK

/-- **The one-output closing**: the synthesis-ref read, one `synthesizeChild`
per call entry (premise `hchild`), a pure closing. -/
theorem closeInstsM_keepsA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (shape : MachineShape) (t m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    Keeps mctx mref cctx cref I (closeInstsM shape t m design) := by
  rw [keeps_iff]
  unfold closeInstsM
  refine Triple.bindQ (tripleA_synthGet O hA hS hsv) ?_
  intro s hs
  subst hs
  dsimp only  -- guess: M3
  refine Triple.bind (Triple.mapM _ (fun x => ?_) _) ?_
  · obtain ⟨c, _, _⟩ := x
    exact keeps_iff.mp (hchild c)
  · intro _
    exact Triple.pure fun _ hw => hw

/-- **The general closing**: a memory-origin entry's child is built (pure),
any other is one `synthesizeChild` (premise `hchild`). -/
theorem closeInstsGM_keepsA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (shape : MachineShape) (t m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    Keeps mctx mref cctx cref I (closeInstsGM shape t m design) := by
  rw [keeps_iff]
  unfold closeInstsGM
  refine Triple.bindQ (tripleA_synthGet O hA hS hsv) ?_
  intro s hs
  subst hs
  dsimp only  -- guess: M3
  refine Triple.bind (Triple.mapM _ (fun x => ?_) _) ?_
  · obtain ⟨c, o⟩ := x
    dsimp only
    cases Sparkle.Compiler.MachInstOrigin.InstOrigin.child? o with
    | some md => exact Triple.pure fun _ hw => hw
    | none => exact keeps_iff.mp (hchild c)
  · intro _
    exact Triple.pure fun _ hw => hw

/-- **`synthesizeMachineCertified` under the admissible boundary**: the mixed
harness (`mixed_keepsA`, translator `htr`), the pure `closeLets` /
`closeMachine`, and the closing (child entry `hchild`). -/
theorem machineCert_keepsA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (htr : ∀ e hint top named, KeepsC mctx mref cctx cref I (translate e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (hsv : ∀ w, I w → sv w = some synthesizeChild) (shape : MachineShape) :
    Keeps mctx mref cctx cref I
      (synthesizeMachineCertified translate (profLogIO b) declName shape) := by
  rw [keeps_iff]
  unfold synthesizeMachineCertified
  refine Triple.bind
    (keeps_iff.mp (mixed_keepsA O hA hS translate b declName shape.binders shape.body htr)) ?_
  rintro ⟨t, d⟩
  dsimp only
  split
  · split
    · exact Triple.pure fun _ hw => hw
    · split
      · exact keeps_iff.mp (closeInstsM_keepsA O hA hS hsv hchild _ _ _ _)
      · exact keeps_iff.mp (closeInstsGM_keepsA O hA hS hsv hchild _ _ _ _)
  · exact Triple.pure fun _ hw => hw

/-! ## The two branches of `synthesizeFromConst` -/

/-- **The mixed branch of the body, from the translator only.** -/
theorem fromConst_mixed_keepsA (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool) {bs : List (Name × MixedGateBinder)} {body : Lean.Expr}
    (hc : certifiedShape? false [] constInfo = none)
    (hm : mixedCertifiedShape? false [] constInfo isInst = some (bs, body))
    (htr : ∀ e hint top named, KeepsC mctx mref cctx cref I (translate e hint top named)) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst) := by
  have hd1 : (if true = true then certifiedShape? false [] constInfo else none) = none := by
    first
      | exact (if_pos rfl).trans hc
      | (rw [if_pos rfl]; exact hc)
      | simpa using hc
  have hd2 : (if true = true then mixedCertifiedShape? false [] constInfo isInst else none) =
      some (bs, body) := by
    first
      | exact (if_pos rfl).trans hm
      | (rw [if_pos rfl]; exact hm)
      | simpa using hm
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  rw [hd1, hd2]
  first  -- (as PathA P5, P6)
    | refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_
    | (dsimp only; refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_)
  intro _
  refine Keeps.bind (mixed_keepsA O hA hS translate b declName bs body htr) ?_
  intro result
  refine Keeps.bind (keepsA_framed O hA hS (FramedA.sideModify _ .subModule)) ?_
  intro _
  exact Keeps.pure _

/-- **Both gates miss: the machine branch, and the fall-through to the
legacy tail.** The machine branch from the translator `htr`, the child entry
`hchild` and `hsv`; the fall-through (shape `none` at the environment read, or
the machine synthesis `none`) from `hlegacy`: the entry with the certified
front end OFF, which runs the same tail. -/
theorem fromConst_machine_keepsA (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool)
    (hc : certifiedShape? false [] constInfo = none)
    (hm : mixedCertifiedShape? false [] constInfo isInst = none)
    (htr : ∀ e hint top named, KeepsC mctx mref cctx cref I (translate e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hlegacy : Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst) := by
  have hd1 : (if true = true then certifiedShape? false [] constInfo else none) = none := by
    first
      | exact (if_pos rfl).trans hc
      | (rw [if_pos rfl]; exact hc)
      | simpa using hc
  have hd2 : (if true = true then mixedCertifiedShape? false [] constInfo isInst else none) =
      none := by
    first
      | exact (if_pos rfl).trans hm
      | (rw [if_pos rfl]; exact hm)
      | simpa using hm
  have h := hlegacy
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  first | delta synthesizeFromConst at h | unfold synthesizeFromConst at h
  rw [hd1, hd2]
  -- (integrator, after fa1: the do-notation pushes the continuation into the branches of the
  -- `if` of the shape read, so the binds are aligned only after reducing the `if`s)
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true,
    List.isEmpty_nil] at h ⊢
  refine Keeps.bind (keepsA_framed O hA hS FramedA.env) (fun env => ?_)
  generalize machineShape? false [] constInfo (structEnv env) = m
  cases m with
  | none =>
    first
      | exact h
      | exact keeps_pure_bind_of h
  | some shape =>
    refine keeps_pure_bind_of ?_
    refine Keeps.bind (machineCert_keepsA O hA hS translate b declName htr hchild hsv shape) ?_
    intro r
    cases r with
    | some result =>
      refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_
      intro _
      refine Keeps.bind (keepsA_framed O hA hS (FramedA.sideModify _ .subModule)) ?_
      intro _
      exact Keeps.pure _
    | none => exact h

/-! ## The three front ends together -/

/-- **The three front-end branches of the body**, for any stable invariant
that fixes the synthesis ref: the certified branch (PathA) and the mixed
branch from the translator `htr`; the machine branch from `htr` and the child
entry `hchild`; the legacy tail — reached only when both gates miss — is the
ONLY uncovered branch (premise `hlegacy`, asked only of such constants). -/
theorem fromConst_frontends_keepsA (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool)
    (htr : ∀ e hint top named, KeepsC mctx mref cctx cref I (translate e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c))
    (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hlegacy : certifiedShape? false [] constInfo = none →
      mixedCertifiedShape? false [] constInfo isInst = none →
      Keeps mctx mref cctx cref I
        (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst) := by
  cases hc : certifiedShape? false [] constInfo with
  | some p =>
    obtain ⟨bs, body⟩ := p
    exact fromConst_certified_keepsA O hA hS translate b declName constInfo isInst hc htr
  | none =>
    cases hm : mixedCertifiedShape? false [] constInfo isInst with
    | some p =>
      obtain ⟨bs, body⟩ := p
      exact fromConst_mixed_keepsA O hA hS translate b declName constInfo isInst hc hm htr
    | none =>
      exact fromConst_machine_keepsA O hA hS translate b declName constInfo isInst hc hm htr
        hchild hsv (hlegacy hc hm)

/-- **`core_tripleA`'s `hbody` for one constant, from the front ends**: at
`JQ O.quiet 1` with the entry's translator; premises the translator, the child
entry, and the legacy tail (only for constants on which both gates miss). -/
theorem fromConst_hbody_frontends (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) {tenv : Lean.Environment} (b : Bool)
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool)
    (htr : ∀ e hint top named,
      KeepsC mctx mref cctx cref (JQ O.quiet 1) (translateExprToWire tenv e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref (JQ O.quiet 1) (synthesizeChild c))
    (hlegacy : certifiedShape? false [] ci = none →
      mixedCertifiedShape? false [] ci isInst = none →
      Keeps mctx mref cctx cref (JQ O.quiet 1)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false false ci isInst)) :
    Keeps mctx mref cctx cref (JQ O.quiet 1)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst) :=
  fromConst_frontends_keepsA O hA (stableA_JQ _ 1) _ b declName ci isInst htr hchild
    (fun _ h => h.2.1) hlegacy  -- guess: M7

/-- **The core entry from the front ends**: `core_tripleA` with `hbody`
discharged by `fromConst_hbody_frontends`. Remaining premises: the translator
(every environment), the child entry at depth 1, and the legacy tail for
constants on which both gates miss. -/
theorem core_tripleA_frontends (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name)
    (htr : ∀ (tenv : Lean.Environment) e hint top named,
      KeepsC mctx mref cctx cref (JQ O.quiet 1) (translateExprToWire tenv e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref (JQ O.quiet 1) (synthesizeChild c))
    (hlegacy : ∀ (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo)
      (isInst : Lean.Expr → Bool),
      certifiedShape? false [] ci = none → mixedCertifiedShape? false [] ci isInst = none →
      Keeps mctx mref cctx cref (JQ O.quiet 1)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false false ci isInst)) :
    Triple mctx mref cctx cref (OutQ O.quiet) (synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e) :=
  core_tripleA O hA declName fun {tenv} b ci isInst =>
    fromConst_hbody_frontends O hA declName (tenv := tenv) b ci isInst (htr tenv) hchild
      (hlegacy tenv b ci isInst)

end Tools.ShippingChildFrontA
