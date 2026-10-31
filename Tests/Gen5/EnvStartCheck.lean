import Tests.Gen5.EnvFrame3Check
import Tools.ShippingGen5EnvStart
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built: Pod kjob lake build Tests.Gen5.EnvStartCheck exit 0, 758 jobs, at tree 0d506a98 (Lean commit; clean issue-linked build is run by the coder). Result: TYPE 3, MUTANT 7, CLOSURE 3 roots, AXIOMS 3 standard.
-- Counting rule: TYPE = Expected comparisons (3 theorems, no definitions); MUTANT = single well-typed changes rejected by the same comparator;
-- CLOSURE = roots; negatives are counted direct + helper; unresolved = throwing controls; self-root = forbidden constant as root; clean = not-flagged controls.

/-! # DG-ENV unit U4 checks (Tools/ShippingGen5EnvStart.lean)

1. TYPE: Expected propositions written from freeze §3, through ONE comparator (`withReducible` around `checkExpected`).
2. MUTANT (7): well-typed single changes M1-M7 rejected by that comparator. Signature/defeq rejections, NOT semantic counterexamples.
3. CLOSURE: QUIET-ONLY mode for S1, S2 (guarded constants reached must be exactly `Laws.O`, `RefLawsAOps.quiet`), and mode with no allowed constant for S3.
   Walker `reachQ` is the one of `Tests.Gen5.EnvFrame3Check` (imported, not copied). Scope: the walk covers the constants reachable through types and values
   from each root; it stops at the allowed projections (leaf) and does not look inside `initialize` / opaque bodies beyond what the environment exposes.
4. AXIOMS: standard only. -/

namespace Tests.Gen5.EnvStartCheck
open Lean Meta
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (cv)
open Tools.ShippingChildCacheA (CacheInvA)
open Tools.ShippingGen5EnvQ (QuietStrength)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvStart
open Tests.Gen3.ExpectedType
open Tests.Gen5.EnvFrameCheck (mkForbid badProj guarded)
open Tests.Gen5.EnvFrame3Check (reachQ QReach allowedQuiet opsN)

/-! ## 1. Expected types, written from freeze §3 -/
def ExpS1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    ∀ (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀) (hA : AdmCtx L'.O.quiet mctx cctx)
      (hC : CacheInvA L'.O (cv w₀)), Start L' mctx cctx w₀
def ExpS2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    ∀ (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀) (hE : cv w₀ = {})
      (hn : mctx.canUnfold? = none), Start L' mctx cctx w₀
def ExpS3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {Fresh : (σ : Type) → IO.Ref σ → Prop} (O : Tools.ShippingChildInvA.RefLawsAOps Fresh mref cref)
    {w₀ : Void IO.RealWorld}, ∀ (hE : cv w₀ = {}), CacheInvA O (cv w₀)

/-! ## Mutants (well-typed single changes) -/
def MutM1 : Prop := -- S2 without `hn`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    QuietStrength L L' (envAt cref w₀) → Start L mctx cctx w₀ → cv w₀ = {} → Start L' mctx cctx w₀
def MutM2 : Prop := -- S2 without `hE`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    QuietStrength L L' (envAt cref w₀) → Start L mctx cctx w₀ → mctx.canUnfold? = none → Start L' mctx cctx w₀
def MutM3 : Prop := -- S2 concluding `Start L`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    QuietStrength L L' (envAt cref w₀) → Start L mctx cctx w₀ → cv w₀ = {} → mctx.canUnfold? = none →
    Start L mctx cctx w₀
def MutM4 : Prop := -- S1 without `hq`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    Start L mctx cctx w₀ → AdmCtx L'.O.quiet mctx cctx → CacheInvA L'.O (cv w₀) → Start L' mctx cctx w₀
def MutM5 : Prop := -- S1 without `hC`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    QuietStrength L L' (envAt cref w₀) → Start L mctx cctx w₀ → AdmCtx L'.O.quiet mctx cctx → Start L' mctx cctx w₀
def MutM6 : Prop := -- S3 with a trivially true hypothesis `cv w₀ = cv w₀`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {Fresh : (σ : Type) → IO.Ref σ → Prop} (O : Tools.ShippingChildInvA.RefLawsAOps Fresh mref cref)
    {w₀ : Void IO.RealWorld}, cv w₀ = cv w₀ → CacheInvA O (cv w₀)
def MutM7 : Prop := -- S2 with `(cv w₀).isEmpty = true`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    QuietStrength L L' (envAt cref w₀) → Start L mctx cctx w₀ → (cv w₀).isEmpty = true → mctx.canUnfold? = none →
    Start L' mctx cctx w₀

/-- The one comparator: reducible transparency for every comparison, positive and negative alike. -/
def cmpExp (thm exp : Name) : MetaM Unit := withReducible (checkExpected thm exp)
def cmpMut (thm mt : Name) : MetaM Unit := withReducible (checkMutant thm mt)

run_cmd Lean.Elab.Command.liftTermElabM do
  cmpExp ``start_up_of_parts ``ExpS1
  cmpExp ``start_up_empty ``ExpS2
  cmpExp ``cacheInvA_of_empty ``ExpS3
  logInfo "ENVSTART TYPE total 3 (3 theorems, no definitions), all through the same withReducible checkExpected"
  cmpMut ``start_up_empty ``MutM1
  cmpMut ``start_up_empty ``MutM2
  cmpMut ``start_up_empty ``MutM3
  cmpMut ``start_up_of_parts ``MutM4
  cmpMut ``start_up_of_parts ``MutM5
  cmpMut ``cacheInvA_of_empty ``MutM6
  cmpMut ``start_up_empty ``MutM7
  logInfo "ENVSTART MUTANT total 7 (M1-M7) rejected by the same comparator (signature/defeq rejections, not semantic counterexamples)"

/-! ## 2. Closure audit -/
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let forbid ← mkForbid
  let ops := opsN
  let F := `Tests.Gen5.EnvFrameFixture
  let G := `Tests.Gen5.EnvFrame2Fixture
  let H := `Tests.Gen5.EnvFrame3Fixture
  let forbidQ := forbid.filter (!allowedQuiet.contains ·)
  let isLast (r : QReach) (t : Name) : Bool := r.hit.map (·.getLast? == some t) == some true
  -- (A) roots. S1, S2: quiet-only, reached guarded constants exactly the allowed two. S3: no guarded constant at all.
  let mut nRoots : Nat := 0
  for c in [``start_up_of_parts, ``start_up_empty] do
    let r ← reachQ forbidQ allowedQuiet c
    if let some p := r.hit then throwError "ENVSTART AUDIT FAILED {c}: forbidden use via {p}"
    unless r.got.toList.toArray.qsort Name.lt == allowedQuiet.toArray.qsort Name.lt do
      throwError "ENVSTART AUDIT FAILED {c}: reaches {r.got.toList}, expected exactly {allowedQuiet}"
    nRoots := nRoots + 1
    logInfo m!"ENVSTART REACH {c}: clean (type and value), reached exactly {allowedQuiet} (visited {r.visited})"
  let r3 ← reachQ forbid [] ``cacheInvA_of_empty
  if let some p := r3.hit then throwError "ENVSTART AUDIT FAILED cacheInvA_of_empty: forbidden use via {p}"
  unless r3.got.isEmpty do throwError "ENVSTART AUDIT FAILED cacheInvA_of_empty: reaches {r3.got.toList}"
  nRoots := nRoots + 1
  logInfo m!"ENVSTART REACH cacheInvA_of_empty: clean (type and value), no allowed constant needed (visited {r3.visited})"
  -- S1, S2 really use the allowed projections: with them forbidden the roots are flagged
  for c in [``start_up_of_parts, ``start_up_empty] do
    let rf ← reachQ forbid [] c
    unless rf.hit.isSome do throwError "ENVSTART AUDIT FAILED: {c} not flagged when Laws.O / quiet are forbidden"
  -- (B) negatives: fixtures reaching a law-bearing constant are flagged in the S1/S2 mode with the intended constant on the path
  let neg : List (Name × Name) :=
    [(F ++ `dOps, ops ++ `frame), (H ++ `qLawsT, ``Tools.ShippingGen2.Laws.T),
     (F ++ `dTele, ``Tools.ShippingChildInvA.RefLawsATele.telescope), (F ++ `dT1, ``Tools.ShippingGen2.T1Hyp.defines),
     (H ++ `qDiag, ops ++ `diag),
     (F ++ `hOps, ops ++ `frame), (F ++ `hT1, ``Tools.ShippingGen2.T1Hyp.defines)]
  let mut nNeg : Nat := 0
  for (c, t) in neg do
    unless forbidQ.contains t do throwError "ENVSTART AUDIT FAILED: intended {t} not forbidden"
    let r ← reachQ forbidQ allowedQuiet c
    if r.hit.isNone then throwError "ENVSTART AUDIT FAILED: misses {c}"
    let rt ← reachQ [t] allowedQuiet c
    unless isLast rt t do throwError "ENVSTART AUDIT FAILED: {c} does not reach its intended {t}"
    let r3' ← reachQ forbid [] c
    if r3'.hit.isNone then throwError "ENVSTART AUDIT FAILED: S3 mode misses {c}"
    nNeg := nNeg + 1
  -- (C) unresolved (throwing) controls, including a helper whose TYPE alone is unknown
  let missing := `Tests.Gen5.EnvStartFixture.noSuchRoot
  let unres : List (Name × Option Name × Name × List Name) :=
    [(missing, none, missing, []), (F ++ `hv, some (F ++ `helperClean), F ++ `helperClean, []),
     (F ++ `ht, some (F ++ `helperTy), F ++ `helperTy, []),
     (F ++ `ht2, some (F ++ `helperTy), F ++ `helperTy, [F ++ `ht2, F ++ `helperHt])]
  let mut nUnres : Nat := 0
  for (c, hid, nm, via) in unres do
    let ok ← try
        let _ ← reachQ forbidQ allowedQuiet c hid
        pure false
      catch e =>
        let msg ← e.toMessageData.toString
        let has (n : Name) := (msg.splitOn (toString n)).length > 1
        pure (msg.startsWith s!"ENVFRAME3 AUDIT UNRESOLVED NAME {nm} " && via.all has)
    unless ok do throwError "ENVSTART AUDIT FAILED: unresolved {nm} under root {c} did not throw"
    nUnres := nUnres + 1
  -- a root of this unit with a hidden constant on its path also throws (unknown fails; never silently clean)
  let hiddenOk ← try
      let _ ← reachQ forbidQ allowedQuiet ``start_up_empty (some ``Tools.ShippingChildCacheA.cacheInvA_empty)
      pure false
    catch e =>
      let msg ← e.toMessageData.toString
      pure (msg.startsWith "ENVFRAME3 AUDIT UNRESOLVED NAME Tools.ShippingChildCacheA.cacheInvA_empty ")
  unless hiddenOk do throwError "ENVSTART AUDIT FAILED: hiding cacheInvA_empty under start_up_empty did not throw"
  nUnres := nUnres + 1
  -- (D) self-root: a forbidden constant as root is flagged on itself
  let selfRoots : List Name :=
    [``Tools.ShippingGen2.T1Hyp.defines, ``Tools.ShippingGen2.T1HypND.defines, ``Tools.ShippingGen2.Laws.T,
     ops ++ `frame, ops ++ `casesOn, ``Tools.ShippingEnvSnapshot.GetEnvFrame]
  let mut nSelf : Nat := 0
  for t in selfRoots do
    unless forbidQ.contains t do throwError "ENVSTART AUDIT FAILED: self-root {t} not forbidden"
    let r ← reachQ forbidQ allowedQuiet t
    unless r.hit == some [t] do throwError "ENVSTART AUDIT FAILED: forbidden root {t} itself not flagged ({toString r.hit})"
    nSelf := nSelf + 1
  -- (E) clean control: the unrelated fixtures of U1 are not flagged
  let mut nClean : Nat := 0
  for c in [F ++ `cUnrelated, F ++ `cBinders, F ++ `cHelper] do
    let r ← reachQ forbidQ allowedQuiet c
    if r.hit.isSome then throwError "ENVSTART AUDIT FAILED: clean control {c} flagged"
    nClean := nClean + 1
  logInfo m!"ENVSTART CLOSURE total: {nRoots} roots (S1, S2 quiet-only; S3 no allowed constant) / negatives: {nNeg} law-bearing fixtures (5 direct + 2 helper) each flagged with the intended constant in both modes + {nUnres} unresolved (incl. 1 helper-type-only, 1 hidden constant under a root) + {nSelf} self-root / clean: {nClean}. Scope: type and value constants reachable in the environment; allowed projections are leaves."

/-! ## 3. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``start_up_of_parts, ``start_up_empty, ``cacheInvA_of_empty] do
    checkAxioms n
  logInfo "ENVSTART AXIOMS total 3 standard (3 theorems)"

end Tests.Gen5.EnvStartCheck
