import Tests.Gen5.EnvFrame3Check
import Tools.ShippingGen5EnvCache
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built: clean issue-linked build env13v-9b886655 exit 0 (759 jobs, dirty=false), approved at 9b886655. Result: TYPE 5, MUTANT 8 (signature/defeq rejection, not semantic counterexamples), CLOSURE 4 roots, AXIOMS 4 standard.
-- Counting rule: TYPE = Expected comparisons (4 theorems) + 1 constructor type of `RealChildN.run`; MUTANT = well-typed single changes rejected by the same comparator;
-- CLOSURE = roots; negatives (forbidden, flagged) are counted direct + helper; unknown = throwing controls, kept apart; self-root = forbidden constant as root; clean = not-flagged controls.

/-! # DG-ENV unit U5 checks (Tools/ShippingGen5EnvCache.lean)

1. TYPE: Expected propositions written from freeze §2, through ONE comparator (`withReducible` around the Gen3 telescope comparison).
2. MUTANT (8): well-typed single changes (M8 binds `L'` explicitly) rejected by that comparator. Signature/defeq rejections, NOT semantic counterexamples.
3. CLOSURE: quiet-only mode for N1-N4 (guarded constants reached exactly `Laws.O`, `RefLawsAOps.quiet`); walker `reachQ` of `Tests.Gen5.EnvFrame3Check`.
4. AXIOMS: standard only. -/

namespace Tests.Gen5.EnvCacheCheck
open Lean Meta
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (cv sv)
open Tools.ShippingChildCacheA (RealChildA CacheInvA)
open Sparkle.Compiler.Elab (synthesizeChild synthesizeCombinational)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvQ (QuietStrength)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvCache
open Tests.Gen3.ExpectedType
open Tests.Gen5.EnvFrameCheck (mkForbid badProj guarded)
open Tests.Gen5.EnvFrame3Check (reachQ QReach allowedQuiet opsN)

/-! ## 1. Expected types, written from freeze §2 -/
def ExpN1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {c : Name} {r : Res}, ∀ (h : RealChildN L env₀ c r), RealChildA L.O c r
def ExpN2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment}, ∀ (hq : QuietStrength L L' env₀) {c : Name} {r : Res} (h : RealChildN L env₀ c r),
    RealChildA L'.O c r
def ExpN3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment}, ∀ (hq : QuietStrength L L' env₀) {m : Std.HashMap Name Res}
    (h : ∀ c r, m.get? c = some r → RealChildN L env₀ c r), CacheInvA L'.O m
def ExpN4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    ∀ (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀) (hn : mctx.canUnfold? = none)
      (hN : ∀ c r, (cv w₀).get? c = some r → RealChildN L (envAt cref w₀) c r), Start L' mctx cctx w₀
def ExpRun : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {c : Name} {r : Res} (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld)
    (hn : mctx.canUnfold? = none) (rd : ReadsAt env₀ cref w)
    (cache : ∀ c' r', (cv w).get? c' = some r' → RealChildN L env₀ c' r') (synth : sv w = some synthesizeChild)
    (quiet : L.O.quiet w) (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w'),
    RealChildN L env₀ c r

/-! ## Mutants (well-typed single changes) -/
def MutM1 : Prop := -- N2 without `hq`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} {c : Name} {r : Res}, RealChildN L env₀ c r → RealChildA L'.O c r
def MutM2 : Prop := -- N4 without `hn`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    QuietStrength L L' (envAt cref w₀) → Start L mctx cctx w₀ →
    (∀ c r, (cv w₀).get? c = some r → RealChildN L (envAt cref w₀) c r) → Start L' mctx cctx w₀
def MutM3 : Prop := -- N4 without `hN`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    QuietStrength L L' (envAt cref w₀) → Start L mctx cctx w₀ → mctx.canUnfold? = none → Start L' mctx cctx w₀
def MutM4 : Prop := -- N4 concluding `Start L`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld},
    QuietStrength L L' (envAt cref w₀) → Start L mctx cctx w₀ → mctx.canUnfold? = none →
    (∀ c r, (cv w₀).get? c = some r → RealChildN L (envAt cref w₀) c r) → Start L mctx cctx w₀
def MutM5 : Prop := -- N3 concluding `CacheInvA L.O m`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment}, QuietStrength L L' env₀ → ∀ {m : Std.HashMap Name Res},
    (∀ c r, m.get? c = some r → RealChildN L env₀ c r) → CacheInvA L.O m
def MutM6 : Prop := -- `RealChildN.run` without `hn`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {c : Name} {r : Res} (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld)
    (rd : ReadsAt env₀ cref w)
    (cache : ∀ c' r', (cv w).get? c' = some r' → RealChildN L env₀ c' r') (synth : sv w = some synthesizeChild)
    (quiet : L.O.quiet w) (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w'),
    RealChildN L env₀ c r
def MutM7 : Prop := -- `RealChildN.run` without `rd`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {c : Name} {r : Res} (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld)
    (hn : mctx.canUnfold? = none)
    (cache : ∀ c' r', (cv w).get? c' = some r' → RealChildN L env₀ c' r') (synth : sv w = some synthesizeChild)
    (quiet : L.O.quiet w) (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w'),
    RealChildN L env₀ c r
def MutM8 : Prop := -- N1 concluding `RealChildA L'.O c r`, `L'` explicitly bound (well-typed)
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} {c : Name} {r : Res}, RealChildN L env₀ c r → RealChildA L'.O c r

/-- The one comparator: reducible transparency for every comparison, positive and negative alike. -/
def cmpExp (thm exp : Name) : MetaM Unit := withReducible (checkExpected thm exp)
def cmpMut (thm mt : Name) : MetaM Unit := withReducible (checkMutant thm mt)
/-- The same comparison for the TYPE of the constructor `RealChildN.run` (`checkExpected` takes theorems / definitions only). -/
def cmpCtor (ctor exp : Name) : MetaM Unit := withReducible do
  let a := (← getConstInfo ctor).type
  let e ← stmtOf exp
  cmpTele s!"{ctor}" a e
  logInfo m!"GEN3 TYPE OK {ctor} against {exp}"
def cmpCtorMut (ctor mt : Name) : MetaM Unit := withReducible do
  let a := (← getConstInfo ctor).type
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try cmpTele s!"{ctor} vs mutant {mt}" a e; pure true catch _ => pure false
  if accepted then throwError "GEN3 MUTANT ACCEPTED: {mt} matches {ctor}"
  if (← withoutModifyingState (isDefEq a e)) then throwError "GEN3 MUTANT ACCEPTED (isDefEq): {mt} vs {ctor}"
  logInfo m!"GEN3 MUTANT REJECTED {mt} (against {ctor})"

run_cmd Lean.Elab.Command.liftTermElabM do
  cmpExp ``realChildA_of_N ``ExpN1
  cmpExp ``realChildA_up_of_N ``ExpN2
  cmpExp ``cacheInvA_up_of_N ``ExpN3
  cmpExp ``start_up_of_N ``ExpN4
  cmpCtor ``RealChildN.run ``ExpRun
  logInfo "ENVCACHE TYPE total 5 (4 theorems + the constructor type of RealChildN.run), all through the same withReducible comparison"
  cmpMut ``realChildA_up_of_N ``MutM1
  cmpMut ``start_up_of_N ``MutM2
  cmpMut ``start_up_of_N ``MutM3
  cmpMut ``start_up_of_N ``MutM4
  cmpMut ``cacheInvA_up_of_N ``MutM5
  cmpCtorMut ``RealChildN.run ``MutM6
  cmpCtorMut ``RealChildN.run ``MutM7
  cmpMut ``realChildA_of_N ``MutM8
  logInfo "ENVCACHE MUTANT total 8 (M1-M8) rejected by the same comparator (signature/defeq rejections, not semantic counterexamples)"

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
  -- (A) roots N1-N4: quiet-only, reached guarded constants exactly the allowed two (`Laws.O`, `RefLawsAOps.quiet`).
  let roots := [``realChildA_of_N, ``realChildA_up_of_N, ``cacheInvA_up_of_N, ``start_up_of_N]
  let mut nRoots : Nat := 0
  for c in roots do
    let r ← reachQ forbidQ allowedQuiet c
    if let some p := r.hit then throwError "ENVCACHE AUDIT FAILED {c}: forbidden use via {p}"
    unless r.got.toList.toArray.qsort Name.lt == allowedQuiet.toArray.qsort Name.lt do
      throwError "ENVCACHE AUDIT FAILED {c}: reaches {r.got.toList}, expected exactly {allowedQuiet}"
    nRoots := nRoots + 1
    logInfo m!"ENVCACHE REACH {c}: clean (type and value), reached exactly {allowedQuiet} (visited {r.visited})"
  -- the roots really use the allowed projections: with them forbidden they are flagged
  for c in roots do
    let rf ← reachQ forbid [] c
    unless rf.hit.isSome do throwError "ENVCACHE AUDIT FAILED: {c} not flagged when Laws.O / quiet are forbidden"
  -- (B) negatives: fixtures reaching a law-bearing constant are flagged (FORBIDDEN controls) with the intended constant on the path
  let neg : List (Name × Name) :=
    [(F ++ `dOps, ops ++ `frame), (H ++ `qLawsT, ``Tools.ShippingGen2.Laws.T),
     (F ++ `dTele, ``Tools.ShippingChildInvA.RefLawsATele.telescope), (F ++ `dT1, ``Tools.ShippingGen2.T1Hyp.defines),
     (H ++ `qDiag, ops ++ `diag),
     (F ++ `hOps, ops ++ `frame), (F ++ `hT1, ``Tools.ShippingGen2.T1Hyp.defines)]
  let mut nNeg : Nat := 0
  for (c, t) in neg do
    unless forbidQ.contains t do throwError "ENVCACHE AUDIT FAILED: intended {t} not forbidden"
    let r ← reachQ forbidQ allowedQuiet c
    if r.hit.isNone then throwError "ENVCACHE AUDIT FAILED: misses {c}"
    let rt ← reachQ [t] allowedQuiet c
    unless isLast rt t do throwError "ENVCACHE AUDIT FAILED: {c} does not reach its intended {t}"
    nNeg := nNeg + 1
  -- (C) UNKNOWN controls (throwing), kept apart from the forbidden ones above, including a helper whose TYPE alone is unknown
  let missing := `Tests.Gen5.EnvCacheFixture.noSuchRoot
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
    unless ok do throwError "ENVCACHE AUDIT FAILED: unresolved {nm} under root {c} did not throw"
    nUnres := nUnres + 1
  -- a root of this unit with a hidden constant on its path also throws (unknown fails; never silently clean)
  let hiddenOk ← try
      let _ ← reachQ forbidQ allowedQuiet ``start_up_of_N (some ``Tools.ShippingGen5EnvStart.start_up_of_parts)
      pure false
    catch e =>
      let msg ← e.toMessageData.toString
      pure (msg.startsWith "ENVFRAME3 AUDIT UNRESOLVED NAME Tools.ShippingGen5EnvStart.start_up_of_parts ")
  unless hiddenOk do throwError "ENVCACHE AUDIT FAILED: hiding start_up_of_parts under start_up_of_N did not throw"
  nUnres := nUnres + 1
  -- (D) self-root: a forbidden constant as root is flagged on itself
  let selfRoots : List Name :=
    [``Tools.ShippingGen2.T1Hyp.defines, ``Tools.ShippingGen2.T1HypND.defines, ``Tools.ShippingGen2.Laws.T,
     ops ++ `frame, ops ++ `casesOn, ``Tools.ShippingEnvSnapshot.GetEnvFrame]
  let mut nSelf : Nat := 0
  for t in selfRoots do
    unless forbidQ.contains t do throwError "ENVCACHE AUDIT FAILED: self-root {t} not forbidden"
    let r ← reachQ forbidQ allowedQuiet t
    unless r.hit == some [t] do throwError "ENVCACHE AUDIT FAILED: forbidden root {t} itself not flagged ({toString r.hit})"
    nSelf := nSelf + 1
  -- (E) clean control: the unrelated fixtures of U1 are not flagged
  let mut nClean : Nat := 0
  for c in [F ++ `cUnrelated, F ++ `cBinders, F ++ `cHelper] do
    let r ← reachQ forbidQ allowedQuiet c
    if r.hit.isSome then throwError "ENVCACHE AUDIT FAILED: clean control {c} flagged"
    nClean := nClean + 1
  logInfo m!"ENVCACHE CLOSURE total: {nRoots} roots (N1-N4 quiet-only) / negatives: {nNeg} law-bearing fixtures (5 direct + 2 helper) each flagged with the intended constant + {nUnres} unknown (incl. 1 helper-type-only, 1 hidden constant under a root) + {nSelf} self-root / clean: {nClean}. Scope: type and value constants reachable in the environment; allowed projections are leaves."

/-! ## 3. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``realChildA_of_N, ``realChildA_up_of_N, ``cacheInvA_up_of_N, ``start_up_of_N] do
    checkAxioms n
  logInfo "ENVCACHE AXIOMS total 4 standard (4 theorems)"

end Tests.Gen5.EnvCacheCheck
