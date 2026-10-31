import Tests.Gen5.EnvFrame3Check
import Tools.ShippingGen5EnvCacheC
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built: clean issue-linked build env17v-3fa51023 exit 0 (761 jobs, dirty=false), approved at 3fa51023. Counting: TYPE = 1 definition-body comparison (O0) + 4 Expected comparisons (O1-O4); MUTANT = 9 well-typed single changes rejected by the same comparator (signature/defeq, not semantic counterexamples);
-- CLOSURE (per-root expected set, observed: O0/O1/O2 reach no guarded constant, O3/O4 reach exactly Laws.O + RefLawsAOps.quiet; the freeze said "at most" those two) = roots; negatives (forbidden, flagged) direct + helper; unknown kept apart; self-root; clean.

/-! # DG-ENV unit U7 checks (Tools/ShippingGen5EnvCacheC.lean)
Expected propositions written from freeze scripts/gen5/DG_ENV_T2_U7_FREEZE.md §2 (not copied from the proofs), one comparator (`withReducible`). -/

namespace Tests.Gen5.EnvCacheCCheck
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildBndCore (cv sv)
open Sparkle.Compiler.Elab (synthesizeChild synthesizeCombinational)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvQ (QuietStrength)
open Tools.ShippingGen2 (Laws)
open Tools.ShippingGen5EnvCache (RealChildN)
open Tools.ShippingGen5EnvCacheC
open Tests.Gen3.ExpectedType
open Tests.Gen5.EnvFrameCheck (mkForbid badProj guarded)
open Tests.Gen5.EnvFrame3Check (reachQ QReach allowedQuiet opsN)

/-! ## 1. Expected types -/
def ExpO0 : ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State},
    Laws mref cref → Environment → Std.HashMap Name Res → Prop :=
  fun {mref} {cref} L env₀ m => ∀ c r, m.get? c = some r → RealChildN L env₀ c r
def ExpO1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref)
    (env₀ : Environment), CacheInvN L env₀ {}
def ExpO2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {m : Std.HashMap Name Res} {c : Name} {r : Res},
    ∀ (h : CacheInvN L env₀ m) (hr : RealChildN L env₀ c r), CacheInvN L env₀ (m.insert c r)
def ExpO3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld},
    ∀ (hn : mctx.canUnfold? = none) (rd : ReadsAt env₀ cref w) (hw : CacheInvN L env₀ (cv w))
      (synth : sv w = some synthesizeChild) (quiet : L.O.quiet w)
      (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w'), RealChildN L env₀ c r
def ExpO4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment}, ∀ (hq : QuietStrength L L' env₀) {m : Std.HashMap Name Res} (h : CacheInvN L env₀ m),
    CacheInvN L' env₀ m

/-! ## Mutants (well-typed single changes) -/
def MutM1 : Prop := -- O1 for a bound map instead of `{}`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref)
    (env₀ : Environment) (m : Std.HashMap Name Res), CacheInvN L env₀ m
def MutM2 : Prop := -- O2 without `hr`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {m : Std.HashMap Name Res} {c : Name} {r : Res},
    CacheInvN L env₀ m → CacheInvN L env₀ (m.insert c r)
def MutM3 : Prop := -- O2 without `h`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {m : Std.HashMap Name Res} {c : Name} {r : Res},
    RealChildN L env₀ c r → CacheInvN L env₀ (m.insert c r)
def MutM4 : Prop := -- O3 without `rd`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld},
    mctx.canUnfold? = none → CacheInvN L env₀ (cv w) → sv w = some synthesizeChild →
    L.O.quiet w → RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' → RealChildN L env₀ c r
def MutM5 : Prop := -- O3 without `hn`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld},
    ReadsAt env₀ cref w → CacheInvN L env₀ (cv w) → sv w = some synthesizeChild →
    L.O.quiet w → RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' → RealChildN L env₀ c r
def MutM6 : Prop := -- O3 without `quiet`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld},
    mctx.canUnfold? = none → ReadsAt env₀ cref w → CacheInvN L env₀ (cv w) → sv w = some synthesizeChild →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' → RealChildN L env₀ c r
def MutM7 : Prop := -- O3 with `hw` at a second bound environment
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ env₁ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld},
    mctx.canUnfold? = none → ReadsAt env₀ cref w → CacheInvN L env₁ (cv w) → sv w = some synthesizeChild →
    L.O.quiet w → RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' → RealChildN L env₀ c r
def MutM8 : Prop := -- O4 without `hq`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} {m : Std.HashMap Name Res}, CacheInvN L env₀ m → CacheInvN L' env₀ m
def MutM9 : Prop := -- O4 concluding at a second bound environment
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ env₁ : Environment}, QuietStrength L L' env₀ → ∀ {m : Std.HashMap Name Res}, CacheInvN L env₀ m →
    CacheInvN L' env₁ m

/-- The one comparator: reducible transparency for every comparison, positive and negative alike. -/
def cmpExp (thm exp : Name) : MetaM Unit := withReducible (checkExpected thm exp)
def cmpMut (thm mt : Name) : MetaM Unit := withReducible (checkMutant thm mt)

run_cmd Lean.Elab.Command.liftTermElabM do
  cmpExp ``CacheInvN ``ExpO0
  cmpExp ``cacheInvN_empty ``ExpO1
  cmpExp ``cacheInvN_insert ``ExpO2
  cmpExp ``realChildN_of_run ``ExpO3
  cmpExp ``cacheInvN_up ``ExpO4
  logInfo "ENVCACHEC TYPE total 5 (O0 definition body + O1-O4), all through the same withReducible comparison"
  cmpMut ``cacheInvN_empty ``MutM1
  cmpMut ``cacheInvN_insert ``MutM2
  cmpMut ``cacheInvN_insert ``MutM3
  cmpMut ``realChildN_of_run ``MutM4
  cmpMut ``realChildN_of_run ``MutM5
  cmpMut ``realChildN_of_run ``MutM6
  cmpMut ``realChildN_of_run ``MutM7
  cmpMut ``cacheInvN_up ``MutM8
  cmpMut ``cacheInvN_up ``MutM9
  logInfo "ENVCACHEC MUTANT total 9 (M1-M9, all well-typed single changes) rejected by the same comparator (signature/defeq rejections, not semantic counterexamples)"

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
  -- (A) roots O0-O4: quiet-only, reached guarded constants exactly the allowed two (`Laws.O`, `RefLawsAOps.quiet`).
  let roots : List (Name × List Name) := [(``cacheInvN_empty, []), (``cacheInvN_insert, []), (``realChildN_of_run, allowedQuiet), (``cacheInvN_up, allowedQuiet)]
  let mut nRoots : Nat := 0
  -- O0 is a definition whose type and value mention only `RealChildN` (an inductive; its constructors are not reached from the type): it must be clean, reaching no guarded constant.
  let r0 ← reachQ forbidQ allowedQuiet ``CacheInvN
  if let some p := r0.hit then throwError "ENVCACHEC AUDIT FAILED CacheInvN: forbidden use via {p}"
  nRoots := nRoots + 1
  logInfo m!"ENVCACHEC REACH {``CacheInvN}: clean (type and value), reached {r0.got.toList} (visited {r0.visited})"
  for (c, ex) in roots do
    let r ← reachQ forbidQ allowedQuiet c
    if let some p := r.hit then throwError "ENVCACHEC AUDIT FAILED {c}: forbidden use via {p}"
    unless r.got.toList.toArray.qsort Name.lt == ex.toArray.qsort Name.lt do
      throwError "ENVCACHEC AUDIT FAILED {c}: reaches {r.got.toList}, expected exactly {ex}"
    nRoots := nRoots + 1
    logInfo m!"ENVCACHEC REACH {c}: clean (type and value), reached exactly {ex} (visited {r.visited})"
  -- the roots really use the allowed projections: with them forbidden they are flagged
  for (c, ex) in roots do
    if ex.isEmpty then continue
    let rf ← reachQ forbid [] c
    unless rf.hit.isSome do throwError "ENVCACHEC AUDIT FAILED: {c} not flagged when Laws.O / quiet are forbidden"
  -- (B) negatives: fixtures reaching a law-bearing constant are flagged (FORBIDDEN controls) with the intended constant on the path
  let neg : List (Name × Name) :=
    [(F ++ `dOps, ops ++ `frame), (H ++ `qLawsT, ``Tools.ShippingGen2.Laws.T),
     (F ++ `dTele, ``Tools.ShippingChildInvA.RefLawsATele.telescope), (F ++ `dT1, ``Tools.ShippingGen2.T1Hyp.defines),
     (H ++ `qDiag, ops ++ `diag),
     (F ++ `hOps, ops ++ `frame), (F ++ `hT1, ``Tools.ShippingGen2.T1Hyp.defines)]
  let mut nNeg : Nat := 0
  for (c, t) in neg do
    unless forbidQ.contains t do throwError "ENVCACHEC AUDIT FAILED: intended {t} not forbidden"
    let r ← reachQ forbidQ allowedQuiet c
    if r.hit.isNone then throwError "ENVCACHEC AUDIT FAILED: misses {c}"
    let rt ← reachQ [t] allowedQuiet c
    unless isLast rt t do throwError "ENVCACHEC AUDIT FAILED: {c} does not reach its intended {t}"
    nNeg := nNeg + 1
  -- (C) UNKNOWN controls (throwing), kept apart from the forbidden ones above, including a helper whose TYPE alone is unknown
  let missing := `Tests.Gen5.EnvCacheCFixture.noSuchRoot
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
    unless ok do throwError "ENVCACHEC AUDIT FAILED: unresolved {nm} under root {c} did not throw"
    nUnres := nUnres + 1
  -- a root of this unit with a hidden constant on its path also throws (unknown fails; never silently clean)
  let hiddenOk ← try
      let _ ← reachQ forbidQ allowedQuiet ``cacheInvN_up (some ``Tools.ShippingGen5EnvQ.QuietStrength)
      pure false
    catch e =>
      let msg ← e.toMessageData.toString
      pure (msg.startsWith "ENVFRAME3 AUDIT UNRESOLVED NAME Tools.ShippingGen5EnvQ.QuietStrength ")
  unless hiddenOk do throwError "ENVCACHEC AUDIT FAILED: hiding QuietStrength under cacheInvN_up did not throw"
  nUnres := nUnres + 1
  -- (D) self-root: a forbidden constant as root is flagged on itself
  let selfRoots : List Name :=
    [``Tools.ShippingGen2.T1Hyp.defines, ``Tools.ShippingGen2.T1HypND.defines, ``Tools.ShippingGen2.Laws.T,
     ops ++ `frame, ops ++ `casesOn, ``Tools.ShippingEnvSnapshot.GetEnvFrame]
  let mut nSelf : Nat := 0
  for t in selfRoots do
    unless forbidQ.contains t do throwError "ENVCACHEC AUDIT FAILED: self-root {t} not forbidden"
    let r ← reachQ forbidQ allowedQuiet t
    unless r.hit == some [t] do throwError "ENVCACHEC AUDIT FAILED: forbidden root {t} itself not flagged ({toString r.hit})"
    nSelf := nSelf + 1
  -- (E) clean control: the unrelated fixtures of U1 are not flagged
  let mut nClean : Nat := 0
  for c in [F ++ `cUnrelated, F ++ `cBinders, F ++ `cHelper] do
    let r ← reachQ forbidQ allowedQuiet c
    if r.hit.isSome then throwError "ENVCACHEC AUDIT FAILED: clean control {c} flagged"
    nClean := nClean + 1
  logInfo m!"ENVCACHEC CLOSURE total: {nRoots} roots (O0-O4 quiet-only) / negatives: {nNeg} law-bearing fixtures (5 direct + 2 helper) each flagged with the intended constant + {nUnres} unknown (incl. 1 helper-type-only, 1 hidden constant under a root) + {nSelf} self-root / clean: {nClean}. Scope: type and value constants reachable in the environment; allowed projections are leaves."

/-! ## 3. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``cacheInvN_empty, ``cacheInvN_insert, ``realChildN_of_run, ``cacheInvN_up] do
    checkAxioms n
  checkAxioms ``CacheInvN
  logInfo "ENVCACHEC AXIOMS total 5 standard (O0 definition + 4 theorems)"

end Tests.Gen5.EnvCacheCCheck
