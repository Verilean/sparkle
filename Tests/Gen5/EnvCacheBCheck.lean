import Tests.Gen5.EnvFrame3Check
import Tools.ShippingGen5EnvCacheB
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built: clean issue-linked build env15v-e511ffc0 exit 0 (760 jobs, dirty=false), approved at e511ffc0. Counting: TYPE = 4 Expected comparisons (B1-B4); MUTANT = 8 well-typed single changes rejected by the same comparator (signature/defeq, not semantic counterexamples);
-- CLOSURE = roots; negatives (forbidden, flagged) direct + helper; unknown kept apart; self-root; clean.

/-! # DG-ENV unit U6 checks (Tools/ShippingGen5EnvCacheB.lean)
Expected propositions written from freeze scripts/gen5/DG_ENV_T2_U6_FREEZE.md §2 (not copied from the proofs), one comparator (`withReducible`). -/

namespace Tests.Gen5.EnvCacheBCheck
open Lean Meta
open Tools.ShippingChildInv (Res)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvQ (QuietStrength)
open Tools.ShippingGen2 (Laws)
open Tools.ShippingGen5EnvCache (RealChildN)
open Tools.ShippingGen5EnvCacheB
open Tests.Gen3.ExpectedType
open Tests.Gen5.EnvFrameCheck (mkForbid badProj guarded)
open Tests.Gen5.EnvFrame3Check (reachQ QReach allowedQuiet opsN)

/-! ## 1. Expected types -/
def ExpB1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' L'' : Laws mref cref}
    {env₀ : Environment}, ∀ (h1 : QuietStrength L L' env₀) (h2 : QuietStrength L' L'' env₀), QuietStrength L L'' env₀
def ExpB2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment}, QuietStrength L L env₀ ↔ ∀ w : Void IO.RealWorld, L.O.quiet w → ReadsAt env₀ cref w
def ExpB3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment}, ∀ (hq : QuietStrength L L' env₀) {c : Name} {r : Res} (h : RealChildN L env₀ c r),
    RealChildN L' env₀ c r
def ExpB4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment}, ∀ (hq : QuietStrength L L' env₀) {c : Name} {r : Res} (h : RealChildN L' env₀ c r),
    RealChildN L env₀ c r

/-! ## Mutants (well-typed single changes) -/
def MutM1 : Prop := -- B1 with `h2` dropped
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' L'' : Laws mref cref}
    {env₀ : Environment}, QuietStrength L L' env₀ → QuietStrength L L'' env₀
def MutM2 : Prop := -- B1 with `h2` at a second bound environment
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' L'' : Laws mref cref}
    {env₀ env₁ : Environment}, QuietStrength L L' env₀ → QuietStrength L' L'' env₁ → QuietStrength L L'' env₀
def MutM3 : Prop := -- B2 forward direction only
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment}, QuietStrength L L env₀ → ∀ w : Void IO.RealWorld, L.O.quiet w → ReadsAt env₀ cref w
def MutM4 : Prop := -- B2 with `ReadsAt env₁` for a second bound environment
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ env₁ : Environment}, QuietStrength L L env₀ ↔ ∀ w : Void IO.RealWorld, L.O.quiet w → ReadsAt env₁ cref w
def MutM5 : Prop := -- B3 without `hq`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} {c : Name} {r : Res}, RealChildN L env₀ c r → RealChildN L' env₀ c r
def MutM6 : Prop := -- B3 concluding at a second bound environment
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ env₁ : Environment}, QuietStrength L L' env₀ → ∀ {c : Name} {r : Res}, RealChildN L env₀ c r →
    RealChildN L' env₁ c r
def MutM7 : Prop := -- B4 without `hq`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} {c : Name} {r : Res}, RealChildN L' env₀ c r → RealChildN L env₀ c r
def MutM8 : Prop := -- B4 concluding `RealChildN L' env₀ c r` (identity form of the input; signature control only)
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment}, QuietStrength L L' env₀ → ∀ {c : Name} {r : Res}, RealChildN L' env₀ c r →
    RealChildN L' env₀ c r

/-- The one comparator: reducible transparency for every comparison, positive and negative alike. -/
def cmpExp (thm exp : Name) : MetaM Unit := withReducible (checkExpected thm exp)
def cmpMut (thm mt : Name) : MetaM Unit := withReducible (checkMutant thm mt)

run_cmd Lean.Elab.Command.liftTermElabM do
  cmpExp ``quietStrength_trans ``ExpB1
  cmpExp ``quietStrength_self_iff ``ExpB2
  cmpExp ``realChildN_up ``ExpB3
  cmpExp ``realChildN_down ``ExpB4
  logInfo "ENVCACHEB TYPE total 4 (B1-B4), all through the same withReducible comparison"
  cmpMut ``quietStrength_trans ``MutM1
  cmpMut ``quietStrength_trans ``MutM2
  cmpMut ``quietStrength_self_iff ``MutM3
  cmpMut ``quietStrength_self_iff ``MutM4
  cmpMut ``realChildN_up ``MutM5
  cmpMut ``realChildN_up ``MutM6
  cmpMut ``realChildN_down ``MutM7
  cmpMut ``realChildN_down ``MutM8
  logInfo "ENVCACHEB MUTANT total 8 (M1-M8, all well-typed single changes; M3 = forward direction only, M8 = identity form of the B4 input) rejected by the same comparator (signature/defeq rejections, not semantic counterexamples)"

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
  -- (A) roots B1-B4: quiet-only, reached guarded constants exactly the allowed two (`Laws.O`, `RefLawsAOps.quiet`).
  let roots := [``quietStrength_trans, ``quietStrength_self_iff, ``realChildN_up, ``realChildN_down]
  let mut nRoots : Nat := 0
  for c in roots do
    let r ← reachQ forbidQ allowedQuiet c
    if let some p := r.hit then throwError "ENVCACHEB AUDIT FAILED {c}: forbidden use via {p}"
    unless r.got.toList.toArray.qsort Name.lt == allowedQuiet.toArray.qsort Name.lt do
      throwError "ENVCACHEB AUDIT FAILED {c}: reaches {r.got.toList}, expected exactly {allowedQuiet}"
    nRoots := nRoots + 1
    logInfo m!"ENVCACHEB REACH {c}: clean (type and value), reached exactly {allowedQuiet} (visited {r.visited})"
  -- the roots really use the allowed projections: with them forbidden they are flagged
  for c in roots do
    let rf ← reachQ forbid [] c
    unless rf.hit.isSome do throwError "ENVCACHEB AUDIT FAILED: {c} not flagged when Laws.O / quiet are forbidden"
  -- (B) negatives: fixtures reaching a law-bearing constant are flagged (FORBIDDEN controls) with the intended constant on the path
  let neg : List (Name × Name) :=
    [(F ++ `dOps, ops ++ `frame), (H ++ `qLawsT, ``Tools.ShippingGen2.Laws.T),
     (F ++ `dTele, ``Tools.ShippingChildInvA.RefLawsATele.telescope), (F ++ `dT1, ``Tools.ShippingGen2.T1Hyp.defines),
     (H ++ `qDiag, ops ++ `diag),
     (F ++ `hOps, ops ++ `frame), (F ++ `hT1, ``Tools.ShippingGen2.T1Hyp.defines)]
  let mut nNeg : Nat := 0
  for (c, t) in neg do
    unless forbidQ.contains t do throwError "ENVCACHEB AUDIT FAILED: intended {t} not forbidden"
    let r ← reachQ forbidQ allowedQuiet c
    if r.hit.isNone then throwError "ENVCACHEB AUDIT FAILED: misses {c}"
    let rt ← reachQ [t] allowedQuiet c
    unless isLast rt t do throwError "ENVCACHEB AUDIT FAILED: {c} does not reach its intended {t}"
    nNeg := nNeg + 1
  -- (C) UNKNOWN controls (throwing), kept apart from the forbidden ones above, including a helper whose TYPE alone is unknown
  let missing := `Tests.Gen5.EnvCacheBFixture.noSuchRoot
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
    unless ok do throwError "ENVCACHEB AUDIT FAILED: unresolved {nm} under root {c} did not throw"
    nUnres := nUnres + 1
  -- a root of this unit with a hidden constant on its path also throws (unknown fails; never silently clean)
  let hiddenOk ← try
      let _ ← reachQ forbidQ allowedQuiet ``realChildN_up (some ``Tools.ShippingGen5EnvQ.QuietStrength)
      pure false
    catch e =>
      let msg ← e.toMessageData.toString
      pure (msg.startsWith "ENVFRAME3 AUDIT UNRESOLVED NAME Tools.ShippingGen5EnvQ.QuietStrength ")
  unless hiddenOk do throwError "ENVCACHEB AUDIT FAILED: hiding QuietStrength under realChildN_up did not throw"
  nUnres := nUnres + 1
  -- (D) self-root: a forbidden constant as root is flagged on itself
  let selfRoots : List Name :=
    [``Tools.ShippingGen2.T1Hyp.defines, ``Tools.ShippingGen2.T1HypND.defines, ``Tools.ShippingGen2.Laws.T,
     ops ++ `frame, ops ++ `casesOn, ``Tools.ShippingEnvSnapshot.GetEnvFrame]
  let mut nSelf : Nat := 0
  for t in selfRoots do
    unless forbidQ.contains t do throwError "ENVCACHEB AUDIT FAILED: self-root {t} not forbidden"
    let r ← reachQ forbidQ allowedQuiet t
    unless r.hit == some [t] do throwError "ENVCACHEB AUDIT FAILED: forbidden root {t} itself not flagged ({toString r.hit})"
    nSelf := nSelf + 1
  -- (E) clean control: the unrelated fixtures of U1 are not flagged
  let mut nClean : Nat := 0
  for c in [F ++ `cUnrelated, F ++ `cBinders, F ++ `cHelper] do
    let r ← reachQ forbidQ allowedQuiet c
    if r.hit.isSome then throwError "ENVCACHEB AUDIT FAILED: clean control {c} flagged"
    nClean := nClean + 1
  logInfo m!"ENVCACHEB CLOSURE total: {nRoots} roots (B1-B4 quiet-only) / negatives: {nNeg} law-bearing fixtures (5 direct + 2 helper) each flagged with the intended constant + {nUnres} unknown (incl. 1 helper-type-only, 1 hidden constant under a root) + {nSelf} self-root / clean: {nClean}. Scope: type and value constants reachable in the environment; allowed projections are leaves."

/-! ## 3. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``quietStrength_trans, ``quietStrength_self_iff, ``realChildN_up, ``realChildN_down] do
    checkAxioms n
  logInfo "ENVCACHEB AXIOMS total 4 standard (4 theorems)"

end Tests.Gen5.EnvCacheBCheck
