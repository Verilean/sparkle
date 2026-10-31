import Tests.Gen5.EnvFrame3Check
import Tools.ShippingGen5EnvCacheD
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: header to be synced to the clean issue-linked build SHA after build. Counting: TYPE = 1 Expected comparison (P1); MUTANT = well-typed single changes rejected by the same comparator (signature/defeq, not semantic counterexamples), count as measured;
-- CLOSURE (quiet-plus-three: Laws.O, RefLawsAOps.quiet, frame, frameQ, cacheSet allowed as leaves; per-root observed set reported) = roots; negatives (forbidden, flagged) direct + helper; unknown kept apart; self-root; clean.

/-! # DG-ENV unit U8 checks (Tools/ShippingGen5EnvCacheD.lean)
Expected proposition written from freeze scripts/gen5/DG_ENV_T2_U8_FREEZE.md §2 (not copied from the proof), one comparator (`withReducible`). -/

namespace Tests.Gen5.EnvCacheDCheck
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildBndCore (cv)
open Sparkle.Compiler.Elab (sparkleChildCache)
open Tools.ShippingGen2 (Laws)
open Tools.ShippingGen5EnvCache (RealChildN)
open Tools.ShippingGen5EnvCacheC (CacheInvN)
open Tools.ShippingGen5EnvCacheD
open Tests.Gen3.ExpectedType
open Tests.Gen5.EnvFrameCheck (mkForbid badProj guarded)
open Tests.Gen5.EnvFrame3Check (reachQ QReach allowedQuiet opsN)

/-! ## 1. Expected type and mutants -/
def ExpP1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld} {u : Unit},
    ∀ (hn : mctx.canUnfold? = none) (quiet : L.O.quiet w) (hw : CacheInvN L env₀ (cv w)) (hr : RealChildN L env₀ c r)
      (h : RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert c r) : MetaM Unit)
        mctx mref cctx cref w u w'),
      CacheInvN L env₀ (cv w')

def MutM1 : Prop := -- without `hn`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld} {u : Unit},
    L.O.quiet w → CacheInvN L env₀ (cv w) → RealChildN L env₀ c r →
    RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert c r) : MetaM Unit)
      mctx mref cctx cref w u w' → CacheInvN L env₀ (cv w')
def MutM2 : Prop := -- without `quiet`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld} {u : Unit},
    mctx.canUnfold? = none → CacheInvN L env₀ (cv w) → RealChildN L env₀ c r →
    RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert c r) : MetaM Unit)
      mctx mref cctx cref w u w' → CacheInvN L env₀ (cv w')
def MutM3 : Prop := -- without `hw`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld} {u : Unit},
    mctx.canUnfold? = none → L.O.quiet w → RealChildN L env₀ c r →
    RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert c r) : MetaM Unit)
      mctx mref cctx cref w u w' → CacheInvN L env₀ (cv w')
def MutM4 : Prop := -- without `hr`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld} {u : Unit},
    mctx.canUnfold? = none → L.O.quiet w → CacheInvN L env₀ (cv w) →
    RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert c r) : MetaM Unit)
      mctx mref cctx cref w u w' → CacheInvN L env₀ (cv w')
def MutM5 : Prop := -- `hw` at a second bound environment
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ env₁ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld} {u : Unit},
    mctx.canUnfold? = none → L.O.quiet w → CacheInvN L env₁ (cv w) → RealChildN L env₀ c r →
    RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert c r) : MetaM Unit)
      mctx mref cctx cref w u w' → CacheInvN L env₀ (cv w')
def MutM6 : Prop := -- conclusion at the start world
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld} {u : Unit},
    mctx.canUnfold? = none → L.O.quiet w → CacheInvN L env₀ (cv w) → RealChildN L env₀ c r →
    RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert c r) : MetaM Unit)
      mctx mref cctx cref w u w' → CacheInvN L env₀ (cv w)
def MutM7 : Prop := -- the modify is the identity instead of the insert
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld} {u : Unit},
    mctx.canUnfold? = none → L.O.quiet w → CacheInvN L env₀ (cv w) → RealChildN L env₀ c r →
    RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m) : MetaM Unit)
      mctx mref cctx cref w u w' → CacheInvN L env₀ (cv w')
def MutM8 : Prop := -- quietness demanded at the end world
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {r : Res}
    {w w' : Void IO.RealWorld} {u : Unit},
    mctx.canUnfold? = none → L.O.quiet w' → CacheInvN L env₀ (cv w) → RealChildN L env₀ c r →
    RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert c r) : MetaM Unit)
      mctx mref cctx cref w u w' → CacheInvN L env₀ (cv w')

/-- The one comparator: reducible transparency for every comparison, positive and negative alike. -/
def cmpExp (thm exp : Name) : MetaM Unit := withReducible (checkExpected thm exp)
def cmpMut (thm mt : Name) : MetaM Unit := withReducible (checkMutant thm mt)

run_cmd Lean.Elab.Command.liftTermElabM do
  cmpExp ``cacheInvN_insert_runs ``ExpP1
  logInfo "ENVCACHED TYPE total 1 (P1), through the withReducible comparison"
  cmpMut ``cacheInvN_insert_runs ``MutM1
  cmpMut ``cacheInvN_insert_runs ``MutM2
  cmpMut ``cacheInvN_insert_runs ``MutM3
  cmpMut ``cacheInvN_insert_runs ``MutM4
  cmpMut ``cacheInvN_insert_runs ``MutM5
  cmpMut ``cacheInvN_insert_runs ``MutM6
  cmpMut ``cacheInvN_insert_runs ``MutM7
  cmpMut ``cacheInvN_insert_runs ``MutM8
  logInfo "ENVCACHED MUTANT total 8 (M1-M8, all well-typed single changes) rejected by the same comparator (signature/defeq rejections, not semantic counterexamples)"

/-! ## 2. Closure fixtures: forbidden fields of `RefLawsAOps` not allowed in this unit -/
namespace Fx
theorem dDepthSet : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.depthSet
theorem dCacheSetQ : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.cacheSetQ
theorem dFrameT : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.frameT
theorem hDepthSet : True := dDepthSet
theorem hCacheSetQ : True := dCacheSetQ
theorem dFrame : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.frame
theorem dFrameQ : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.frameQ
theorem dCacheSet : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.cacheSet
end Fx

def allowedD : List Name := allowedQuiet ++ [opsN ++ `frame, opsN ++ `frameQ, opsN ++ `cacheSet]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let forbid ← mkForbid
  let ops := opsN
  let F := `Tests.Gen5.EnvFrameFixture
  let H := `Tests.Gen5.EnvFrame3Fixture
  let X := `Tests.Gen5.EnvCacheDCheck.Fx
  let forbidD := forbid.filter (!allowedD.contains ·)
  let isLast (r : QReach) (t : Name) : Bool := r.hit.map (·.getLast? == some t) == some true
  -- the three allowed-but-guarded fields are not forbidden; the others are
  for a in allowedD do
    if forbidD.contains a then throwError "ENVCACHED AUDIT FAILED: allowed {a} is forbidden"
  for f in [`diag, `frameT, `excOk, `cacheSetQ, `depthSetQ, `depthSet] do
    unless forbidD.contains (ops ++ f) do throwError "ENVCACHED AUDIT FAILED: {ops ++ f} not forbidden"
  -- (A) root P1: no forbidden use; reached guarded constants are a subset of the allowed five (freeze: "at most"); observed set reported
  let r ← reachQ forbidD allowedD ``cacheInvN_insert_runs
  if let some p := r.hit then throwError "ENVCACHED AUDIT FAILED P1: forbidden use via {p}"
  for g in r.got.toList do
    unless allowedD.contains g do throwError "ENVCACHED AUDIT FAILED P1: reaches {g} outside the allowed set"
  unless r.got.contains (ops ++ `quiet) do throwError "ENVCACHED AUDIT FAILED P1: does not reach RefLawsAOps.quiet"
  logInfo m!"ENVCACHED REACH {``cacheInvN_insert_runs}: clean (type and value), observed {r.got.toList} (visited {r.visited}); allowed (at most) {allowedD}"
  -- the root really uses guarded projections: with the allowed ones forbidden it is flagged
  let rf ← reachQ forbid [] ``cacheInvN_insert_runs
  unless rf.hit.isSome do throwError "ENVCACHED AUDIT FAILED: P1 not flagged when the allowed fields are forbidden"
  -- each allowed field is detected as ALLOWED (a fixture using it is flagged only when it is forbidden)
  let mut nAllowed : Nat := 0
  for (fx, t) in [(X ++ `dFrame, ops ++ `frame), (X ++ `dFrameQ, ops ++ `frameQ), (X ++ `dCacheSet, ops ++ `cacheSet)] do
    let ok ← reachQ forbidD allowedD fx
    if let some p := ok.hit then throwError "ENVCACHED AUDIT FAILED: allowed use {fx} flagged via {p}"
    unless ok.got.contains t do throwError "ENVCACHED AUDIT FAILED: {fx} does not reach {t}"
    let fb ← reachQ (forbid.filter (!(allowedD.erase t).contains ·)) (allowedD.erase t) fx
    unless isLast fb t do throwError "ENVCACHED AUDIT FAILED: {fx} not flagged on {t} when {t} is forbidden"
    nAllowed := nAllowed + 1
  -- (B) negatives: fixtures reaching a forbidden constant are flagged, intended constant on the path (direct, then helper)
  let direct : List (Name × Name) :=
    [(X ++ `dDepthSet, ops ++ `depthSet), (X ++ `dCacheSetQ, ops ++ `cacheSetQ), (X ++ `dFrameT, ops ++ `frameT),
     (H ++ `qDiag, ops ++ `diag), (H ++ `qLawsT, ``Tools.ShippingGen2.Laws.T),
     (F ++ `dTele, ``Tools.ShippingChildInvA.RefLawsATele.telescope), (F ++ `dT1, ``Tools.ShippingGen2.T1Hyp.defines),
     (F ++ `dND, ``Tools.ShippingGen2.T1HypND.defines), (F ++ `dRec, ops ++ `casesOn)]
  let helper : List (Name × Name) :=
    [(X ++ `hDepthSet, ops ++ `depthSet), (X ++ `hCacheSetQ, ops ++ `cacheSetQ), (H ++ `hQDiag, ops ++ `diag),
     (F ++ `hT1, ``Tools.ShippingGen2.T1Hyp.defines)]
  let mut nDir : Nat := 0
  let mut nHelp : Nat := 0
  for (c, t) in direct ++ helper do
    unless forbidD.contains t do throwError "ENVCACHED AUDIT FAILED: intended {t} not forbidden"
    let rr ← reachQ forbidD allowedD c
    if rr.hit.isNone then throwError "ENVCACHED AUDIT FAILED: misses {c}"
    let rt ← reachQ [t] allowedD c
    unless isLast rt t do throwError "ENVCACHED AUDIT FAILED: {c} does not reach its intended {t}"
    if direct.any (·.1 == c) then nDir := nDir + 1 else nHelp := nHelp + 1
  -- (C) UNKNOWN controls (throwing), apart from the forbidden ones, incl. a helper whose TYPE alone is unknown and a hidden constant under the root
  let missing := `Tests.Gen5.EnvCacheDFixture.noSuchRoot
  let unres : List (Name × Option Name × Name × List Name) :=
    [(missing, none, missing, []), (F ++ `hv, some (F ++ `helperClean), F ++ `helperClean, []),
     (F ++ `ht, some (F ++ `helperTy), F ++ `helperTy, []),
     (F ++ `ht2, some (F ++ `helperTy), F ++ `helperTy, [F ++ `ht2, F ++ `helperHt])]
  let mut nUnres : Nat := 0
  for (c, hid, nm, via) in unres do
    let ok ← try
        let _ ← reachQ forbidD allowedD c hid
        pure false
      catch e =>
        let msg ← e.toMessageData.toString
        let has (n : Name) := (msg.splitOn (toString n)).length > 1
        pure (msg.startsWith s!"ENVFRAME3 AUDIT UNRESOLVED NAME {nm} " && via.all has)
    unless ok do throwError "ENVCACHED AUDIT FAILED: unresolved {nm} under root {c} did not throw"
    nUnres := nUnres + 1
  let hiddenOk ← try
      let _ ← reachQ forbidD allowedD ``cacheInvN_insert_runs (some ``Tools.ShippingGen5EnvCacheC.cacheInvN_insert)
      pure false
    catch e =>
      let msg ← e.toMessageData.toString
      pure (msg.startsWith "ENVFRAME3 AUDIT UNRESOLVED NAME Tools.ShippingGen5EnvCacheC.cacheInvN_insert ")
  unless hiddenOk do throwError "ENVCACHED AUDIT FAILED: hiding cacheInvN_insert under the root did not throw"
  nUnres := nUnres + 1
  -- (D) self-root: a forbidden constant as root is flagged on itself
  let selfRoots : List Name :=
    [``Tools.ShippingGen2.T1Hyp.defines, ``Tools.ShippingGen2.T1HypND.defines, ``Tools.ShippingGen2.Laws.T,
     ops ++ `depthSet, ops ++ `cacheSetQ, ops ++ `casesOn, ``Tools.ShippingEnvSnapshot.GetEnvFrame]
  let mut nSelf : Nat := 0
  for t in selfRoots do
    unless forbidD.contains t do throwError "ENVCACHED AUDIT FAILED: self-root {t} not forbidden"
    let rs ← reachQ forbidD allowedD t
    unless rs.hit == some [t] do throwError "ENVCACHED AUDIT FAILED: forbidden root {t} itself not flagged ({toString rs.hit})"
    nSelf := nSelf + 1
  -- (E) clean control
  let mut nClean : Nat := 0
  for c in [F ++ `cUnrelated, F ++ `cBinders, F ++ `cHelper] do
    let rc ← reachQ forbidD allowedD c
    if rc.hit.isSome then throwError "ENVCACHED AUDIT FAILED: clean control {c} flagged"
    nClean := nClean + 1
  logInfo m!"ENVCACHED CLOSURE total: 1 root (P1, quiet-plus-three) + {nAllowed} allowed-field controls / negatives: {nDir} direct + {nHelp} helper law-bearing fixtures each flagged with the intended constant + {nUnres} unknown (incl. 1 helper-type-only, 1 hidden constant under the root) + {nSelf} self-root / clean: {nClean}. Scope: type and value constants reachable in the environment; allowed projections are leaves."

/-! ## 3. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``cacheInvN_insert_runs
  logInfo "ENVCACHED AXIOMS total 1 standard (P1)"

end Tests.Gen5.EnvCacheDCheck
