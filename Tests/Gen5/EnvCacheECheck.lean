import Tests.Gen5.EnvFrame3Check
import Tools.ShippingGen5EnvCacheE
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- BUILT: clean issue-linked build env22v-b6b3206b exit 0 (763 jobs, dirty=false) at b6b3206b: U9 check of freeze scripts/gen5/DG_ENV_T2_U9_FREEZE.md. Counting: TYPE = 1 Expected comparison (Q1); MUTANT = well-typed single changes rejected by the same comparator (signature/defeq, not semantic counterexamples), count as measured;
-- CLOSURE (quiet-plus-four: Laws.O, RefLawsAOps.quiet, frame, frameQ, cacheSet, cacheSetQ allowed as leaves; per-root observed set reported) = roots; negatives (forbidden, flagged) direct + helper; unknown kept apart; self-root; clean.

/-! # DG-ENV unit U9 checks (Tools/ShippingGen5EnvCacheE.lean)
Expected proposition written from freeze scripts/gen5/DG_ENV_T2_U9_FREEZE.md §2 (not copied from the proof), one comparator (`withReducible`). -/

namespace Tests.Gen5.EnvCacheECheck
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildBndCore (cv sv)
open Sparkle.Compiler.Elab (synthesizeChild synthesizeCombinational sparkleChildCache)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingGen2 (Laws)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvCache (RealChildN)
open Tools.ShippingGen5EnvCacheC (CacheInvN)
open Tools.ShippingGen5EnvCacheE
open Tests.Gen3.ExpectedType
open Tests.Gen5.EnvFrameCheck (mkForbid badProj guarded)
open Tests.Gen5.EnvFrame3Check (reachQ QReach allowedQuiet opsN)

/-! ## 1. Expected type and mutants -/
def ExpQ1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M1 without hn
def MutM1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M2 without hrw
def MutM2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M3 without hentry
def MutM3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M4 hentry conclusion without quiet w2
def MutM4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M5 hentry without its CacheInvN hypothesis
def MutM5 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M6 without quiet
def MutM6 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M7 without synth
def MutM7 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M8 without rd
def MutM8 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M9 without hw
def MutM9 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M10 conclusion without CacheInvN at end
def MutM10 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M11 CacheInvN at start world in conclusion
def MutM11 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₀ n y ∧ CacheInvN L env₀ (cv w) ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

-- M12 RealChildN at a second bound environment
def MutM12 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref}
    {env₀ env₁ : Environment} {mctx : Meta.Context} {cctx : Core.Context} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res},
    ∀ (hn : mctx.canUnfold? = none)
    (hrw : ReadWorld (sparkleChildCache : IO.Ref (Std.HashMap Name Res)))
    (hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res),
      (L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)))
    (quiet : L.O.quiet w)
    (synth : sv w = some synthesizeChild)
    (rd : ReadsAt env₀ cref w)
    (hw : CacheInvN L env₀ (cv w))
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w'),
      RealChildN L env₁ n y ∧ CacheInvN L env₀ (cv w') ∧ L.O.quiet w' ∧ sv w' = some synthesizeChild

/-- The one comparator: reducible transparency for every comparison, positive and negative alike. -/
def cmpExp (thm exp : Name) : MetaM Unit := withReducible (checkExpected thm exp)
def cmpMut (thm mt : Name) : MetaM Unit := withReducible (checkMutant thm mt)

run_cmd Lean.Elab.Command.liftTermElabM do
  cmpExp ``synthesizeChild_realN ``ExpQ1
  logInfo "ENVCACHEE TYPE total 1 (Q1), through the withReducible comparison"
  cmpMut ``synthesizeChild_realN ``MutM1
  cmpMut ``synthesizeChild_realN ``MutM2
  cmpMut ``synthesizeChild_realN ``MutM3
  cmpMut ``synthesizeChild_realN ``MutM4
  cmpMut ``synthesizeChild_realN ``MutM5
  cmpMut ``synthesizeChild_realN ``MutM6
  cmpMut ``synthesizeChild_realN ``MutM7
  cmpMut ``synthesizeChild_realN ``MutM8
  cmpMut ``synthesizeChild_realN ``MutM9
  cmpMut ``synthesizeChild_realN ``MutM10
  cmpMut ``synthesizeChild_realN ``MutM11
  cmpMut ``synthesizeChild_realN ``MutM12
  logInfo "ENVCACHEE MUTANT total 12 (M1-M12, all well-typed single changes) rejected by the same comparator (signature/defeq rejections, not semantic counterexamples)"

/-! ## 2. Closure fixtures: forbidden fields of `RefLawsAOps` not allowed in this unit -/
namespace Fx
theorem dDepthSet : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.depthSet
theorem dDepthSetQ : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.depthSetQ
theorem dCacheSetQ : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.cacheSetQ
theorem dFrameT : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.frameT
theorem hDepthSet : True := dDepthSet
theorem hDepthSetQ : True := dDepthSetQ
theorem dFrame : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.frame
theorem dFrameQ : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.frameQ
theorem dCacheSet : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.cacheSet
end Fx

def allowedE : List Name := allowedQuiet ++ [opsN ++ `frame, opsN ++ `frameQ, opsN ++ `cacheSet, opsN ++ `cacheSetQ]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let forbid ← mkForbid
  let ops := opsN
  let F := `Tests.Gen5.EnvFrameFixture
  let H := `Tests.Gen5.EnvFrame3Fixture
  let X := `Tests.Gen5.EnvCacheECheck.Fx
  let forbidE := forbid.filter (!allowedE.contains ·)
  let isLast (r : QReach) (t : Name) : Bool := r.hit.map (·.getLast? == some t) == some true
  -- the three allowed-but-guarded fields are not forbidden; the others are
  for a in allowedE do
    if forbidE.contains a then throwError "ENVCACHEE AUDIT FAILED: allowed {a} is forbidden"
  for f in [`diag, `frameT, `excOk, `depthSetQ, `depthSet] do
    unless forbidE.contains (ops ++ f) do throwError "ENVCACHEE AUDIT FAILED: {ops ++ f} not forbidden"
  -- (A) root Q1: no forbidden use; reached guarded constants are a subset of the allowed six (freeze: "at most"); observed set reported
  let r ← reachQ forbidE allowedE ``synthesizeChild_realN
  if let some p := r.hit then throwError "ENVCACHEE AUDIT FAILED Q1: forbidden use via {p}"
  for g in r.got.toList do
    unless allowedE.contains g do throwError "ENVCACHEE AUDIT FAILED Q1: reaches {g} outside the allowed set"
  unless r.got.contains (ops ++ `quiet) do throwError "ENVCACHEE AUDIT FAILED Q1: does not reach RefLawsAOps.quiet"
  logInfo m!"ENVCACHEE REACH {``synthesizeChild_realN}: clean (type and value), observed {r.got.toList} (visited {r.visited}); allowed (at most) {allowedE}"
  -- the root really uses guarded projections: with the allowed ones forbidden it is flagged
  let rf ← reachQ forbid [] ``synthesizeChild_realN
  unless rf.hit.isSome do throwError "ENVCACHEE AUDIT FAILED: Q1 not flagged when the allowed fields are forbidden"
  -- each allowed field is detected as ALLOWED (a fixture using it is flagged only when it is forbidden)
  let mut nAllowed : Nat := 0
  for (fx, t) in [(X ++ `dFrame, ops ++ `frame), (X ++ `dFrameQ, ops ++ `frameQ), (X ++ `dCacheSet, ops ++ `cacheSet), (X ++ `dCacheSetQ, ops ++ `cacheSetQ)] do
    let ok ← reachQ forbidE allowedE fx
    if let some p := ok.hit then throwError "ENVCACHEE AUDIT FAILED: allowed use {fx} flagged via {p}"
    unless ok.got.contains t do throwError "ENVCACHEE AUDIT FAILED: {fx} does not reach {t}"
    let fb ← reachQ (forbid.filter (!(allowedE.erase t).contains ·)) (allowedE.erase t) fx
    unless isLast fb t do throwError "ENVCACHEE AUDIT FAILED: {fx} not flagged on {t} when {t} is forbidden"
    nAllowed := nAllowed + 1
  -- (B) negatives: fixtures reaching a forbidden constant are flagged, intended constant on the path (direct, then helper)
  let direct : List (Name × Name) :=
    [(X ++ `dDepthSet, ops ++ `depthSet), (X ++ `dDepthSetQ, ops ++ `depthSetQ), (X ++ `dFrameT, ops ++ `frameT),
     (H ++ `qDiag, ops ++ `diag), (H ++ `qLawsT, ``Tools.ShippingGen2.Laws.T),
     (F ++ `dTele, ``Tools.ShippingChildInvA.RefLawsATele.telescope), (F ++ `dT1, ``Tools.ShippingGen2.T1Hyp.defines),
     (F ++ `dND, ``Tools.ShippingGen2.T1HypND.defines), (F ++ `dRec, ops ++ `casesOn)]
  let helper : List (Name × Name) :=
    [(X ++ `hDepthSet, ops ++ `depthSet), (X ++ `hDepthSetQ, ops ++ `depthSetQ), (H ++ `hQDiag, ops ++ `diag),
     (F ++ `hT1, ``Tools.ShippingGen2.T1Hyp.defines)]
  let mut nDir : Nat := 0
  let mut nHelp : Nat := 0
  for (c, t) in direct ++ helper do
    unless forbidE.contains t do throwError "ENVCACHEE AUDIT FAILED: intended {t} not forbidden"
    let rr ← reachQ forbidE allowedE c
    if rr.hit.isNone then throwError "ENVCACHEE AUDIT FAILED: misses {c}"
    let rt ← reachQ [t] allowedE c
    unless isLast rt t do throwError "ENVCACHEE AUDIT FAILED: {c} does not reach its intended {t}"
    if direct.any (·.1 == c) then nDir := nDir + 1 else nHelp := nHelp + 1
  -- (C) UNKNOWN controls (throwing), apart from the forbidden ones, incl. a helper whose TYPE alone is unknown and a hidden constant under the root
  let missing := `Tests.Gen5.EnvCacheEFixture.noSuchRoot
  let unres : List (Name × Option Name × Name × List Name) :=
    [(missing, none, missing, []), (F ++ `hv, some (F ++ `helperClean), F ++ `helperClean, []),
     (F ++ `ht, some (F ++ `helperTy), F ++ `helperTy, []),
     (F ++ `ht2, some (F ++ `helperTy), F ++ `helperTy, [F ++ `ht2, F ++ `helperHt])]
  let mut nUnres : Nat := 0
  for (c, hid, nm, via) in unres do
    let ok ← try
        let _ ← reachQ forbidE allowedE c hid
        pure false
      catch e =>
        let msg ← e.toMessageData.toString
        let has (n : Name) := (msg.splitOn (toString n)).length > 1
        pure (msg.startsWith s!"ENVFRAME3 AUDIT UNRESOLVED NAME {nm} " && via.all has)
    unless ok do throwError "ENVCACHEE AUDIT FAILED: unresolved {nm} under root {c} did not throw"
    nUnres := nUnres + 1
  let hiddenOk ← try
      let _ ← reachQ forbidE allowedE ``synthesizeChild_realN (some ``Tools.ShippingGen5EnvCacheD.cacheInvN_insert_runs)
      pure false
    catch e =>
      let msg ← e.toMessageData.toString
      pure (msg.startsWith "ENVFRAME3 AUDIT UNRESOLVED NAME Tools.ShippingGen5EnvCacheD.cacheInvN_insert_runs ")
  unless hiddenOk do throwError "ENVCACHEE AUDIT FAILED: hiding cacheInvN_insert_runs under the root did not throw"
  nUnres := nUnres + 1
  -- (D) self-root: a forbidden constant as root is flagged on itself
  let selfRoots : List Name :=
    [``Tools.ShippingGen2.T1Hyp.defines, ``Tools.ShippingGen2.T1HypND.defines, ``Tools.ShippingGen2.Laws.T,
     ops ++ `depthSet, ops ++ `depthSetQ, ops ++ `casesOn, ``Tools.ShippingEnvSnapshot.GetEnvFrame]
  let mut nSelf : Nat := 0
  for t in selfRoots do
    unless forbidE.contains t do throwError "ENVCACHEE AUDIT FAILED: self-root {t} not forbidden"
    let rs ← reachQ forbidE allowedE t
    unless rs.hit == some [t] do throwError "ENVCACHEE AUDIT FAILED: forbidden root {t} itself not flagged ({toString rs.hit})"
    nSelf := nSelf + 1
  -- (E) clean control
  let mut nClean : Nat := 0
  for c in [F ++ `cUnrelated, F ++ `cBinders, F ++ `cHelper] do
    let rc ← reachQ forbidE allowedE c
    if rc.hit.isSome then throwError "ENVCACHEE AUDIT FAILED: clean control {c} flagged"
    nClean := nClean + 1
  logInfo m!"ENVCACHEE CLOSURE total: 1 root (Q1, quiet-plus-four) + {nAllowed} allowed-field controls / negatives: {nDir} direct + {nHelp} helper law-bearing fixtures each flagged with the intended constant + {nUnres} unknown (incl. 1 helper-type-only, 1 hidden constant under the root) + {nSelf} self-root / clean: {nClean}. Scope: type and value constants reachable in the environment; allowed projections are leaves."

/-! ## 3. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``synthesizeChild_realN
  logInfo "ENVCACHEE AXIOMS total 1 standard (Q1)"

end Tests.Gen5.EnvCacheECheck
