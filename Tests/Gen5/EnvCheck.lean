import Tools.ShippingGen5Env
import Tools.ShippingGen5T1ND
import Tools.ShippingStRefCorrespondence
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT yet.

/-! # DG-ENV checks (Tools/ShippingGen5Env.lean; scripts/gen5/DG_ENV_FREEZE.md rev1 §3, par/gen5-t2 2d8c6498)

1. TYPE: `ReadsAt`'s body against an independent `ExpReadsAt`; E1-E6 against the freeze §2 statements (fully bound,
   binder names/info and order compared by `cmpTele`).
2. MUTANT (signature/defeq rejections, NOT semantic counterexamples): `ReadsAt` without the `structEnv` conjunct;
   E4 with `ReadsAt` at the END world `w'` of the `getConstInfo` run instead of its start; E5 concluding
   `envR = env₀`; E6 with `hall` weakened to `ReadsAt` at one fixed world `w0`.
3. FIELD SCAN (a description of the clause types, NOT a non-derivability proof): the field types of `Laws`,
   `RefLawsAOps`, `RefLawsATele` and the body of `StableA` mention none of `envAt`, `Lean.Core.State.env`,
   `Lean.getEnv`, `EnvFrame`, `GetEnvFrame`, `ReadKeeps` directly. Control: the scanner finds `envAt` in `ReadsAt`.
4. CLOSURE: E1-E6 reach no `Laws`/`RefLawsAOps`/`RefLawsATele`/`T1Hyp`/`T1HypND` field (named projection, raw
   `.proj`, recursor) and none of `GetEnvFrame`, `ReadKeeps`, `EnvSnapshot`. Controls: one per forbidden class, one
   through two helpers, unrelated (not flagged). Positive reach per root.
5. Axioms. -/

/-! ## 0. Fixtures -/
namespace Tests.Gen5.EnvHelperA
theorem helperA : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsATele.telescope
end Tests.Gen5.EnvHelperA
namespace Tests.Gen5.EnvHelperB
theorem helperB : True := Tests.Gen5.EnvHelperA.helperA
end Tests.Gen5.EnvHelperB
namespace Tests.Gen5.EnvFixture
theorem badLaws : True := (fun _ => trivial) @Tools.ShippingGen2.Laws.O
theorem badOps : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.frame
theorem badTele2 : True := Tests.Gen5.EnvHelperB.helperB
theorem badOpsRec : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.casesOn.{0}
theorem badT1 : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.defines
theorem badND : True := (fun _ => trivial) @Tools.ShippingGen2.T1HypND.defines
theorem badGetEnvFrame : True := (fun _ => trivial) @Tools.ShippingEnvSnapshot.GetEnvFrame
theorem badReadKeeps : True := (fun _ => trivial) @Tools.ShippingStRefCorrespondence.ReadKeeps
theorem badSnapshot : True := (fun _ => trivial) @Tools.ShippingEntryReadsLinked.EnvSnapshot
theorem unrelated : True := trivial
end Tests.Gen5.EnvFixture

namespace Tests.Gen5.EnvCheck
open Lean Meta
open Sparkle.Compiler.Elab (instancePredicate userInliner structEnv entryConst certifiedShape? mixedCertifiedShape?
  machineShape? MachineShape)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Env
open Tests.Gen3.ExpectedType

/-! ## 1. Expected types -/
def ExpReadsAt (env₀ : Environment) (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Prop :=
  (∀ X ci, (envAt cref w).find? X = some ci → env₀.find? X = some ci) ∧
  instancePredicate (envAt cref w) = instancePredicate env₀ ∧
  userInliner (envAt cref w) = userInliner env₀ ∧
  structEnv (envAt cref w) = structEnv env₀

def MutReadsAtNoStruct (env₀ : Environment) (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Prop :=
  (∀ X ci, (envAt cref w).find? X = some ci → env₀.find? X = some ci) ∧
  instancePredicate (envAt cref w) = instancePredicate env₀ ∧
  userInliner (envAt cref w) = userInliner env₀

def ExpE1 : Prop :=
  ∀ (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld), ReadsAt (envAt cref w) cref w

def ExpE2 : Prop :=
  ∀ {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {w w' : Void IO.RealWorld}
    (he : envAt cref w' = envAt cref w) (h : ReadsAt env₀ cref w), ReadsAt env₀ cref w'

def ExpE3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {α : Type} {x : MetaM α}
    (hx : Tools.ShippingEnvSnapshot.EnvFrame x mctx mref cctx cref) {w w' : Void IO.RealWorld} {a : α}
    (hr : RunsTo x mctx mref cctx cref w a w') (h : ReadsAt env₀ cref w), ReadsAt env₀ cref w'

def ExpE4 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {X : Name} {w w' : Void IO.RealWorld}
    {ci : ConstantInfo}
    (hget : RunsTo (Lean.getConstInfo X : MetaM ConstantInfo) mctx mref cctx cref w ci w')
    (h : ReadsAt env₀ cref w), env₀.find? X = some ci

def MutE4End : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {X : Name} {w w' : Void IO.RealWorld}
    {ci : ConstantInfo}
    (hget : RunsTo (Lean.getConstInfo X : MetaM ConstantInfo) mctx mref cctx cref w ci w')
    (h : ReadsAt env₀ cref w'), env₀.find? X = some ci

def ExpE5 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ envR : Environment} {w w' : Void IO.RealWorld}
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR w')
    (h : ReadsAt env₀ cref w),
    (∀ X ci, envR.find? X = some ci → env₀.find? X = some ci) ∧
    instancePredicate envR = instancePredicate env₀ ∧ userInliner envR = userInliner env₀ ∧
    structEnv envR = structEnv env₀

def MutE5Eq : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ envR : Environment} {w w' : Void IO.RealWorld}
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR w')
    (h : ReadsAt env₀ cref w), envR = env₀

def ExpE6 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {c : Name} {ci₀ : ConstantInfo} {shape : MachineShape}
    (hall : ∀ u, ReadsAt env₀ cref u) (hc : env₀.find? c = some ci₀)
    (hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) = none)
    (hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (instancePredicate env₀) = none)
    (hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) = some shape),
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c shape

def MutE6NoAll : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {c : Name} {ci₀ : ConstantInfo} {shape : MachineShape}
    (w0 : Void IO.RealWorld) (hall : ReadsAt env₀ cref w0) (hc : env₀.find? c = some ci₀)
    (hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) = none)
    (hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (instancePredicate env₀) = none)
    (hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) = some shape),
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c shape

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``ReadsAt ``ExpReadsAt
  checkExpected ``readsAt_self ``ExpE1
  checkExpected ``ReadsAt.of_envEq ``ExpE2
  checkExpected ``ReadsAt.of_frame ``ExpE3
  checkExpected ``ci_of_readsAt ``ExpE4
  checkExpected ``envR_of_readsAt ``ExpE5
  checkExpected ``machineDefines_of_readsAll ``ExpE6
  checkMutant ``ReadsAt ``MutReadsAtNoStruct
  checkMutant ``ci_of_readsAt ``MutE4End
  checkMutant ``envR_of_readsAt ``MutE5Eq
  checkMutant ``machineDefines_of_readsAll ``MutE6NoAll

/-! ## 2. Field scan (description only) -/
def envNames : List Name :=
  [``Tools.ShippingEntryReadsLinked.envAt, ``Lean.Core.State.env, ``Lean.getEnv, ``Tools.ShippingEnvSnapshot.EnvFrame,
   ``Tools.ShippingEnvSnapshot.GetEnvFrame, ``Tools.ShippingStRefCorrespondence.ReadKeeps]

def mentionsEnv (e : Expr) : Option Name := e.getUsedConstants.toList.find? envNames.contains

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let some (.defnInfo ra) := env.find? ``ReadsAt | throwError "ENV SCAN FAILED: no ReadsAt"
  unless (mentionsEnv ra.value).isSome do throwError "ENV SCAN FAILED: control (envAt in ReadsAt) missed"
  logInfo "ENV SCAN CONTROL: envAt found in ReadsAt"
  let mut n : Nat := 0
  for s in [``Tools.ShippingGen2.Laws, ``Tools.ShippingChildInvA.RefLawsAOps,
      ``Tools.ShippingChildInvA.RefLawsATele] do
    let fs := getStructureFields env s
    if fs.isEmpty then throwError "ENV SCAN FAILED: {s} has no fields"
    for f in fs do
      let pj := s ++ f
      let ci ← getConstInfo pj
      if let some u := mentionsEnv ci.type then throwError "ENV SCAN: {pj} mentions {u}"
      n := n + 1
  let some (.defnInfo st) := env.find? ``Tools.ShippingChildVCA.StableA | throwError "ENV SCAN FAILED: no StableA"
  if let some u := mentionsEnv st.value then throwError "ENV SCAN: StableA mentions {u}"
  logInfo m!"ENV SCAN: {n} field types of Laws/RefLawsAOps/RefLawsATele and StableA's body mention none of {envNames} directly (description, not a non-derivability proof)"

/-! ## 3. Closure audit -/
def forbidStructs : List Name :=
  [``Tools.ShippingGen2.Laws, ``Tools.ShippingChildInvA.RefLawsAOps, ``Tools.ShippingChildInvA.RefLawsATele,
   ``Tools.ShippingGen2.T1Hyp, ``Tools.ShippingGen2.T1HypND]

def forbidConsts : MetaM (List Name) := do
  let env ← getEnv
  let mut out : List Name :=
    [``Tools.ShippingEnvSnapshot.GetEnvFrame, ``Tools.ShippingStRefCorrespondence.ReadKeeps,
     ``Tools.ShippingEntryReadsLinked.EnvSnapshot]
  for s in forbidStructs do
    let fs := getStructureFields env s
    if fs.isEmpty then throwError "ENV AUDIT FAILED: {s} has no fields"
    out := out ++ fs.toList.map (s ++ ·) ++ [s ++ `rec, s ++ `casesOn, s ++ `recOn]
  return out

def badProj (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .proj s _ _ => forbidStructs.contains s
    | _ => false).isSome

def body? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

structure AReach where
  hit : Option (List Name) := none
  seen : NameSet := {}
  visited : Nat := 0
  noBody : Nat := 0
  opaques : Nat := 0

def reach (forbid : List Name) (root : Name) (cap : Nat := 3000000) : MetaM AReach := do
  let env ← getEnv
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i : Nat := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "ENV AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | continue
    let body := body? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques + 1 }
    if badProj ci.type || (body.map badProj).getD false then
      return { out with hit := some (path ++ [`rawProj]) }
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      if forbid.contains u then return { out with hit := some (path ++ [u]) }
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let forbid ← forbidConsts
  for s in forbidStructs do
    unless badProj (.proj s 0 (.bvar 0)) do throwError "ENV AUDIT FAILED: raw {s} proj missed"
  if badProj (.proj ``Prod 0 (.bvar 0)) then throwError "ENV AUDIT FAILED: unrelated raw proj flagged"
  logInfo "ENV CONTROL rawProj: all forbidden structures flagged, Prod not flagged"
  let F := `Tests.Gen5.EnvFixture
  for (c, bad) in [(F ++ `badLaws, true), (F ++ `badOps, true), (F ++ `badTele2, true), (F ++ `badOpsRec, true),
      (F ++ `badT1, true), (F ++ `badND, true), (F ++ `badGetEnvFrame, true), (F ++ `badReadKeeps, true),
      (F ++ `badSnapshot, true), (F ++ `unrelated, false)] do
    let r ← reach forbid c
    if bad && r.hit.isNone then throwError "ENV AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "ENV AUDIT FAILED: detector flags {c}"
    logInfo m!"ENV CONTROL {c}: {toString r.hit}"
  for (c, req) in [(``readsAt_self, [``ReadsAt]), (``ReadsAt.of_envEq, [``ReadsAt]),
      (``ReadsAt.of_frame, [``Tools.ShippingEnvSnapshot.EnvFrame, ``ReadsAt.of_envEq]),
      (``ci_of_readsAt, [``Tools.ShippingEntryReadsLinked.getConstInfo_value]),
      (``envR_of_readsAt, [``Tools.ShippingEntryReadsLinked.getEnv_value]),
      (``machineDefines_of_readsAll, [``Tools.ShippingMachineEntry.MachineDefines, ``ci_of_readsAt,
        ``envR_of_readsAt])] do
    let r ← reach forbid c
    if let some p := r.hit then throwError "ENV AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "ENV AUDIT FAILED {c}: {t} not reached"
    logInfo m!"ENV REACH {c}: no Laws/RefLawsAOps/RefLawsATele/T1Hyp/T1HypND field (named, raw proj, recursor), no GetEnvFrame/ReadKeeps/EnvSnapshot; reaches {req} (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques})"

/-! ## 4. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``readsAt_self, ``ReadsAt.of_envEq, ``ReadsAt.of_frame, ``ci_of_readsAt, ``envR_of_readsAt,
      ``machineDefines_of_readsAll] do
    checkAxioms n

end Tests.Gen5.EnvCheck
