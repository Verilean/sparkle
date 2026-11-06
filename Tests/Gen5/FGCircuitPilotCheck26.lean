import Tools.ShippingFGCircuitS2dKids
set_option autoImplicit false
-- FG circuit pilot S2d check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §32.

/-! # FGCircuitPilotCheck26 (light: each part is a small `run_cmd`)

1. SIGNATURES-A: `KidStartEnv` against an independently written `ExpKS`; mutants: only one conjunct, a conjunct at the END world, environment equality instead of `ReadsAt`, a dropped premise, the profile-free entry, `True`.
2. SIGNATURES-B: `hftCoreCloses_of_kidsK` and `synth_hftPcieOutByte_finalOffLNKK_Z` (14 hypotheses, `hkids` gone, `hkenv`/`hkgates` last, no `MachineDefines` reachable from the new hypotheses).
3. CONTROLS: kernel-decided name facts the supply uses.
4. REMAINING, AXIOMS. -/
namespace Tests.Gen5.FGCircuitPilotCheck26
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt)
open Tools.ShippingFGCircuitS2dKids
open Sparkle.Compiler.Elab

/-! ## 1. KidStartEnv, independently -/

section KS
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- the child-start environment facts, written again -/
def ExpKS (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' →
    ReadsAt e cref w ∧ GetEnvProfileAt mctx' mref cctx' cref w
def KSOnlyReads (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' → ReadsAt e cref w
def KSOnlyProf (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' → GetEnvProfileAt mctx' mref cctx' cref w
def KSEndReads (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' →
    ReadsAt e cref w' ∧ GetEnvProfileAt mctx' mref cctx' cref w
def KSEndProf (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' →
    ReadsAt e cref w ∧ GetEnvProfileAt mctx' mref cctx' cref w'
def KSEq (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' →
    envAt cref w = e ∧ GetEnvProfileAt mctx' mref cctx' cref w
def KSNoCache (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' →
    ReadsAt e cref w ∧ GetEnvProfileAt mctx' mref cctx' cref w
def KSOff (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinationalOff c) mctx' mref cctx' cref w y w' →
    ReadsAt e cref w ∧ GetEnvProfileAt mctx' mref cctx' cref w
def KSTrue (_ : RefLawsAOps MkRefd mref cref) (_ : Environment) (_ : Name) : Prop := True
end KS

def normOnce (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if c == ``KidStartEnv || (`Tests.Gen5.FGCircuitPilotCheck26).isPrefixOf c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:5] do
    e ← normOnce e
  return e
def sameTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  let a ← norm ty
  let e ← norm exp
  unless ← withDefault (isDefEq a e) do throwError "{what}: type is NOT the expected statement"
def diffTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  let a ← norm ty
  let e ← norm exp
  if a == e then throwError "{what}: the MUTANT is the same expression"
  if ← withReducible (isDefEq a e) then throwError "{what}: the MUTANT was accepted"
def tyOf (n : Name) : MetaM Lean.Expr := do
  let ci ← getConstInfo n
  unless ci.levelParams.isEmpty do throwError "{n}: level parameters"
  pure ci.type

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS2dKids
  let Q := `Tests.Gen5.FGCircuitPilotCheck26
  sameTy "KidStartEnv" (C (X ++ `KidStartEnv)) (C (Q ++ `ExpKS))
  let mut nm : Nat := 0
  for mu in ["KSOnlyReads", "KSOnlyProf", "KSEndReads", "KSEndProf", "KSEq", "KSNoCache", "KSOff", "KSTrue"] do
    diffTy s!"KidStartEnv vs {mu}" (C (X ++ `KidStartEnv)) (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT26 SIGNATURES-A: KidStartEnv matches the independently written ExpKS (for every full-entry run of the child in a RealChildA start world w: ReadsAt e at w and GetEnvProfileAt at w); {nm} mutants rejected (ReadsAt only, profile only, ReadsAt at the end world, profile at the end world, environment equality instead of ReadsAt, the cache premise dropped, the profile-free entry, True)"

/-! ## 2. the closing and the final statement -/

partial def binderNames : Lean.Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

/-- the constants reachable from the value of `n` through definitions of this development (bounded) -/
partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | some (.defnInfo d) =>
        if (`Tools).isPrefixOf n || (`Sparkle).isPrefixOf n then reach env (d.value.getUsedConstants.toList ++ d.type.getUsedConstants.toList ++ rest) seen
        else reach env rest seen
      | _ => reach env rest seen

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2dKids
  let mut nm : Nat := 0
  let t ← tyOf (X ++ `hftCoreCloses_of_kidsK)
  let names := binderNames (← instantiateMVars t) |>.map (·.toString)
  let exp0 := ["mctx", "mref", "cctx", "cref", "L", "w", "hstart", "hcell", "lvl", "hrH", "hrT", "hg", "hke"]
  unless names == exp0 do throwError "hftCoreCloses_of_kidsK binders: {names}"
  let uses := t.getUsedConstants
  for c in [``Tools.ShippingGen2.Start, ``HftKidsStartEnv, ``HftKidsGates, ``Tools.ShippingFGCircuitCover.RootReader, ``Tools.ShippingFGCircuitS1zClose.HftCoreCloses] do
    unless uses.contains c do throwError "hftCoreCloses_of_kidsK does not mention {c}"
  for bad in [``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingChildRunAKids.MachineClosesAtA, ``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine] do
    if uses.contains bad then throwError "hftCoreCloses_of_kidsK mentions {bad}"
  nm := nm + 2
  let t2 ← tyOf (X ++ `synth_hftPcieOutByte_finalOffLNKK_Z)
  let some ty2 ← unfoldDefinition? t2 | throwError "the instance's type is not a definition"
  let hs ← forallTelescope ty2 fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, ← instantiateMVars d.type)]
    return hs
  let expected := ["hlink", "L", "lvl", "env₀", "hstart", "hr", "hcell", "hchk", "hreadH", "hreadT", "hcd", "htop", "hkenv", "hkgates"]
  unless hs.map (·.1) == expected do throwError "hypotheses are {hs.map (·.1)}, expected {expected}"
  for gone in ["hkids", "hclL", "hcl", "hgate", "hnoraw", "hdRun", "hsrc", "hhead"] do
    if (hs.map (·.1)).contains gone then throwError "{gone} is a hypothesis"
  let some (_, hke) := hs.find? (·.1 == "hkenv") | throwError "hkenv missing"
  let some (_, hkg) := hs.find? (·.1 == "hkgates") | throwError "hkgates missing"
  unless hke.getUsedConstants.contains ``HftKidsStartEnv do throwError "hkenv is not HftKidsStartEnv"
  unless hkg.getUsedConstants.contains ``HftKidsGates do throwError "hkgates is not HftKidsGates"
  -- no all-world reflection is reachable from the two new hypotheses
  let env ← getEnv
  let r := reach env [``HftKidsStartEnv, ``HftKidsGates] {}
  for bad in [``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine, ``Tools.ShippingMachineEntry.MachineCloses] do
    if r.contains bad then throwError "{bad} is reachable from hkenv/hkgates"
  unless r.contains ``Tools.ShippingFGCircuitS1oHead.GetEnvProfileAt do throwError "hkenv does not reach GetEnvProfileAt"
  unless r.contains ``Tools.ShippingFGCircuitFinal4.EntryGates do throwError "hkgates does not reach EntryGates"
  -- different from the S2a statement
  let t3 ← tyOf (`Tools.ShippingFGCircuitS2aClose ++ `synth_hftPcieOutByte_finalOffLNK_Z)
  unless (← norm t3) != (← norm t2) do throwError "finalOffLNKK_Z is the finalOffLNK_Z statement"
  nm := nm + 6
  logInfo m!"FGCIRCUIT26 SIGNATURES-B: hftCoreCloses_of_kidsK (binders {exp0}; mentions Start, HftKidsStartEnv, HftKidsGates, RootReader, HftCoreCloses; no MachineDefines / HftKidsDefine / MachineCloses / MachineClosesAtA) and synth_hftPcieOutByte_finalOffLNKK_Z: {nm} structural checks; hkids is gone, hkenv and hkgates are last; MachineDefines is not reachable from the two new hypotheses (reach set {r.size})"
  logInfo m!"FGCIRCUIT26 HYPS: HftFinalStmtOffLNKK Ob CV = {expected}: {hs.length} explicit hypotheses (S2a had 13 ending in hkids)"

/-! ## 3. CONTROLS (kernel-decided; the build fails if one flips) -/

open Tools.ShippingFGCircuitS1kStmt in
theorem ctl_http_name : hftHttp = ``Sparkle.IP.Net.HTTP.httpGetByte := by decide +kernel
open Tools.ShippingFGCircuitS1kStmt in
theorem ctl_tlp_name : hftTlp = ``Sparkle.IP.Bus.PCIe.tlpCplByte := by decide +kernel
open Tools.ShippingFGCircuitS1kStmt in
theorem ctl_kids_distinct : hftHttp ≠ hftTlp := by decide +kernel
open Tools.ShippingFGCircuitS1kStmt in
theorem ctl_kids_not_root : hftHttp ≠ hftRoot ∧ hftTlp ≠ hftRoot := by decide +kernel
open Tools.ShippingFGCircuitS1kStmt in
theorem ctl_swapped_not_same : ¬ (hftHttp = ``Sparkle.IP.Bus.PCIe.tlpCplByte) := by decide +kernel
open Tools.ShippingFGCircuitS1kStmt in
theorem ctl_root_not_kid : ¬ (hftRoot = hftHttp ∨ hftRoot = hftTlp) := by decide +kernel

run_cmd liftTermElabM do
  let Q := `Tests.Gen5.FGCircuitPilotCheck26
  let env ← getEnv
  let names := ["ctl_http_name", "ctl_tlp_name", "ctl_kids_distinct", "ctl_kids_not_root", "ctl_swapped_not_same", "ctl_root_not_kid"]
  for n in names do
    unless env.contains (Q ++ Name.mkSimple n) do throwError "{n} missing"
    for ax in ← Lean.collectAxioms (Q ++ Name.mkSimple n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{n} uses {ax}"
  logInfo m!"FGCIRCUIT26 CONTROLS: {names.length} kernel-decided controls (hftHttp / hftTlp are the two called declarations, distinct from each other and from the root; a swapped name is rejected)"

/-! ## 4. REMAINING, AXIOMS -/

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2dKids
  let a ← getConstInfo (X ++ `KidStartEnv)
  let pp ← try pure (toString (← ppExpr a.value!)) catch _ => pure "<unprintable>"
  logInfo m!"FGCIRCUIT26 REMAINING hkenv : HftKidsStartEnv L.O (envAt cref w) [FG D.T-4k] := KidStartEnv O e hftHttp ∧ KidStartEnv O e hftTlp, KidStartEnv O e c := {pp}"
  logInfo m!"FGCIRCUIT26 REMAINING hkgates : HftKidsGates (envAt cref w) [FG D.T-4g] := EntryGates e hftHttp ∧ EntryGates e hftTlp (the refusal half of the reader for the two called declarations; machineShape? is hreadH/hreadT)"

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2dKids
  let names : List Name := [X ++ `machineDefinesLinked_of_readerE, X ++ `machineChild_ifaceK, X ++ `machineChild_of_realK, X ++ `hft_kid_ifaceK, X ++ `hft_closesAtK,
    X ++ `hftCoreCloses_of_kidsK, X ++ `synth_hftPcieOutByte_finalOffLNKK, X ++ `synth_hftPcieOutByte_finalOffLNKK_Z, X ++ `synth_hftPcieOutByte_finalOffLNKK_Y, X ++ `synth_hftPcieOutByte_finalOffLNKK_X]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT26 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck26
