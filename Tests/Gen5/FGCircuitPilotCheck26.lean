import Tools.ShippingFGCircuitS2dKids
import Tests.Gen5.FGCircuitCmp
set_option autoImplicit false
-- FG circuit pilot S2d check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §32.

/-! # FGCircuitPilotCheck26 (light: each part is a small `run_cmd`)

1. SIGNATURES-A: `KidStartEnv` against an independently written `ExpKS`; mutants: only one conjunct, a conjunct at the END world, environment equality instead of `ReadsAt`, a dropped premise, the profile-free entry, `True`.
2. SIGNATURES-B: `hftCoreCloses_of_kidsK` and `synth_hftPcieOutByte_finalOffLNKK_Z` (14 hypotheses, `hkids` gone, `hkenv`/`hkgates` last, no `MachineDefines` reachable from the new hypotheses WITHIN the reach walk below — a walk over the types and values of `defnInfo` under `Tools`/`Sparkle`; it does not unfold inductive constructors or theorems, so this is not a claim about the whole dependency closure).
2b. SIGNATURES-C (S2h): the COMPLETE types of `machineDefinesLinked_of_readerE`, `hftCoreCloses_of_kidsK` and `synth_hftPcieOutByte_finalOffLNKK_Z` against independently written expected types (`isDefEq`, binder kinds too; the real types are normalised once and compared with every mutant); mutants: the environment of `hkenv`/`hkgates` moved to the end world or to an independent environment, another reference / context, swapped child names or shapes, the profile condition missing, the old entry, a changed artifact / output / design / conclusion. WHENEVER the final wrapper changes, this check must be updated in the same commit.
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
open Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Tools.ShippingFGCircuitS1uSrc (HftRootLink)
open Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kPkg Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1tFinal
open Tools.ShippingFGCircuitLinked (MachineDefinesLinked)
open Tools.ShippingFGCircuitFinal4 (EntryGates)

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
  Tests.Gen5.FGCircuitCmp.normCommon e

def litBool : Lean.Expr → Option Bool
  | .const ``Bool.true _ => some true
  | .const ``Bool.false _ => some false
  | _ => none
def iteStep (e : Lean.Expr) : Option Lean.Expr :=
  if e.isAppOfArity ``ite 5 then
    let c := e.getArg! 1
    if c.isAppOfArity ``Eq 3 then
      match litBool (c.getArg! 1), c.getArg! 2 with
      | some true, .const ``Bool.true _ => some (e.getArg! 3)
      | some false, .const ``Bool.true _ => some (e.getArg! 4)
      | _, _ => none
    else none
  else none
def normOnce2 (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let some e' := iteStep e then return .visit e'
    if let .const c _ := e.getAppFn then
      if c == ``KidStartEnv || c == ``HftKidsStartEnv || c == ``HftKidsGates || c == ``Tools.ShippingFGCircuitS2dKids.HftFinalStmtOffLNKK || (`Tests.Gen5.FGCircuitPilotCheck26).isPrefixOf c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm2 (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:6] do
    e ← normOnce2 e
  Tests.Gen5.FGCircuitCmp.normCommon e
/-- ONE criterion (`FGCircuitCmp.stmtEq`) for the expected statement and for every mutant; both sides go through the same `norm` -/
def sameTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  Tests.Gen5.FGCircuitCmp.checkSame what (← norm ty) (← norm exp)
def diffTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  Tests.Gen5.FGCircuitCmp.checkDiff what (← norm ty) (← norm exp)
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


/-! ## 2b. the complete expected types, written independently (SIGNATURES-C) -/

abbrev W := Void IO.RealWorld
abbrev Mod := Sparkle.IR.AST.Module
abbrev Cx := Meta.Context
abbrev Rf1 := ST.Ref IO.RealWorld Meta.State
abbrev Cc := Core.Context
abbrev Rf2 := ST.Ref IO.RealWorld Core.State
def NmRoot : Name := `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte
def NmHttp : Name := `Sparkle.IP.Net.HTTP.httpGetByte
def NmTlp : Name := `Sparkle.IP.Bus.PCIe.tlpCplByte
def ZS : W → W → W := fun w _ => w
def ZE : W → W → W := fun _ w' => w'
def ShE : SigShape := { args := [.bits 8, .bool, .bool, .bits 32, .bits 16], res := .one (.bits 8) }
noncomputable def HttpData : MachineData := Sparkle.IP.Net.HTTP.httpGetByte.machineData
noncomputable def TlpData : MachineData := Sparkle.IP.Bus.PCIe.tlpCplByte.machineData
noncomputable def RootData : MachineData := synth_hftPcieOutByte.machineData
noncomputable def OtherData : MachineData := Sparkle.Tests.SignalLoopTest.counterLoop.machineData
/-- `P` is a premise iff `b` (no vacuous `True →` when it is absent) -/
def Pre (b : Bool) (P R : Prop) : Prop := if b then (P → R) else R
def EntryOf (diag : Bool) (X : Name) : MetaM (Mod × Design) :=
  if diag then synthesizeCombinational X else synthesizeCombinationalOff X

/-- the children's start-environment hypothesis, written again (two `ExpKS`) -/
def ExpKidsEnv {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpKS O e NmHttp ∧ ExpKS O e NmTlp
def ExpKidsEnvSwapped {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpKS O e NmTlp ∧ ExpKS O e NmHttp
def ExpKidsEnvHttp {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpKS O e NmHttp ∧ ExpKS O e NmHttp
def ExpKidsEnvNoProf {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  KSOnlyReads O e NmHttp ∧ KSOnlyReads O e NmTlp
def ExpKidsEnvNoReads {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  KSOnlyProf O e NmHttp ∧ KSOnlyProf O e NmTlp
def ExpKidsEnvOff {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  KSOff O e NmHttp ∧ KSOff O e NmTlp
def ExpKidsEnvTrue {mref : Rf1} {cref : Rf2} (_ : RefLawsAOps MkRefd mref cref) (_ : Environment) : Prop := True
def ExpKidsGates (e : Environment) (a b : Name) : Prop := EntryGates e a ∧ EntryGates e b

/-- `machineDefinesLinked_of_readerE`: the run-local linked boundary of ONE child run, from the reads at its start world, the head fact, the frame, the reader and the gates.
Knobs: the premises, the worlds the reads / head fact are stated at, the environment of the gates, the shape and the worlds of the conclusion. -/
def ExpReaderE (needReads needHead needFrame needReader needGates : Bool) (rW hW : W → W → W) (gX : Name → Name) (cs : MachineData → MachineData) (c1 c2 : W → W → W) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {lvl : Lean.Expr → Nat} {X : Name} {dd : MachineData} {e : Environment}
    {w w' : W} {M : Mod} {D : Design},
    Pre needReads (ReadsAt e cref (rW w w')) (
    Pre needHead (HeadAt X mctx mref cctx cref (hW w w')) (
    Pre needFrame (Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref) (
    Pre needReader (RootReader lvl e X dd) (
    Pre needGates (EntryGates e (gX X)) (
    MachineDefinesLinked mctx mref cctx cref X (cs dd).shape (c1 w w') M D (c2 w w'))))))
def REAL : Prop := ExpReaderE true true true true true ZS ZS (fun x => x) (fun x => x) ZS ZE
def RENoReads : Prop := ExpReaderE false true true true true ZS ZS (fun x => x) (fun x => x) ZS ZE
def RENoHead : Prop := ExpReaderE true false true true true ZS ZS (fun x => x) (fun x => x) ZS ZE
def RENoFrame : Prop := ExpReaderE true true false true true ZS ZS (fun x => x) (fun x => x) ZS ZE
def RENoReader : Prop := ExpReaderE true true true false true ZS ZS (fun x => x) (fun x => x) ZS ZE
def RENoGates : Prop := ExpReaderE true true true true false ZS ZS (fun x => x) (fun x => x) ZS ZE
def REReadsEnd : Prop := ExpReaderE true true true true true ZE ZS (fun x => x) (fun x => x) ZS ZE
def REHeadEnd : Prop := ExpReaderE true true true true true ZS ZE (fun x => x) (fun x => x) ZS ZE
def REGatesOther : Prop := ExpReaderE true true true true true ZS ZS (fun _ => NmHttp) (fun x => x) ZS ZE
def REOtherShape : Prop := ExpReaderE true true true true true ZS ZS (fun x => x) (fun _ => OtherData) ZS ZE
def REConclSwap : Prop := ExpReaderE true true true true true ZS ZS (fun x => x) (fun x => x) ZE ZS
def REConclStart : Prop := ExpReaderE true true true true true ZS ZS (fun x => x) (fun x => x) ZS ZS
/-- the reads are about an independent environment -/
def REOtherEnv : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {lvl : Lean.Expr → Nat} {X : Name} {dd : MachineData} {e : Environment} {e' : Environment}
    {w w' : W} {M : Mod} {D : Design},
    ReadsAt e' cref w → HeadAt X mctx mref cctx cref w → Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    RootReader lvl e X dd → EntryGates e X → MachineDefinesLinked mctx mref cctx cref X dd.shape w M D w'
def REConclTrue : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {lvl : Lean.Expr → Nat} {X : Name} {dd : MachineData} {e : Environment}
    {w w' : W} {M : Mod} {D : Design},
    ReadsAt e cref w → HeadAt X mctx mref cctx cref w → Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref →
    RootReader lvl e X dd → EntryGates e X → True

/-- `hftCoreCloses_of_kidsK`. Knobs (each mutant turns one): the children's environment hypothesis `kenv`, the readers' names and data, the world the environments `envAt cref _` are taken at
(readers `fR`, gates `fG`, `kenv` `fK`), the premises, the conclusion's root world / context / reference. -/
def ExpCoreK (kenv : ∀ {mref : Rf1} {cref : Rf2}, RefLawsAOps MkRefd mref cref → Environment → Prop)
    (hn tn : Name) (hd td : MachineData) (gn gt : Name)
    (needStart needCell needR needG needK concl : Bool)
    (fR fG fK : W → W) (fW : W → W) (fM : Cx → Cx) (fRf : Rf1 → Rf1) (fC : Cc → Cc) (fF : Rf2 → Rf2) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : Laws mref cref) {w : W},
    Pre needStart (Start L mctx cctx w) (
    Pre needCell (CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (
    ∀ {lvl : Lean.Expr → Nat},
    Pre needR (RootReader lvl (envAt cref (fR w)) hn hd) (
    Pre needR (RootReader lvl (envAt cref (fR w)) tn td) (
    Pre needG (ExpKidsGates (envAt cref (fG w)) gn gt) (
    Pre needK (kenv L.O (envAt cref (fK w))) (
    if concl then HftCoreCloses (fM mctx) (fRf mref) (fC cctx) (fF cref) (fW w) else True))))))
def idW : W → W := fun w => w
def idF {α : Type} : α → α := fun x => x
def CK_True : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CK_KenvSwapped : Prop := ExpCoreK ExpKidsEnvSwapped NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CK_KenvHttp : Prop := ExpCoreK ExpKidsEnvHttp NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CK_KenvNoProf : Prop := ExpCoreK ExpKidsEnvNoProf NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CK_KenvNoReads : Prop := ExpCoreK ExpKidsEnvNoReads NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CK_KenvOff : Prop := ExpCoreK ExpKidsEnvOff NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CK_KenvTrue : Prop := ExpCoreK ExpKidsEnvTrue NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CK_ReadersSwapped : Prop := ExpCoreK ExpKidsEnv NmTlp NmHttp TlpData HttpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CK_ReaderShapes : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp TlpData HttpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CK_ReaderRoot : Prop := ExpCoreK ExpKidsEnv NmRoot NmTlp RootData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CK_GatesSwapped : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmTlp NmHttp true true true true true true idW idW idW idW idF idF idF idF
def CK_GatesHttp : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmHttp true true true true true true idW idW idW idW idF idF idF idF
def CK_NoStart : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp false true true true true true idW idW idW idW idF idF idF idF
def CK_NoCell : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true false true true true true idW idW idW idW idF idF idF idF
def CK_NoReaders : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true false true true true idW idW idW idW idF idF idF idF
def CK_NoGates : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true false true true idW idW idW idW idF idF idF idF
def CK_NoKenv : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true false true idW idW idW idW idF idF idF idF
def CK_NoConcl : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true false idW idW idW idW idF idF idF idF
/-- the environments of the readers / the gates / `hkenv` are taken at an INDEPENDENT world `a` -/
def CK_ReadersIndep : Prop := ∀ {a : W}, ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true (fun _ => a) idW idW idW idF idF idF idF
def CK_GatesIndep : Prop := ∀ {a : W}, ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW (fun _ => a) idW idW idF idF idF idF
def CK_KenvIndep : Prop := ∀ {a : W}, ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW (fun _ => a) idW idF idF idF idF
def CK_ConclWorld : Prop := ∀ {a : W}, ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW (fun _ => a) idF idF idF idF
def CK_CtxM : Prop := ∀ {a : Cx}, ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW (fun _ => a) idF idF idF
def CK_CtxC : Prop := ∀ {a : Cc}, ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF (fun _ => a) idF
def CK_RefM : Prop := ∀ {a : Rf1}, ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF (fun _ => a) idF idF
def CK_RefC : Prop := ∀ {a : Rf2}, ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF (fun _ => a)

/-- `HftFinalStmtOffLNKK`. Knobs: the entry (`diag`), the carrier of the artifact (`oldArt`), the premises, the children's hypotheses `kenv`/`kg` and the worlds their environments are taken at
(`gW`: the gates, `kW`: `kenv`), the root / post root / output shape, the world of `hcd` / of the conclusion, the reference / context / design the post run is stated at, and which conjunct of the conclusion is present. -/
def ExpFinalKK (Ob : Environment → Prop) (CV : CDRel) (kenv : ∀ {mref : Rf1} {cref : Rf2}, RefLawsAOps MkRefd mref cref → Environment → Prop)
    (kg : Environment → Prop) (diag oldArt needHcd needTop needKenv needKg c1 c2 : Bool)
    (gW kW : W → W → W) (root postRoot : Name) (sh : SigShape) (hw cw : W → W → W)
    (fM : Cx → Cx) (fR : Rf1 → Rf1) (fC : Cc → Cc) (fF : Rf2 → Rf2) (fD : Design → Design) : Prop :=
  HftRootLink →
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Start L mctx cctx w →
    RunsTo (EntryOf diag root) mctx mref cctx cref w (b, D') w' →
    CellPrem Tools.ShippingChildFresh.MkRefd mref cref →
    CheckedStart lvl env₀ cref w root hftRootType hftRootValue RootData →
    RootReader lvl (envAt cref w) NmHttp HttpData →
    RootReader lvl (envAt cref w) NmTlp TlpData →
    Pre needHcd (Ob (envAt cref (hw w w'))) (
    Pre needTop (∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) NmRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p) (
    Pre needKenv (kenv L.O (envAt cref (kW w w'))) (
    Pre needKg (kg (envAt cref (gW w w'))) (
    (if c1 then (∃ raw, PostRunOff (fM mctx) (fR mref) (fC cctx) (fF cref) w postRoot (fD D') b raw) else True) ∧
    (if c2 then (∃ (mm : MonoTy sh) (p : Pkg ι (fun _ => defaultDomain)),
      (if oldArt then RootArtifactMono (envAt cref (cw w w')) (GPt (ι := ι) lvl (envAt cref (cw w w'))) (PostRunOff (fM mctx) (fR mref) (fC cctx) (fF cref) w postRoot (fD D')) NmRoot sh mm b (fD D') p
       else RootArtifactMonoV CV (envAt cref (cw w w')) (GPt (ι := ι) lvl (envAt cref (cw w w'))) (PostRunOff (fM mctx) (fR mref) (fC cctx) (fF cref) w postRoot (fD D')) NmRoot sh mm b (fD D') p)) else True)))))
def kgReal (e : Environment) : Prop := ExpKidsGates e NmHttp NmTlp
def kgSwapped (e : Environment) : Prop := ExpKidsGates e NmTlp NmHttp
def kgHttp (e : Environment) : Prop := ExpKidsGates e NmHttp NmHttp
def kgTrue (_ : Environment) : Prop := True

def FK (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKKenvEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZE NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKGatesEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZE ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKBothEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZE ZE NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKDiag (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal true false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKOldArt (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false true true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKNoHcd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false false true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKNoTop (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true false true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKNoKenv (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true false true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKNoKg (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true false true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKNoC1 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true false true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKNoC2 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true false ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKNoConcl (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true false false ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKKenvSwapped (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnvSwapped kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKKenvHttp (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnvHttp kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKKenvNoProf (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnvNoProf kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKKenvNoReads (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnvNoReads kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKKenvOff (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnvOff kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKKenvTrue (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnvTrue kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKKgSwapped (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgSwapped false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKKgHttp (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgHttp false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKKgTrue (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgTrue false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF idF
def FKRoot (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmHttp NmRoot ShE ZS ZS idF idF idF idF idF
def FKPostRoot (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmRoot NmHttp ShE ZS ZS idF idF idF idF idF
def FKOutput (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmRoot NmRoot { ShE with res := .one (.bits 16) } ZS ZS idF idF idF idF idF
def FKHcdEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZE ZS idF idF idF idF idF
def FKConclEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZE idF idF idF idF idF
def FKRefM (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Rf1}, ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF (fun _ => a) idF idF idF
def FKRefC (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Rf2}, ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF (fun _ => a) idF
def FKCtxM (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Cx}, ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS (fun _ => a) idF idF idF idF
def FKCtxC (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Cc}, ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF (fun _ => a) idF idF
def FKDesign (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Design}, ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true true ZS ZS NmRoot NmRoot ShE ZS ZS idF idF idF idF (fun _ => a)
/-- the carrier / obligation of the S2a final statement's neighbours -/
def FKCarrierY : Prop := FK HftObCDZ cdvY
def FKCarrierOld : Prop := FK HftObCDZ cdvOld
def FKObY : Prop := FK HftObCDY cdvZ

partial def binderInfos : Lean.Expr → List BinderInfo
  | .forallE _ _ b bi => bi :: binderInfos b
  | _ => []

/-- `a` is the normal form of a real type, computed once and compared with every expected statement / mutant -/
def sameN (what : String) (a exp : Lean.Expr) : MetaM Unit := do
  Tests.Gen5.FGCircuitCmp.checkSame what a (← norm2 exp)
def diffN (what : String) (a exp : Lean.Expr) : MetaM Unit := do
  Tests.Gen5.FGCircuitCmp.checkDiff what a (← norm2 exp)

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS2dKids
  let Q := `Tests.Gen5.FGCircuitPilotCheck26
  let q (n : String) : Lean.Expr := mkConst (Q ++ Name.mkSimple n)
  -- machineDefinesLinked_of_readerE
  let reN ← norm2 (← tyOf (X ++ `machineDefinesLinked_of_readerE))
  sameN "machineDefinesLinked_of_readerE" reN (q "REAL")
  let mut nm0 : Nat := 0
  for mu in ["RENoReads", "RENoHead", "RENoFrame", "RENoReader", "RENoGates", "REReadsEnd", "REHeadEnd", "REGatesOther", "REOtherShape", "REConclSwap", "REConclStart", "REOtherEnv", "REConclTrue"] do
    diffN s!"machineDefinesLinked_of_readerE vs {mu}" reN (q mu); nm0 := nm0 + 1
  -- hftCoreCloses_of_kidsK
  let coreN ← norm2 (← tyOf (X ++ `hftCoreCloses_of_kidsK))
  sameN "hftCoreCloses_of_kidsK" coreN (q "CK_True")
  let mut nm1 : Nat := 0
  for mu in ["CK_KenvSwapped", "CK_KenvHttp", "CK_KenvNoProf", "CK_KenvNoReads", "CK_KenvOff", "CK_KenvTrue", "CK_ReadersSwapped", "CK_ReaderShapes", "CK_ReaderRoot", "CK_GatesSwapped", "CK_GatesHttp",
      "CK_NoStart", "CK_NoCell", "CK_NoReaders", "CK_NoGates", "CK_NoKenv", "CK_NoConcl", "CK_ReadersIndep", "CK_GatesIndep", "CK_KenvIndep", "CK_ConclWorld", "CK_CtxM", "CK_CtxC", "CK_RefM", "CK_RefC"] do
    diffN s!"hftCoreCloses_of_kidsK vs {mu}" coreN (q mu); nm1 := nm1 + 1
  -- the final statement
  let finN ← norm2 (← tyOf (X ++ `synth_hftPcieOutByte_finalOffLNKK_Z))
  sameN "synth_hftPcieOutByte_finalOffLNKK_Z" finN (mkApp2 (q "FK") (C ``HftObCDZ) (C ``cdvZ))
  let mut nm2 : Nat := 0
  for mu in ["FKCarrierY", "FKCarrierOld", "FKObY"] do
    diffN s!"finalOffLNKK_Z vs {mu}" finN (q mu); nm2 := nm2 + 1
  for mu in ["FKKenvEnd", "FKGatesEnd", "FKBothEnd", "FKDiag", "FKOldArt", "FKNoHcd", "FKNoTop", "FKNoKenv", "FKNoKg", "FKNoC1", "FKNoC2", "FKNoConcl",
      "FKKenvSwapped", "FKKenvHttp", "FKKenvNoProf", "FKKenvNoReads", "FKKenvOff", "FKKenvTrue", "FKKgSwapped", "FKKgHttp", "FKKgTrue",
      "FKRoot", "FKPostRoot", "FKOutput", "FKHcdEnd", "FKConclEnd", "FKRefM", "FKRefC", "FKCtxM", "FKCtxC", "FKDesign"] do
    diffN s!"finalOffLNKK_Z vs {mu}" finN (mkApp2 (q mu) (C ``HftObCDZ) (C ``cdvZ)); nm2 := nm2 + 1
  logInfo m!"FGCIRCUIT26 SIGNATURES-C: the complete types of machineDefinesLinked_of_readerE, hftCoreCloses_of_kidsK and synth_hftPcieOutByte_finalOffLNKK_Z match the independently written expected types (isDefEq, binder kinds too; the real types normalised once); mutants rejected: machineDefinesLinked_of_readerE {nm0} (a premise missing, the reads / head fact at the end world, the gates of another declaration, another shape, the conclusion's worlds swapped or equal, reads about an independent environment, a True conclusion), hftCoreCloses_of_kidsK {nm1} (the children's environment hypothesis swapped / both httpGetByte / without the profile condition / without ReadsAt / the profile-free entry / True, readers swapped or with the wrong shapes or the root, gates swapped, a premise missing, the conclusion missing, the readers' / gates' / hkenv environment taken at an independent world, another conclusion world / context / reference), final statement {nm2} (another carrier / obligation, hkenv or hkgates environment at the END world or both, the diagnostic entry, the old artifact, a premise missing, hkenv / hkgates swapped / one name twice / without the profile condition / without ReadsAt / profile-free entry / True, another root / post root / output, hcd or conclusion at the end world, another reference / context / design, a missing conjunct)"

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
