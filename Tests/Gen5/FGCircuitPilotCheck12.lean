import Tests.Gen5.FGCircuitPilotCheck10
import Tools.ShippingFGCircuitS1nRoots
set_option autoImplicit false
-- FG circuit pilot S1n check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §18.

/-! # FGCircuitPilotCheck12

1. SIGNATURES: complete expected types, written independently of the theorems, for the two common structures' constructors (`RootExtern.mk`, `RootEnvFacts.mk`), `entryOfDecl_inl`, `checkedEnv_of_inl`, and per root (shift4Loop, counterEnableLoop, arbiterSignal) the gates, `dataOfAt`, `checkedEnv_of_finite` and `X_final11`; one-point MUTANTS rejected (another root's data / value / type, the peeled body replaced by the value, the polarity of the instance predicate, `proj` asked at another name, the inliner argument, dropped hypotheses, END-WORLD controls = the same run's end world w').
2. HYPS: the explicit hypotheses of the three finals, the field names of the two structures.
3. AXIOMS of every new name.
4. SNAPSHOT12: the named facts EVALUATED on this build's ONE environment in `MetaM` (an evaluation, not a supply of the hypotheses): the quote `arbiterInlinedValue` equals `userInliner` of the arbiter's value; the gates and the data depend on the instance predicate only at the peeled bodies and on `proj` only at the one name (probed with altered arguments); controls. -/
namespace Tests.Gen5.FGCircuitPilotCheck12
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4 Tools.ShippingFGCircuitRoots4
open Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1lReader Tools.ShippingFGCircuitS1iRoots Tools.ShippingFGCircuitS1nRoots
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved coreHead)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingGen5Env (ReadsAt)
open Sparkle.Compiler.Elab Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tests.Gen5.FGCircuitPilotCheck5 (W GPd explicitBinders binderInfos dataExprOf shapeExprOf literalExpr)
open Tests.Gen5.FGCircuitPilotCheck7 (ZS ZE)

/-! ## 1. expected statements, written independently -/

/-- the peeled body, written independently -/
def PB (e : Lean.Expr) : Lean.Expr :=
  match mixedGatePeel e with
  | some p => p.2
  | none => e
def idE (e : Lean.Expr) : Lean.Expr := e

/-- `RootExtern.mk`: knobs: the argument of `packTupleInputs`, of `rootFloat`, of `Expr.find?`, the arity of the `runCircuitH` test -/
def ExpExternMk (f1 f2 f3 : Lean.Expr → Lean.Expr) (arity : Nat) : Prop :=
  ∀ {Vi : Lean.Expr},
    Sparkle.Compiler.MachTupleIn.packTupleInputs (f1 Vi) = Vi →
    Sparkle.Compiler.MachRawSurface.rootFloat (f2 Vi) = f2 Vi →
    (f3 Vi).find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH arity) = none →
    RootExtern Vi
def ExternMkTrue := ExpExternMk idE PB PB 8
def MutExternPackPeeled := ExpExternMk PB PB PB 8
def MutExternFloatValue := ExpExternMk idE idE PB 8
def MutExternFindValue := ExpExternMk idE PB idE 8
def MutExternArity := ExpExternMk idE PB PB 7

/-- `RootEnvFacts.mk`: knobs: the declaration the shape is read from (inlined or not), the argument of the inliner at the value, the points of the instance predicate (peeled or not), its polarity, the name `proj` is asked at, whether the inlined-point fact is present -/
def ExpEnvFactsMk (shapeInl : Bool) (uiOnInl : Bool) (g1 g2 : Lean.Expr → Lean.Expr) (pol : Bool) (otherName : Bool) (needInl : Bool) : Prop :=
  ∀ {env₀ : Environment} {X : Name} {T V Vi : Lean.Expr} {dd : MachineData} {pn : Name},
    (∃ d : DefinitionVal, (env₀.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = T ∧ d.value = V) ∧
      machineShape? false [] (.defnInfo { d with value := (if shapeInl then Vi else V), type := T }) (structEnv env₀) = some dd.shape) →
    userInliner env₀ (if uiOnInl then Vi else V) = Vi →
    userInliner env₀ T = T →
    instancePredicate env₀ (g1 V) = pol →
    (if needInl then instancePredicate env₀ (g2 Vi) = pol else True) →
    (structEnv env₀).proj (if otherName then ``Sparkle.Core.Signal.Signal.pure else pn) = none →
    RootEnvFacts env₀ X T V Vi dd pn
def EnvFactsMkTrue := ExpEnvFactsMk true false PB PB false false true
def MutEnvShapeValue := ExpEnvFactsMk false false PB PB false false true
def MutEnvUiOnInl := ExpEnvFactsMk true true PB PB false false true
def MutEnvIpValueUnpeeled := ExpEnvFactsMk true false idE PB false false true
def MutEnvIpInlUnpeeled := ExpEnvFactsMk true false PB idE false false true
def MutEnvPolarity := ExpEnvFactsMk true false PB PB true false true
def MutEnvName := ExpEnvFactsMk true false PB PB false true true
def MutEnvNoInl := ExpEnvFactsMk true false PB PB false false false

/-- `entryOfDecl_inl` -/
def ExpEntryInl (needG1 needG2 needS : Bool) (inlType : Bool) : Prop :=
  ∀ {d : DefinitionVal} {ip : Lean.Expr → Bool} {ui : Lean.Expr → Lean.Expr} {se : StructEnv} {V' T : Lean.Expr},
    ui d.value = V' → ui d.type = T →
    (if needG1 then (certifiedShape? false [] (.defnInfo d)).isNone = true else True) →
    (if needG2 then (mixedCertifiedShape? false [] (.defnInfo d) ip).isNone = true else True) →
    (if needS then (machineShape? false [] (.defnInfo { d with value := V', type := T }) se).isSome = true else True) →
    entryConst true false [] (.defnInfo d) ip ui se = .defnInfo { d with value := V', type := (if inlType then T else d.type) }
def EntryInlTrue := ExpEntryInl true true true true
def MutEntryNoG1 := ExpEntryInl false true true true
def MutEntryNoG2 := ExpEntryInl true false true true
def MutEntryNoShape := ExpEntryInl true true false true
def MutEntryKeepType := ExpEntryInl true true true false

/-- `checkedEnv_of_inl`: knobs: which premise is present, where the shape / data are read (inlined declaration or the original) -/
def ExpCheckedInl (needShape needG1 needG2 needData : Bool) (dataInl : Bool) : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {env₀ : Environment} {X : Name} {T V V' : Lean.Expr} {d : DefinitionVal} {dd : MachineData},
    (env₀.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = T ∧ d.value = V) →
    (if needShape then machineShape? false [] (.defnInfo { d with value := V', type := T }) (structEnv env₀) = some dd.shape else True) →
    userInliner env₀ V = V' → userInliner env₀ T = T →
    (if needG1 then (certifiedShape? false [] (.defnInfo d)).isNone = true ∧ (mixedCertifiedShape? false [] (.defnInfo d) (instancePredicate env₀)).isNone = true else True) →
    (if needG2 then (certifiedShape? false [] (.defnInfo { d with value := V', type := T })).isNone = true ∧
      (mixedCertifiedShape? false [] (.defnInfo { d with value := V', type := T }) (instancePredicate env₀)).isNone = true else True) →
    (if needData then Tools.ShippingGen5DataOf.dataOfAt lvl (.defnInfo (if dataInl then { d with value := V', type := T } else d)) (structEnv env₀) dd.shape = some dd else True) →
    CheckedEnv lvl env₀ X T V dd
def CheckedInlTrue := ExpCheckedInl true true true true true
def MutCInlNoShape := ExpCheckedInl false true true true true
def MutCInlNoG1 := ExpCheckedInl true false true true true
def MutCInlNoG2 := ExpCheckedInl true true false true true
def MutCInlNoData := ExpCheckedInl true true true false true
def MutCInlDataOrig := ExpCheckedInl true true true true false

/-- the gates of a closed declaration: knobs: the type / value, the point of the instance predicate (peeled body or the value), its polarity, whether the premise is present -/
def ExpGates (T V : Lean.Expr) (pt : Lean.Expr → Lean.Expr) (pol : Bool) (needIp : Bool) : Prop :=
  ∀ (d : DefinitionVal), d.type = T → d.value = V →
    ∀ (ip : Lean.Expr → Bool), (if needIp then ip (pt V) = pol else True) →
      (certifiedShape? false [] (.defnInfo d)).isNone = true ∧ (mixedCertifiedShape? false [] (.defnInfo d) ip).isNone = true
def GatesS4True := ExpGates shift4LoopType shift4LoopValue PB false true
def MutGatesS4Pol := ExpGates shift4LoopType shift4LoopValue PB true true
def MutGatesS4Unpeeled := ExpGates shift4LoopType shift4LoopValue idE false true
def MutGatesS4NoIp := ExpGates shift4LoopType shift4LoopValue PB false false
def MutGatesS4Value := ExpGates shift4LoopType counterEnableLoopValue PB false true
def GatesENTrue := ExpGates counterEnableLoopType counterEnableLoopValue PB false true
def MutGatesENPol := ExpGates counterEnableLoopType counterEnableLoopValue PB true true
def MutGatesENUnpeeled := ExpGates counterEnableLoopType counterEnableLoopValue idE false true
def MutGatesENNoIp := ExpGates counterEnableLoopType counterEnableLoopValue PB false false
def MutGatesENValue := ExpGates counterEnableLoopType shift4LoopValue PB false true
def GatesAOTrue := ExpGates arbiterType arbiterValue PB false true
def MutGatesAOPol := ExpGates arbiterType arbiterValue PB true true
def MutGatesAOUnpeeled := ExpGates arbiterType arbiterValue idE false true
def MutGatesAONoIp := ExpGates arbiterType arbiterValue PB false false
def MutGatesAOInlined := ExpGates arbiterType arbiterInlinedValue PB false true
def GatesAITrue := ExpGates arbiterType arbiterInlinedValue PB false true
def MutGatesAIPol := ExpGates arbiterType arbiterInlinedValue PB true true
def MutGatesAIUnpeeled := ExpGates arbiterType arbiterInlinedValue idE false true
def MutGatesAINoIp := ExpGates arbiterType arbiterInlinedValue PB false false
def MutGatesAIOrig := ExpGates arbiterType arbiterValue PB false true

/-- `X_dataOfAt`: knobs: the shape the reader is given, the data asked for, the fuel, the type / value of the declaration, the name `proj` is asked at, whether `RootExtern` is present -/
def ExpDataOfAtG (ddShape ddBody ddOut : MachineData) (T Vi : Lean.Expr) (pn : Name) (fuel : Nat) (xV : Lean.Expr) (needX : Bool) : Prop :=
  ∀ (lvl : Lean.Expr → Nat), lvl ddBody.shape.body = fuel →
    ∀ (d : DefinitionVal), d.type = T → d.value = Vi →
    ∀ (se : StructEnv), se.proj pn = none → (if needX then RootExtern xV else True) →
      Tools.ShippingGen5DataOf.dataOfAt lvl (.defnInfo d) se ddShape.shape = some ddOut
def DS4True := ExpDataOfAtG shift4Loop.machineData shift4Loop.machineData shift4Loop.machineData shift4LoopType shift4LoopValue ``Sparkle.Core.Signal.Signal.register 1000000 shift4LoopValue true
def MutDS4Data := ExpDataOfAtG shift4Loop.machineData shift4Loop.machineData counterEnableLoop.machineData shift4LoopType shift4LoopValue ``Sparkle.Core.Signal.Signal.register 1000000 shift4LoopValue true
def MutDS4Fuel := ExpDataOfAtG shift4Loop.machineData shift4Loop.machineData shift4Loop.machineData shift4LoopType shift4LoopValue ``Sparkle.Core.Signal.Signal.register 1000001 shift4LoopValue true
def MutDS4Name := ExpDataOfAtG shift4Loop.machineData shift4Loop.machineData shift4Loop.machineData shift4LoopType shift4LoopValue ``Sparkle.Core.Signal.Signal.loop 1000000 shift4LoopValue true
def MutDS4NoX := ExpDataOfAtG shift4Loop.machineData shift4Loop.machineData shift4Loop.machineData shift4LoopType shift4LoopValue ``Sparkle.Core.Signal.Signal.register 1000000 shift4LoopValue false
def MutDS4OtherX := ExpDataOfAtG shift4Loop.machineData shift4Loop.machineData shift4Loop.machineData shift4LoopType shift4LoopValue ``Sparkle.Core.Signal.Signal.register 1000000 counterEnableLoopValue true
def DENTrue := ExpDataOfAtG counterEnableLoop.machineData counterEnableLoop.machineData counterEnableLoop.machineData counterEnableLoopType counterEnableLoopValue ``Sparkle.Core.Signal.Signal.loop 1000000 counterEnableLoopValue true
def MutDENData := ExpDataOfAtG counterEnableLoop.machineData counterEnableLoop.machineData shift4Loop.machineData counterEnableLoopType counterEnableLoopValue ``Sparkle.Core.Signal.Signal.loop 1000000 counterEnableLoopValue true
def MutDENFuel := ExpDataOfAtG counterEnableLoop.machineData counterEnableLoop.machineData counterEnableLoop.machineData counterEnableLoopType counterEnableLoopValue ``Sparkle.Core.Signal.Signal.loop 999999 counterEnableLoopValue true
def MutDENName := ExpDataOfAtG counterEnableLoop.machineData counterEnableLoop.machineData counterEnableLoop.machineData counterEnableLoopType counterEnableLoopValue ``Sparkle.Core.Signal.Signal.register 1000000 counterEnableLoopValue true
def MutDENNoX := ExpDataOfAtG counterEnableLoop.machineData counterEnableLoop.machineData counterEnableLoop.machineData counterEnableLoopType counterEnableLoopValue ``Sparkle.Core.Signal.Signal.loop 1000000 counterEnableLoopValue false
def DATrue := ExpDataOfAtG Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData arbiterType arbiterInlinedValue ``Sparkle.Core.Signal.Signal.loop 1000000 arbiterInlinedValue true
def MutDAData := ExpDataOfAtG Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData counterEnableLoop.machineData arbiterType arbiterInlinedValue ``Sparkle.Core.Signal.Signal.loop 1000000 arbiterInlinedValue true
def MutDAFuel := ExpDataOfAtG Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData arbiterType arbiterInlinedValue ``Sparkle.Core.Signal.Signal.loop 1000001 arbiterInlinedValue true
def MutDAUninlined := ExpDataOfAtG Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData arbiterType arbiterValue ``Sparkle.Core.Signal.Signal.loop 1000000 arbiterValue true
def MutDAName := ExpDataOfAtG Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData arbiterType arbiterInlinedValue ``Sparkle.Core.Signal.Signal.register 1000000 arbiterInlinedValue true
def MutDANoX := ExpDataOfAtG Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData arbiterType arbiterInlinedValue ``Sparkle.Core.Signal.Signal.loop 1000000 arbiterInlinedValue false

/-- `X_checkedEnv_of_finite`: knobs: the root, type, value, entry value, data, `proj` name, fuel, which finite premise is present, the value the extern facts are about -/
def ExpCheckedFin (X : Name) (T V Vi : Lean.Expr) (dd ddBody : MachineData) (pn : Name) (fuel : Nat) (xV : Lean.Expr) (needX needF : Bool) : Prop :=
  ∀ (lvl : Lean.Expr → Nat) (env₀ : Environment), lvl ddBody.shape.body = fuel →
    (if needX then RootExtern xV else True) → (if needF then RootEnvFacts env₀ X T V Vi dd pn else True) →
      CheckedEnv lvl env₀ X T V dd
noncomputable abbrev S4M := shift4Loop.machineData
noncomputable abbrev ENM := counterEnableLoop.machineData
noncomputable abbrev ARM := Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData
def ARN : Name := ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def CFS4True := ExpCheckedFin ``shift4Loop shift4LoopType shift4LoopValue shift4LoopValue S4M S4M ``Sparkle.Core.Signal.Signal.register 1000000 shift4LoopValue true true
def MutCFS4Data := ExpCheckedFin ``shift4Loop shift4LoopType shift4LoopValue shift4LoopValue ENM S4M ``Sparkle.Core.Signal.Signal.register 1000000 shift4LoopValue true true
def MutCFS4Val := ExpCheckedFin ``shift4Loop shift4LoopType counterEnableLoopValue shift4LoopValue S4M S4M ``Sparkle.Core.Signal.Signal.register 1000000 shift4LoopValue true true
def MutCFS4Name := ExpCheckedFin ``shift4Loop shift4LoopType shift4LoopValue shift4LoopValue S4M S4M ``Sparkle.Core.Signal.Signal.loop 1000000 shift4LoopValue true true
def MutCFS4Fuel := ExpCheckedFin ``shift4Loop shift4LoopType shift4LoopValue shift4LoopValue S4M S4M ``Sparkle.Core.Signal.Signal.register 999999 shift4LoopValue true true
def MutCFS4NoX := ExpCheckedFin ``shift4Loop shift4LoopType shift4LoopValue shift4LoopValue S4M S4M ``Sparkle.Core.Signal.Signal.register 1000000 shift4LoopValue false true
def MutCFS4NoF := ExpCheckedFin ``shift4Loop shift4LoopType shift4LoopValue shift4LoopValue S4M S4M ``Sparkle.Core.Signal.Signal.register 1000000 shift4LoopValue true false
def CFENTrue := ExpCheckedFin ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ENM ``Sparkle.Core.Signal.Signal.loop 1000000 counterEnableLoopValue true true
def MutCFENData := ExpCheckedFin ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoopValue S4M ENM ``Sparkle.Core.Signal.Signal.loop 1000000 counterEnableLoopValue true true
def MutCFENVal := ExpCheckedFin ``counterEnableLoop counterEnableLoopType shift4LoopValue counterEnableLoopValue ENM ENM ``Sparkle.Core.Signal.Signal.loop 1000000 counterEnableLoopValue true true
def MutCFENName := ExpCheckedFin ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ENM ``Sparkle.Core.Signal.Signal.register 1000000 counterEnableLoopValue true true
def MutCFENFuel := ExpCheckedFin ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ENM ``Sparkle.Core.Signal.Signal.loop 999999 counterEnableLoopValue true true
def MutCFENNoX := ExpCheckedFin ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ENM ``Sparkle.Core.Signal.Signal.loop 1000000 counterEnableLoopValue false true
def MutCFENNoF := ExpCheckedFin ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ENM ``Sparkle.Core.Signal.Signal.loop 1000000 counterEnableLoopValue true false
def CFATrue := ExpCheckedFin ARN arbiterType arbiterValue arbiterInlinedValue ARM ARM ``Sparkle.Core.Signal.Signal.loop 1000000 arbiterInlinedValue true true
def MutCFAData := ExpCheckedFin ARN arbiterType arbiterValue arbiterInlinedValue ENM ARM ``Sparkle.Core.Signal.Signal.loop 1000000 arbiterInlinedValue true true
def MutCFAUninlined := ExpCheckedFin ARN arbiterType arbiterValue arbiterValue ARM ARM ``Sparkle.Core.Signal.Signal.loop 1000000 arbiterValue true true
def MutCFAExternOnValue := ExpCheckedFin ARN arbiterType arbiterValue arbiterInlinedValue ARM ARM ``Sparkle.Core.Signal.Signal.loop 1000000 arbiterValue true true
def MutCFAName := ExpCheckedFin ARN arbiterType arbiterValue arbiterInlinedValue ARM ARM ``Sparkle.Core.Signal.Signal.register 1000000 arbiterInlinedValue true true
def MutCFAFuel := ExpCheckedFin ARN arbiterType arbiterValue arbiterInlinedValue ARM ARM ``Sparkle.Core.Signal.Signal.loop 999999 arbiterInlinedValue true true
def MutCFANoX := ExpCheckedFin ARN arbiterType arbiterValue arbiterInlinedValue ARM ARM ``Sparkle.Core.Signal.Signal.loop 1000000 arbiterInlinedValue false true
def MutCFANoF := ExpCheckedFin ARN arbiterType arbiterValue arbiterInlinedValue ARM ARM ``Sparkle.Core.Signal.Signal.loop 1000000 arbiterInlinedValue true false

/-- `X_final11` (the three roots share the hypotheses of the structures; knobs as in `counterLoop_final11`, plus the root of the head, the extern value, the facts' arguments) -/
def ExpF11S (hhw rdw : W → W → W) (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (headRoot : Name) (lvlBody : Lean.Expr) (postRoot : Name)
    (needLvl needX needF : Bool) (xV : Lean.Expr) (fT fV : Lean.Expr) (fdd : MachineData) (fn : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``shift4Loop) mctx mref cctx cref w (b, D') w' →
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead headRoot) mctx mref cctx cref (hhw w w') s w1 → envAt cref w1 = envAt cref (hhw w w')) →
    ReadWorld cref →
    (if needLvl then lvl lvlBody = 1000000 else True) →
    (if needX then RootExtern xV else True) →
    (if needF then RootEnvFacts env₀ ``shift4Loop fT fV fV fdd fn else True) →
    ReadsAt env₀ cref (rdw w w') →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PostRun mctx mref cctx cref w postRoot D') ``shift4Loop shShift4 mm b D' p

def ExpF11S4 (hhw rdw : W → W → W) (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (headRoot : Name) (lvlBody : Lean.Expr) (postRoot : Name)
    (needLvl needX needF : Bool) (xV : Lean.Expr) (fT fV fVi : Lean.Expr) (fdd : MachineData) (fn : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``shift4Loop) mctx mref cctx cref w (b, D') w' →
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead headRoot) mctx mref cctx cref (hhw w w') s w1 → envAt cref w1 = envAt cref (hhw w w')) →
    ReadWorld cref →
    (if needLvl then lvl lvlBody = 1000000 else True) →
    (if needX then RootExtern xV else True) →
    (if needF then RootEnvFacts env₀ ``shift4Loop fT fV fVi fdd fn else True) →
    ReadsAt env₀ cref (rdw w w') →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PostRun mctx mref cctx cref w postRoot D') ``shift4Loop shShift4 mm b D' p

def ExpF11EN (hhw rdw : W → W → W) (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (headRoot : Name) (lvlBody : Lean.Expr) (postRoot : Name)
    (needLvl needX needF : Bool) (xV : Lean.Expr) (fT fV fVi : Lean.Expr) (fdd : MachineData) (fn : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterEnableLoop) mctx mref cctx cref w (b, D') w' →
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead headRoot) mctx mref cctx cref (hhw w w') s w1 → envAt cref w1 = envAt cref (hhw w w')) →
    ReadWorld cref →
    (if needLvl then lvl lvlBody = 1000000 else True) →
    (if needX then RootExtern xV else True) →
    (if needF then RootEnvFacts env₀ ``counterEnableLoop fT fV fVi fdd fn else True) →
    ReadsAt env₀ cref (rdw w w') →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shEnable) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PostRun mctx mref cctx cref w postRoot D') ``counterEnableLoop shEnable mm b D' p

def ExpF11A (hhw rdw : W → W → W) (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (headRoot : Name) (lvlBody : Lean.Expr) (postRoot : Name)
    (needLvl needX needF : Bool) (xV : Lean.Expr) (fT fV fVi : Lean.Expr) (fdd : MachineData) (fn : Name) (needB needC : Bool) : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w (b, D') w' →
    (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead headRoot) mctx mref cctx cref (hhw w w') s w1 → envAt cref w1 = envAt cref (hhw w w')) →
    ReadWorld cref →
    (if needLvl then lvl lvlBody = 1000000 else True) →
    (if needX then RootExtern xV else True) →
    (if needF then RootEnvFacts env₀ ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal fT fV fVi fdd fn else True) →
    ReadsAt env₀ cref (rdw w w') →
    (if needB then BoundaryRowsInEnv env₀ else True) → (if needC then ContainsAt env₀ cref w boundaryNames else True) →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (eC env₀ cref w w') (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (eC env₀ cref w w'))
        (PostRun mctx mref cctx cref w postRoot D') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b D' p

def F11S4True := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``shift4Loop S4M.shape.body ``shift4Loop true true true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4HeadEnd := ExpF11S4 (fun _ w' => w') (fun w _ => w) ZS ``shift4Loop S4M.shape.body ``shift4Loop true true true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4LinkEnd := ExpF11S4 (fun w _ => w) (fun _ w' => w') ZS ``shift4Loop S4M.shape.body ``shift4Loop true true true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4ConclEnd := ExpF11S4 (fun w _ => w) (fun w _ => w) ZE ``shift4Loop S4M.shape.body ``shift4Loop true true true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4HeadRoot := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop S4M.shape.body ``shift4Loop true true true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4Data := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``shift4Loop ENM.shape.body ``shift4Loop true true true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4Post := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``shift4Loop S4M.shape.body ``counterEnableLoop true true true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4NoLvl := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``shift4Loop S4M.shape.body ``shift4Loop false true true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4NoX := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``shift4Loop S4M.shape.body ``shift4Loop true false true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4NoF := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``shift4Loop S4M.shape.body ``shift4Loop true true false shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4OtherX := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``shift4Loop S4M.shape.body ``shift4Loop true true true counterEnableLoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4FactsRoot := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``shift4Loop S4M.shape.body ``shift4Loop true true true shift4LoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue S4M ``Sparkle.Core.Signal.Signal.register
def M11S4FactsData := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``shift4Loop S4M.shape.body ``shift4Loop true true true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue ENM ``Sparkle.Core.Signal.Signal.register
def M11S4FactsName := ExpF11S4 (fun w _ => w) (fun w _ => w) ZS ``shift4Loop S4M.shape.body ``shift4Loop true true true shift4LoopValue shift4LoopType shift4LoopValue shift4LoopValue S4M ``Sparkle.Core.Signal.Signal.loop
def F11ENTrue := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop ENM.shape.body ``counterEnableLoop true true true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENHeadEnd := ExpF11EN (fun _ w' => w') (fun w _ => w) ZS ``counterEnableLoop ENM.shape.body ``counterEnableLoop true true true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENLinkEnd := ExpF11EN (fun w _ => w) (fun _ w' => w') ZS ``counterEnableLoop ENM.shape.body ``counterEnableLoop true true true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENConclEnd := ExpF11EN (fun w _ => w) (fun w _ => w) ZE ``counterEnableLoop ENM.shape.body ``counterEnableLoop true true true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENHeadRoot := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``shift4Loop ENM.shape.body ``counterEnableLoop true true true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENData := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop S4M.shape.body ``counterEnableLoop true true true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENPost := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop ENM.shape.body ``shift4Loop true true true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENNoLvl := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop ENM.shape.body ``counterEnableLoop false true true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENNoX := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop ENM.shape.body ``counterEnableLoop true false true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENNoF := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop ENM.shape.body ``counterEnableLoop true true false counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENOtherX := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop ENM.shape.body ``counterEnableLoop true true true shift4LoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENFactsRoot := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop ENM.shape.body ``counterEnableLoop true true true counterEnableLoopValue shift4LoopType shift4LoopValue shift4LoopValue ENM ``Sparkle.Core.Signal.Signal.loop
def M11ENFactsData := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop ENM.shape.body ``counterEnableLoop true true true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue S4M ``Sparkle.Core.Signal.Signal.loop
def M11ENFactsName := ExpF11EN (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop ENM.shape.body ``counterEnableLoop true true true counterEnableLoopValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ENM ``Sparkle.Core.Signal.Signal.register
def F11ATrue := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11AHeadEnd := ExpF11A (fun _ w' => w') (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11ALinkEnd := ExpF11A (fun w _ => w) (fun _ w' => w') ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11AConclEnd := ExpF11A (fun w _ => w) (fun w _ => w) ZE ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11AHeadRoot := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``counterEnableLoop ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11AData := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ENM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11APost := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``counterEnableLoop true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11ANoLvl := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal false true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11ANoX := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true false true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11ANoF := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true false arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11AOtherX := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true counterEnableLoopValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11AFactsRoot := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ARM ``Sparkle.Core.Signal.Signal.loop true true
def M11AFactsData := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ENM ``Sparkle.Core.Signal.Signal.loop true true
def M11AFactsName := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.register true true
def M11ANoB := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop false true
def M11ANoCont := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterInlinedValue ARM ``Sparkle.Core.Signal.Signal.loop true false
def M11AFactsUninlined := ExpF11A (fun w _ => w) (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal ARM.shape.body ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal true true true arbiterInlinedValue arbiterType arbiterValue arbiterValue ARM ``Sparkle.Core.Signal.Signal.loop true true

def whitelistExtra : List Name := [``PB, ``idE, ``S4M, ``ENM, ``ARM, ARN, ``Tests.Gen5.FGCircuitPilotCheck7.ZS, ``Tests.Gen5.FGCircuitPilotCheck7.ZE, ``Tests.Gen5.FGCircuitPilotCheck5.GPd, ``ARN,
  -- definitions under test
  ``HeadAt, ``RootInEnv, ``GatesOnDecl, ``ReaderOnDecl, ``EntryOfDecl, ``peeledBody]

/-- the whitelist: every definition of this file whose name starts with `Exp`, `Mut`, a `…True`/`F11`/`M11` statement, plus the extras -/
def isStmtName (n : Name) : Bool :=
  match n with
  | .str (.str (.str (.str .anonymous "Tests") "Gen5") "FGCircuitPilotCheck12") s =>
    s.startsWith "Exp" || s.startsWith "Mut" || s.startsWith "F11" || s.startsWith "M11" || s.endsWith "True"
  | _ => false

def normW (wl : Name → Bool) (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if wl c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let wl : Name → Bool := fun n => isStmtName n || whitelistExtra.contains n
  let norm := normW wl
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    let a ← norm ci.type
    let e ← norm (mkConst exp)
    unless ← withDefault (isDefEq a e) do throwError "{thm}: type is NOT the expected statement {exp}"
    let ba ← binderInfos a
    let be ← binderInfos e
    unless ba == be do throwError "{thm}: binder kinds differ from {exp}: {repr ba} vs {repr be}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    let a ← norm ci.type
    let e ← norm (mkConst mu0)
    if ← withDefault (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let S := `Tools.ShippingFGCircuitS1nRoots
  let T := `Tests.Gen5.FGCircuitPilotCheck12
  let mut nm : Nat := 0
  let mut nsame : Nat := 0
  -- (theorem, true statement, mutants)
  let items : List (Name × String × List String) := [
    (S ++ `RootExtern.mk, "ExternMkTrue", ["MutExternPackPeeled", "MutExternFloatValue", "MutExternFindValue", "MutExternArity"]),
    (S ++ `RootEnvFacts.mk, "EnvFactsMkTrue", ["MutEnvShapeValue", "MutEnvUiOnInl", "MutEnvIpValueUnpeeled", "MutEnvIpInlUnpeeled", "MutEnvPolarity", "MutEnvName", "MutEnvNoInl"]),
    (S ++ `entryOfDecl_inl, "EntryInlTrue", ["MutEntryNoG1", "MutEntryNoG2", "MutEntryNoShape", "MutEntryKeepType"]),
    (S ++ `checkedEnv_of_inl, "CheckedInlTrue", ["MutCInlNoShape", "MutCInlNoG1", "MutCInlNoG2", "MutCInlNoData", "MutCInlDataOrig"]),
    (S ++ `shift4Loop_gates, "GatesS4True", ["MutGatesS4Pol", "MutGatesS4Unpeeled", "MutGatesS4NoIp", "MutGatesS4Value"]),
    (S ++ `counterEnableLoop_gates, "GatesENTrue", ["MutGatesENPol", "MutGatesENUnpeeled", "MutGatesENNoIp", "MutGatesENValue"]),
    (S ++ `arbiterSignal_gates_orig, "GatesAOTrue", ["MutGatesAOPol", "MutGatesAOUnpeeled", "MutGatesAONoIp", "MutGatesAOInlined"]),
    (S ++ `arbiterSignal_gates_inl, "GatesAITrue", ["MutGatesAIPol", "MutGatesAIUnpeeled", "MutGatesAINoIp", "MutGatesAIOrig"]),
    (S ++ `shift4Loop_dataOfAt, "DS4True", ["MutDS4Data", "MutDS4Fuel", "MutDS4Name", "MutDS4NoX", "MutDS4OtherX"]),
    (S ++ `counterEnableLoop_dataOfAt, "DENTrue", ["MutDENData", "MutDENFuel", "MutDENName", "MutDENNoX"]),
    (S ++ `arbiterSignal_dataOfAt, "DATrue", ["MutDAData", "MutDAFuel", "MutDAUninlined", "MutDAName", "MutDANoX"]),
    (S ++ `shift4Loop_checkedEnv_of_finite, "CFS4True", ["MutCFS4Data", "MutCFS4Val", "MutCFS4Name", "MutCFS4Fuel", "MutCFS4NoX", "MutCFS4NoF"]),
    (S ++ `counterEnableLoop_checkedEnv_of_finite, "CFENTrue", ["MutCFENData", "MutCFENVal", "MutCFENName", "MutCFENFuel", "MutCFENNoX", "MutCFENNoF"]),
    (S ++ `arbiterSignal_checkedEnv_of_finite, "CFATrue", ["MutCFAData", "MutCFAUninlined", "MutCFAExternOnValue", "MutCFAName", "MutCFAFuel", "MutCFANoX", "MutCFANoF"])]
  for (thm, tr, mus) in items do
    same thm (T ++ Name.mkSimple tr); nsame := nsame + 1
    for mu in mus do differs thm (T ++ Name.mkSimple mu); nm := nm + 1
  let finals : List (Name × String × List String) := [
    (S ++ `shift4Loop_final11, "S4", ["HeadEnd", "LinkEnd", "ConclEnd", "HeadRoot", "Data", "Post", "NoLvl", "NoX", "NoF", "OtherX", "FactsRoot", "FactsData", "FactsName"]),
    (S ++ `counterEnableLoop_final11, "EN", ["HeadEnd", "LinkEnd", "ConclEnd", "HeadRoot", "Data", "Post", "NoLvl", "NoX", "NoF", "OtherX", "FactsRoot", "FactsData", "FactsName"]),
    (S ++ `arbiterSignal_final11, "A", ["HeadEnd", "LinkEnd", "ConclEnd", "HeadRoot", "Data", "Post", "NoLvl", "NoX", "NoF", "OtherX", "FactsRoot", "FactsData", "FactsName", "NoB", "NoCont", "FactsUninlined"])]
  for (thm, r, mus) in finals do
    same thm (T ++ Name.mkSimple ("F11" ++ r ++ "True")); nsame := nsame + 1
    for mu in mus do differs thm (T ++ Name.mkSimple ("M11" ++ r ++ mu)); nm := nm + 1
    for (_, r', _) in finals do
      if r' != r then differs thm (T ++ Name.mkSimple ("F11" ++ r' ++ "True")); nm := nm + 1
  -- the counterLoop final of S1l is not any of the three statements
  logInfo m!"FGCIRCUIT12 SIGNATURES: {nsame} theorems (RootExtern.mk, RootEnvFacts.mk, entryOfDecl_inl, checkedEnv_of_inl, gates ×4, dataOfAt ×3, checkedEnv_of_finite ×3, shift4Loop_final11, counterEnableLoop_final11, arbiterSignal_final11): complete types match the independently written statements; {nm} mutants rejected (each counted per check: the argument of rootFloat / find? / packTupleInputs, the arity of the runCircuitH test, the instance predicate at the value instead of the peeled body, its polarity, the declaration the shape is read from, the inliner argument, `proj` asked at another name, the fuel, another root's data / value / type / extern value / head root / post root, an uninlined arbiter value, dropped fuel / extern / env-facts / boundary / containment premises, END-WORLD controls = the same run's end world w' (head start, link, conclusion environment), another root's final statement)"

/-! ## 2. the hypotheses that remain -/

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1nRoots
  let std := ["L", "lvl", "env₀", "hstart", "hr", "hhead", "hcell", "hlvl", "hx", "hf", "hlink"]
  for (thm, expected) in [(S ++ `shift4Loop_final11, std), (S ++ `counterEnableLoop_final11, std), (S ++ `arbiterSignal_final11, std ++ ["hB0", "hcont"])] do
    let bs ← explicitBinders thm
    let names := (bs.map (·.1)).filter fun n => !n.startsWith "a._@"
    unless names == expected do throwError "{thm}: hypotheses are {names}, expected {expected}"
    for gone in ["hchk", "hquiet", "hg", "hw", "hA6", "hsrc", "hdRun", "hgates", "hRead", "hE", "hreader", "hquote", "hgatesB", "hcd", "htop", "hnoraw"] do
      if names.contains gone then throwError "{thm}: {gone} is a hypothesis"
    for (n, t) in bs do
      let cs := t.getUsedConstants
      if cs.contains ``sorryAx then throwError "{thm}: hypothesis {n} mentions sorryAx"
      if cs.contains ``CheckedStart then throwError "{thm}: hypothesis {n} is CheckedStart"
      let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<unprintable; constants: {t.getUsedConstants.toList.map (·.toString)}>"
      logInfo m!"FGCIRCUIT12 REMAINING {thm.getString!} {n} : {pp}"
  let f1 := getStructureFields (← getEnv) (S ++ `RootExtern)
  unless f1.toList == [`pack, `rootFloat, `find] do throwError "RootExtern fields: {f1}"
  let f2 := getStructureFields (← getEnv) (S ++ `RootEnvFacts)
  unless f2.toList == [`root, `ui_val, `ui_ty, `ip_val, `ip_inl, `proj] do throwError "RootEnvFacts fields: {f2}"
  logInfo "FGCIRCUIT12 HYPS: X_final11 = L lvl env₀ hstart hr hhead(HeadAt) hcell(ReadWorld cref) hlvl(lvl at the shape's body = 1000000) hx(RootExtern of the entry value: packTupleInputs / rootFloat of the peeled body / Expr.find? of the peeled body) hf(RootEnvFacts env₀: root + machineShape? of the inlined declaration, userInliner at value and type, instancePredicate at the peeled bodies of the value and the entry value, proj at ONE name: Signal.register for shift4Loop, Signal.loop for counterEnableLoop and arbiterSignal) hlink(ReadsAt env₀ cref w); arbiterSignal + hB0 (BoundaryRowsInEnv env₀) + hcont (ContainsAt). NOT hypotheses: hchk(CheckedStart), the gates / the reader as evaluation statements, hquiet, GetEnvFrame, hdRun, MachineDefinesLinked, hsrc, DesignTransport, hw. RootExtern fields: pack rootFloat find. RootEnvFacts fields: root ui_val ui_ty ip_val ip_inl proj"

/-! ## 3. axioms -/
run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1nRoots
  let names : List Name := [S ++ `entryOfDecl_inl, S ++ `checkedEnv_of_inl, S ++ `dataOfAt_of_pieces, S ++ `machRoot_of_head,
    S ++ `shift4Loop_gates, S ++ `shift4Loop_srcDomOf, S ++ `shift4Loop_dataOfCore, S ++ `shift4Loop_dataOfAt, S ++ `shift4Loop_checkedEnv_of_finite, S ++ `shift4Loop_final11,
    S ++ `counterEnableLoop_gates, S ++ `counterEnableLoop_srcDomOf, S ++ `counterEnableLoop_dataOfCore, S ++ `counterEnableLoop_dataOfAt, S ++ `counterEnableLoop_checkedEnv_of_finite, S ++ `counterEnableLoop_final11,
    S ++ `arbiterSignal_gates_orig, S ++ `arbiterSignal_gates_inl, S ++ `arbiterSignal_srcDomOf, S ++ `arbiterSignal_dataOfCore, S ++ `arbiterSignal_dataOfAt, S ++ `arbiterSignal_checkedEnv_of_finite, S ++ `arbiterSignal_final11,
    S ++ `arbiterInlinedValue]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT12 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT12: the named facts evaluated on ONE environment; the finite-input claim probed -/

def rootDef (env : Environment) (nm : Name) : Option DefinitionVal :=
  match env.find? nm with
  | some (.defnInfo d) => some d
  | _ => none

/-- the named facts of one root evaluated on `env` (everything the structures say, plus the whole data read by `dataOfAt`) -/
def snapFacts (nm : Name) (T V Vi : Lean.Expr) (dn pn : Name) : MetaM Unit := do
  let env ← getEnv
  let some d := rootDef env nm | throwError "{nm}: no root"
  let se := structEnv env
  let ip := instancePredicate env
  let ui := userInliner env
  unless Sparkle.Compiler.MachTupleIn.packTupleInputs Vi == Vi do throwError "{nm}: RootExtern.pack false"
  unless Sparkle.Compiler.MachRawSurface.rootFloat (PB Vi) == PB Vi do throwError "{nm}: RootExtern.rootFloat false"
  unless ((PB Vi).find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8)).isNone do throwError "{nm}: RootExtern.find false"
  unless d.levelParams.isEmpty && d.type == T && d.value == V do throwError "{nm}: RootInEnv false"
  unless ui V == Vi do throwError "{nm}: ui_val false"
  unless ui T == T do throwError "{nm}: ui_ty false"
  unless ip (PB V) == false do throwError "{nm}: ip_val false"
  unless ip (PB Vi) == false do throwError "{nm}: ip_inl false"
  unless (se.proj pn).isNone do throwError "{nm}: proj false"
  let E := ConstantInfo.defnInfo { d with value := Vi, type := T }
  let some s := machineShape? false [] E se | throwError "{nm}: machineShape? none"
  let some dd := Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E se s | throwError "{nm}: dataOfAt none"
  let e1 ← dataExprOf dd
  let lit ← literalExpr dn
  unless e1 == lit do throwError "{nm}: machineShape? / dataOfAt: the data (with its shape) differs from {dn}"
  -- the entry constant the run computes is the inlined declaration
  let E0 := EntryOfDecl d ip ui se
  unless E0.value? == E.value? && E0.type == E.type do throwError "{nm}: the entry constant is not the inlined declaration"
  logInfo m!"FGCIRCUIT12 SNAPSHOT12a {nm}: on this build's ONE environment (an EVALUATION, not a supply of the hypotheses): RootExtern (3 facts), RootEnvFacts (root, ui at value and type, ip at the two peeled bodies, proj at the one name; machineShape? read by dataOfAt gives the whole data = {dn}) hold; EntryOfDecl is the inlined declaration"

/-- the finite-input claim: gates with the instance predicate altered off the two peeled bodies, data with `proj`/`fields` altered off the one name; and where the predicate is asked -/
def snapProbe (nm : Name) (T V Vi : Lean.Expr) (dn pn : Name) : MetaM Unit := do
  let env ← getEnv
  let some d := rootDef env nm | throwError "{nm}: no root"
  let se := structEnv env
  let ip := instancePredicate env
  let ui := userInliner env
  let E := ConstantInfo.defnInfo { d with value := Vi, type := T }
  let some s := machineShape? false [] E se | throwError "{nm}: machineShape? none"
  let ipAlt : Lean.Expr → Bool := fun e => if e == PB V || e == PB Vi then ip e else true
  let projAlt : Name → Option (Name × Nat × Nat) := fun n => if n == pn then se.proj n else some (`x, 1, 0)
  let seAlt : StructEnv := { se with proj := projAlt, fields := fun n => some (n, []) }
  let uiAlt : Lean.Expr → Lean.Expr := fun e => if e == V || e == T then ui e else Lean.Expr.bvar 0
  unless (certifiedShape? false [] (.defnInfo d)).isNone && (mixedCertifiedShape? false [] (.defnInfo d) ipAlt).isNone &&
      (certifiedShape? false [] E).isNone && (mixedCertifiedShape? false [] E ipAlt).isNone do
    throwError "{nm}: the gates depend on the instance predicate off the peeled bodies"
  unless (EntryOfDecl d ipAlt uiAlt se).value? == E.value? do throwError "{nm}: the entry constant depends on the inliner off the value and the type"
  let lit ← literalExpr dn
  match Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E seAlt s with
  | none => throwError "{nm}: dataOfAt none under altered proj/fields"
  | some dd =>
    let e ← dataExprOf dd
    unless e == lit do throwError "{nm}: dataOfAt (altered proj/fields) differs from {dn}"
  -- the instance predicate is asked at the PEELED body, not the value: true at the value only changes nothing; true at the peeled body only changes the gate
  let ipVal : Lean.Expr → Bool := fun e => e == V
  let ipBody : Lean.Expr → Bool := fun e => e == PB Vi || e == PB V
  unless (mixedCertifiedShape? false [] E ipVal).isNone do throwError "{nm}: control: the gate asked the predicate at the value"
  if PB V == V then throwError "{nm}: control: the peeled body is the value (no binders)"
  if (mixedCertifiedShape? false [] E ipBody).isNone then throwError "{nm}: control: the predicate true at the peeled body did not change the gate"
  logInfo m!"FGCIRCUIT12 SNAPSHOT12b {nm}: the gates (instance predicate true everywhere except at the two peeled bodies), the entry constant (inliner answering a variable off the value and type) and dataOfAt (proj answering `some` off {pn}, fields answering `some` everywhere) are unchanged on this build's one environment; the gate asks the predicate at the PEELED body (true at the value only: unchanged; true at the peeled body: the gate changes) — a probe, not a proof of independence"

def snapControls : MetaM Unit := do
  let env ← getEnv
  let ui := userInliner env
  -- (a) the arbiter's inliner does change the value, and the quote is the inlined value
  unless ui arbiterValue == arbiterInlinedValue do throwError "arbiterInlinedValue is not userInliner of arbiterValue on this build"
  if ui arbiterValue == arbiterValue then throwError "control: the arbiter's value is fixed by the inliner (ui_val would be trivial)"
  unless ui shift4LoopValue == shift4LoopValue && ui counterEnableLoopValue == counterEnableLoopValue do throwError "control: shift4Loop / counterEnableLoop values are not fixed"
  -- (b) another root's data under this root's shape is none or different
  let se := structEnv env
  let ip := instancePredicate env
  let some d := rootDef env ``shift4Loop | throwError "no shift4Loop"
  let E1 := ConstantInfo.defnInfo { d with value := shift4LoopValue, type := shift4LoopType }
  let some s := machineShape? false [] E1 se | throwError "machineShape? none"
  let E2 := ConstantInfo.defnInfo { d with value := counterEnableLoopValue, type := counterEnableLoopType }
  let lit ← literalExpr ``shift4Loop.machineData
  match Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E2 se s with
  | none => pure ()
  | some dd2 =>
    let e2 ← dataExprOf dd2
    if e2 == lit then throwError "negative control: another root's value gave the same data"
  -- (c) the instance predicate is not constantly false
  unless ip (.const ``Sparkle.IP.Net.HTTP.httpGetByte []) do throwError "negative control: the instance predicate is false on httpGetByte"
  logInfo "FGCIRCUIT12 SNAPSHOT12c: controls: arbiterInlinedValue = userInliner arbiterValue on this build, and the inliner changes the arbiter's value (so ui_val is not trivial) while it fixes the values of shift4Loop and counterEnableLoop; another root's value gives other data or none; the instance predicate is true on `httpGetByte`, so ip_val / ip_inl = false are not vacuous"

def snapS4 : MetaM Unit := snapFacts ``shift4Loop shift4LoopType shift4LoopValue shift4LoopValue ``shift4Loop.machineData ``Sparkle.Core.Signal.Signal.register
def snapEN : MetaM Unit := snapFacts ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ``counterEnableLoop.machineData ``Sparkle.Core.Signal.Signal.loop
def snapAR : MetaM Unit := snapFacts ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue arbiterInlinedValue ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData ``Sparkle.Core.Signal.Signal.loop
def probeS4 : MetaM Unit := snapProbe ``shift4Loop shift4LoopType shift4LoopValue shift4LoopValue ``shift4Loop.machineData ``Sparkle.Core.Signal.Signal.register
def probeEN : MetaM Unit := snapProbe ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoopValue ``counterEnableLoop.machineData ``Sparkle.Core.Signal.Signal.loop
def probeAR : MetaM Unit := snapProbe ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue arbiterInlinedValue ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData ``Sparkle.Core.Signal.Signal.loop

run_cmd liftTermElabM snapS4
run_cmd liftTermElabM snapEN
run_cmd liftTermElabM snapAR
run_cmd liftTermElabM probeS4
run_cmd liftTermElabM probeEN
run_cmd liftTermElabM probeAR
run_cmd liftTermElabM snapControls

end Tests.Gen5.FGCircuitPilotCheck12
