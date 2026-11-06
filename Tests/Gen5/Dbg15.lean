import Tests.Gen5.FGCircuitPilotCheck13
import Tools.ShippingFGCircuitS1qHead
set_option autoImplicit false
-- FG circuit pilot S1q check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §21.

/-! # FGCircuitPilotCheck15

1. SIGNATURES: complete expected types, written independently of the theorems, for `core_eqOff`, `envFrame_coreHeadOff`, `headAtOff_of_cellPrem` and the four finals `X_final12` (counterLoop, shift4Loop, counterEnableLoop, arbiterSignal); one-point MUTANTS rejected: the run of the diagnostic entry (`synthesizeCombinational`) instead of `synthesizeCombinationalOff`, the old `PostRun`, only `ReadWorld` instead of `CellPrem`, a dropped cell premise, an added `GetEnvProfileAt` premise (the removed one), the old head `coreHead`, an end-world link / conclusion, another post root, dropped lvl / extern / facts premises.
2. HYPS: the explicit hypotheses of the finals, of `headAtOff_of_cellPrem` and `envFrame_coreHeadOff`; `hhead`, `hg`, `hio`, `HeadIO`, `GetEnvProfileAt` are not among them.
3. NOGETENV (compiler level): `synthesizeCombinationalCoreOff`, `coreHeadOff`, `coreRestOff` and everything `coreHeadOff` reaches in `Sparkle.*`/`Tools.*` contain no `IO.getEnv`, `IO.eprintln`, `IO.FS.Handle.mk`, `flushStderr`, `profLogIO`, nor the strings `"SPARKLE_PROFILE"` / `"/tmp/sparkle-profile.log"`; controls: the same walk finds them in `coreHead` and in `synthesizeCombinationalCoreWith`, and `"SPARKLE_PROFILE"` is read by `synthesizeEntry` (outside the entry).
4. NOTUSED / AXIOMS: no value reachable through `Tools.*` from the finals mentions `coreHead`, `HeadIO`, `GetEnvProfileAt`, `headAt_of_profileOff`, `synthesizeCombinationalCore`/`…With`/`synthesizeCombinational`; standard axioms only. -/
namespace Tests.Gen5.FGCircuitPilotCheck15
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4 Tools.ShippingFGCircuitRoots4
open Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1lReader Tools.ShippingFGCircuitS1iRoots Tools.ShippingFGCircuitS1nRoots
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt)
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEnvSnapshot (EnvFrame)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved coreHead)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Sparkle.Compiler.Elab Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tests.Gen5.FGCircuitPilotCheck5 (W GPd explicitBinders binderInfos)
open Tests.Gen5.FGCircuitPilotCheck7 (ZS ZE)

/-! ## 1. expected statements, written independently -/

/-- the post relation: the old `PostRun` or the profile-free `PostRunOff` -/
def PR (old : Bool) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : W) (X : Name) (D' : Sparkle.IR.AST.Design) (b raw : Sparkle.IR.AST.Module) : Prop :=
  if old then PostRun mctx mref cctx cref w X D' b raw else PostRunOff mctx mref cctx cref w X D' b raw

/-- an extra premise `Q` in front of `P` (a mutant adds back a removed premise); with `extra = false` the statement is `P` itself, no arrow -/
def With (extra : Bool) (Q P : Prop) : Prop := if extra then (Q → P) else P

/-- the entry whose run the final speaks about -/
def Ent (diag : Bool) (X : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) :=
  if diag then synthesizeCombinational X else synthesizeCombinationalOff X

/-- the cell premise: `CellPrem`, or (mutant) only `ReadWorld cref`, or (mutant) none -/
def CellP (needCell cellRW : Bool) (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  if needCell then (if cellRW then ReadWorld cref else CellPrem Tools.ShippingChildFresh.MkRefd mref cref) else True

/-- `counterLoop_final12`.  Knobs: the entry (`diag`), the cell premise, the removed `GetEnvProfileAt` (`extraG`), the old post, which finite premise is present, the link world, the environment of the conclusion, the post root -/
def ExpFC (diag cellRW extraG postOld needCell needLvl needX needF : Bool) (rdw : W → W → W)
    (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (Ent diag ``counterLoop) mctx mref cctx cref w (b, D') w' →
    With extraG (GetEnvProfileAt mctx mref cctx cref w) (
    CellP needCell cellRW mref cref →
    (if needLvl then lvl counterLoop.machineData.shape.body = 1000000 else True) →
    (if needX then CounterLoopExtern else True) →
    (if needF then CounterLoopEnvFacts env₀ else True) →
    ReadsAt env₀ cref (rdw w w') →
    (∃ raw, PR postOld mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PR postOld mctx mref cctx cref w postRoot D') ``counterLoop shCounter mm b D' p)
def FCTrue := ExpFC false false false false true true true true (fun w _ => w) ZS ``counterLoop
def MCDiag := ExpFC true false false false true true true true (fun w _ => w) ZS ``counterLoop
def MCCellRW := ExpFC false true false false true true true true (fun w _ => w) ZS ``counterLoop
def MCExtraG := ExpFC false false true false true true true true (fun w _ => w) ZS ``counterLoop
def MCNoCell := ExpFC false false false false false true true true (fun w _ => w) ZS ``counterLoop
def MCPostOld := ExpFC false false false true true true true true (fun w _ => w) ZS ``counterLoop
def MCLinkEnd := ExpFC false false false false true true true true (fun _ w' => w') ZS ``counterLoop
def MCConclEnd := ExpFC false false false false true true true true (fun w _ => w) ZE ``counterLoop
def MCPostRoot := ExpFC false false false false true true true true (fun w _ => w) ZS ``shift4Loop
def MCNoLvl := ExpFC false false false false true false true true (fun w _ => w) ZS ``counterLoop
def MCNoX := ExpFC false false false false true true false true (fun w _ => w) ZS ``counterLoop
def MCNoF := ExpFC false false false false true true true false (fun w _ => w) ZS ``counterLoop

def ExpFS (diag cellRW extraG postOld needCell needLvl needX needF : Bool) (rdw : W → W → W)
    (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (Ent diag ``shift4Loop) mctx mref cctx cref w (b, D') w' →
    With extraG (GetEnvProfileAt mctx mref cctx cref w) (
    CellP needCell cellRW mref cref →
    (if needLvl then lvl shift4Loop.machineData.shape.body = 1000000 else True) →
    (if needX then RootExtern shift4LoopValue else True) →
    (if needF then RootEnvFacts env₀ ``shift4Loop shift4LoopType shift4LoopValue shift4LoopValue shift4Loop.machineData ``Sparkle.Core.Signal.Signal.register else True) →
    ReadsAt env₀ cref (rdw w w') →
    (∃ raw, PR postOld mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PR postOld mctx mref cctx cref w postRoot D') ``shift4Loop shShift4 mm b D' p)
def FSTrue := ExpFS false false false false true true true true (fun w _ => w) ZS ``shift4Loop
def MSDiag := ExpFS true false false false true true true true (fun w _ => w) ZS ``shift4Loop
def MSCellRW := ExpFS false true false false true true true true (fun w _ => w) ZS ``shift4Loop
def MSExtraG := ExpFS false false true false true true true true (fun w _ => w) ZS ``shift4Loop
def MSNoCell := ExpFS false false false false false true true true (fun w _ => w) ZS ``shift4Loop
def MSPostOld := ExpFS false false false true true true true true (fun w _ => w) ZS ``shift4Loop
def MSLinkEnd := ExpFS false false false false true true true true (fun _ w' => w') ZS ``shift4Loop
def MSConclEnd := ExpFS false false false false true true true true (fun w _ => w) ZE ``shift4Loop
def MSPostRoot := ExpFS false false false false true true true true (fun w _ => w) ZS ``counterEnableLoop

def ExpFE (diag cellRW extraG postOld needCell needLvl needX needF : Bool) (rdw : W → W → W)
    (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (postRoot : Name) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (Ent diag ``counterEnableLoop) mctx mref cctx cref w (b, D') w' →
    With extraG (GetEnvProfileAt mctx mref cctx cref w) (
    CellP needCell cellRW mref cref →
    (if needLvl then lvl counterEnableLoop.machineData.shape.body = 1000000 else True) →
    (if needX then RootExtern counterEnableLoopValue else True) →
    (if needF then RootEnvFacts env₀ ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoopValue counterEnableLoop.machineData ``Sparkle.Core.Signal.Signal.loop else True) →
    ReadsAt env₀ cref (rdw w w') →
    (∃ raw, PR postOld mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shEnable) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PR postOld mctx mref cctx cref w postRoot D') ``counterEnableLoop shEnable mm b D' p)
def FETrue := ExpFE false false false false true true true true (fun w _ => w) ZS ``counterEnableLoop
def MEDiag := ExpFE true false false false true true true true (fun w _ => w) ZS ``counterEnableLoop
def MECellRW := ExpFE false true false false true true true true (fun w _ => w) ZS ``counterEnableLoop
def MEExtraG := ExpFE false false true false true true true true (fun w _ => w) ZS ``counterEnableLoop
def MENoCell := ExpFE false false false false false true true true (fun w _ => w) ZS ``counterEnableLoop
def MEPostOld := ExpFE false false false true true true true true (fun w _ => w) ZS ``counterEnableLoop
def MELinkEnd := ExpFE false false false false true true true true (fun _ w' => w') ZS ``counterEnableLoop
def MEConclEnd := ExpFE false false false false true true true true (fun w _ => w) ZE ``counterEnableLoop
def MEPostRoot := ExpFE false false false false true true true true (fun w _ => w) ZS ``shift4Loop

def ExpFA (diag cellRW extraG postOld needCell needLvl needX needF needB needC : Bool) (rdw : W → W → W)
    (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (postRoot : Name) : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (Ent diag ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w (b, D') w' →
    With extraG (GetEnvProfileAt mctx mref cctx cref w) (
    CellP needCell cellRW mref cref →
    (if needLvl then lvl Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape.body = 1000000 else True) →
    (if needX then RootExtern arbiterInlinedValue else True) →
    (if needF then RootEnvFacts env₀ ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue arbiterInlinedValue Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData ``Sparkle.Core.Signal.Signal.loop else True) →
    ReadsAt env₀ cref (rdw w w') →
    (if needB then BoundaryRowsInEnv env₀ else True) → (if needC then ContainsAt env₀ cref w boundaryNames else True) →
    (∃ raw, PR postOld mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (eC env₀ cref w w') (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (eC env₀ cref w w'))
        (PR postOld mctx mref cctx cref w postRoot D') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b D' p)
def FATrue := ExpFA false false false false true true true true true true (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def MADiag := ExpFA true false false false true true true true true true (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def MACellRW := ExpFA false true false false true true true true true true (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def MAExtraG := ExpFA false false true false true true true true true true (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def MANoCell := ExpFA false false false false false true true true true true (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def MAPostOld := ExpFA false false false true true true true true true true (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def MALinkEnd := ExpFA false false false false true true true true true true (fun _ w' => w') ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def MAConclEnd := ExpFA false false false false true true true true true true (fun w _ => w) ZE ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def MAPostRoot := ExpFA false false false false true true true true true true (fun w _ => w) ZS ``counterEnableLoop
def MANoB := ExpFA false false false false true true true true false true (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
def MANoC := ExpFA false false false false true true true true true false (fun w _ => w) ZS ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal

/-- `envFrame_coreHeadOff`.  Knobs: the head (old `coreHead` or `coreHeadOff`), the cell premise, the removed `HeadIO` -/
def ExpEF (oldHead : Bool) (needCell extraIO : Bool) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (X : Lean.Name),
    With extraIO (HeadIO mctx mref cctx cref) (
    (if needCell then CellPrem Tools.ShippingChildFresh.MkRefd mref cref else True) →
    EnvFrame (if oldHead then coreHead X else coreHeadOff X) mctx mref cctx cref)
def EFTrue := ExpEF false true false
def MEFOld := ExpEF true true false
def MEFNoCell := ExpEF false false false
def MEFHeadIO := ExpEF false true true

/-- `headAtOff_of_cellPrem` (with `HeadAtOff` unfolded).  Knobs: the head, the cell premise, the removed `GetEnvProfileAt`, the world of the conclusion -/
def ExpHA (oldHead : Bool) (needCell extraG : Bool) (cw : W → W → W) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : W} (X : Lean.Name),
    With extraG (GetEnvProfileAt mctx mref cctx cref w) (
    (if needCell then CellPrem Tools.ShippingChildFresh.MkRefd mref cref else True) →
    ∀ (s : CoreSaved) (w1 : W), RunsTo (if oldHead then coreHead X else coreHeadOff X) mctx mref cctx cref w s w1 → envAt cref w1 = envAt cref (cw w w1))
def HATrue := ExpHA false true false (fun w _ => w)
def MHAOld := ExpHA true true false (fun w _ => w)
def MHANoCell := ExpHA false false false (fun w _ => w)
def MHAExtraG := ExpHA false true true (fun w _ => w)
def MHAEnd := ExpHA false true false (fun _ w1 => w1)

/-- `core_eqOff` -/
def ExpEq (oldHead : Bool) : Prop :=
  ∀ (declName : Name),
    synthesizeCombinationalCoreOff declName =
      ((if oldHead then coreHead declName else coreHeadOff declName) >>= fun s => coreRestOff declName s)
def EqTrue := ExpEq false
def MEqOld := ExpEq true

def whitelist : List Name := [``PR, ``With, ``Ent, ``CellP,
  ``ExpFC, ``FCTrue, ``MCDiag, ``MCCellRW, ``MCExtraG, ``MCNoCell, ``MCPostOld, ``MCLinkEnd, ``MCConclEnd, ``MCPostRoot, ``MCNoLvl, ``MCNoX, ``MCNoF,
  ``ExpFS, ``FSTrue, ``MSDiag, ``MSCellRW, ``MSExtraG, ``MSNoCell, ``MSPostOld, ``MSLinkEnd, ``MSConclEnd, ``MSPostRoot,
  ``ExpFE, ``FETrue, ``MEDiag, ``MECellRW, ``MEExtraG, ``MENoCell, ``MEPostOld, ``MELinkEnd, ``MEConclEnd, ``MEPostRoot,
  ``ExpFA, ``FATrue, ``MADiag, ``MACellRW, ``MAExtraG, ``MANoCell, ``MAPostOld, ``MALinkEnd, ``MAConclEnd, ``MAPostRoot, ``MANoB, ``MANoC,
  ``ExpEF, ``EFTrue, ``MEFOld, ``MEFNoCell, ``MEFHeadIO, ``ExpHA, ``HATrue, ``MHAOld, ``MHANoCell, ``MHAExtraG, ``MHAEnd, ``ExpEq, ``EqTrue, ``MEqOld,
  ``Tests.Gen5.FGCircuitPilotCheck7.ZS, ``Tests.Gen5.FGCircuitPilotCheck7.ZE, ``Tests.Gen5.FGCircuitPilotCheck5.GPd,
  -- definitions under test
  ``HeadAtOff]

/-- `if b then x else y` with a literal Boolean `b`: the chosen branch -/
def iteStep (e : Lean.Expr) : Option Lean.Expr :=
  if e.isAppOfArity ``ite 5 then
    let c := e.getArg! 1
    if c.isAppOfArity ``Eq 3 then
      match c.getArg! 1, c.getArg! 2 with
      | .const ``Bool.true _, .const ``Bool.true _ => some (e.getArg! 3)
      | .const ``Bool.false _, .const ``Bool.true _ => some (e.getArg! 4)
      | _, _ => none
    else none
  else none

def normOnce (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let some e' := iteStep e then return .visit e'
    if let .const c _ := e.getAppFn then
      if whitelist.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

/-- unfold the whitelisted definitions and select the literal Boolean branches (a few passes, until no `ite` on a literal remains) -/
def norm (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:4] do
    e ← normOnce e
  return e


set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let ci ← getConstInfo `Tools.ShippingFGCircuitS1qHead.envFrame_coreHeadOff
  let a ← norm ci.type
  let e ← norm (mkConst ``EFTrue)
  logInfo m!"ACT {← ppExpr a}"
  logInfo m!"EXP {← ppExpr e}"
  logInfo m!"DEFEQ {← withDefault (isDefEq a e)}"
end Tests.Gen5.FGCircuitPilotCheck15
