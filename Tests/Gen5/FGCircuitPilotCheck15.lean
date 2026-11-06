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
    -- a mutant differs structurally after normalization, and is not reducible-defeq (a default-transparency search through the compiler entries is not attempted)
    if a == e then throwError "{thm}: the MUTANT {mu0} is the same expression"
    if ← withReducible (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let L := `Tools.ShippingFGCircuitS1qLinked
  let H := `Tools.ShippingFGCircuitS1qHead
  let mut nm : Nat := 0
  same (L ++ `core_eqOff) ``EqTrue
  differs (L ++ `core_eqOff) ``MEqOld; nm := nm + 1
  same (H ++ `envFrame_coreHeadOff) ``EFTrue
  for mu in [``MEFOld, ``MEFNoCell, ``MEFHeadIO] do differs (H ++ `envFrame_coreHeadOff) mu; nm := nm + 1
  same (H ++ `headAtOff_of_cellPrem) ``HATrue
  for mu in [``MHAOld, ``MHANoCell, ``MHAExtraG, ``MHAEnd] do differs (H ++ `headAtOff_of_cellPrem) mu; nm := nm + 1
  same (H ++ `counterLoop_final12) ``FCTrue
  for mu in [``MCDiag, ``MCCellRW, ``MCExtraG, ``MCNoCell, ``MCPostOld, ``MCLinkEnd, ``MCConclEnd, ``MCPostRoot, ``MCNoLvl, ``MCNoX, ``MCNoF] do differs (H ++ `counterLoop_final12) mu; nm := nm + 1
  same (H ++ `shift4Loop_final12) ``FSTrue
  for mu in [``MSDiag, ``MSCellRW, ``MSExtraG, ``MSNoCell, ``MSPostOld, ``MSLinkEnd, ``MSConclEnd, ``MSPostRoot] do differs (H ++ `shift4Loop_final12) mu; nm := nm + 1
  same (H ++ `counterEnableLoop_final12) ``FETrue
  for mu in [``MEDiag, ``MECellRW, ``MEExtraG, ``MENoCell, ``MEPostOld, ``MELinkEnd, ``MEConclEnd, ``MEPostRoot] do differs (H ++ `counterEnableLoop_final12) mu; nm := nm + 1
  same (H ++ `arbiterSignal_final12) ``FATrue
  for mu in [``MADiag, ``MACellRW, ``MAExtraG, ``MANoCell, ``MAPostOld, ``MALinkEnd, ``MAConclEnd, ``MAPostRoot, ``MANoB, ``MANoC] do differs (H ++ `arbiterSignal_final12) mu; nm := nm + 1
  logInfo m!"FGCIRCUIT15 SIGNATURES: core_eqOff, envFrame_coreHeadOff, headAtOff_of_cellPrem, counterLoop_final12, shift4Loop_final12, counterEnableLoop_final12, arbiterSignal_final12: complete types match the independently written statements; {nm} mutants rejected (the diagnostic entry instead of synthesizeCombinationalOff, the old PostRun, ReadWorld instead of CellPrem, a dropped cell premise, the removed GetEnvProfileAt / HeadIO added back, the old coreHead, an end-world link / conclusion / frame, another post root, dropped lvl / extern / facts / boundary premises)"

/-! ## 2. the hypotheses that remain -/

run_cmd liftTermElabM do
  let H := `Tools.ShippingFGCircuitS1qHead
  let check (thm : Name) (expected : List String) : MetaM Unit := do
    let bs ← explicitBinders (H ++ thm)
    let names := (bs.map (·.1)).filter fun n => !n.startsWith "a._@"
    unless names == expected do throwError "{thm}: hypotheses are {names}, expected {expected}"
    for gone in ["hhead", "hg", "hio", "hquiet", "hdRun", "hsrc", "hchk", "hgates", "hRead", "hE", "hreader", "hquote", "hgatesB"] do
      if names.contains gone then throwError "{thm}: {gone} is a hypothesis"
    for (n, t) in bs do
      let used := t.getUsedConstants
      for b in [``HeadIO, ``GetEnvProfileAt] do
        if used.contains b then throwError "{thm}: hypothesis {n} mentions {b}"
      let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<unprintable; constants: {used.toList.map (·.toString)}>"
      logInfo m!"FGCIRCUIT15 REMAINING {thm} {n} : {pp}"
  let std := ["L", "lvl", "env₀", "hstart", "hr", "hcell", "hlvl", "hx", "hf", "hlink"]
  check `counterLoop_final12 std
  check `shift4Loop_final12 std
  check `counterEnableLoop_final12 std
  check `arbiterSignal_final12 (std ++ ["hB0", "hcont"])
  check `headAtOff_of_cellPrem ["X", "hcell"]
  check `envFrame_coreHeadOff ["X", "hcell"]
  logInfo "FGCIRCUIT15 HYPS: X_final12 = L lvl env₀ hstart hr(synthesizeCombinationalOff) hcell(CellPrem MkRefd mref cref) hlvl hx hf hlink (arbiter: + hB0 hcont). headAtOff_of_cellPrem = X hcell. NOT hypotheses: hhead, hg (GetEnvProfileAt), hio (HeadIO). Still NAMED hypotheses: Laws/Start/hr, CellPrem, hlvl, RootExtern, RootEnvFacts, ReadsAt (hlink), BoundaryRowsInEnv/ContainsAt (arbiter). That the command took the `else` branch of synthesizeEntry (no SPARKLE_PROFILE in the process environment) is NOT a hypothesis and NOT proved: the guarantee speaks about synthesizeCombinationalOff only."

/-! ## 3. NOGETENV: the compiler-level fact -/

/-- constants a definition's value refers to -/
def valueOf? (env : Environment) (n : Name) : Option Lean.Expr :=
  match env.find? n with
  | some (.defnInfo d) => some d.value
  | some (.thmInfo t) => some t.value
  | some (.opaqueInfo o) => some o.value
  | _ => none

def valueConsts (env : Environment) (n : Name) : Array Name :=
  match valueOf? env n with
  | some v => v.getUsedConstants
  | none => #[]

def hasStr (env : Environment) (n : Name) (s : String) : Bool :=
  match valueOf? env n with
  | some v => (v.find? fun t => match t with | .lit (.strVal x) => x == s | _ => false).isSome
  | none => false

/-- everything reachable from `roots` through values of constants with a name prefix in `pref`; also returns every referenced name -/
partial def reach (env : Environment) (pref : List String) (roots : List Name) : NameSet × NameSet :=
  let rec go (todo : List Name) (visited refd : NameSet) (fuel : Nat) : NameSet × NameSet :=
    match fuel, todo with
    | 0, _ => (visited, refd)
    | _, [] => (visited, refd)
    | fuel+1, n :: rest =>
      if visited.contains n then go rest visited refd fuel
      else
        let visited := visited.insert n
        let cs := valueConsts env n
        let refd := cs.foldl (fun s c => s.insert c) refd
        let next := cs.toList.filter fun c => !visited.contains c && (pref.any fun p => (c.toString).startsWith p)
        go (next ++ rest) visited refd fuel
  go roots {} {} 2000000

run_cmd liftTermElabM do
  let env ← getEnv
  let pref := ["Sparkle.", "Tools."]
  let bannedConsts : List Name := [``IO.getEnv, ``IO.eprintln, ``IO.FS.Handle.mk, ``Sparkle.Compiler.flushStderr, ``Tools.ShippingChildInv.profLogIO, ``Tools.ShippingFGCircuitS1iHead.profLogIO]
  let bannedStrs := ["SPARKLE_PROFILE", "/tmp/sparkle-profile.log"]
  -- everything coreHeadOff reaches (head only: no walk into `synthesizeFromConst`)
  let (vOff, rOff) := reach env pref [``Tools.ShippingFGCircuitS1qLinked.coreHeadOff]
  for b in bannedConsts do
    if rOff.contains b then throwError "coreHeadOff reaches {b}"
  for n in vOff.toList do
    for s in bannedStrs do
      if hasStr env n s then throwError "coreHeadOff reaches the string {s} in {n}"
  -- direct: the compiler entry and the mirrored rest
  for n in [``Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff, ``Tools.ShippingFGCircuitS1qLinked.coreRestOff] do
    let cs := valueConsts env n
    for b in bannedConsts do
      if cs.contains b then throwError "{n} mentions {b}"
    for s in bannedStrs do
      if hasStr env n s then throwError "{n} mentions the string {s}"
  -- controls: the old head and the old entry DO
  let (_, rOld) := reach env pref [``Tools.ShippingEntryReadsLinked.coreHead]
  unless rOld.contains ``IO.getEnv && rOld.contains ``IO.eprintln && rOld.contains ``IO.FS.Handle.mk do throwError "control: coreHead does not reach the getEnv / log constants"
  unless hasStr env ``Tools.ShippingEntryReadsLinked.coreHead "SPARKLE_PROFILE" do throwError "control: coreHead has no SPARKLE_PROFILE string"
  unless hasStr env ``Sparkle.Compiler.Elab.synthesizeCombinationalCoreWith "SPARKLE_PROFILE" do throwError "control: synthesizeCombinationalCoreWith has no SPARKLE_PROFILE string"
  unless hasStr env ``Sparkle.Compiler.Elab.synthesizeEntry "SPARKLE_PROFILE" do throwError "synthesizeEntry does not read SPARKLE_PROFILE"
  let ce := valueConsts env ``Sparkle.Compiler.Elab.synthesizeEntry
  unless ce.contains ``Sparkle.Compiler.Elab.synthesizeCombinational && ce.contains ``Sparkle.Compiler.Elab.synthesizeCombinationalOff do
    throwError "synthesizeEntry does not dispatch between the two entries"
  -- the entry does not call the dispatcher, and the commands call the dispatcher (not the diagnostic entry directly)
  if (valueConsts env ``Sparkle.Compiler.Elab.synthesizeCombinationalOff).contains ``Sparkle.Compiler.Elab.synthesizeEntry then throwError "synthesizeCombinationalOff calls synthesizeEntry"
  logInfo m!"FGCIRCUIT15 NOGETENV: coreHeadOff reaches {vOff.size} constants in Sparkle.*/Tools.* and none of IO.getEnv / IO.eprintln / IO.FS.Handle.mk / flushStderr / profLogIO / \"SPARKLE_PROFILE\" / \"/tmp/sparkle-profile.log\"; synthesizeCombinationalCoreOff and coreRestOff mention none of them; controls: the old coreHead reaches IO.getEnv, IO.eprintln, IO.FS.Handle.mk and the string; synthesizeCombinationalCoreWith has the string; synthesizeEntry reads SPARKLE_PROFILE (outside the entry) and dispatches between synthesizeCombinational and synthesizeCombinationalOff"

/-! ## 4. NOTUSED and axioms -/
set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let env ← getEnv
  let H := `Tools.ShippingFGCircuitS1qHead
  let names : List Name := [H ++ `counterLoop_final12, H ++ `shift4Loop_final12, H ++ `counterEnableLoop_final12, H ++ `arbiterSignal_final12, H ++ `headAtOff_of_cellPrem, H ++ `envFrame_coreHeadOff]
  let banned : List Name := [``Tools.ShippingEntryReadsLinked.coreHead, ``HeadIO, ``GetEnvProfileAt, ``Tools.ShippingFGCircuitS1oHead.headAt_of_profileOff, ``Tools.ShippingFGCircuitS1iHead.envFrame_coreHead,
    ``Tools.ShippingFGCircuitS1iHead.headAt_of_cellPrem, ``Sparkle.Compiler.Elab.synthesizeCombinationalCore, ``Sparkle.Compiler.Elab.synthesizeCombinationalCoreWith,
    ``Sparkle.Compiler.Elab.synthesizeCombinational, ``Sparkle.Compiler.Elab.synthesizeCombinationalWith, ``Sparkle.Compiler.Elab.synthesizeEntry]
  let (vis, refd) := reach env ["Tools.ShippingFGCircuit"] names
  let bannedHead : List Name := [``Tools.ShippingEntryReadsLinked.coreHead, ``HeadIO, ``GetEnvProfileAt, ``Tools.ShippingFGCircuitS1oHead.headAt_of_profileOff, ``Tools.ShippingFGCircuitS1iHead.envFrame_coreHead,
    ``Tools.ShippingFGCircuitS1iHead.headAt_of_cellPrem]
  for b in bannedHead do
    if refd.contains b then
      let wit := vis.toList.filter fun n => (valueConsts env n).contains b
      throwError "a value reachable from the finals mentions {b}; first witnesses {wit.take 5}"
  -- the entries: through the S1q files only (generic lemmas elsewhere speak about the old entry in their own statements)
  let (visQ, refdQ) := reach env ["Tools.ShippingFGCircuitS1q"] names
  let bannedEntry : List Name := [``Sparkle.Compiler.Elab.synthesizeCombinationalCore, ``Sparkle.Compiler.Elab.synthesizeCombinationalCoreWith,
    ``Sparkle.Compiler.Elab.synthesizeCombinational, ``Sparkle.Compiler.Elab.synthesizeCombinationalWith, ``Sparkle.Compiler.Elab.synthesizeEntry]
  for b in bannedEntry do
    if refdQ.contains b then
      let wit := visQ.toList.filter fun n => (valueConsts env n).contains b
      throwError "a value of the S1q files reachable from the finals mentions {b}; first witnesses {wit.take 5}"
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT15 NOTUSED: the {names.length} names reach {vis.size} Tools.ShippingFGCircuit* constants through values, none of which mentions coreHead / HeadIO / GetEnvProfileAt / headAt_of_profileOff / envFrame_coreHead; the {visQ.size} S1q constants reachable among them mention none of synthesizeCombinationalCore / …With / synthesizeCombinational / synthesizeCombinationalWith / synthesizeEntry (the old and the diagnostic entries)"
  logInfo m!"FGCIRCUIT15 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck15
