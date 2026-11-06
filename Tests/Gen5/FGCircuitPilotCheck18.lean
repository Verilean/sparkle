import Tools.ShippingFGCircuitS1tFinal
set_option autoImplicit false
-- FG circuit pilot S1t check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §24.

/-! # FGCircuitPilotCheck18

1. SIGNATURES: complete types, written independently of the theorems (`ExpStmt`, `ExpThm`, `ExpSDV`, `ExpRAV`, `ExpDCV`, ...), of `synth_hftPcieOutByte_finalOff` and its instances (`_Z`, `_Y`, `_X`, `_old`), of the carrier-generic lemmas and of the new definitions;
   `isDefEq` (default) for the match, and for every MUTANT: structurally different after normalisation and not reducible-defeq. Mutants: the old (diagnostic) entry in `hr`, the old core entry/boundary in the core obligations, the old `PostRun`, the old carrier in the conclusion
   (`RootArtifactMono`), a conclusion/obligation/reader at the END world, each dropped premise (`hcell`, `hchk`, both child readers, `hcd`, `hsrc`, `htop`, `hnoraw`, `hdRun` inside `htop`, `hOb`), another root, another post root, another declaration's data in `hchk`, another carrier.
2. HYPS: the explicit hypotheses of the final statement by name and the list of what is NOT a hypothesis; no hypothesis mentions a diagnostic-entry constant.
3. SCOPE: nothing reachable from the final theorem mentions `synthesizeChild`/`sparkleChildSynth`/`childSynthEntry`/`synthesizeEntry`/the diagnostic entries (controls: the old S1k final does reach the diagnostic entry; `synthesizeChild` itself calls `synthesizeCombinational`, not `…Off`).
4. AXIOMS. -/
namespace Tests.Gen5.FGCircuitPilotCheck18
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitLinked (MachineDefinesLinked)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1tFinal
open Sparkle.Compiler.Elab

/-! ## 1. expected statements, written independently -/

abbrev W := Void IO.RealWorld
def NmRoot : Name := `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte
def NmHttp : Name := `Sparkle.IP.Net.HTTP.httpGetByte
def NmTlp : Name := `Sparkle.IP.Bus.PCIe.tlpCplByte
def NmOther : Name := `Sparkle.Tests.SignalLoopTest.counterLoop
def ShE : SigShape := { args := [.bits 8, .bool, .bool, .bits 32, .bits 16], res := .one (.bits 8) }
def varBad : Lean.Expr := .lam `x (.const ``Nat []) (.bvar 0) .default
def ZS : W → W → W := fun w _ => w
def ZE : W → W → W := fun _ w' => w'

noncomputable def GPx {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Pkgs ι (fun _ => defaultDomain) :=
  genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env

/-- the entry whose run the final speaks about: the diagnostic `synthesizeCombinational` or the guaranteed `synthesizeCombinationalOff` -/
def EntryOf (diag : Bool) (X : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) :=
  if diag then synthesizeCombinational X else synthesizeCombinationalOff X
/-- the core run the core obligations speak about -/
def CoreEntryOf (old : Bool) (X : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) :=
  if old then synthesizeCombinationalCore X [] false else synthesizeCombinationalCoreOff X
def PostSel (old : Bool) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : W) (X : Name) (D' : Sparkle.IR.AST.Design) : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop :=
  if old then PostRun mctx mref cctx cref w X D' else PostRunOff mctx mref cctx cref w X D'
def ArtOf (old : Bool) (CV : CDRel) {ι : Type} (env : Environment) (P : Pkgs ι (fun _ => defaultDomain))
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop) (mm : MonoTy ShE) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  if old then RootArtifactMono env P Post NmRoot ShE mm b D p else RootArtifactMonoV CV env P Post NmRoot ShE mm b D p

/-- the final statement. Knobs (each mutant turns exactly one; the order is: diag oldCore oldPost oldArt | needCell needChk needRdH needRdT needCD needSrc needTop needNoRaw hdRunIn | root postRoot chk | rdw hw cw):
the diagnostic entry in `hr`; the old core entry + old boundary in the core obligations; the old post; the old artifact (`CD`, no environment); which premises are present; the root of the run; the post root;
the data in `hchk`; the world the child readers / `hcd` / the conclusion are read at. -/
def ExpStmt (Ob : Environment → Prop) (CV : CDRel) (diag oldCore oldPost oldArt needCell needChk needRdH needRdT needCD needSrc needTop needNoRaw hdRunIn : Bool)
    (root postRoot : Name) (chk : MachineData) (rdw hw cw : W → W → W) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (EntryOf diag root) mctx mref cctx cref w (b, D') w' →
    (if needCell then CellPrem Tools.ShippingChildFresh.MkRefd mref cref else True) →
    (if needChk then CheckedStart lvl env₀ cref w root hftRootType hftRootValue chk else True) →
    (if needRdH then RootReader lvl (envAt cref (rdw w w')) NmHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData else True) →
    (if needRdT then RootReader lvl (envAt cref (rdw w w')) NmTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData else True) →
    (if needCD then Ob (envAt cref (hw w w')) else True) →
    (if needSrc then (∀ p : Pkg ι (fun _ => defaultDomain), GPx (ι := ι) lvl (envAt cref w) NmRoot = some p →
        ∀ i bools bits, p.src i bools bits = monoObs ShE synth_hftPcieOutByte bools bits) else True) →
    (if needTop then (∀ p : Pkg ι (fun _ => defaultDomain), GPx (ι := ι) lvl (envAt cref w) NmRoot = some p →
        ((if hdRunIn then
            (if oldCore then (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
                MachineDefinesLinked mctx mref cctx cref NmRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1)
             else (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
                MachineDefinesLinkedOff mctx mref cctx cref NmRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1))
          else True) →
          ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
            RunsTo (CoreEntryOf oldCore NmRoot) mctx mref cctx cref w (raw, D₀) w1 →
            Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → ∃ n, TopShips p n NmRoot b raw D₀)) else True) →
    (if needNoRaw then (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
        RunsTo (CoreEntryOf oldCore NmRoot) mctx mref cctx cref w (raw, D₀) w1 →
        Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' →
        (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) raw) ∧
        (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) (Sparkle.IR.OptCheck.checkedOptimize b)) ∧
        (∀ mn iname conns, Sparkle.IR.AST.Stmt.inst mn iname conns ∈ b.body → mn ≠ raw.name)) else True) →
    (∃ raw, PostSel oldPost mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy ShE) (p : Pkg ι (fun _ => defaultDomain)),
      ArtOf oldArt CV (envAt cref (cw w w')) (GPx (ι := ι) lvl (envAt cref (cw w w'))) (PostSel oldPost mctx mref cctx cref w postRoot D') mm b D' p

def StmtTrue (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MDiag (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV true false false false true true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MOldCore (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false true false false true true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MOldPost (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false true false true true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MOldArt (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false true true true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoCell (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false false true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoChk (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true false true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoRdH (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true false true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoRdT (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true false true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoCD (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true false true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoSrc (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true false true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoTop (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true true false true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoNoRaw (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true true true false true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoHdRun (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true true true true false NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MRoot (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true true true true true NmOther NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MPostRoot (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true true true true true NmRoot NmHttp synth_hftPcieOutByte.machineData ZS ZS ZS
def MChk (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true true true true true NmRoot NmRoot Sparkle.IP.Net.HTTP.httpGetByte.machineData ZS ZS ZS
def MRdEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZE ZS ZS
def MHcdEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZE ZS
def MConclEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpStmt Ob CV false false false false true true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZE

/-- the assembly theorem: for every carrier and every obligation that gives the root-value derivation. `needH`: the bridge `hOb` is present; `hv`: the value expression it is about -/
def ExpThm (S : (Environment → Prop) → CDRel → Prop) (needH : Bool) (hv : Lean.Expr) : Prop :=
  ∀ (CV : CDRel) (Ob : Environment → Prop),
    (if needH then (∀ env, Ob env → CV env hv (MonoTy ShE) synth_hftPcieOutByte) else True) → S Ob CV
def ThmTrue := ExpThm StmtTrue true hftRootValue
def TNoH := ExpThm StmtTrue false hftRootValue
def THOther := ExpThm StmtTrue true varBad
def TDiag := ExpThm MDiag true hftRootValue
def TOldCore := ExpThm MOldCore true hftRootValue
def TOldPost := ExpThm MOldPost true hftRootValue
def TOldArt := ExpThm MOldArt true hftRootValue
def TNoCell := ExpThm MNoCell true hftRootValue
def TNoChk := ExpThm MNoChk true hftRootValue
def TNoRdH := ExpThm MNoRdH true hftRootValue
def TNoRdT := ExpThm MNoRdT true hftRootValue
def TNoCD := ExpThm MNoCD true hftRootValue
def TNoSrc := ExpThm MNoSrc true hftRootValue
def TNoTop := ExpThm MNoTop true hftRootValue
def TNoNoRaw := ExpThm MNoNoRaw true hftRootValue
def TNoHdRun := ExpThm MNoHdRun true hftRootValue
def TRoot := ExpThm MRoot true hftRootValue
def TPostRoot := ExpThm MPostRoot true hftRootValue
def TChk := ExpThm MChk true hftRootValue
def TRdEnd := ExpThm MRdEnd true hftRootValue
def THcdEnd := ExpThm MHcdEnd true hftRootValue
def TConclEnd := ExpThm MConclEnd true hftRootValue

/-- the instances: a named obligation with its carrier. Mutants on the carrier / obligation pair: another carrier, another obligation, the old carrier -/
def ZTrue : Prop := StmtTrue HftObCDZ cdvZ
def ZCarrierY : Prop := StmtTrue HftObCDZ cdvY
def ZCarrierOld : Prop := StmtTrue HftObCDZ cdvOld
def ZObY : Prop := StmtTrue HftObCDY cdvZ
def YTrue : Prop := StmtTrue HftObCDY cdvY
def XTrue : Prop := StmtTrue HftObCDX cdvX
def OldTrue : Prop := StmtTrue (fun _ => HftObCD) cdvOld
def OldCarrierZ : Prop := StmtTrue (fun _ => HftObCD) cdvZ
def OfTrue (CV : CDRel) : Prop := StmtTrue (HftObOf CV) CV

/-- the carrier-generic lemmas -/
def ExpOldToZ (rev : Bool) : Prop :=
  ∀ (env : Environment) (e : Lean.Expr) (α : Type) (v : α), (if rev then CDZ env [] e α v else CD [] e α v) → (if rev then CD [] e α v else CDZ env [] e α v)
def OldToZTrue := ExpOldToZ false
def OldToZRev := ExpOldToZ true
def ExpFunc (mixed hEq : Bool) : Prop :=
  ∀ (env : Environment) (e : Lean.Expr) (α β : Type) (v : α) (w : β),
    CDZ env [] e α v → (if mixed then CDY env [] e β w else CDZ env [] e β w) → (if hEq then (α = β ∧ HEq v w) else α = β)
def FuncTrue := ExpFunc false true
def FuncMixed := ExpFunc true true
def FuncNoHEq := ExpFunc false false
def ExpUnique (conclShape : Bool) : Prop :=
  ∀ {CV : CDRel}, (∀ (env : Environment) (e : Lean.Expr) (α β : Type) (v : α) (w : β), CV env e α v → CV env e β w → α = β ∧ HEq v w) →
    ∀ {env : Environment} {X : Name} {params : List (String × Nat)} {sh sh' : SigShape} {m : MonoTy sh} {m' : MonoTy sh'},
      SourceDenotesMonoV CV env X params sh m → SourceDenotesMonoV CV env X params sh' m' → (if conclShape then (sh = sh' ∧ HEq m m') else sh = sh')
def UniqueTrue := ExpUnique true
def UniqueShapeOnly := ExpUnique false

/-- the new definitions, spelled out (compared as applied definitions). Knobs drop one conjunct / use the old carrier -/
def ExpSDV (noEnv noParams noLevel noShape : Bool) (CV : CDRel) (env : Environment) (source : Name) (params : List (String × Nat)) (sh : SigShape) (m : MonoTy sh) : Prop :=
  (if noParams then True else params = []) ∧ ∃ d : DefinitionVal, env.find? source = some (.defnInfo d) ∧ (if noLevel then True else d.levelParams = []) ∧
    (if noShape then True else monoShapeOf (.defnInfo d) = some sh) ∧ (if noEnv then CD [] d.value (MonoTy sh) m else CV env d.value (MonoTy sh) m)
def SDVTrue := ExpSDV false false false false
def SDVOldCarrier := ExpSDV true false false false
def SDVNoParams := ExpSDV false true false false
def SDVNoLevel := ExpSDV false false true false
def SDVNoShape := ExpSDV false false false true
def ExpRAV (noObs noPost oldSD : Bool) (ι : Type) (CV : CDRel) (env : Environment) (P : Pkgs ι (fun _ => defaultDomain))
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop) (X : Name) (sh : SigShape) (mm : MonoTy sh)
    (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  P X = some p ∧ (if oldSD then SourceDenotesMono env X [] sh mm else SourceDenotesMonoV CV env X [] sh mm) ∧ (if noObs then True else ObservationsEqualMono sh mm p) ∧
    (if noPost then True else ∀ raw, Post b raw → ∃ n, HasConcretePackage p n X b raw D)
def RAVTrue := ExpRAV false false false
def RAVNoObs := ExpRAV true false false
def RAVNoPost := ExpRAV false true false
def RAVOld := ExpRAV false false true
def ExpDCV (noShape noObs oldCV : Bool) (ι : Type) (CV : CDRel) (env₀ : Environment) (P : Pkgs ι (fun _ => defaultDomain)) (Tgt : Name → Prop) : Prop :=
  ∀ X, Tgt X → ∀ p, P X = some p →
    ∃ (d : DefinitionVal) (sh : SigShape) (mm : MonoTy sh), env₀.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ monoShapeOf (.defnInfo d) = some sh ∧
      (if noShape then True else ShapeMatchesMono sh p.d p.kD) ∧ (if oldCV then CD [] d.value (MonoTy sh) mm else CV env₀ d.value (MonoTy sh) mm) ∧
      (if noObs then True else ∀ i bools bits, monoObs sh mm bools bits = p.src i bools bits)
def DCVTrue := ExpDCV false false false
def DCVNoShape := ExpDCV true false false
def DCVNoObs := ExpDCV false true false
def DCVOld := ExpDCV false false true

def whitelist : List Name := [``EntryOf, ``CoreEntryOf, ``PostSel, ``ArtOf, ``ExpStmt, ``StmtTrue, ``MDiag, ``MOldCore, ``MOldPost, ``MOldArt, ``MNoCell, ``MNoChk, ``MNoRdH, ``MNoRdT, ``MNoCD,
  ``MNoSrc, ``MNoTop, ``MNoNoRaw, ``MNoHdRun, ``MRoot, ``MPostRoot, ``MChk, ``MRdEnd, ``MHcdEnd, ``MConclEnd,
  ``ExpThm, ``ThmTrue, ``TNoH, ``THOther, ``TDiag, ``TOldCore, ``TOldPost, ``TOldArt, ``TNoCell, ``TNoChk, ``TNoRdH, ``TNoRdT, ``TNoCD, ``TNoSrc, ``TNoTop, ``TNoNoRaw, ``TNoHdRun,
  ``TRoot, ``TPostRoot, ``TChk, ``TRdEnd, ``THcdEnd, ``TConclEnd,
  ``ZTrue, ``ZCarrierY, ``ZCarrierOld, ``ZObY, ``YTrue, ``XTrue, ``OldTrue, ``OldCarrierZ, ``OfTrue,
  ``ExpOldToZ, ``OldToZTrue, ``OldToZRev, ``ExpFunc, ``FuncTrue, ``FuncMixed, ``FuncNoHEq, ``ExpUnique, ``UniqueTrue, ``UniqueShapeOnly,
  ``ZS, ``ZE, ``GPx,
  -- definitions under test (unfolded on the theorem side)
  ``HftFinalStmtOff, ``HftObTopCoreOff, ``HftObNoRawOff, ``HftObSrc, ``GPt, ``HftObOf, ``cdvOld, ``cdvX, ``cdvY, ``cdvZ, ``CDFunctional]

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

/-- unfold the whitelisted definitions and select the literal Boolean branches -/
def norm (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:6] do
    e ← normOnce e
  return e

partial def binderInfos : Lean.Expr → List BinderInfo
  | .forallE _ _ b bi => bi :: binderInfos b
  | _ => []

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    let a ← norm ci.type
    let e ← norm (mkConst exp)
    unless ← withDefault (isDefEq a e) do throwError "{thm}: type is NOT the expected statement {exp}"
    let ba := binderInfos a
    let be := binderInfos e
    unless ba == be do throwError "{thm}: binder kinds differ from {exp}: {repr ba} vs {repr be}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    let a ← norm ci.type
    let e ← norm (mkConst mu0)
    if a == e then throwError "{thm}: the MUTANT {mu0} is the same expression"
    if ← withReducible (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let F := `Tools.ShippingFGCircuitS1tFinal
  let Q := `Tests.Gen5.FGCircuitPilotCheck18
  let mut nm : Nat := 0
  -- the assembly theorem, over every carrier and obligation
  same (F ++ `synth_hftPcieOutByte_finalOff) (Q ++ `ThmTrue)
  for mu in ["TNoH", "THOther", "TDiag", "TOldCore", "TOldPost", "TOldArt", "TNoCell", "TNoChk", "TNoRdH", "TNoRdT", "TNoCD", "TNoSrc", "TNoTop", "TNoNoRaw", "TNoHdRun", "TRoot", "TPostRoot", "TChk", "TRdEnd", "THcdEnd", "TConclEnd"] do
    differs (F ++ `synth_hftPcieOutByte_finalOff) (Q ++ Name.mkSimple mu); nm := nm + 1
  -- the instances
  same (F ++ `synth_hftPcieOutByte_finalOff_Z) (Q ++ `ZTrue)
  same (F ++ `synth_hftPcieOutByte_finalOff_Y) (Q ++ `YTrue)
  same (F ++ `synth_hftPcieOutByte_finalOff_X) (Q ++ `XTrue)
  same (F ++ `synth_hftPcieOutByte_finalOff_old) (Q ++ `OldTrue)
  for mu in ["ZCarrierY", "ZCarrierOld", "ZObY"] do
    differs (F ++ `synth_hftPcieOutByte_finalOff_Z) (Q ++ Name.mkSimple mu); nm := nm + 1
  differs (F ++ `synth_hftPcieOutByte_finalOff_old) (Q ++ `OldCarrierZ); nm := nm + 1
  differs (F ++ `synth_hftPcieOutByte_finalOff_Y) (Q ++ `ZTrue); nm := nm + 1
  differs (F ++ `synth_hftPcieOutByte_finalOff_X) (Q ++ `YTrue); nm := nm + 1
  -- the statement the assembly proves is the one stated (the Z instance is the statement itself, with the named S1r obligation)
  let ZM := [`MDiag, `MOldCore, `MOldPost, `MOldArt, `MNoCell, `MNoChk, `MNoRdH, `MNoRdT, `MNoCD, `MNoSrc, `MNoTop, `MNoNoRaw, `MNoHdRun, `MRoot, `MPostRoot, `MChk, `MRdEnd, `MHcdEnd, `MConclEnd]
  for mu in ZM do
    let a ← norm (← getConstInfo (F ++ `synth_hftPcieOutByte_finalOff_Z)).type
    let e ← norm (mkApp2 (mkConst (Q ++ mu)) (mkConst ``HftObCDZ) (mkConst (F ++ `cdvZ)))
    if a == e then throwError "finalOff_Z: the MUTANT {mu} is the same expression"
    if ← withReducible (isDefEq a e) then throwError "finalOff_Z: the MUTANT {mu} was accepted"
    nm := nm + 1
  -- the carrier-generic lemmas
  same (F ++ `cdvOld_to_Z) (Q ++ `OldToZTrue)
  differs (F ++ `cdvOld_to_Z) (Q ++ `OldToZRev); nm := nm + 1
  same (F ++ `cdvZ_functional) (Q ++ `FuncTrue)
  differs (F ++ `cdvZ_functional) (Q ++ `FuncMixed); nm := nm + 1
  differs (F ++ `cdvZ_functional) (Q ++ `FuncNoHEq); nm := nm + 1
  same (F ++ `sourceDenotesMonoV_unique) (Q ++ `UniqueTrue)
  differs (F ++ `sourceDenotesMonoV_unique) (Q ++ `UniqueShapeOnly); nm := nm + 1
  -- the definitions, as applied definitions
  let defeqApplied (d e : Name) : MetaM Bool := do
    let ci ← getConstInfo d
    forallTelescope ci.type fun xs _ => do
      withDefault (isDefEq (mkAppN (mkConst d) xs) (mkAppN (mkConst e) xs))
  unless ← defeqApplied (F ++ `SourceDenotesMonoV) (Q ++ `SDVTrue) do throwError "SourceDenotesMonoV differs from the expected definition"
  unless ← defeqApplied (F ++ `RootArtifactMonoV) (Q ++ `RAVTrue) do throwError "RootArtifactMonoV differs from the expected definition"
  unless ← defeqApplied (F ++ `DeclConnectMonoV) (Q ++ `DCVTrue) do throwError "DeclConnectMonoV differs from the expected definition"
  for mu in ["SDVOldCarrier", "SDVNoParams", "SDVNoLevel", "SDVNoShape"] do
    if ← defeqApplied (F ++ `SourceDenotesMonoV) (Q ++ Name.mkSimple mu) then throwError "SourceDenotesMonoV: the MUTANT {mu} was accepted"
    nm := nm + 1
  for mu in ["RAVNoObs", "RAVNoPost", "RAVOld"] do
    if ← defeqApplied (F ++ `RootArtifactMonoV) (Q ++ Name.mkSimple mu) then throwError "RootArtifactMonoV: the MUTANT {mu} was accepted"
    nm := nm + 1
  for mu in ["DCVNoShape", "DCVNoObs", "DCVOld"] do
    if ← defeqApplied (F ++ `DeclConnectMonoV) (Q ++ Name.mkSimple mu) then throwError "DeclConnectMonoV: the MUTANT {mu} was accepted"
    nm := nm + 1
  logInfo m!"FGCIRCUIT18 SIGNATURES: synth_hftPcieOutByte_finalOff (every carrier CV, every obligation Ob with the bridge hOb), its instances _Z/_Y/_X/_old, cdvOld_to_Z, cdvZ_functional, sourceDenotesMonoV_unique and the definitions SourceDenotesMonoV/RootArtifactMonoV/DeclConnectMonoV match the independently written statements; {nm} mutants rejected (the diagnostic entry in hr, the old core entry+boundary, the old PostRun, the old carrier RootArtifactMono, the END world for readers / hcd / conclusion, each dropped premise: hcell, hchk, both child readers, hcd, hsrc, htop, hnoraw, hdRun inside htop, the bridge hOb; another root, another post root, another declaration's data in hchk, another carrier / obligation pair; reversed CD→CDZ, a mixed-carrier functionality, a shape-only uniqueness, the definitions with the old carrier / without params / level / shape / observation / post / ShapeMatches)"

/-! ## 2. the hypotheses that remain -/

run_cmd liftTermElabM do
  let env ← getEnv
  let some (.defnInfo d) := env.find? (`Tools.ShippingFGCircuitS1tFinal ++ `HftFinalStmtOff) | throwError "HftFinalStmtOff not found"
  let names ← lambdaTelescope d.value fun _ body => forallTelescope body fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let dd ← x.fvarId!.getDecl
      if dd.binderInfo.isExplicit then hs := hs ++ [(dd.userName.toString, ← instantiateMVars dd.type)]
    return hs
  let expected := ["L", "lvl", "env₀", "hstart", "hr", "hcell", "hchk", "hreadH", "hreadT", "hcd", "hsrc", "htop", "hnoraw"]
  unless names.map (·.1) == expected do throwError "HftFinalStmtOff: hypotheses are {names.map (·.1)}, expected {expected}"
  for gone in ["hhead", "hdRun", "hquiet", "hg", "hio", "hgates", "hRead", "hE", "hP", "hdesign", "hcdOld"] do
    if (names.map (·.1)).contains gone then throwError "HftFinalStmtOff: {gone} is a hypothesis"
  let diag : List Name := [``synthesizeCombinational, ``synthesizeCombinationalCore, ``synthesizeCombinationalWith, ``synthesizeCombinationalCoreWith, ``synthesizeEntry,
    ``MachineDefinesLinked, ``PostRun, ``Tools.ShippingEntryReadsLinked.coreHead, ``HeadIO, ``HeadAt, ``synthesizeChild]
  -- constants a hypothesis type mentions, one level into the S1t/S1k obligations
  let mut cnt := 0
  for (n, t) in names do
    let mut used := t.getUsedConstants
    for c in t.getUsedConstants do
      if c.toString.startsWith "Tools.ShippingFGCircuitS1t" || c.toString.startsWith "Tools.ShippingFGCircuitS1kStmt" then
        match env.find? c with
        | some (.defnInfo dd) => used := used ++ dd.value.getUsedConstants
        | _ => pure ()
    for b in diag do
      if used.contains b then throwError "HftFinalStmtOff: hypothesis {n} mentions {b}"
    let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<unprintable; constants: {t.getUsedConstants.toList.map (·.toString)}>"
    logInfo m!"FGCIRCUIT18 REMAINING {n} : {pp}"
    cnt := cnt + 1
  -- the premise of the assembly theorem
  let ci ← getConstInfo (`Tools.ShippingFGCircuitS1tFinal ++ `synth_hftPcieOutByte_finalOff)
  let bs ← forallTelescope ci.type fun xs _ => do
    let mut r : List String := []
    for x in xs do
      let dd ← x.fvarId!.getDecl
      if dd.binderInfo.isExplicit then r := r ++ [dd.userName.toString]
    return r
  unless bs == ["CV", "Ob", "hOb"] do throwError "synth_hftPcieOutByte_finalOff: explicit arguments are {bs}"
  logInfo m!"FGCIRCUIT18 HYPS: HftFinalStmtOff Ob CV = L lvl env₀ hstart hr(synthesizeCombinationalOff) hcell(CellPrem MkRefd mref cref) hchk hreadH hreadT hcd(Ob (envAt cref w)) hsrc htop(HftObTopCoreOff) hnoraw(HftObNoRawOff); {cnt} hypotheses. The assembly theorem takes CV Ob and the bridge hOb : ∀ env, Ob env → CV env hftRootValue (MonoTy shHft) synth_hftPcieOutByte. NOT hypotheses: hhead, hdRun (derived from hchk/hcell and passed to htop), GetEnvFrame, hgates/hRead/hE, hquiet, HeadIO, GetEnvProfileAt. All of hcd, hsrc, htop, hnoraw and the three RootReader/CheckedStart premises remain NAMED and unproved."

/-! ## 3. SCOPE: children and the diagnostic entry; AXIOMS -/

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

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let env ← getEnv
  let F := `Tools.ShippingFGCircuitS1tFinal
  let names : List Name := [F ++ `synth_hftPcieOutByte_finalOff, F ++ `synth_hftPcieOutByte_finalOff_Z, F ++ `HftFinalStmtOff, F ++ `HftObTopCoreOff, F ++ `HftObNoRawOff]
  let pref := ["Tools.ShippingFGCircuitS1t", "Tools.ShippingFGCircuitS1q", "Tools.ShippingFGCircuitS1kStmt"]
  let (vis, refd) := reach env pref names
  let banned : List Name := [``synthesizeCombinational, ``synthesizeCombinationalCore, ``synthesizeCombinationalWith, ``synthesizeCombinationalCoreWith, ``synthesizeEntry,
    ``Tools.ShippingFGCircuitLinked.MachineDefinesLinked, ``PostRun, ``Tools.ShippingEntryReadsLinked.coreHead, ``HeadIO, ``HeadAt,
    ``synthesizeChild, ``sparkleChildSynth, ``childSynthEntry]
  for b in banned do
    if refd.contains b then
      let wit := vis.toList.filter fun n => (valueConsts env n).contains b
      throwError "a value reachable from the final theorem mentions {b}; first witnesses {wit.take 5}"
  -- controls: the S1k final DOES reach the diagnostic entry; synthesizeChild runs the diagnostic entry (so the children are not guaranteed)
  let (visK, refdK) := reach env ["Tools.ShippingFGCircuitS1k"] [`Tools.ShippingFGCircuitS1kPkg.synth_hftPcieOutByte_final]
  unless refdK.contains ``synthesizeCombinationalCore && refdK.contains ``PostRun do throwError "control: the S1k final does not reach the diagnostic entry"
  let cc := valueConsts env ``synthesizeChild
  unless cc.contains ``synthesizeCombinational do throwError "control: synthesizeChild does not call synthesizeCombinational"
  if cc.contains ``synthesizeCombinationalOff then throwError "control: synthesizeChild calls synthesizeCombinationalOff (the children were moved; update docs §24.2)"
  let ce := valueConsts env ``synthesizeCombinationalOff
  if ce.contains ``synthesizeChild || ce.contains ``synthesizeEntry then throwError "synthesizeCombinationalOff mentions synthesizeChild/synthesizeEntry"
  let allNames := names ++ [F ++ `synth_hftPcieOutByte_finalOff_Y, F ++ `synth_hftPcieOutByte_finalOff_X, F ++ `synth_hftPcieOutByte_finalOff_old, F ++ `synth_hftPcieOutByte_finalOff_of, F ++ `hftFinalStmtOff_mono,
      F ++ `cdvOld_to_Z, F ++ `cdvZ_functional, F ++ `sourceDenotesMonoV_unique, F ++ `sourceDenotesMonoV_eq, F ++ `observationsEqualMono_of_denotes, F ++ `rootArtifactMonoV_mono, F ++ `rootArtifactMono_to_Z,
      F ++ `fgCircuitConclusionMonoV_of_artifact, F ++ `declConnectMonoV_of_rootArtifact, F ++ `declConnectMonoV_mono, F ++ `sourceDenotesMonoV_mono, F ++ `observationsEqualMono_congr,
      F ++ `cdvX_functional, F ++ `cdvY_functional, F ++ `cdvOld_functional, F ++ `cdvOld_to_X, F ++ `cdvX_to_Y, F ++ `cdvY_to_Z]
  for nm in allNames do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT18 SCOPE: the final theorem and its statement reach {vis.size} S1t/S1q/S1k-statement constants and mention none of synthesizeCombinational / …Core / …With / synthesizeEntry / MachineDefinesLinked / PostRun / coreHead / HeadIO / HeadAt / synthesizeChild / sparkleChildSynth / childSynthEntry; controls: the S1k final reaches the diagnostic entry; synthesizeChild calls synthesizeCombinational and not synthesizeCombinationalOff; synthesizeCombinationalOff mentions neither synthesizeChild nor synthesizeEntry. The children's entry is NOT guaranteed by this statement (docs §24.2)."
  logInfo m!"FGCIRCUIT18 AXIOMS: {allNames.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck18
