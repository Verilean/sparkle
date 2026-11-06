import Tests.Gen5.FGCircuitPilotCheck8
import Tools.ShippingFGCircuitS1kPkg
set_option autoImplicit false
-- FG circuit pilot S1k check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §15.

/-! # FGCircuitPilotCheck9

1. SIGNATURES: the complete type of `synth_hftPcieOutByte_final` (= `HftFinalStmt`), the four obligations, the kernel facts and `genGP_root_kids`, against independently written statements (`isDefEq`), with mutants that must be rejected.
2. HYPS: the explicit hypotheses of the final theorem by name, and the list of what is NOT a hypothesis.
3. AXIOMS of every new name.
4. SNAPSHOT9: ONE environment (the build's): the type/value `Expr` of the root, the machine route, the reader's data of the root and of its two children (whole structure vs. the endpoint literals), the endpoint inventory (which `machine_*` exist). -/
namespace Tests.Gen5.FGCircuitPilotCheck9
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved coreHead)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitLinked Sparkle.Compiler.Elab
open Tests.Gen5.FGCircuitPilotCheck5 (W GPd explicitBinders binderInfos dataExprOf literalExpr)

/-! ## 1. expected statements, written independently -/

/-- the shape, spelled out -/
def ShE : SigShape := { args := [.bits 8, .bool, .bool, .bits 32, .bits 16], res := .one (.bits 8) }
def ShBad : SigShape := { args := [.bits 8, .bool, .bool, .bits 16, .bits 32], res := .one (.bits 8) }
def NmRoot : Name := `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte
def NmHttp : Name := `Sparkle.IP.Net.HTTP.httpGetByte
def NmTlp : Name := `Sparkle.IP.Bus.PCIe.tlpCplByte

/-- the final theorem. Knobs (each mutant turns exactly one): the root name in `hr`/`hhead`/`hchk`; `chk` = the data in `hchk`; which premises are present; the world the child readers are read at;
the environment of the conclusion; the post-relation root; whether `hdRun` is a premise of the core obligation; the design the core `TopShips` is about. -/
def ExpHft (root postRoot : Name) (chk : MachineData) (needHead needCell needRdH needRdT needCD needSrc needTop needNoRaw hdRunIn : Bool)
    (rdw cw : W → W → W) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational root) mctx mref cctx cref w (b, D') w' →
    (if needHead then (∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead root) mctx mref cctx cref w s w1 → envAt cref w1 = envAt cref w) else True) →
    (if needCell then ReadWorld cref else True) →
    CheckedStart lvl env₀ cref w root hftRootType hftRootValue chk →
    (if needRdH then RootReader lvl (envAt cref (rdw w w')) NmHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData else True) →
    (if needRdT then RootReader lvl (envAt cref (rdw w w')) NmTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData else True) →
    (if needCD then CD [] hftRootValue (MonoTy ShE) synth_hftPcieOutByte else True) →
    (if needSrc then (∀ p : Pkg ι (fun _ => defaultDomain), GPd (ι := ι) lvl (envAt cref w) NmRoot = some p →
        ∀ i bools bits, p.src i bools bits = monoObs ShE synth_hftPcieOutByte bools bits) else True) →
    (if needTop then (∀ p : Pkg ι (fun _ => defaultDomain), GPd (ι := ι) lvl (envAt cref w) NmRoot = some p →
        ((if hdRunIn then (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
            MachineDefinesLinked mctx mref cctx cref NmRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1) else True) →
          ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
            RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore NmRoot [] false) mctx mref cctx cref w (raw, D₀) w1 →
            Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → ∃ n, TopShips p n NmRoot b raw D₀)) else True) →
    (if needNoRaw then (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
        RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore NmRoot [] false) mctx mref cctx cref w (raw, D₀) w1 →
        Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' →
        (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) raw) ∧
        (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) (Sparkle.IR.OptCheck.checkedOptimize b)) ∧
        (∀ mn iname conns, Sparkle.IR.AST.Stmt.inst mn iname conns ∈ b.body → mn ≠ raw.name)) else True) →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy ShE) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref (cw w w')) (GPd (ι := ι) lvl (envAt cref (cw w w')))
        (PostRun mctx mref cctx cref w postRoot D') NmRoot ShE mm b D' p

def ZS : W → W → W := fun w _ => w
def ZE : W → W → W := fun _ w' => w'
def HftTrue := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true true true true true true true true true ZS ZS
def MutRootInRun := ExpHft ``Sparkle.Tests.SignalLoopTest.counterLoop NmRoot synth_hftPcieOutByte.machineData true true true true true true true true true ZS ZS
def MutChkData := ExpHft NmRoot NmRoot Sparkle.IP.Net.HTTP.httpGetByte.machineData true true true true true true true true true ZS ZS
def MutPostRoot := ExpHft NmRoot NmHttp synth_hftPcieOutByte.machineData true true true true true true true true true ZS ZS
def MutNoHead := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData false true true true true true true true true ZS ZS
def MutNoCell := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true false true true true true true true true ZS ZS
def MutNoRdH := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true true false true true true true true true ZS ZS
def MutNoRdT := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true true true false true true true true true ZS ZS
def MutNoCD := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true true true true false true true true true ZS ZS
def MutNoSrc := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true true true true true false true true true ZS ZS
def MutNoTop := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true true true true true true false true true ZS ZS
def MutNoNoRaw := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true true true true true true true false true ZS ZS
def MutNoHdRun := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true true true true true true true true false ZS ZS
def MutRdEnd := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true true true true true true true true true ZE ZS
def MutConclEnd := ExpHft NmRoot NmRoot synth_hftPcieOutByte.machineData true true true true true true true true true ZS ZE

/-- the obligations, spelled out. Knobs: the observer in O-SRC; the design `TopShips` is stated on and the `hdRun` premise in O-TOP; the third conjunct of O-NORAW -/
def ExpObCD (v : Lean.Expr) : Prop := CD [] v (MonoTy ShE) synth_hftPcieOutByte
def ExpObSrc (obs : Bool) {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Prop :=
  ∀ p : Pkg ι (fun _ => defaultDomain), GPd (ι := ι) lvl env NmRoot = some p →
    ∀ i bools bits, p.src i bools bits = (if obs then monoObs ShE synth_hftPcieOutByte bools bits else [])
def ExpObTop (onCore hdRunIn : Bool) {ι : Type} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : W) (b : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  (if hdRunIn then (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
      MachineDefinesLinked mctx mref cctx cref NmRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1) else True) →
  ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore NmRoot [] false) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → ∃ n, TopShips p n NmRoot b raw (if onCore then D₀ else D')
def ExpObNoRaw (third : Bool) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : W) (b : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design) : Prop :=
  ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore NmRoot [] false) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' →
    (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) raw) ∧
    (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) (Sparkle.IR.OptCheck.checkedOptimize b)) ∧
    (if third then (∀ mn iname conns, Sparkle.IR.AST.Stmt.inst mn iname conns ∈ b.body → mn ≠ raw.name) else True)

/-- the kernel facts, spelled out -/
def ExpInsts (l : List Name) : Prop := synth_hftPcieOutByte.machineData.shape.insts.map (·.1) = l
def ExpKD (k : Nat) : Prop := Tools.ShippingGen5Sem.kDOf synth_hftPcieOutByte.machineData = k
def ExpWf (d : MachineData) : Prop := Tools.ShippingGen5Sem.GenWF d = true
def ExpLeaf (d : MachineData) : Prop := d.shape.insts = []
def ExpShape (sh : SigShape) (k : Nat) : Prop := ShapeMatchesMono sh synth_hftPcieOutByte.machineData k
def InstsTrue := ExpInsts [NmHttp, NmTlp]
def InstsSwapped := ExpInsts [NmTlp, NmHttp]
def InstsOne := ExpInsts [NmHttp]
def KDTrue := ExpKD 5
def KD4 := ExpKD 4
def WfRoot := ExpWf synth_hftPcieOutByte.machineData
def WfHttp := ExpWf Sparkle.IP.Net.HTTP.httpGetByte.machineData
def WfTlp := ExpWf Sparkle.IP.Bus.PCIe.tlpCplByte.machineData
def LeafHttp := ExpLeaf Sparkle.IP.Net.HTTP.httpGetByte.machineData
def LeafTlp := ExpLeaf Sparkle.IP.Bus.PCIe.tlpCplByte.machineData
def WfFalse : Prop := Tools.ShippingGen5Sem.GenWF synth_hftPcieOutByte.machineData = false
def LeafNe : Prop := Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.insts ≠ []
def ShapeTrue := ExpShape ShE 5
def ShapeBad := ExpShape ShBad 5
def ShapeK4 := ExpShape ShE 4

/-- `genGP_root_kids`. Knobs: the callees are asked of the list `insts.map (·.1)` (true) or of nothing (false) -/
def ExpKids (needKids : Bool) : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (Tools.ShippingMachineDenote.tys d.ss)}
    (hs : Tools.ShippingGen5Sem.DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) → Option (Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    (env : Environment) {X : Name} {E : ConstantInfo} {g : Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)},
    Tools.ShippingGen5Acc.entry₀ env X = some E → genData₀ env E = some g →
    (if needKids then (∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) Ec (structEnv env)),
      Tools.ShippingGen5Acc.entry₀ env c = some Ec ∧ genData₀ env Ec = some gc ∧ gc.d.shape.insts = []) else True) →
    ∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl hs genData₀ env X = some p ∧ p.decl = X ∧ p.d = g.d ∧ p.kD = Tools.ShippingGen5Sem.kDOf g.d

def KidsTrue := ExpKids true
def KidsNone := ExpKids false
def varBad : Lean.Expr := .lam `x (.const ``Nat []) (.bvar 0) .default

set_option maxHeartbeats 16000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    unless ← withDefault (isDefEq ci.type (mkConst exp)) do throwError "{thm}: type is NOT the expected statement {exp}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    if ← withDefault (isDefEq ci.type (mkConst mu0)) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let S := `Tools.ShippingFGCircuitS1kStmt
  let P := `Tools.ShippingFGCircuitS1kPkg
  let Q := `Tests.Gen5.FGCircuitPilotCheck9
  let mut nm : Nat := 0
  -- the final theorem, and the statement it proves
  same (P ++ `synth_hftPcieOutByte_final) (Q ++ `HftTrue)
  unless ← withDefault (isDefEq (mkConst (S ++ `HftFinalStmt)) (mkConst (Q ++ `HftTrue))) do throwError "HftFinalStmt differs from the expected statement"
  for mu in ["MutRootInRun", "MutChkData", "MutPostRoot", "MutNoHead", "MutNoCell", "MutNoRdH", "MutNoRdT", "MutNoCD", "MutNoSrc", "MutNoTop", "MutNoNoRaw", "MutNoHdRun", "MutRdEnd", "MutConclEnd"] do
    differs (P ++ `synth_hftPcieOutByte_final) (Q ++ Name.mkSimple mu)
    if ← withDefault (isDefEq (mkConst (S ++ `HftFinalStmt)) (mkConst (Q ++ Name.mkSimple mu))) then throwError "HftFinalStmt: the MUTANT {mu} was accepted"
    nm := nm + 2
  -- the obligations
  let defeq (a b : Lean.Expr) : MetaM Bool := withDefault (isDefEq a b)
  let ob (n : Name) : Lean.Expr := mkConst (S ++ n)
  unless ← defeq (ob `HftObCD) (mkApp (mkConst (Q ++ `ExpObCD)) (mkConst (S ++ `hftRootValue))) do throwError "HftObCD differs from the expected statement"
  if ← defeq (ob `HftObCD) (mkApp (mkConst (Q ++ `ExpObCD)) (mkConst (Q ++ `varBad))) then throwError "HftObCD: mutant (another value) accepted"
  nm := nm + 1
  let q (n : Name) (args : List Lean.Expr) : Lean.Expr := mkAppN (Lean.mkConst (Q ++ n)) args.toArray
  let tt := Lean.mkConst ``true
  let ff := Lean.mkConst ``false
  unless ← defeq (ob `HftObSrc) (q `ExpObSrc [tt]) do throwError "HftObSrc differs from the expected statement"
  if ← defeq (ob `HftObSrc) (q `ExpObSrc [ff]) then throwError "HftObSrc: mutant (no observation) accepted"
  unless ← defeq (ob `HftObTopCore) (q `ExpObTop [tt, tt]) do throwError "HftObTopCore differs from the expected statement"
  if ← defeq (ob `HftObTopCore) (q `ExpObTop [ff, tt]) then throwError "HftObTopCore: mutant (TopShips on the printed design) accepted"
  if ← defeq (ob `HftObTopCore) (q `ExpObTop [tt, ff]) then throwError "HftObTopCore: mutant (no hdRun) accepted"
  unless ← defeq (ob `HftObNoRaw) (q `ExpObNoRaw [tt]) do throwError "HftObNoRaw differs from the expected statement"
  if ← defeq (ob `HftObNoRaw) (q `ExpObNoRaw [ff]) then throwError "HftObNoRaw: mutant (no instance-of-b conjunct) accepted"
  nm := nm + 4
  -- kernel facts
  same (P ++ `root_insts) (Q ++ `InstsTrue)
  same (P ++ `root_kD) (Q ++ `KDTrue)
  same (P ++ `root_wf) (Q ++ `WfRoot)
  same (P ++ `http_wf) (Q ++ `WfHttp)
  same (P ++ `tlp_wf) (Q ++ `WfTlp)
  same (P ++ `http_leaf) (Q ++ `LeafHttp)
  same (P ++ `tlp_leaf) (Q ++ `LeafTlp)
  same (P ++ `root_shape) (Q ++ `ShapeTrue)
  for (t, mu) in [(`root_insts, `InstsSwapped), (`root_insts, `InstsOne), (`root_kD, `KD4), (`root_wf, `WfFalse), (`http_leaf, `LeafNe), (`root_shape, `ShapeBad), (`root_shape, `ShapeK4)] do
    differs (P ++ t) (Q ++ mu); nm := nm + 1
  same (P ++ `genGP_root_kids) (Q ++ `KidsTrue)
  differs (P ++ `genGP_root_kids) (Q ++ `KidsNone); nm := nm + 1
  -- (the four obligations: each compared with its spelled-out text, mutants rejected: another value, no observation, the printed design, no hdRun, no third conjunct)
  logInfo m!"FGCIRCUIT9 SIGNATURES: synth_hftPcieOutByte_final and HftFinalStmt (complete type), HftObCD/Src/TopCore/NoRaw, root_insts/kD/wf/leaf/shape, genGP_root_kids match the independently written statements; {nm} mutants rejected (root of the run / head / post, data of another declaration in hchk, dropped head / cell / child reader / each of the four obligations / hdRun in the core obligation, child readers or the conclusion at the end world, swapped instance order, kD 4, other leaf data, other shape, callees dropped)"


/-! ## 2. the hypotheses that remain -/

run_cmd liftTermElabM do
  let thm := `Tools.ShippingFGCircuitS1kPkg.synth_hftPcieOutByte_final
  let ci ← getConstInfo thm
  let some ty ← unfoldDefinition? ci.type | throwError "the theorem's type is not a definition"
  forallTelescope ty fun xs _ => do
    let mut names : List String := []
    let mut ts : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then
        names := names ++ [d.userName.toString]
        ts := ts ++ [(d.userName.toString, ← instantiateMVars d.type)]
    let expected := ["L", "lvl", "env₀", "hstart", "hr", "hhead", "hcell", "hchk", "hreadH", "hreadT", "hcd", "hsrc", "htop", "hnoraw"]
    unless names == expected do throwError "hypotheses are {names}, expected {expected}"
    for gone in ["hquiet", "hg", "hw", "hA6", "hdRun", "hgates", "hRead", "hE", "hP", "hl", "hTop", "hd", "hcl", "hDT"] do
      if names.contains gone then throwError "{gone} is a hypothesis"
    for (n, t) in ts do
      let cs := t.getUsedConstants
      if cs.contains ``sorryAx then throwError "hypothesis {n} mentions sorryAx"
      if cs.contains ``Tools.ShippingEnvSnapshot.GetEnvFrame then throwError "{n} is GetEnvFrame"
      if cs.contains ``Tools.ShippingEnvSnapshot.EnvFrame then throwError "{n} is an all-worlds EnvFrame"
      if cs.contains ``Tools.ShippingGen5FG.EntryWitness then throwError "{n} is EntryWitness"
      if cs.contains ``Tools.ShippingFGCircuitBridge.DesignTransport then throwError "{n} is DesignTransport"
      if cs.contains ``Tools.ShippingMachineEntry.MachineDefines then throwError "{n} is the global MachineDefines"
    -- exactly four obligations
    let obl := ts.filter fun (n, _) => n ∈ ["hcd", "hsrc", "htop", "hnoraw"]
    let want : List (String × Name) := [("hcd", ``HftObCD), ("hsrc", ``HftObSrc), ("htop", ``HftObTopCore), ("hnoraw", ``HftObNoRaw)]
    for (n, c) in want do
      let some (_, t) := obl.find? (·.1 == n) | throwError "{n} missing"
      unless t.getUsedConstants.contains c do throwError "{n} does not mention {c}"
    for (n, t) in ts do
      let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<constants: {t.getUsedConstants.toList.map (·.toString)}>"
      logInfo m!"FGCIRCUIT9 REMAINING {n} : {pp}"
    logInfo "FGCIRCUIT9 HYPS: hypotheses = L lvl env₀ hstart(A.P-02) hr(A.P-04) hhead(C.EN-4 HeadAt) hcell(ReadWorld) hchk(CheckedStart: DG-ENV C0 / DG-DATAOF/COVER) hreadH hreadT(children's RootReader: DG-DATAOF/COVER/ENV) hcd(D.D-1: CD) hsrc(D.D-3: ExtStage) htop(D.D-4: TopShips machine path with instances) hnoraw(D.T-4: NoRawBelow from the run). NOT hypotheses: hquiet, GetEnvFrame, all-worlds EnvFrame, hdRun, hgates/hRead/hE of the start environment, hP (genGP covers the root: PROVED), DesignTransport (PROVED from hnoraw by topShips_transport), hw, EntryWitness"

/-! ## 3. axioms -/
run_cmd liftTermElabM do
  let P := `Tools.ShippingFGCircuitS1kPkg
  let names : List Name := [P ++ `root_wf, P ++ `http_wf, P ++ `tlp_wf, P ++ `http_leaf, P ++ `tlp_leaf, P ++ `root_insts, P ++ `root_kD, P ++ `root_shape,
    P ++ `genS_leaf_isSome, P ++ `genGP_root_kids, P ++ `hftRootType_shape, P ++ `synth_hftPcieOutByte_final]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT9 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT9: ONE environment -/

run_cmd liftTermElabM do
  let env ← getEnv
  let some ci := env.find? NmRoot | throwError "root missing"
  unless ci.levelParams.isEmpty && ci.type == hftRootType && ci.value! == hftRootValue do throwError "the root's type/value in this environment differ from hftRootType/hftRootValue"
  if ci.value! == varBad then throwError "control: varBad equals the value"
  -- the public copy has the same body as Check8's `hftOutProbe` (a copy of the private test definition)
  let some cp := env.find? ``Tests.Gen5.FGCircuitPilotCheck8.hftOutProbe | throwError "probe missing"
  unless cp.value! == ci.value! && cp.type == ci.type do throwError "the root differs from hftOutProbe (the private test definition's body)"
  let mut inv : List String := []
  let mut sigs : List (Name × Nat) := []
  for x in [NmRoot, NmHttp, NmTlp] do
    let some c := env.find? x | throwError "{x} missing"
    let E := entryConst true false [] c (instancePredicate env) (userInliner env) (structEnv env)
    unless entryGatesB env x do throwError "{x}: entryGatesB false"
    unless (certifiedShape? false [] E).isNone && (mixedCertifiedShape? false [] E (instancePredicate env)).isNone do throwError "{x}: not a machine-route declaration"
    let some s := machineShape? false [] E (structEnv env) | throwError "{x}: machineShape? none"
    let some d := Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E (structEnv env) s | throwError "{x}: dataOfAt none"
    let lit ← literalExpr (x ++ `machineData)
    unless (← dataExprOf d) == lit do throwError "{x}: dataOfAt differs from the endpoint literal machineData (whole structure)"
    sigs := sigs ++ [(x, d.shape.insts.length)]
    if x == NmRoot then
      unless d.shape.insts.map (·.1) == [NmHttp, NmTlp] do throwError "root insts are {d.shape.insts.map (·.1)}"
    else
      unless d.shape.insts.isEmpty do throwError "{x}: not a leaf"
    -- endpoint inventory
    let mut have_ : List String := []
    for sfx in ["machineData", "machine_ok", "machine_body", "machine_closes", "machine_sound", "machine_ships", "machine_ships_wired", "machine_ships_comb", "machine_closes_at", "machine_design_svHR"] do
      if env.contains (x ++ Name.mkSimple sfx) then have_ := have_ ++ [sfx]
    inv := inv ++ [s!"{x}: {have_}"]
  -- controls: the comparison rejects another declaration's data
  let lit ← literalExpr (NmHttp ++ `machineData)
  let some c := env.find? NmRoot | throwError "x"
  let E := entryConst true false [] c (instancePredicate env) (userInliner env) (structEnv env)
  let some s := machineShape? false [] E (structEnv env) | throwError "x"
  let some d := Tools.ShippingGen5DataOf.dataOfAt (fun _ => 1000000) E (structEnv env) s | throwError "x"
  if (← dataExprOf d) == lit then throwError "control: the root's data equals httpGetByte's"
  -- the children have machine_closes, the root has none: the root's closing endpoint is NOT generated
  unless env.contains (NmHttp ++ `machine_closes) && env.contains (NmTlp ++ `machine_closes) do throwError "a child has no machine_closes"
  if env.contains (NmRoot ++ `machine_closes) then throwError "the root now has machine_closes: update §15"
  logInfo m!"FGCIRCUIT9 SNAPSHOT9: in this build's environment the root's type/value Expr equal hftRootType/hftRootValue (and hftOutProbe's, the copy of the private test definition); for the root and both children: entryGatesB true, machine route (certified none, mixed none, machineShape? some), dataOfAt (fuel 1000000) equals the endpoint literal machineData over its WHOLE structure; root insts = [httpGetByte, tlpCplByte] (2), children insts = []; control: root data ≠ httpGetByte data. Endpoint inventory: {inv}. The root has machineData/machine_ok/machine_body/machine_sound and NO machine_closes / machine_ships (not generated for a module with instances). These are values of ONE environment, not kernel statements about an arbitrary run"

end Tests.Gen5.FGCircuitPilotCheck9
