import Tools.ShippingFGCircuitS1uSrc
set_option autoImplicit false
-- FG circuit pilot S1u check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §25.

/-! # FGCircuitPilotCheck19

1. SIGNATURES: complete types of `HftObSrc` (unchanged), `HftRootLink`, `hftObSrc_of_rootLink`, `ExtStage_agree_tables`, `genSemI_comb_src`, `HftFinalStmtOffL` and `synth_hftPcieOutByte_finalOffL` (+ `_Z`), against independently written statements (`isDefEq`, default
   transparency); every mutant is rejected. Mutants: swapped children, a child's src of another declaration, swapped children's data, wrong stage count `k` (1, 3), a dropped start / recurrence premise, another root's data / another declaration's observation,
   a dropped reader / link / premise, the hsrc premise kept, a reader / conclusion at the END world, the diagnostic entry, the old carrier.
2. HYPS: the explicit hypotheses of `synth_hftPcieOutByte_finalOffL_Z` by name (`hsrc` is gone; `hlink : HftRootLink` is in front), and what is not a hypothesis.
3. AXIOMS.
4. SNAPSHOT19: kernel facts about the two children's observations and the callee table. -/
namespace Tests.Gen5.FGCircuitPilotCheck19
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc
open Tools.ShippingGen5Sem Tools.ShippingMachineDenote
open Tools.ShippingUnifiedSource (eval)
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
def RootData : MachineData := synth_hftPcieOutByte.machineData
def HttpData : MachineData := Sparkle.IP.Net.HTTP.httpGetByte.machineData
def TlpData : MachineData := Sparkle.IP.Bus.PCIe.tlpCplByte.machineData

noncomputable def GPx {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Pkgs ι (fun _ => defaultDomain) :=
  genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env

/-- the table of the children's declaration-level observations (written again here). Knobs: `swapAll` (each name carries the other child entirely), `swapSrc` (both observations exchanged),
`httpOfTlp` (the http entry observes the tlp child), `dataSwap` (the two data exchanged) -/
noncomputable def HttpSrcE {ι : Type} : (i : ι) → (Nat → Signal defaultDomain Bool) → ((j n : Nat) → Signal defaultDomain (BitVec n)) → List (Nat → Nat) :=
  fun _ bools bits => Sparkle.IP.Net.HTTP.httpGetByte.machineSource defaultDomain bools bits
noncomputable def TlpSrcE {ι : Type} : (i : ι) → (Nat → Signal defaultDomain Bool) → ((j n : Nat) → Signal defaultDomain (BitVec n)) → List (Nat → Nat) :=
  fun _ bools bits => Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource defaultDomain bools bits
noncomputable def KidE {ι : Type} (decl : Name) (d : MachineData)
    (src : (i : ι) → (Nat → Signal defaultDomain Bool) → ((j n : Nat) → Signal defaultDomain (BitVec n)) → List (Nat → Nat)) : SemPkg ι (fun _ => defaultDomain) :=
  .comb ⟨decl, d, kDOf d, Tools.ShippingGen5DataOfPure.initsOf d, src⟩
noncomputable def KidsE {ι : Type} (swapAll swapSrc httpOfTlp dataSwap : Bool) : Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun c =>
  if c = NmHttp then
    some (if swapAll then KidE NmTlp TlpData TlpSrcE else KidE NmHttp (if dataSwap then TlpData else HttpData) (if swapSrc || httpOfTlp then TlpSrcE else HttpSrcE))
  else if c = NmTlp then
    some (if swapAll then KidE NmHttp HttpData HttpSrcE else KidE NmTlp (if dataSwap then HttpData else TlpData) (if swapSrc then HttpSrcE else TlpSrcE))
  else none

/-- `HftRootLink`. Knobs: the callee table; the stage count (`none` = all calls: `insts.length`; `some n` = the first `n`); the start premise; the recurrence premise; the declaration observed in the conclusion; the data `gi` is over -/
def StageK (gi : GenIn) (k : Option Nat) : Nat := k.getD gi.d.shape.insts.length
def ExpLink (kids : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain))) (k : Option Nat) (needStart needRec : Bool) (obsRoot : Bool) (dataIs : MachineData) : Prop :=
  ∀ {ι : Type} (gi : GenIn), gi.d = dataIs → ∀ (i : ι) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n))
    (S : Signal defaultDomain (HList (tys gi.d.ss))),
    (if needStart then S.val 0 = gi.inits else True) →
    (if needRec then (∀ t, S.val (t + 1) = evalTerms
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (ExtStage (dom := fun _ => defaultDomain) (kids ι) gi i bools bits S (StageK gi k)).1
        (ExtStage (dom := fun _ => defaultDomain) (kids ι) gi i bools bits S (StageK gi k)).2 t (S.val t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (ExtStage (dom := fun _ => defaultDomain) (kids ι) gi i bools bits S (StageK gi k)).1
        (ExtStage (dom := fun _ => defaultDomain) (kids ι) gi i bools bits S (StageK gi k)).2 t (S.val t)).v (gi.d.vpos j) w) gi.d.nexts) else True) →
    ∀ t, (if obsRoot then monoObs ShE synth_hftPcieOutByte bools bits else monoObs ShE synth_hftPcieOutByte (fun _ => bools 0) bits).map (fun f => f t) = gi.d.outs.map fun o => enc o.1 (eval
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (ExtStage (dom := fun _ => defaultDomain) (kids ι) gi i bools bits S (StageK gi k)).1
        (ExtStage (dom := fun _ => defaultDomain) (kids ι) gi i bools bits S (StageK gi k)).2 t (S.val t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (ExtStage (dom := fun _ => defaultDomain) (kids ι) gi i bools bits S (StageK gi k)).1
        (ExtStage (dom := fun _ => defaultDomain) (kids ι) gi i bools bits S (StageK gi k)).2 t (S.val t)).v (gi.d.vpos j) w) o.2)

def KidsTrue : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun ι => KidsE (ι := ι) false false false false
def KidsSwapAll : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun ι => KidsE (ι := ι) true false false false
def KidsSwapSrc : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun ι => KidsE (ι := ι) false true false false
def KidsHttpOfTlp : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun ι => KidsE (ι := ι) false false true false
def KidsDataSwap : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun ι => KidsE (ι := ι) false false false true
def KidsNone : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun _ _ => none
def LinkTrue := ExpLink KidsTrue none true true true RootData
def LinkSwapAll := ExpLink KidsSwapAll none true true true RootData
def LinkSwapSrc := ExpLink KidsSwapSrc none true true true RootData
def LinkHttpOfTlp := ExpLink KidsHttpOfTlp none true true true RootData
def LinkDataSwap := ExpLink KidsDataSwap none true true true RootData
def LinkNoKids := ExpLink KidsNone none true true true RootData
def LinkK1 := ExpLink KidsTrue (some 1) true true true RootData
def LinkK3 := ExpLink KidsTrue (some 3) true true true RootData
def LinkK0 := ExpLink KidsTrue (some 0) true true true RootData
def LinkNoStart := ExpLink KidsTrue none false true true RootData
def LinkNoRec := ExpLink KidsTrue none true false true RootData
def LinkObsOther := ExpLink KidsTrue none true true false RootData
def LinkHttpData := ExpLink KidsTrue none true true true HttpData

/-- `HftObSrc` (unchanged from S1k). Knobs: the observation; the declaration the table row is asked for -/
def ExpObSrc (obs : Bool) (nm : Name) {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Prop :=
  ∀ p : Pkg ι (fun _ => defaultDomain), GPx (ι := ι) lvl env nm = some p →
    ∀ i bools bits, p.src i bools bits = (if obs then monoObs ShE synth_hftPcieOutByte bools bits else [])

/-- `hftObSrc_of_rootLink`. Knobs: the link premise; each reader; the readers at the right names (false: root's reader is asked of the http child's data) -/
def ExpSrcThm (needLink needRd needRdH needRdT rdOk : Bool) (nm : Name) : Prop :=
  ∀ (hlink : if needLink then LinkTrue else True) {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    (if needRd then RootReader lvl env NmRoot (if rdOk then RootData else HttpData) else True) →
    (if needRdH then RootReader lvl env NmHttp HttpData else True) →
    (if needRdT then RootReader lvl env NmTlp TlpData else True) →
    ExpObSrc true nm (ι := ι) lvl env
def SrcThmTrue := ExpSrcThm true true true true true NmRoot
def SrcThmNoLink := ExpSrcThm false true true true true NmRoot
def SrcThmNoRd := ExpSrcThm true false true true true NmRoot
def SrcThmNoRdH := ExpSrcThm true true false true true NmRoot
def SrcThmNoRdT := ExpSrcThm true true true false true NmRoot
def SrcThmRdData := ExpSrcThm true true true true false NmRoot
def SrcThmOtherDecl := ExpSrcThm true true true true true NmHttp

/-- the `ExtStage` induction. Knobs: which of the three fields of a callee package the agreement asks for -/
def ExpStageAgree (needD needKD needSrc : Bool) : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (Q Q' : Name → Option (SemPkg ι dom)) (g : GenIn),
    (∀ (k : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder), g.d.shape.insts[k]? = some (c, a, κ) →
      (Q c = none ∧ Q' c = none) ∨ ∃ q q', Q c = some q ∧ Q' c = some q' ∧
        (if needD then q.d = q'.d else True) ∧ (if needKD then q.kD = q'.kD else True) ∧ (if needSrc then q.src = q'.src else True)) →
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (S : Signal (dom i) (HList (tys g.d.ss))) (n : Nat),
      ExtStage Q g i bools bits S n = ExtStage Q' g i bools bits S n
def StageTrue := ExpStageAgree true true true
def StageNoSrc := ExpStageAgree true true false
def StageNoKD := ExpStageAgree true false true
def StageNoD := ExpStageAgree false true true

/-- a combinational leaf's `src`. Knobs: `ss = []`, `insts = []`, the observation equation -/
def ExpCombSrc (needSs needIn needRes : Bool) : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (gi : GenIn) {d : MachineData}, gi.d = d →
    (if needSs then d.ss = [] else True) → (if needIn then d.shape.insts = [] else True) →
    ∀ (obs : (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)),
      (if needRes then (∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (t : Nat) (x : HList (tys d.ss)),
        (obs i bools bits).map (fun f => f t) = d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).v (d.vpos k) w) o.2)) else True) →
      (genSemI Q X gi).src = obs
def CombTrue := ExpCombSrc true true true
def CombNoSs := ExpCombSrc false true true
def CombNoIn := ExpCombSrc true false true
def CombNoRes := ExpCombSrc true true false

/-- the final statement with `hsrc` discharged. Knobs (each mutant turns one): the link premise; the (kept) `hsrc` premise; the diagnostic entry in `hr`; the old carrier in the conclusion;
the other premises; the root; the post root; the data in `hchk`; the world of the child readers / `hcd` / the conclusion -/
def EntryOf (diag : Bool) (X : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) :=
  if diag then synthesizeCombinational X else synthesizeCombinationalOff X
def ExpFinalL (Ob : Environment → Prop) (CV : CDRel) (needLink keepSrc diag oldArt needCell needChk needRdH needRdT needCD needTop needNoRaw hdRunIn : Bool)
    (root postRoot : Name) (chk : MachineData) (rdw hw cw : W → W → W) : Prop :=
  (if needLink then LinkTrue else True) →
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
    (if keepSrc then ExpObSrc true NmRoot (ι := ι) lvl (envAt cref w) else True) →
    (if needTop then (∀ p : Pkg ι (fun _ => defaultDomain), GPx (ι := ι) lvl (envAt cref w) NmRoot = some p →
        ((if hdRunIn then (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
            MachineDefinesLinkedOff mctx mref cctx cref NmRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1) else True) →
          ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
            RunsTo (synthesizeCombinationalCoreOff NmRoot) mctx mref cctx cref w (raw, D₀) w1 →
            Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → ∃ n, TopShips p n NmRoot b raw D₀)) else True) →
    (if needNoRaw then (∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : W),
        RunsTo (synthesizeCombinationalCoreOff NmRoot) mctx mref cctx cref w (raw, D₀) w1 →
        Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' →
        (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) raw) ∧
        (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) (Sparkle.IR.OptCheck.checkedOptimize b)) ∧
        (∀ mn iname conns, Sparkle.IR.AST.Stmt.inst mn iname conns ∈ b.body → mn ≠ raw.name)) else True) →
    (∃ raw, PostRunOff mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy ShE) (p : Pkg ι (fun _ => defaultDomain)),
      (if oldArt then RootArtifactMono (envAt cref (cw w w')) (GPx (ι := ι) lvl (envAt cref (cw w w'))) (PostRunOff mctx mref cctx cref w postRoot D') NmRoot ShE mm b D' p
       else RootArtifactMonoV CV (envAt cref (cw w w')) (GPx (ι := ι) lvl (envAt cref (cw w w'))) (PostRunOff mctx mref cctx cref w postRoot D') NmRoot ShE mm b D' p)

def FL (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoLink (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV false false false false true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MKeepSrc (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true true false false true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MDiag (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false true false true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MOldArt (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false true true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoCell (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false false true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoChk (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true false true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoRdH (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true false true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoRdT (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true false true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoCD (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true false true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoTop (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true true false true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoNoRaw (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true true true false true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MNoHdRun (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true true true true false NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MRoot (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true true true true true NmOther NmRoot synth_hftPcieOutByte.machineData ZS ZS ZS
def MPostRoot (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true true true true true NmRoot NmHttp synth_hftPcieOutByte.machineData ZS ZS ZS
def MChk (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true true true true true NmRoot NmRoot Sparkle.IP.Net.HTTP.httpGetByte.machineData ZS ZS ZS
def MRdEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZE ZS ZS
def MHcdEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZE ZS
def MConclEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalL Ob CV true false false false true true true true true true true true NmRoot NmRoot synth_hftPcieOutByte.machineData ZS ZS ZE

/-- the assembly theorem for every carrier and every obligation with the bridge `hOb` -/
def ExpThmL (S : (Environment → Prop) → CDRel → Prop) (needH : Bool) (hv : Lean.Expr) : Prop :=
  ∀ (CV : CDRel) (Ob : Environment → Prop),
    (if needH then (∀ env, Ob env → CV env hv (MonoTy ShE) synth_hftPcieOutByte) else True) → S Ob CV
def ThmLTrue := ExpThmL FL true hftRootValue
def TLNoH := ExpThmL FL false hftRootValue
def TLHOther := ExpThmL FL true varBad
def TLNoLink := ExpThmL MNoLink true hftRootValue
def TLKeepSrc := ExpThmL MKeepSrc true hftRootValue
def TLDiag := ExpThmL MDiag true hftRootValue
def TLOldArt := ExpThmL MOldArt true hftRootValue
def TLNoCell := ExpThmL MNoCell true hftRootValue
def TLNoChk := ExpThmL MNoChk true hftRootValue
def TLNoRdH := ExpThmL MNoRdH true hftRootValue
def TLNoRdT := ExpThmL MNoRdT true hftRootValue
def TLNoCD := ExpThmL MNoCD true hftRootValue
def TLNoTop := ExpThmL MNoTop true hftRootValue
def TLNoNoRaw := ExpThmL MNoNoRaw true hftRootValue
def TLNoHdRun := ExpThmL MNoHdRun true hftRootValue
def TLRoot := ExpThmL MRoot true hftRootValue
def TLPostRoot := ExpThmL MPostRoot true hftRootValue
def TLChk := ExpThmL MChk true hftRootValue
def TLRdEnd := ExpThmL MRdEnd true hftRootValue
def TLHcdEnd := ExpThmL MHcdEnd true hftRootValue
def TLConclEnd := ExpThmL MConclEnd true hftRootValue

def ZTrue : Prop := FL HftObCDZ cdvZ
def ZCarrierY : Prop := FL HftObCDZ cdvY
def ZCarrierOld : Prop := FL HftObCDZ cdvOld
def ZObY : Prop := FL HftObCDY cdvZ

set_option maxHeartbeats 16000000 in
run_cmd liftTermElabM do
  let same (thm exp : Lean.Expr) : MetaM Unit := do
    let ci ← getConstInfo thm.constName!
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    unless ← withDefault (isDefEq ci.type exp) do throwError "{thm}: type is NOT the expected statement {exp}"
  let sameT (a b : Lean.Expr) (what : String) : MetaM Unit := do
    unless ← withDefault (isDefEq a b) do throwError "{what}: differs from the expected statement"
  let diffT (a b : Lean.Expr) (what : String) : MetaM Unit := do
    if ← withDefault (isDefEq a b) then throwError "{what}: the MUTANT was accepted"
  let C (n : Name) : Lean.Expr := mkConst n
  let Q := `Tests.Gen5.FGCircuitPilotCheck19
  let U := `Tools.ShippingFGCircuitS1uSrc
  let q (n : String) : Lean.Expr := mkConst (Q ++ Name.mkSimple n)
  let mut nm : Nat := 0
  -- HftRootLink
  sameT (C (U ++ `HftRootLink)) (q "LinkTrue") "HftRootLink"
  for mu in ["LinkSwapAll", "LinkSwapSrc", "LinkHttpOfTlp", "LinkDataSwap", "LinkNoKids", "LinkK1", "LinkK3", "LinkK0", "LinkNoStart", "LinkNoRec", "LinkObsOther", "LinkHttpData"] do
    diffT (C (U ++ `HftRootLink)) (q mu) s!"HftRootLink vs {mu}"; nm := nm + 1
  -- HftObSrc (unchanged)
  let tt := C ``true
  let ff := C ``false
  let obsrc (obs : Lean.Expr) (n : Name) : Lean.Expr := mkAppN (q "ExpObSrc") #[obs, toExpr n]
  sameT (C (`Tools.ShippingFGCircuitS1kStmt ++ `HftObSrc)) (obsrc tt NmRoot) "HftObSrc"
  diffT (C (`Tools.ShippingFGCircuitS1kStmt ++ `HftObSrc)) (obsrc ff NmRoot) "HftObSrc vs no observation"; nm := nm + 1
  diffT (C (`Tools.ShippingFGCircuitS1kStmt ++ `HftObSrc)) (obsrc tt NmHttp) "HftObSrc vs another declaration"; nm := nm + 1
  -- hftObSrc_of_rootLink
  same (C (U ++ `hftObSrc_of_rootLink)) (q "SrcThmTrue")
  for mu in ["SrcThmNoLink", "SrcThmNoRd", "SrcThmNoRdH", "SrcThmNoRdT", "SrcThmRdData", "SrcThmOtherDecl"] do
    diffT (← getConstInfo (U ++ `hftObSrc_of_rootLink)).type (q mu) s!"hftObSrc_of_rootLink vs {mu}"; nm := nm + 1
  -- the ExtStage induction and the combinational leaf
  same (C (U ++ `ExtStage_agree_tables)) (q "StageTrue")
  for mu in ["StageNoSrc", "StageNoKD", "StageNoD"] do
    diffT (← getConstInfo (U ++ `ExtStage_agree_tables)).type (q mu) s!"ExtStage_agree_tables vs {mu}"; nm := nm + 1
  same (C (U ++ `genSemI_comb_src)) (q "CombTrue")
  for mu in ["CombNoSs", "CombNoIn", "CombNoRes"] do
    diffT (← getConstInfo (U ++ `genSemI_comb_src)).type (q mu) s!"genSemI_comb_src vs {mu}"; nm := nm + 1
  -- the final statement and the assembly theorem
  let S1t := `Tools.ShippingFGCircuitS1tFinal
  let mkL (Ob CV : Lean.Expr) (f : String) : Lean.Expr := mkAppN (q f) #[Ob, CV]
  let genericThm := (← getConstInfo (U ++ `synth_hftPcieOutByte_finalOffL)).type
  sameT genericThm (q "ThmLTrue") "synth_hftPcieOutByte_finalOffL"
  for mu in ["TLNoH", "TLHOther", "TLNoLink", "TLKeepSrc", "TLDiag", "TLOldArt", "TLNoCell", "TLNoChk", "TLNoRdH", "TLNoRdT", "TLNoCD", "TLNoTop", "TLNoNoRaw", "TLNoHdRun", "TLRoot", "TLPostRoot", "TLChk", "TLRdEnd", "TLHcdEnd", "TLConclEnd"] do
    diffT genericThm (q mu) s!"synth_hftPcieOutByte_finalOffL vs {mu}"; nm := nm + 1
  -- HftFinalStmtOffL (the statement itself), at the Z carrier
  same (C (U ++ `synth_hftPcieOutByte_finalOffL_Z)) (q "ZTrue")
  diffT (← getConstInfo (U ++ `synth_hftPcieOutByte_finalOffL_Z)).type (q "ZCarrierY") "finalOffL_Z vs cdvY"; nm := nm + 1
  diffT (← getConstInfo (U ++ `synth_hftPcieOutByte_finalOffL_Z)).type (q "ZCarrierOld") "finalOffL_Z vs cdvOld"; nm := nm + 1
  diffT (← getConstInfo (U ++ `synth_hftPcieOutByte_finalOffL_Z)).type (q "ZObY") "finalOffL_Z vs HftObCDY"; nm := nm + 1
  logInfo m!"FGCIRCUIT19 SIGNATURES: HftObSrc (unchanged), HftRootLink, hftObSrc_of_rootLink, ExtStage_agree_tables, genSemI_comb_src, synth_hftPcieOutByte_finalOffL and _Z match the independently written statements; {nm} mutants rejected"

end Tests.Gen5.FGCircuitPilotCheck19
