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
noncomputable def RootData : MachineData := synth_hftPcieOutByte.machineData
noncomputable def HttpData : MachineData := Sparkle.IP.Net.HTTP.httpGetByte.machineData
noncomputable def TlpData : MachineData := Sparkle.IP.Bus.PCIe.tlpCplByte.machineData

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

noncomputable def KidsTrue : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun ι => KidsE (ι := ι) false false false false
noncomputable def KidsSwapAll : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun ι => KidsE (ι := ι) true false false false
noncomputable def KidsSwapSrc : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun ι => KidsE (ι := ι) false true false false
noncomputable def KidsHttpOfTlp : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun ι => KidsE (ι := ι) false false true false
noncomputable def KidsDataSwap : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun ι => KidsE (ι := ι) false false false true
noncomputable def KidsNone : (ι : Type) → Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun _ _ => none
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
/-- `Pre b P R`: the premise `P` is present iff `b` (no vacuous `True →` when it is absent) -/
def Pre (b : Bool) (P R : Prop) : Prop := if b then (P → R) else R
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
    Pre keepSrc (ExpObSrc true NmRoot (ι := ι) lvl (envAt cref w)) (
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
       else RootArtifactMonoV CV (envAt cref (cw w w')) (GPx (ι := ι) lvl (envAt cref (cw w w'))) (PostRunOff mctx mref cctx cref w postRoot D') NmRoot ShE mm b D' p))

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

def whitelist : List Name := [``StageK, ``ExpLink, ``KidsE, ``KidsTrue, ``KidsSwapAll, ``KidsSwapSrc, ``KidsHttpOfTlp, ``KidsDataSwap, ``KidsNone,
  ``LinkTrue, ``LinkSwapAll, ``LinkSwapSrc, ``LinkHttpOfTlp, ``LinkDataSwap, ``LinkNoKids, ``LinkK1, ``LinkK3, ``LinkK0, ``LinkNoStart, ``LinkNoRec, ``LinkObsOther, ``LinkHttpData,
  ``ExpObSrc, ``ExpSrcThm, ``SrcThmTrue, ``SrcThmNoLink, ``SrcThmNoRd, ``SrcThmNoRdH, ``SrcThmNoRdT, ``SrcThmRdData, ``SrcThmOtherDecl,
  ``ExpStageAgree, ``StageTrue, ``StageNoSrc, ``StageNoKD, ``StageNoD, ``ExpCombSrc, ``CombTrue, ``CombNoSs, ``CombNoIn, ``CombNoRes,
  ``EntryOf, ``Pre, ``ExpFinalL, ``FL, ``MNoLink, ``MKeepSrc, ``MDiag, ``MOldArt, ``MNoCell, ``MNoChk, ``MNoRdH, ``MNoRdT, ``MNoCD, ``MNoTop, ``MNoNoRaw, ``MNoHdRun, ``MRoot, ``MPostRoot, ``MChk,
  ``MRdEnd, ``MHcdEnd, ``MConclEnd, ``ExpThmL, ``ThmLTrue, ``TLNoH, ``TLHOther, ``TLNoLink, ``TLKeepSrc, ``TLDiag, ``TLOldArt, ``TLNoCell, ``TLNoChk, ``TLNoRdH, ``TLNoRdT, ``TLNoCD,
  ``TLNoTop, ``TLNoNoRaw, ``TLNoHdRun, ``TLRoot, ``TLPostRoot, ``TLChk, ``TLRdEnd, ``TLHcdEnd, ``TLConclEnd, ``ZTrue, ``ZCarrierY, ``ZCarrierOld, ``ZObY, ``ZS, ``ZE, ``GPx,
  ``RootData, ``HttpData, ``TlpData,
  -- definitions under test (unfolded on the theorem side)
  ``HftRootLink, ``HftFinalStmtOffL, ``HftObTopCoreOff, ``HftObNoRawOff, ``HftObSrc, ``GPt, ``HftObOf, ``cdvOld, ``cdvX, ``cdvY, ``cdvZ, ``hftKids]

/-- a literal Boolean (`true`, `false`, `or`/`and` of literals) -/
partial def litBool : Lean.Expr → Option Bool
  | .const ``Bool.true _ => some true
  | .const ``Bool.false _ => some false
  | e => if e.isAppOfArity ``or 2 then (do let a ← litBool (e.getArg! 0); let b ← litBool (e.getArg! 1); pure (a || b))
         else if e.isAppOfArity ``and 2 then (do let a ← litBool (e.getArg! 0); let b ← litBool (e.getArg! 1); pure (a && b))
         else none

/-- `if b then x else y` with a literal Boolean `b`: the chosen branch -/
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
  -- the normal form of the real type is computed once per type (the mutants of one statement share it)
  let cache ← IO.mkRef (∅ : Std.HashMap Lean.Expr Lean.Expr)
  let normC (ty : Lean.Expr) : MetaM Lean.Expr := do
    if let some a := (← cache.get)[ty]? then return a
    let a ← norm ty
    cache.modify (·.insert ty a)
    return a
  let sameE (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
    let a ← normC ty
    let e ← norm exp
    unless ← withDefault (isDefEq a e) do throwError "{what}: type is NOT the expected statement"
    unless binderInfos a == binderInfos e do throwError "{what}: binder kinds differ"
  let diffE (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
    let a ← normC ty
    let e ← norm exp
    if a == e then throwError "{what}: the MUTANT is the same expression"
    if ← withReducible (isDefEq a e) then throwError "{what}: the MUTANT was accepted"
  let C (n : Name) : Lean.Expr := mkConst n
  let Q := `Tests.Gen5.FGCircuitPilotCheck19
  let U := `Tools.ShippingFGCircuitS1uSrc
  let q (n : String) : Lean.Expr := mkConst (Q ++ Name.mkSimple n)
  let tyOf (n : Name) : MetaM Lean.Expr := do
    let ci ← getConstInfo n
    unless ci.levelParams.isEmpty do throwError "{n}: level parameters"
    pure ci.type
  let mut nm : Nat := 0
  -- HftRootLink
  sameE "HftRootLink" (C (U ++ `HftRootLink)) (q "LinkTrue")
  for mu in ["LinkSwapAll", "LinkSwapSrc", "LinkHttpOfTlp", "LinkDataSwap", "LinkNoKids", "LinkK1", "LinkK3", "LinkK0", "LinkNoStart", "LinkNoRec", "LinkObsOther", "LinkHttpData"] do
    diffE s!"HftRootLink vs {mu}" (C (U ++ `HftRootLink)) (q mu); nm := nm + 1
  -- HftObSrc (unchanged), compared as an applied definition
  let tt := C ``true
  let ff := C ``false
  let hsrcT := C (`Tools.ShippingFGCircuitS1kStmt ++ `HftObSrc)
  let appliedObSrc (obs : Lean.Expr) (n : Name) : MetaM (Lean.Expr × Lean.Expr) := do
    forallTelescope (← inferType hsrcT) fun xs _ => do
      let a ← mkLambdaFVars xs (mkAppN hsrcT xs)
      let b ← mkLambdaFVars xs (mkAppN (q "ExpObSrc") (#[obs, toExpr n] ++ xs))
      pure (a, b)
  let (a1, b1) ← appliedObSrc tt NmRoot
  sameE "HftObSrc" a1 b1
  let (a2, b2) ← appliedObSrc ff NmRoot
  diffE "HftObSrc vs no observation" a2 b2; nm := nm + 1
  let (a3, b3) ← appliedObSrc tt NmHttp
  diffE "HftObSrc vs another declaration" a3 b3; nm := nm + 1
  -- hftObSrc_of_rootLink
  let srcThm ← tyOf (U ++ `hftObSrc_of_rootLink)
  sameE "hftObSrc_of_rootLink" srcThm (q "SrcThmTrue")
  for mu in ["SrcThmNoLink", "SrcThmNoRd", "SrcThmNoRdH", "SrcThmNoRdT", "SrcThmRdData", "SrcThmOtherDecl"] do
    diffE s!"hftObSrc_of_rootLink vs {mu}" srcThm (q mu); nm := nm + 1
  -- the ExtStage induction and the combinational leaf
  let stageThm ← tyOf (U ++ `ExtStage_agree_tables)
  sameE "ExtStage_agree_tables" stageThm (q "StageTrue")
  for mu in ["StageNoSrc", "StageNoKD", "StageNoD"] do
    diffE s!"ExtStage_agree_tables vs {mu}" stageThm (q mu); nm := nm + 1
  let combThm ← tyOf (U ++ `genSemI_comb_src)
  sameE "genSemI_comb_src" combThm (q "CombTrue")
  for mu in ["CombNoSs", "CombNoIn", "CombNoRes"] do
    diffE s!"genSemI_comb_src vs {mu}" combThm (q mu); nm := nm + 1
  -- the assembly theorem, over every carrier and obligation
  let genericThm ← tyOf (U ++ `synth_hftPcieOutByte_finalOffL)
  sameE "synth_hftPcieOutByte_finalOffL" genericThm (q "ThmLTrue")
  for mu in ["TLNoH", "TLHOther", "TLNoLink", "TLKeepSrc", "TLDiag", "TLOldArt", "TLNoCell", "TLNoChk", "TLNoRdH", "TLNoRdT", "TLNoCD", "TLNoTop", "TLNoNoRaw", "TLNoHdRun", "TLRoot", "TLPostRoot", "TLChk", "TLRdEnd", "TLHcdEnd", "TLConclEnd"] do
    diffE s!"synth_hftPcieOutByte_finalOffL vs {mu}" genericThm (q mu); nm := nm + 1
  -- the instance at the Z carrier is the statement `HftFinalStmtOffL HftObCDZ cdvZ`
  let zThm ← tyOf (U ++ `synth_hftPcieOutByte_finalOffL_Z)
  sameE "synth_hftPcieOutByte_finalOffL_Z" zThm (q "ZTrue")
  for mu in ["ZCarrierY", "ZCarrierOld", "ZObY"] do
    diffE s!"finalOffL_Z vs {mu}" zThm (q mu); nm := nm + 1
  let mutZ := [`MNoLink, `MKeepSrc, `MDiag, `MOldArt, `MNoCell, `MNoChk, `MNoRdH, `MNoRdT, `MNoCD, `MNoTop, `MNoNoRaw, `MNoHdRun, `MRoot, `MPostRoot, `MChk, `MRdEnd, `MHcdEnd, `MConclEnd]
  for mu in mutZ do
    diffE s!"finalOffL_Z vs {mu}" zThm (mkApp2 (mkConst (Q ++ mu)) (C ``HftObCDZ) (C (`Tools.ShippingFGCircuitS1tFinal ++ `cdvZ))); nm := nm + 1
  logInfo m!"FGCIRCUIT19 SIGNATURES: HftObSrc (unchanged), HftRootLink, hftObSrc_of_rootLink, ExtStage_agree_tables, genSemI_comb_src, synth_hftPcieOutByte_finalOffL and its Z instance match the independently written statements (binder kinds too); {nm} mutants rejected (normalised expression different and not reducible-defeq)"

/-! ## 2. the hypotheses -/

run_cmd liftTermElabM do
  let env ← getEnv
  let U := `Tools.ShippingFGCircuitS1uSrc
  let ci ← getConstInfo (U ++ `synth_hftPcieOutByte_finalOffL_Z)
  let some ty ← unfoldDefinition? ci.type | throwError "the instance's type is not a definition"
  let names ← forallTelescope ty fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, ← instantiateMVars d.type)]
    return hs
  let expected := ["hlink", "L", "lvl", "env₀", "hstart", "hr", "hcell", "hchk", "hreadH", "hreadT", "hcd", "htop", "hnoraw"]
  unless names.map (·.1) == expected do throwError "hypotheses are {names.map (·.1)}, expected {expected}"
  for gone in ["hsrc", "hhead", "hdRun", "hquiet", "hg", "hio", "hgates", "hRead", "hE", "hP", "hdesign", "hcdOld"] do
    if (names.map (·.1)).contains gone then throwError "{gone} is a hypothesis"
  -- no hypothesis mentions the (removed) `HftObSrc`, a diagnostic entry, or sorry
  let diag : List Name := [``synthesizeCombinational, ``synthesizeCombinationalCore, ``synthesizeEntry, ``Tools.ShippingFGCircuitLinked.MachineDefinesLinked, ``Tools.ShippingFGCircuitBridge.PostRun,
    ``Tools.ShippingEntryReadsLinked.coreHead, ``synthesizeChild, ``HftObSrc, ``sorryAx]
  for (n, t) in names do
    let mut used := t.getUsedConstants
    for c in t.getUsedConstants do
      if c.toString.startsWith "Tools.ShippingFGCircuitS1t" || c.toString.startsWith "Tools.ShippingFGCircuitS1kStmt" || c.toString.startsWith "Tools.ShippingFGCircuitS1u" then
        match env.find? c with
        | some (.defnInfo dd) => used := used ++ dd.value.getUsedConstants
        | _ => pure ()
    for b in diag do
      if used.contains b then throwError "hypothesis {n} mentions {b}"
    let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<unprintable; constants: {t.getUsedConstants.toList.map (·.toString)}>"
    logInfo m!"FGCIRCUIT19 REMAINING {n} : {pp}"
  -- hlink is run-independent: it mentions no world, no context, no environment
  let some (_, hl) := names.find? (·.1 == "hlink") | throwError "hlink missing"
  let mut used := hl.getUsedConstants
  for c in hl.getUsedConstants do
    if c.toString.startsWith "Tools.ShippingFGCircuitS1u" then
      match env.find? c with
      | some (.defnInfo dd) => used := used ++ dd.value.getUsedConstants
      | _ => pure ()
  for b in [``RunsTo, ``Lean.Environment, ``Lean.Core.Context, ``Lean.Meta.Context, ``Tools.ShippingFGCircuitLinked.MachineDefinesLinked, ``Tools.ShippingEntryReadsLinked.envAt] do
    if used.contains b then throwError "hlink mentions {b}"
  -- the assembly theorem's explicit arguments
  let ci2 ← getConstInfo (U ++ `synth_hftPcieOutByte_finalOffL)
  let bs ← forallTelescope ci2.type fun xs _ => do
    let mut r : List String := []
    for x in xs do
      let dd ← x.fvarId!.getDecl
      if dd.binderInfo.isExplicit then r := r ++ [dd.userName.toString]
    return r
  unless bs == ["CV", "Ob", "hOb"] do throwError "synth_hftPcieOutByte_finalOffL: explicit arguments are {bs}"
  logInfo m!"FGCIRCUIT19 HYPS: HftFinalStmtOffL Ob CV = hlink(HftRootLink: run-independent, D.D-3 / DG-SEM) L lvl env₀ hstart hr(synthesizeCombinationalOff) hcell(CellPrem) hchk hreadH hreadT hcd(Ob (envAt cref w)) htop(HftObTopCoreOff) hnoraw(HftObNoRawOff): {names.length} explicit hypotheses (S1t: 13 with hsrc; here hsrc is replaced by hlink, count unchanged). NOT hypotheses: hsrc, hhead, hdRun, hquiet, hg, hio, hgates, hRead, hE, hP. The theorem's explicit arguments: CV Ob hOb."

/-! ## 3. axioms -/

run_cmd liftTermElabM do
  let U := `Tools.ShippingFGCircuitS1uSrc
  let names : List Name := [U ++ `ExtStage_agree_tables, U ++ `calleeOut_agree_tables, U ++ `callOut_agree_tables, U ++ `genSemGen_agree_tables, U ++ `genSemGen_src_eq_of_link,
    U ++ `genSemI_comb_src, U ++ `genS_leaf_eq, U ++ `genGP_root_kids_src, U ++ `hftObSrc_of_rootLink, U ++ `hftGenIn, U ++ `hftGenIn_d, U ++ `root_insts_nonempty, U ++ `http_ss, U ++ `tlp_ss,
    U ++ `synth_hftPcieOutByte_finalOffL, U ++ `synth_hftPcieOutByte_finalOffL_Z, U ++ `synth_hftPcieOutByte_finalOffL_Y, U ++ `synth_hftPcieOutByte_finalOffL_X, U ++ `synth_hftPcieOutByte_finalOffL_of]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT19 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT19: the callee table and the children's observations -/

/-- the children's declaration-level observations, spelled out in Lean (kernel `rfl`) -/
example (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) :
    Sparkle.IP.Net.HTTP.httpGetByte.machineSource defaultDomain bools bits = [fun t => ((Sparkle.IP.Net.HTTP.httpGetByte (bits 1 6)).val t).toNat] := rfl
example (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) :
    Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource defaultDomain bools bits =
      [fun t => ((Sparkle.IP.Bus.PCIe.tlpCplByte (bits 1 16) (bits 2 16) (bits 3 8) (bits 4 8) (bits 5 32) (bits 6 5)).val t).toNat] := rfl
/-- the static table has exactly the two children: both present, nothing else -/
example {ι : Type} : (hftKids (ι := ι) hftHttp).isSome = true := by simp [hftKids]
example {ι : Type} : (hftKids (ι := ι) hftTlp).isSome = true := by simp [hftKids, hftTlp_ne_http]
example {ι : Type} : hftKids (ι := ι) `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte = none := by
  simp [hftKids, hftHttp, hftTlp, hftRoot]
/-- the quantifier over `GenIn` in `HftRootLink` is not empty -/
example : hftGenIn.d = synth_hftPcieOutByte.machineData := rfl
/-- the root's callees are the two children, in this order; the stage count is `insts.length = 2` -/
example : synth_hftPcieOutByte.machineData.shape.insts.length = 2 := by decide +kernel
example : synth_hftPcieOutByte.machineData.shape.insts.map (·.1) = [hftHttp, hftTlp] := by decide +kernel

run_cmd liftTermElabM do
  let env ← getEnv
  -- the two children are combinational leaves (no state, no calls) on the machine route; the root has two calls and states
  for (x, leaf) in [(NmHttp, true), (NmTlp, true), (NmRoot, false)] do
    unless env.contains (x ++ `machine_result) do throwError "{x}: no machine_result"
    unless env.contains (x ++ `machineSource) do throwError "{x}: no machineSource"
    if leaf then
      unless env.contains (x ++ `machine_next) do throwError "{x}: a combinational leaf has machine_next"
  -- the root has machineExt (the call streams as the Lean calls over the state), no machineSigma: the fused-state link is not an endpoint fact
  unless env.contains (NmRoot ++ `machineExt) do throwError "the root has no machineExt"
  if env.contains (NmRoot ++ `machineSigma) then throwError "the root now has machineSigma: update §25.3 (b)"
  if env.contains (NmRoot ++ `machine_closes) then throwError "the root now has machine_closes: update §15/§25"
  logInfo m!"FGCIRCUIT19 SNAPSHOT19: the children's machineSource are the declarations' observations (kernel rfl); hftKids has exactly the two children; hftGenIn : GenIn over the root's data exists; the root has machineExt and no machineSigma (the fused-state link and the call-argument link are not endpoint facts: HftRootLink stays a named hypothesis)"

end Tests.Gen5.FGCircuitPilotCheck19
