import Tools.ShippingFGCircuitS1kRoot
import Tools.ShippingFGCircuitS1iRoots
import Tools.ShippingFGCircuitS1iChild
set_option autoImplicit false
-- FG circuit pilot S1k, unit 2: the COMPLETE statement of the non-leaf root's final theorem, with every unproved obligation as a named Prop. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `synth_hftPcieOutByte_final`: the type, fixed before any proof

Root: `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte` (the public copy of the private test definition `Tests/IP/Bus/PCIeHFTTest.lean:89`; same body), two children `httpGetByte`, `tlpCplByte` (both `@[hardware_module]`, leaves with `insts = []`).
Shape: `shHft` (5 input streams, one 8-bit output). Same conclusion as `X_final10`; the premises are `X_final10`'s (`Laws L`, `hstart`, `hr`, `hhead`, `hcell`, `hchk`) plus the readers of the two children and four NAMED obligations (`HftObCD`, `HftObSrc`, `HftObTopCore`, `HftObNoRaw`). -/
namespace Tools.ShippingFGCircuitS1kStmt
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingFGCircuitS1kRoot
open Tools.ShippingFGCircuitLinked (MachineDefinesLinked)

/-- the root's name -/
def hftRoot : Name := ``Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte
def hftHttp : Name := ``Sparkle.IP.Net.HTTP.httpGetByte
def hftTlp : Name := ``Sparkle.IP.Bus.PCIe.tlpCplByte

/-- the shape: `rxByte : bits 8`, `rxValid sopTlp : bool`, `dataDword : bits 32`, `cplId : bits 16`; one 8-bit output -/
def shHft : SigShape := { args := [.bits 8, .bool, .bool, .bits 32, .bits 16], res := .one (.bits 8) }

def hftRootType : Expr :=
  .forallE `rxByte (eSig (eBV 8)) (.forallE `rxValid (eSig (.const ``Bool []))
    (.forallE `sopTlp (eSig (.const ``Bool [])) (.forallE `dataDword (eSig (eBV 32)) (.forallE `cplId (eSig (eBV 16)) (eSig (eBV 8)) .default) .default) .default) .default) .default

def hftRootValue : Expr :=
  .lam `rxByte (eSig (eBV 8)) (.lam `rxValid (eSig (.const ``Bool []))
    (.lam `sopTlp (eSig (.const ``Bool [])) (.lam `dataDword (eSig (eBV 32)) (.lam `cplId (eSig (eBV 16))
      (.app (.app (.const `Sparkle.IP.Bus.PCIeHFT.HFTPcieOut.outByte []) (.const ``Sparkle.Core.Domain.defaultDomain []))
        (.app (.app (.app (.app (.app (.app (.const `Sparkle.IP.Bus.PCIeHFT.hftPcieLoop []) (.const ``Sparkle.Core.Domain.defaultDomain []))
          (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))) .default) .default) .default) .default) .default

/-- the generated-package table at the start environment -/
noncomputable abbrev GPt {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Pkgs ι (fun _ => defaultDomain) :=
  genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env

/-! ## the named obligations (each is a hypothesis of the final theorem until proved) -/

/-- **O-CD** (FG D.D-1 / D.D-4 `CircCV`): the root's value `Expr` is denoted by `CD` as the declaration itself. UNSUPPLIED (未供給): `CD` has no rule for an application of a user constant
(`hftPcieLoop`) nor for a structure projection (`HFTPcieOut.outByte`); extending the inductive means changing an existing file. -/
def HftObCD : Prop := CD [] hftRootValue (MonoTy shHft) synth_hftPcieOutByte

/-- **O-SRC** (FG D.D-3 / DG-SEM, `hsrc` for a non-leaf): any package the table returns for the root observes the declaration. UNPROVED (未実装): `src_eq_of_states` is `ExtStage … 0 = id`; here `ExtStage … 2` runs through the two children's `src` (`calleeOut`, `ExtStage_succ`). -/
def HftObSrc {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Prop :=
  ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftRoot = some p →
    ∀ i bools bits, p.src i bools bits = monoObs shHft synth_hftPcieOutByte bools bits

/-- **O-TOP** (FG D.D-4 `TopShips`, the machine path with instances, at the CORE design `D₀`): the run's `raw` ships at the package, at some height `n`, on the design the core synthesis returned.
UNPROVED (未実装): `LeafFacts` is leaf-only; the children's packages and `ChildShips` enter here. The machine boundary `hdRun` of the root is a premise (derived from `hchk`/`hhead`/`hcell`). -/
def HftObTopCore {ι : Type} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  (∀ raw D₀ w1, MachineDefinesLinked mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1) →
  ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCore hftRoot [] false) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → ∃ n, TopShips p n hftRoot b raw D₀

/-- **O-NORAW** (FG D.T-4): no instance below the top, in `raw`, in `checkedOptimize b` and in `b`, names the top module (acyclic hierarchy: the instance module names differ from the top's).
UNPROVED (未実装): checked on one compile by `noRawBelowB` (Check8 SNAPSHOT8b), not derived from the run. -/
def HftObNoRaw (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design) : Prop :=
  ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCore hftRoot [] false) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' →
    (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) raw) ∧
    (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) (Sparkle.IR.OptCheck.checkedOptimize b)) ∧
    (∀ mn iname conns, Sparkle.IR.AST.Stmt.inst mn iname conns ∈ b.body → mn ≠ raw.name)

/-! ## the statement -/

/-- **`synth_hftPcieOutByte_final`**, as a Prop. Premises: `Laws L`, `hstart` (A.P-02), `hr` (A.P-04), `hhead` (C.EN-4), `hcell` (C.EN-4 CellPrem), `hchk` (the root: DG-ENV C0 link, DG-DATAOF/COVER reader, gates),
the readers of the two children (DG-DATAOF / DG-COVER / DG-ENV, at the start environment), the four named obligations. -/
def HftFinalStmt : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational hftRoot) mctx mref cctx cref w (b, D') w' →
    HeadAt hftRoot mctx mref cctx cref w → ReadWorld cref →
    CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData →
    RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData →
    HftObCD → HftObSrc (ι := ι) lvl (envAt cref w) →
    (∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCore mctx mref cctx cref w b D' p) →
    HftObNoRaw mctx mref cctx cref w b D' →
    (∃ raw, PostRun mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRun mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

end Tools.ShippingFGCircuitS1kStmt
