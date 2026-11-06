import Tools.ShippingFGCircuitS2jTop
set_option autoImplicit false
-- FG circuit pilot S2j check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §36.

/-! # FGCircuitPilotCheck30 (light)

1. SIGNATURES-A: `HftCallDec` (the one named hypothesis) and `oneOut_topShipsOff` against independently written complete statements; mutants: another child's output (fixed callee / wrong call index), end world, old entry (diagnostic core run, all-world `MachineDefines`), a dropped premise, the printed design.
2. SIGNATURES-B: `hftTop_of_run` and `synth_hftPcieOutByte_finalOffLNKKGT_Z` against independently written complete statements; mutants as above plus `htop` kept, `hdec` at the end world, old entry `hr`.
3. HYPS: the binder list of the final statement (no `htop`, `hdec` in its place; no all-world fact reachable from `hdec`).
4. REMAINING, AXIOMS. -/
namespace Tests.Gen5.FGCircuitPilotCheck30
open Lean Meta Elab Command Term
open Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain
open Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG Tools.ShippingFGCircuit Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc
open Tools.ShippingFGCircuitS2dKids Tools.ShippingFGCircuitS2gGates Tools.ShippingFGCircuitS2jTop
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildBndCore (dv)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

abbrev Mod := Sparkle.IR.AST.Module
abbrev Des := Sparkle.IR.AST.Design

/-! ## 1. `HftCallDec` and `oneOut_topShipsOff`, independently -/

def ExpDec {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Prop :=
  ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftRoot = some p →
    ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, GPt (ι := ι) lvl env (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k
/-- mutant: one fixed callee for every call (another child's output) -/
def MuDecFixed {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Prop :=
  ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftRoot = some p →
    ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, GPt (ι := ι) lvl env hftHttp = some q ∧ CallDec p q k
/-- mutant: the decoding of call 0 for every call -/
def MuDecZero {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Prop :=
  ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftRoot = some p →
    ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, GPt (ι := ι) lvl env (p.d.shape.insts[k]).1 = some q ∧ CallDec p q 0
/-- mutant: another design's package (the first callee's table row asked for the root) -/
def MuDecOtherRoot {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Prop :=
  ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftTlp = some p →
    ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, GPt (ι := ι) lvl env (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k
/-- mutant: the callee's package not required to exist -/
def MuDecNoPkg {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Prop :=
  ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftRoot = some p →
    ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∀ q, GPt (ι := ι) lvl env (p.d.shape.insts[k]).1 = some q → CallDec p q k

def ExpOneOut : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Mod} {D : Des},
    MemParentDataOk p →
    (∀ (k : Nat), k < p.d.shape.insts.length → (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none) →
    p.d.shape.insts ≠ [] → p.d.shape.instFields = [] → p.d.shape.layout.slots ≠ [] →
    Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
    RunsTo (synthesizeCombinationalCoreOff p.decl) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefinesLinkedOff mctx mref cctx cref p.decl p.d.shape w raw D w1 →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    (∀ (k : Nat), OneOutWidth P p k) →
    ∀ (n : Nat), TopShips p (n + 1) p.decl b raw D
/-- mutant: the diagnostic core run and the all-world `MachineDefines` (the old entry) -/
def MuOneOutOld : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Mod} {D : Des},
    MemParentDataOk p →
    (∀ (k : Nat), k < p.d.shape.insts.length → (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none) →
    p.d.shape.insts ≠ [] → p.d.shape.instFields = [] → p.d.shape.layout.slots ≠ [] →
    Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    (∀ (k : Nat), OneOutWidth P p k) →
    ∀ (n : Nat), TopShips p (n + 1) p.decl b raw D
/-- mutant: no served-children-ship trace (`ServedRealA` only would be weaker; here the decoding premise is dropped) -/
def MuOneOutNoDec : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Mod} {D : Des},
    MemParentDataOk p →
    (∀ (k : Nat), k < p.d.shape.insts.length → (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none) →
    p.d.shape.insts ≠ [] → p.d.shape.instFields = [] → p.d.shape.layout.slots ≠ [] →
    Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
    RunsTo (synthesizeCombinationalCoreOff p.decl) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefinesLinkedOff mctx mref cctx cref p.decl p.d.shape w raw D w1 →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    (∀ (k : Nat), OneOutWidth P p k) →
    ∀ (n : Nat), TopShips p (n + 1) p.decl b raw D
/-- mutant: the trace's served predicate is `ServedRealA` (the children only real, not shipping) -/
def MuOneOutReal : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Mod} {D : Des},
    MemParentDataOk p →
    (∀ (k : Nat), k < p.d.shape.insts.length → (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none) →
    p.d.shape.insts ≠ [] → p.d.shape.instFields = [] → p.d.shape.layout.slots ≠ [] →
    Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
    RunsTo (synthesizeCombinationalCoreOff p.decl) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefinesLinkedOff mctx mref cctx cref p.decl p.d.shape w raw D w1 →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) →
    Tools.ShippingMachineTraceX.MachineTraceLBX (Tools.ShippingServedRealA.ServedRealA L.O p.decl p.d.shape raw D) p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    (∀ (k : Nat), OneOutWidth P p k) →
    ∀ (n : Nat), TopShips p (n + 1) p.decl b raw D
/-- mutant: the conclusion on a design other than the run's core design -/
def MuOneOutDesign : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Mod} {D D' : Des},
    MemParentDataOk p →
    (∀ (k : Nat), k < p.d.shape.insts.length → (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none) →
    p.d.shape.insts ≠ [] → p.d.shape.instFields = [] → p.d.shape.layout.slots ≠ [] →
    Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
    RunsTo (synthesizeCombinationalCoreOff p.decl) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefinesLinkedOff mctx mref cctx cref p.decl p.d.shape w raw D w1 →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    (∀ (k : Nat), OneOutWidth P p k) →
    ∀ (n : Nat), TopShips p (n + 1) p.decl b raw D'

/-! ## 2. `hftTop_of_run` and the final statement, independently -/

/-- the conclusion of `htop` for a package `p` (what `HftObTopCoreOff` says): written again -/
def ExpTopOb {ι : Type} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (b : Mod) (D' : Des) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  (∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1) →
  ∀ (raw : Mod) (D₀ : Des) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → ∃ n, TopShips p n hftRoot b raw D₀
/-- mutant: shipping on the printed design `D'` -/
def MuTopObD {ι : Type} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (b : Mod) (D' : Des) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  (∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1) →
  ∀ (raw : Mod) (D₀ : Des) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → ∃ n, TopShips p n hftRoot b raw D'
/-- mutant: the old (diagnostic) core run -/
def MuTopObOld {ι : Type} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (b : Mod) (D' : Des) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  (∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1) →
  ∀ (raw : Mod) (D₀ : Des) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCore hftRoot [] false) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → ∃ n, TopShips p n hftRoot b raw D₀
/-- mutant: another declaration's top (`hftHttp`) -/
def MuTopObName {ι : Type} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (b : Mod) (D' : Des) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  (∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1) →
  ∀ (raw : Mod) (D₀ : Des) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → ∃ n, TopShips p n hftHttp b raw D₀

def ExpTop (Ob : ∀ {ι : Type} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
      (w : Void IO.RealWorld) (b : Mod) (D' : Des), Pkg ι (fun _ => defaultDomain) → Prop)
    (Dec : ∀ {ι : Type}, (Lean.Expr → Nat) → Environment → Prop) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {b : Mod} {D' : Des}
    (hstart : Start L mctx cctx w) (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hkenv : HftKidsStartEnv L.O (envAt cref w)) (hkgfacts : HftKidsGateFacts (envAt cref w))
    (hdec : Dec (ι := ι) lvl (envAt cref w)),
    ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → Ob mctx mref cctx cref w b D' p

def ExpFinal (Dec : ∀ {ι : Type}, (Lean.Expr → Nat) → Environment → Prop) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Mod} {D' : Des}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hcd : HftObCDZ (envAt cref w))
    (hdec : Dec (ι := ι) lvl (envAt cref w))
    (hkenv : HftKidsStartEnv L.O (envAt cref w)) (hkgfacts : HftKidsGateFacts (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvZ (envAt cref w) (GPt (ι := ι) lvl (envAt cref w)) (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p
/-- mutant: the decoding at the END world `w'` -/
def MuFinalEnd : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Mod} {D' : Des}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hcd : HftObCDZ (envAt cref w))
    (hdec : HftCallDec (ι := ι) lvl (envAt cref w'))
    (hkenv : HftKidsStartEnv L.O (envAt cref w)) (hkgfacts : HftKidsGateFacts (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvZ (envAt cref w) (GPt (ι := ι) lvl (envAt cref w)) (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p
/-- mutant: the old entry `synthesizeCombinational` for the run -/
def MuFinalOld : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Mod} {D' : Des}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinational hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hcd : HftObCDZ (envAt cref w))
    (hdec : HftCallDec (ι := ι) lvl (envAt cref w))
    (hkenv : HftKidsStartEnv L.O (envAt cref w)) (hkgfacts : HftKidsGateFacts (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvZ (envAt cref w) (GPt (ι := ι) lvl (envAt cref w)) (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p
/-- mutant: the carrier `cdvY` in the conclusion -/
def MuFinalCarrier : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Mod} {D' : Des}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hcd : HftObCDZ (envAt cref w))
    (hdec : HftCallDec (ι := ι) lvl (envAt cref w))
    (hkenv : HftKidsStartEnv L.O (envAt cref w)) (hkgfacts : HftKidsGateFacts (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvY (envAt cref w) (GPt (ι := ι) lvl (envAt cref w)) (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p
/-- mutant: `htop` kept in place of `hdec` (the S2g statement) -/
def MuFinalTop : Prop := HftFinalStmtOffLNKKG HftObCDZ cdvZ
/-- mutant: `hdec` dropped -/
def MuFinalNoDec : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Mod} {D' : Des}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hcd : HftObCDZ (envAt cref w))
    (hkenv : HftKidsStartEnv L.O (envAt cref w)) (hkgfacts : HftKidsGateFacts (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvZ (envAt cref w) (GPt (ι := ι) lvl (envAt cref w)) (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

/-! ## the comparison helpers -/

def normOnce (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if c == ``HftCallDec || c == ``HftFinalStmtOffLNKKGT || c == ``HftFinalStmtOffLNKKG || c == ``HftObTopCoreOff || c == ``Tools.ShippingFGCircuitS2gGates.HftKidsGateFacts
          || (`Tests.Gen5.FGCircuitPilotCheck30).isPrefixOf c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:6] do
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

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let Q := `Tests.Gen5.FGCircuitPilotCheck30
  let C (n : Name) : Lean.Expr := mkConst n
  -- (a) hdec: a Prop family over `ι`, lvl, env: compare the unfolded bodies at fresh variables
  let some hty ← (do
      let ci ← getConstInfo ``HftCallDec
      pure (some ci.type)) | throwError "missing"
  let mut nm : Nat := 0
  let cmpDec (what : String) (mu : Name) (diff : Bool) : MetaM Unit := do
    let lvlTy ← mkArrow (mkConst ``Lean.Expr) (mkConst ``Nat)
    withLocalDeclD `ι (mkSort 1) fun ι => withLocalDeclD `lvl lvlTy fun lvl =>
      withLocalDeclD `env (mkConst ``Environment) fun env => do
        let a := mkApp3 (C ``HftCallDec) ι lvl env
        let e := mkApp3 (C mu) ι lvl env
        if diff then diffTy what a e else sameTy what a e
  let _ := hty
  cmpDec "HftCallDec" (Q ++ `ExpDec) false
  for mu in ["MuDecFixed", "MuDecZero", "MuDecOtherRoot", "MuDecNoPkg"] do
    cmpDec s!"HftCallDec vs {mu}" (Q ++ Name.mkSimple mu) true; nm := nm + 1
  -- (b) oneOut_topShipsOff
  let t1 ← tyOf ``Tools.ShippingGen2.oneOut_topShipsOff
  sameTy "oneOut_topShipsOff" t1 (C (Q ++ `ExpOneOut))
  for mu in ["MuOneOutOld", "MuOneOutNoDec", "MuOneOutReal", "MuOneOutDesign"] do
    diffTy s!"oneOut_topShipsOff vs {mu}" t1 (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  -- the old theorem is NOT the new statement (old entry)
  let told ← tyOf ``Tools.ShippingGen2.oneOut_topShipsO
  diffTy "oneOut_topShipsO (old entry) vs the new statement" told t1; nm := nm + 1
  sameTy "oneOut_topShipsO is the old-entry mutant" told (C (Q ++ `MuOneOutOld))
  logInfo m!"FGCIRCUIT30 SIGNATURES-A: HftCallDec (the callee's package per call + CallDec) and oneOut_topShipsOff (profile-free core run, run-local entry, ShipsRes trace) match the independently written statements; {nm} mutants rejected (fixed callee, call index 0, another root, package not required; old entry, dropped decoding, ServedRealA, another design); the old oneOut_topShipsO is exactly the old-entry mutant"

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let Q := `Tests.Gen5.FGCircuitPilotCheck30
  let C (n : Name) : Lean.Expr := mkConst n
  let mut nm : Nat := 0
  -- Ob and Dec as lambdas over the real definitions
  let obE ← elabTerm (← `(fun {ι : Type} (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context)
      (cref : ST.Ref IO.RealWorld Lean.Core.State) (w : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design)
      (p : Tools.ShippingGen2.Pkg ι (fun _ => Sparkle.Core.Domain.defaultDomain)) => Tools.ShippingFGCircuitS1tFinal.HftObTopCoreOff mctx mref cctx cref w b D' p)) none
  let decE ← elabTerm (← `(fun {ι : Type} (lvl : Lean.Expr → Nat) (env : Lean.Environment) => Tools.ShippingFGCircuitS2jTop.HftCallDec (ι := ι) lvl env)) none
  let t2 ← tyOf ``Tools.ShippingFGCircuitS2jTop.hftTop_of_run
  let obExp ← elabTerm (← `(fun {ι : Type} (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context)
      (cref : ST.Ref IO.RealWorld Lean.Core.State) (w : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design)
      (p : Tools.ShippingGen2.Pkg ι (fun _ => Sparkle.Core.Domain.defaultDomain)) => Tests.Gen5.FGCircuitPilotCheck30.ExpTopOb mctx mref cctx cref w b D' p)) none
  let _ := obE
  sameTy "hftTop_of_run" t2 (mkApp2 (C (Q ++ `ExpTop)) obExp decE)
  -- mutants of the conclusion predicate
  for mu in ["MuTopObD", "MuTopObOld", "MuTopObName"] do
    let m ← elabTerm (← `(fun {ι : Type} (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context)
      (cref : ST.Ref IO.RealWorld Lean.Core.State) (w : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design)
      (p : Tools.ShippingGen2.Pkg ι (fun _ => Sparkle.Core.Domain.defaultDomain)) => $(mkIdent (Q ++ Name.mkSimple mu)) mctx mref cctx cref w b D' p)) none
    diffTy s!"hftTop_of_run vs {mu}" t2 (mkApp2 (C (Q ++ `ExpTop)) m decE); nm := nm + 1
  -- the final statement
  let tF ← tyOf ``Tools.ShippingFGCircuitS2jTop.synth_hftPcieOutByte_finalOffLNKKGT_Z
  sameTy "synth_hftPcieOutByte_finalOffLNKKGT_Z" tF (mkApp (C (Q ++ `ExpFinal)) decE)
  for mu in ["MuFinalEnd", "MuFinalOld", "MuFinalCarrier", "MuFinalTop", "MuFinalNoDec"] do
    diffTy s!"final_Z vs {mu}" tF (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT30 SIGNATURES-B: hftTop_of_run (13 hypotheses, conclusion HftObTopCoreOff at every table package of the root) and synth_hftPcieOutByte_finalOffLNKKGT_Z (14 hypotheses, hdec in the place of htop) match the independently written complete statements; {nm} mutants rejected (TopShips on the printed design, old core run, another declaration's top; decoding at the end world, old entry hr, carrier cdvY, htop kept (the S2g statement), hdec dropped)"

/-! ## 3. HYPS -/

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
      | some (.inductInfo i) => if (`Tools).isPrefixOf n then reach env (i.ctors ++ rest) seen else reach env rest seen
      | some (.ctorInfo c) => reach env (c.type.getUsedConstants.toList ++ rest) seen
      | _ => reach env rest seen

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let tF ← tyOf ``Tools.ShippingFGCircuitS2jTop.synth_hftPcieOutByte_finalOffLNKKGT_Z
  let some ty2 ← unfoldDefinition? tF | throwError "not a definition"
  let hs ← forallTelescope ty2 fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, ← instantiateMVars d.type)]
    return hs
  let expected := ["hlink", "L", "lvl", "env₀", "hstart", "hr", "hcell", "hchk", "hreadH", "hreadT", "hcd", "hdec", "hkenv", "hkgfacts"]
  unless hs.map (·.1) == expected do throwError "hypotheses are {hs.map (·.1)}, expected {expected}"
  for gone in ["htop", "hkids", "hkgates", "hclL", "hcl", "hgate", "hnoraw", "hdRun", "hsrc", "hhead"] do
    if (hs.map (·.1)).contains gone then throwError "{gone} is a hypothesis"
  let some (_, hd) := hs.find? (·.1 == "hdec") | throwError "hdec missing"
  let env ← getEnv
  let r := reach env [``HftCallDec] {}
  for bad in [``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine, ``Tools.ShippingMachineEntry.MachineCloses,
      ``Tools.ShippingGen2.Start, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingGen5Env.ReadsAt, ``Tools.ShippingFGCircuitS1iEnv.CheckedStart,
      ``Tools.ShippingEntrySoundness.RunsTo, ``Tools.ShippingGen2.ShipsRes, ``Tools.ShippingGen2.ChildShips, ``Tools.ShippingGen2.TopShips] do
    if r.contains bad then throwError "{bad} is reachable from hdec (a run / all-world / shipping statement)"
  for need in [``Tools.ShippingGen2.CallDec, ``Tools.ShippingFGCircuitS1kStmt.GPt] do
    unless r.contains need do throwError "hdec does not reach {need}"
  let _ := hd
  logInfo m!"FGCIRCUIT30 HYPS: synth_hftPcieOutByte_finalOffLNKKGT_Z = {expected} (14 explicit); htop is gone, hdec (package-level G-CALLDEC) is in its place; no run, no MachineDefines/MachineCloses/Start/ReadsAt, no ShipsRes/ChildShips/TopShips reachable from hdec (reach set {r.size}): it is a statement about the table's packages only"

/-! ## 4. REMAINING, AXIOMS -/

run_cmd liftTermElabM do
  logInfo m!"FGCIRCUIT30 REMAINING (S2j): hdec : HftCallDec lvl (envAt cref w) [FG D.D-4 G-CALLDEC / T2-TIE, package-level]: for every call k of the root's table package p, the callee's package q is in the table and CallDec p q k. Its parts: GenExtAtCall (derivable from hDT1_of_genGP, not yet connected), CallOutRange (open, hDG_SEM_range), the field row (the callee's module has one output, from the run's CallStmt) and static data checks (kernel). PROVED from the run (not hypotheses any more): the kids' ShipsRes (kid_shipsRes: ChildShips of a slotless comb leaf from its own run + KidStartEnv), the root's machine run (MachineTaken), MemParentDataOk/hord/instFields/slots, OneOutWidth, the ServedP trace, TopShips (oneOut_topShipsOff). Unchanged: hkenv (D.T-4k), hkgfacts (D.T-4g), HftRootLink, hcd(Ob), hreadH/T, hchk, CellPrem, Laws/Start/hr"

run_cmd liftTermElabM do
  let T := `Tools.ShippingFGCircuitS2jTop
  let K := `Tools.ShippingFGCircuitS2jKid
  let names : List Name := [`Tools.ShippingFGCircuitS2jCopy.machine_ships_hierC_runOff, ``Tools.ShippingGen2.oneOut_topShipsOff, K ++ `kidRunK, K ++ `kid_pkg, K ++ `kid_shipsRes,
    ``Tools.ShippingGen2.slotlessLeaf_childShips_of_ran, T ++ `servedP_of_real, T ++ `traceLBX_mono, T ++ `hftTop_of_run,
    T ++ `synth_hftPcieOutByte_finalOffLNKKGT, T ++ `synth_hftPcieOutByte_finalOffLNKKGT_Z, T ++ `synth_hftPcieOutByte_finalOffLNKKGT_Y, T ++ `synth_hftPcieOutByte_finalOffLNKKGT_X]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT30 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck30
