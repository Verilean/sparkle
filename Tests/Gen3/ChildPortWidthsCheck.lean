import Tools.ShippingGen3ChildPortWidths
import Tests.Gen3.ExpectedType
import Tests.Compiler.ShippingMachineLinkedTest
set_option autoImplicit false
-- Built: g3dsc-1b840215 (clean snapshot, exit 0, standard axioms).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # U-CHILD-PORTTYS (U-CHILD-PORTW-P) checks (scripts/gen3/UCHILD_PORTTYS_TABLE.md §1, §3, §5)

1. **Expected types.** `ChildPortWidths` (its body, parameter by parameter), `argPortWidths_of_eq`,
   `childPortWidths_of_tys`, N-A (`argPorts_noCalls_of_wired`, `argPorts_noCalls_post`), N-B
   (`childPortWidths_of_composedNW`), `noCalls_childPortWidths` and P1-P4 are compared MECHANICALLY
   (`Tests.Gen3.ExpectedType.checkExpected`) against independent `Expected…` statements. MUTANTS must FAIL:
   the definition against the package's unfiltered binder list, against the module's full input list (clk/rst not
   filtered); N-A against all binders; N-B without `hpost`; P4 without `hsimple`; P3 concluding the TYPE form.
2. **Data controls** (data only): `pickByteH`'s package against toy modules: the exact ports (positive), the same with
   `clk`/`rst` (positive: filtered), one 8-bit port (negative), the ports swapped (negative).
3. Axioms: `checkAxioms` (standard only) and `#print axioms`. -/

namespace Tests.Gen3.ChildPortWidthsCheck
open Tools.ShippingGen3ChildPortWidths Tools.ShippingGen3PortWidthsCore
open Tests.Gen3.ExpectedType

section Expected
-- the opens of Tools/ShippingGen3ChildPortWidths.lean
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingGen2
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (dv)

def ExpectedCPW {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (mc : Module) : Prop :=
  (argPorts mc).map (fun p => p.ty.bitWidth) = q.ports.map (fun b => (kindTy b.2).bitWidth)

def ExpectedWidthsOfEq : Prop :=
  ∀ {declName : Name} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    {bs : List (Name × MixedGateBinder)} {m : Module}
    (h : argPorts m = machPorts declName ids cache bs) (hl : bs.length ≤ ids.length),
    (argPorts m).map (fun p => p.ty.bitWidth) =
      (bs.filter fun b => b.2 != .domain).map (fun b => (kindTy b.2).bitWidth)

def ExpectedOfTys : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (mc : Module)
    (h : (argPorts mc).map (fun p => p.ty) = q.ports.map (fun b => kindTy b.2)),
    (argPorts mc).map (fun p => p.ty.bitWidth) = q.ports.map (fun b => (kindTy b.2).bitWidth)

def ExpectedNA : Prop :=
  ∀ {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (hnoI : d.shape.insts = []) (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets),
    argPorts m = machPorts declName ids cache d.bsIn

def ExpectedNApost : Prop :=
  ∀ {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {raw b : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache raw dsn regs lets)
    (hnoI : d.shape.insts = []) (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)),
    argPorts b = machPorts declName ids cache d.bsIn

def ExpectedNB : Prop :=
  ∀ (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl : d.shape.layout.slots ≠ []) (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {mc raw : Module} {D : Design}
    (hcomp : Tools.ShippingMachineDepthRun.ComposedNW n c d kD raw D dom src ext extB)
    (hpost : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)),
    (argPorts mc).map (fun p => p.ty.bitWidth) =
      ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).map (fun b => (kindTy b.2).bitWidth)

def ExpectedNoCalls : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)),
    (argPorts b).map (fun x => x.ty.bitWidth) = p.ports.map (fun b => (kindTy b.2).bitWidth)

def ExpectedP1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)),
    ChildPortWidths p b

def ExpectedP2 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)),
    ChildPortWidths p b

def ExpectedP3 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld}
    {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p) (hmo : MemOrigin p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hmd : ∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) (n : Nat),
    ChildPortWidths p b

def ExpectedP4 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld} {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat),
    ChildPortWidths p b

/-! ### Mutants (each must be REJECTED) -/

/-- The definition against the package's UNFILTERED, untruncated binder list. -/
def MutCPWbsIn {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (mc : Module) : Prop :=
  (argPorts mc).map (fun p => p.ty.bitWidth) = q.d.bsIn.map (fun b => (kindTy b.2).bitWidth)

/-- The definition on the module's FULL input list (clk/rst counted). -/
def MutCPWinputs {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (mc : Module) : Prop :=
  mc.inputs.map (fun p => p.ty.bitWidth) = q.ports.map (fun b => (kindTy b.2).bitWidth)

/-- N-A against all the binders (slots and lets included). -/
def MutNA : Prop :=
  ∀ {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (hnoI : d.shape.insts = []) (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets),
    argPorts m = machPorts declName ids cache d.shape.binders

/-- N-B without `hpost` (`mc` unrelated to the run). -/
def MutNBnoPost : Prop :=
  ∀ (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl : d.shape.layout.slots ≠ []) (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {mc raw : Module} {D : Design}
    (hcomp : Tools.ShippingMachineDepthRun.ComposedNW n c d kD raw D dom src ext extB),
    (argPorts mc).map (fun p => p.ty.bitWidth) =
      ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).map (fun b => (kindTy b.2).bitWidth)

/-- P4 without `hsimple` (group parents not excluded). -/
def MutP4 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld} {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat),
    ChildPortWidths p b

/-- P3 concluding the TYPE form (candidate T; stronger, not what is proved). -/
def MutP3tys : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld}
    {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p) (hmo : MemOrigin p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hmd : ∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) (n : Nat),
    (argPorts b).map (fun p => p.ty) = p.ports.map (fun b => kindTy b.2)

end Expected

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``Tools.ShippingGen2.ChildPortWidths ``ExpectedCPW
  checkExpected ``argPortWidths_of_eq ``ExpectedWidthsOfEq
  checkExpected ``childPortWidths_of_tys ``ExpectedOfTys
  checkExpected ``argPorts_noCalls_of_wired ``ExpectedNA
  checkExpected ``argPorts_noCalls_post ``ExpectedNApost
  checkExpected ``Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW ``ExpectedNB
  checkExpected ``noCalls_childPortWidths ``ExpectedNoCalls
  checkExpected ``leaf_childPortWidths ``ExpectedP1
  checkExpected ``slotlessLeaf_childPortWidths ``ExpectedP2
  checkExpected ``memParent_childPortWidths ``ExpectedP3
  checkExpected ``oneOut_childPortWidths ``ExpectedP4
  checkMutant ``Tools.ShippingGen2.ChildPortWidths ``MutCPWbsIn
  checkMutant ``Tools.ShippingGen2.ChildPortWidths ``MutCPWinputs
  checkMutant ``argPorts_noCalls_of_wired ``MutNA
  checkMutant ``Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW ``MutNBnoPost
  checkMutant ``oneOut_childPortWidths ``MutP4
  checkMutant ``memParent_childPortWidths ``MutP3tys

/-! ## Data controls (data only) -/

open Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Tools.ShippingGen2 (ChildPortWidths)

abbrev U := fun _ : Unit => Sparkle.Core.Domain.defaultDomain

/-- `pickByteH`'s comb package (as Tests/Gen2/DataBridgeCheck.lean:37-43; copied, not imported). -/
noncomputable def pbhC : Tools.ShippingGen2.CombPkg Unit U :=
  { decl := ``pickByteH, d := pickByteH.machineData, kD := pickByteH.machineData.bsIn.length,
    inits := pickByteH.machineInits, src := pickByteH.machineSource,
    facts := ⟨pickByteH.machine_ok, pickByteH.machine_body, pickByteH.machine_inits, pickByteH.machine_next,
      pickByteH.machine_result⟩ }

noncomputable abbrev pbhPkg : Tools.ShippingGen2.Pkg Unit U := .comb pbhC

/-- The exact ports of `pickByteH` (16 and 2 bits). -/
def mcAB : Sparkle.IR.AST.Module :=
  { name := "ab", inputs := [{ name := "a", ty := .bitVector 16 }, { name := "b", ty := .bitVector 2 }],
    outputs := [], wires := [], body := [] }

/-- The same with a clock and a reset (filtered by `argPorts`). -/
def mcClk : Sparkle.IR.AST.Module :=
  { name := "abclk", inputs := [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit },
      { name := "a", ty := .bitVector 16 }, { name := "b", ty := .bitVector 2 }],
    outputs := [], wires := [], body := [] }

/-- One 8-bit port. -/
def mc8 : Sparkle.IR.AST.Module :=
  { name := "a8", inputs := [{ name := "a", ty := .bitVector 8 }], outputs := [], wires := [], body := [] }

/-- The two ports in the other order. -/
def mcBA : Sparkle.IR.AST.Module :=
  { name := "ba", inputs := [{ name := "b", ty := .bitVector 2 }, { name := "a", ty := .bitVector 16 }],
    outputs := [], wires := [], body := [] }

set_option maxRecDepth 100000

theorem pbh_cpw_ab : ChildPortWidths pbhPkg mcAB := by
  unfold ChildPortWidths
  first | decide | decide +kernel

theorem pbh_cpw_clk : ChildPortWidths pbhPkg mcClk := by
  unfold ChildPortWidths
  first | decide | decide +kernel

theorem pbh_cpw_8 : ¬ ChildPortWidths pbhPkg mc8 := by
  unfold ChildPortWidths
  first | decide | decide +kernel

theorem pbh_cpw_ba : ¬ ChildPortWidths pbhPkg mcBA := by
  unfold ChildPortWidths
  first | decide | decide +kernel

/-! ## Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``argPortWidths_of_eq, ``childPortWidths_of_tys, ``argPorts_noCalls_of_wired,
      ``argPorts_noCalls_post, ``childPortWidths_of_composedNW, ``noCalls_childPortWidths,
      ``leaf_childPortWidths, ``slotlessLeaf_childPortWidths, ``memParent_childPortWidths,
      ``oneOut_childPortWidths, ``pbh_cpw_ab, ``pbh_cpw_clk, ``pbh_cpw_8, ``pbh_cpw_ba] do
    checkAxioms n

#print axioms argPortWidths_of_eq
#print axioms childPortWidths_of_tys
#print axioms argPorts_noCalls_of_wired
#print axioms argPorts_noCalls_post
#print axioms childPortWidths_of_composedNW
#print axioms noCalls_childPortWidths
#print axioms leaf_childPortWidths
#print axioms slotlessLeaf_childPortWidths
#print axioms memParent_childPortWidths
#print axioms oneOut_childPortWidths
#print axioms pbh_cpw_ab
#print axioms pbh_cpw_clk
#print axioms pbh_cpw_8
#print axioms pbh_cpw_ba

end Tests.Gen3.ChildPortWidthsCheck
