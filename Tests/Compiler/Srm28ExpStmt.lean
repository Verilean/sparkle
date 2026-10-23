import Tests.Compiler.Srm28InstTest
set_option autoImplicit false
-- Expected statements written from the Lean text of scripts/srm28/EXPECTED.txt (committed before any Lean edit); fully qualified, independent of the proof files.
namespace Tests.Compiler.Srm28ExpStmt
open Sparkle.IR.AST
open Tools.ShippingMachineEntry (MachineWired)
open Sparkle.IR.Machine (SlotField)

/-- EXPECTED §1: the new LAST clause of `MachineWired`, instantiated at the generic names (checked structurally against the 19th conjunct by the audit). -/
def Exp_lastClause (shape : Sparkle.Compiler.Elab.MachineShape) (m : Module) (regs : List String) : Prop :=
  ∀ (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
    Stmt.register r c rs inp init ∈ m.body →
    ∃ (k : Nat) (f : SlotField), regs[k]? = some r ∧ shape.layout.slots[k]? = some f ∧ init = Int.ofNat f.init

def Exp_source : Prop :=
  ∀ {declName : Lean.Name} {shape : Sparkle.Compiler.Elab.MachineShape} {ids : List Lean.FVarId}
    {cache : IO.Ref (Lean.ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (hW : MachineWired declName shape ids cache m dsn regs lets),
    Tools.ShippingSrm25Init.SourceRegsAreSlots m regs shape.layout.slots

def Exp_g5 : Prop :=
  ∀ {declName : Lean.Name} {shape : Sparkle.Compiler.Elab.MachineShape} {ids : List Lean.FVarId}
    {cache : IO.Ref (Lean.ExprStructMap String)} {m b : Module} {dsn : Design} {regs lets : List String}
    (hgate : Sparkle.IR.RefineCheck.hierGate b = true) (hb : b.body = m.body)
    (hW : MachineWired declName shape ids cache m dsn regs lets),
    Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs shape.layout.slots

-- MUTATIONS of Exp_g5 (must be rejected)
def Exp_mut_noHb : Prop :=
  ∀ {declName : Lean.Name} {shape : Sparkle.Compiler.Elab.MachineShape} {ids : List Lean.FVarId}
    {cache : IO.Ref (Lean.ExprStructMap String)} {m b : Module} {dsn : Design} {regs lets : List String}
    (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (hW : MachineWired declName shape ids cache m dsn regs lets),
    Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs shape.layout.slots
def Exp_mut_withTrue : Prop :=
  ∀ {declName : Lean.Name} {shape : Sparkle.Compiler.Elab.MachineShape} {ids : List Lean.FVarId}
    {cache : IO.Ref (Lean.ExprStructMap String)} {m b : Module} {dsn : Design} {regs lets : List String}
    (hgate : Sparkle.IR.RefineCheck.hierGate b = true) (hb : b.body = m.body)
    (hW : MachineWired declName shape ids cache m dsn regs lets ∧ True),
    Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs shape.layout.slots
def Exp_mut_addedBinder : Prop :=
  ∀ {declName : Lean.Name} {shape : Sparkle.Compiler.Elab.MachineShape} {ids : List Lean.FVarId}
    {cache : IO.Ref (Lean.ExprStructMap String)} {m b : Module} {dsn : Design} {regs lets : List String}
    (hgate : Sparkle.IR.RefineCheck.hierGate b = true) (hb : b.body = m.body) (extra : Nat)
    (hW : MachineWired declName shape ids cache m dsn regs lets),
    Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs shape.layout.slots
def Exp_mut_reordered : Prop :=
  ∀ {declName : Lean.Name} {shape : Sparkle.Compiler.Elab.MachineShape} {ids : List Lean.FVarId}
    {cache : IO.Ref (Lean.ExprStructMap String)} {m b : Module} {dsn : Design} {regs lets : List String}
    (hb : b.body = m.body) (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (hW : MachineWired declName shape ids cache m dsn regs lets),
    Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs shape.layout.slots

open Tools.ShippingMachineDepthRun (ComposedNW)
open Tools.ShippingSrm28 (ComposedNWRegs)

def Exp_lift : Prop :=
  ∀ {n : Nat} {declName : Lean.Name} {d : Tools.ShippingMachineAuto.MachineData} {kD : Nat} {m : Module} {dsn : Design}
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {src : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) → Nat → Sparkle.Core.Signal.Signal (dom i) Bool}
    (P : List String → Prop)
    (h : ComposedNW n declName d kD m dsn dom src ext extB)
    (hP : ∀ (ids : List Lean.FVarId) (cache : IO.Ref (Lean.ExprStructMap String)) (regs lets : List String),
      regs.Nodup → regs.length = d.ss.length → MachineWired declName d.shape ids cache m dsn regs lets → P regs),
    ComposedNWRegs n declName d kD m dsn dom src ext extB P

def Exp_toNW : Prop :=
  ∀ {n : Nat} {declName : Lean.Name} {d : Tools.ShippingMachineAuto.MachineData} {kD : Nat} {m : Module} {dsn : Design}
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {src : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) → Nat → Sparkle.Core.Signal.Signal (dom i) Bool}
    {P : List String → Prop}
    (h : ComposedNWRegs n declName d kD m dsn dom src ext extB P),
    ComposedNW n declName d kD m dsn dom src ext extB

open Tests.Compiler.SharedLeafMemKidTest (topshareM topshareQ)
open Tests.Compiler.Srm9ComposedTest (TmBnd TqBnd tmExt tmExtB tqExt tqExtB)

def Exp_M_g5 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {b raw : Module} {D : Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D),
    ComposedNWRegs 2 ``topshareM topshareM.machineData 4 raw D (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineSource tmExt tmExtB
      (fun regs => Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs topshareM.machineData.shape.layout.slots)

def Exp_M_noG5 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {b raw : Module} {D : Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D),
    ComposedNWRegs 2 ``topshareM topshareM.machineData 4 raw D (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineSource tmExt tmExtB
      (fun regs => ∀ st0 : String → Nat,
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → topshareM.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
        Tools.ShippingSrm13Supply.RegsAtInit (Sparkle.IR.OptCheck.checkedOptimize b) st0)

def Exp_Q_g5 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {b raw : Module} {D : Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D),
    ComposedNWRegs 2 ``topshareQ topshareQ.machineData 4 raw D (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineSource tqExt tqExtB
      (fun regs => Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs topshareQ.machineData.shape.layout.slots)

def Exp_Q_noG5 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {b raw : Module} {D : Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hBnd : TqBnd mctx mref cctx cref w raw D),
    ComposedNWRegs 2 ``topshareQ topshareQ.machineData 4 raw D (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineSource tqExt tqExtB
      (fun regs => ∀ st0 : String → Nat,
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → topshareQ.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
        Tools.ShippingSrm13Supply.RegsAtInit (Sparkle.IR.OptCheck.checkedOptimize b) st0)

-- MUTATIONS of Exp_M_g5 (must be rejected): G5 conjunct replaced by True; wrong run (D for raw module); hpost dropped
def Exp_mut_M_trivialP : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {b raw : Module} {D : Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D),
    ComposedNWRegs 2 ``topshareM topshareM.machineData 4 raw D (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineSource tmExt tmExtB
      (fun _ => True)
def Exp_mut_M_noHpost : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {b raw : Module} {D : Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hBnd : TmBnd mctx mref cctx cref w raw D),
    ComposedNWRegs 2 ``topshareM topshareM.machineData 4 raw D (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineSource tmExt tmExtB
      (fun regs => Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs topshareM.machineData.shape.layout.slots)

end Tests.Compiler.Srm28ExpStmt
