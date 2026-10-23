import Tools.ShippingSrm25Init
set_option autoImplicit false
-- Expected statements written from the Lean text of scripts/srm25/EXPECTED.txt (committed before the proof file); fully qualified, independent of Tools/ShippingSrm25Init.lean.
namespace Tests.Compiler.Srm25ExpStmt
open Sparkle.IR.AST

def Exp_regInit : Prop := ∀ {m o : Module} (h : Sparkle.IR.RefineCheck.refineCheck m o = true),
    ∀ ro ∈ Sparkle.IR.OptCheck.seqRegs o, ∃ rm ∈ Sparkle.IR.OptCheck.seqRegs m, rm.1 = ro.1 ∧ rm.2.2.2.2 = ro.2.2.2.2

def Exp_shippedInit : Prop := ∀ {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
    Stmt.register r c rs inp init ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body →
      ∃ (c' : String) (rs' : String × Sparkle.IR.Type.ResetKind) (inp' : Expr), Stmt.register r c' rs' inp' init ∈ b.body

def Exp_SourceRegsAreSlots (b : Module) (regs : List String) (slots : List Sparkle.IR.Machine.SlotField) : Prop :=
  ∀ (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
    Stmt.register r c rs inp init ∈ b.body →
      ∃ (k : Nat) (f : Sparkle.IR.Machine.SlotField), regs[k]? = some r ∧ slots[k]? = some f ∧ init = Int.ofNat f.init

def Exp_reduction : Prop := ∀ {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true) (regs : List String)
    (slots : List Sparkle.IR.Machine.SlotField) (hS : Exp_SourceRegsAreSlots b regs slots),
    Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs slots

-- MUTATIONS (must be rejected)
def Exp_mut_initDropped : Prop := ∀ {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
    Stmt.register r c rs inp init ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body →
      ∃ (c' : String) (rs' : String × Sparkle.IR.Type.ResetKind) (inp' : Expr) (init' : Int), Stmt.register r c' rs' inp' init' ∈ b.body

def Exp_mut_noGate : Prop := ∀ {b : Module} (regs : List String)
    (slots : List Sparkle.IR.Machine.SlotField) (hS : Exp_SourceRegsAreSlots b regs slots),
    Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs slots

def Exp_mut_withTrue : Prop := ∀ {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true) (regs : List String)
    (slots : List Sparkle.IR.Machine.SlotField) (hS : Exp_SourceRegsAreSlots b regs slots ∧ True),
    Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs slots

def Exp_mut_addedBinder : Prop := ∀ {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true) (regs : List String)
    (slots : List Sparkle.IR.Machine.SlotField) (extra : Nat) (hS : Exp_SourceRegsAreSlots b regs slots),
    Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs slots

def Exp_mut_reordered : Prop := ∀ {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (slots : List Sparkle.IR.Machine.SlotField) (regs : List String) (hS : Exp_SourceRegsAreSlots b regs slots),
    Tools.ShippingSrm22Width.ShippedRegsAreSlots b regs slots

end Tests.Compiler.Srm25ExpStmt
