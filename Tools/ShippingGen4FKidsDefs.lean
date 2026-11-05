import Sparkle.IR.Builder
import Sparkle.Compiler.Elab
set_option autoImplicit false
set_option maxHeartbeats 200000
-- F-kids (scripts/gen4/FKIDS_FREEZE.md): the invariant `parameters = []` and the builder facts it needs. No sorry / axiom / native_decide.

/-! # The StatePF invariant and the circuit-builder facts

`design` of a `CircuitState` changes only at `CircuitM.addModuleToDesign`; `module.parameters` only at `CircuitM.addParameter`
(read in PARAM_INV_ESTIMATE §2.1). Here: the predicates (`ParamFree`, `DesignPF`, `StatePF`, `PairPF`) and, for every builder
operation the translator uses, that it keeps `design` and `module.parameters` (`View`). -/

namespace Tools.ShippingGen4FKids
open Lean Sparkle.IR.AST Sparkle.IR.Builder

/-- the invariant "parameters = []" on one module -/
def ParamFree (m : Sparkle.IR.AST.Module) : Prop := m.parameters = []
def DesignPF (D : Design) : Prop := ∀ x ∈ D.modules, ParamFree x
def StatePF (cs : CircuitState) : Prop := DesignPF cs.design
def PairPF (r : Sparkle.IR.AST.Module × Design) : Prop := ParamFree r.1 ∧ DesignPF r.2

/-- the part of the circuit state the invariant reads -/
def View (cs : CircuitState) : Design × List Parameter := (cs.design, cs.module.parameters)

theorem designPF_empty (n : String) : DesignPF (Design.empty n) := by
  intro x hx; simp [Design.empty] at hx

theorem designPF_addModule {D : Design} {m : Sparkle.IR.AST.Module} (hD : DesignPF D) (hm : ParamFree m) :
    DesignPF (D.addModule m) := by
  intro x hx
  simp only [Design.addModule, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hD x hx
  · exact hm

theorem statePF_init (n : String) : StatePF (CircuitM.init n) := designPF_empty n

theorem init_params (n : String) : (CircuitM.init n).module.parameters = [] := rfl

/-! ## builder operations keep the view -/

section Builder
variable (cs : CircuitState)

theorem view_freshNamed (base : String) : View (CircuitM.freshNamed base cs).2 = View cs := by
  unfold CircuitM.freshNamed
  split <;> rfl

theorem view_freshTemporary (base : String) : View (CircuitM.freshTemporary base cs).2 = View cs := by
  unfold CircuitM.freshTemporary
  rfl

theorem view_freshName (hint : String) (named : Bool) : View (CircuitM.freshName hint named cs).2 = View cs := by
  unfold CircuitM.freshName
  split
  · exact view_freshNamed cs _
  · exact view_freshTemporary cs _

theorem view_reserveName (n : String) : View (CircuitM.reserveName n cs).2 = View cs := by
  unfold CircuitM.reserveName
  rfl

theorem view_makeWire (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    View (CircuitM.makeWire hint ty named cs).2 = View cs := by
  exact (show View (CircuitM.makeWire hint ty named cs).2 =
    View (CircuitM.freshName (CircuitM.sanitizeName hint) named cs).2 from rfl).trans
    (view_freshName cs (CircuitM.sanitizeName hint) named)

theorem view_emitAssign (lhs : String) (rhs : Sparkle.IR.AST.Expr) :
    View (CircuitM.emitAssign lhs rhs cs).2 = View cs := rfl

theorem view_emitRegisterStmt (out clk rst : String) (input : Sparkle.IR.AST.Expr) (initVal : Nat)
    (rk : Sparkle.IR.Type.ResetKind) :
    View (CircuitM.emitRegisterStmt out clk rst input initVal rk cs).2 = View cs := rfl

theorem view_emitInstance (mn instName : String) (conns : List (String × Sparkle.IR.AST.Expr)) :
    View (CircuitM.emitInstance mn instName conns cs).2 = View cs := rfl

theorem view_addInput (name : String) (ty : Sparkle.IR.Type.HWType) :
    View (CircuitM.addInput name ty cs).2 = View cs := rfl

theorem view_addOutput (name : String) (ty : Sparkle.IR.Type.HWType) :
    View (CircuitM.addOutput name ty cs).2 = View cs := rfl

theorem view_bindSourceVariable (key : Lean.Name) (wire : String) :
    View (CircuitM.bindSourceVariable key wire cs).2 = View cs := rfl

theorem view_emitRegister (hint clk rst : String) (input : Sparkle.IR.AST.Expr) (initVal : Int)
    (ty : Sparkle.IR.Type.HWType) (named : Bool) (rk : Sparkle.IR.Type.ResetKind) :
    View (CircuitM.emitRegister hint clk rst input initVal ty named rk cs).2 = View cs := by
  exact (show View (CircuitM.emitRegister hint clk rst input initVal ty named rk cs).2 =
    View (CircuitM.freshName (CircuitM.sanitizeName hint) named cs).2 from rfl).trans
    (view_freshName cs (CircuitM.sanitizeName hint) named)

theorem view_emitMemory (hint : String) (aw dw : Nat) (clk : String) (wa wd we ra : Sparkle.IR.AST.Expr)
    (named : Bool) :
    View (CircuitM.emitMemory hint aw dw clk wa wd we ra named cs).2 = View cs := by
  have h1 := view_freshName cs (CircuitM.sanitizeName hint) named
  have h2 := view_freshName (CircuitM.freshName (CircuitM.sanitizeName hint) named cs).2
    (CircuitM.sanitizeName s!"{hint}_rdata") named
  exact (show View (CircuitM.emitMemory hint aw dw clk wa wd we ra named cs).2 =
    View (CircuitM.freshName (CircuitM.sanitizeName s!"{hint}_rdata") named
      (CircuitM.freshName (CircuitM.sanitizeName hint) named cs).2).2 from rfl).trans (h2.trans h1)

theorem view_emitMemoryComboRead (hint : String) (aw dw : Nat) (clk : String) (wa wd we ra : Sparkle.IR.AST.Expr)
    (named : Bool) :
    View (CircuitM.emitMemoryComboRead hint aw dw clk wa wd we ra named cs).2 = View cs := by
  have h1 := view_freshName cs (CircuitM.sanitizeName hint) named
  have h2 := view_freshName (CircuitM.freshName (CircuitM.sanitizeName hint) named cs).2
    (CircuitM.sanitizeName s!"{hint}_rdata") named
  exact (show View (CircuitM.emitMemoryComboRead hint aw dw clk wa wd we ra named cs).2 =
    View (CircuitM.freshName (CircuitM.sanitizeName s!"{hint}_rdata") named
      (CircuitM.freshName (CircuitM.sanitizeName hint) named cs).2).2 from rfl).trans (h2.trans h1)

/-- the one operation that adds to `design` -/
theorem design_addModuleToDesign (m : Sparkle.IR.AST.Module) :
    (CircuitM.addModuleToDesign m cs).2.design = cs.design.addModule m := rfl

theorem params_addModuleToDesign (m : Sparkle.IR.AST.Module) :
    (CircuitM.addModuleToDesign m cs).2.module.parameters = cs.module.parameters := rfl

/-- `addParameter` writes `module`, not `design` -/
theorem design_addParameter (n : String) (v : Nat) : (CircuitM.addParameter n v cs).2.design = cs.design := rfl

end Builder

end Tools.ShippingGen4FKids
