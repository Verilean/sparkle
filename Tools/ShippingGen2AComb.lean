import Tools.ShippingGen2Defs
set_option autoImplicit false

/-! # A-COMB checks C1-C3 (scripts/gen2/STEP_IFACE_FREEZE.md rev3 §2)

C1: a sequential child run is a child run. C2: with a clock input, a child run is exactly a sequential one. C3: the
two branches exclude each other (`"clk" ∈` against `"clk" ∉`; no `Nodup` premise). -/
namespace Tools.ShippingGen2
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingMachineDepth

variable {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn : Design} {n : Nat}
  {mc : Sparkle.IR.AST.Module} {bsC : List (Name × MixedGateBinder)} {outsC : List OutField}
  {S : (Nat → List Nat) → List (Nat → Nat)}

/-- **C1**: the embedding of the sequential child run. -/
theorem childRunN_of_seq (h : SeqChildRunN children dsn n mc bsC outsC S) :
    ChildRunN children dsn n mc bsC outsC S :=
  Or.inl h

/-- **C3**: the two branches exclude each other. -/
theorem not_seq_and_comb :
    ¬ (SeqChildRunN children dsn n mc bsC outsC S ∧ CombChildRunN children dsn n mc bsC outsC S) :=
  fun ⟨hs, hc⟩ => hc.2.2.1 hs.2.2.1

/-- **C2**: with a clock input, the child run is the sequential one. -/
theorem childRunN_iff_seq (hclk : "clk" ∈ mc.inputs.map (·.name)) :
    ChildRunN children dsn n mc bsC outsC S ↔ SeqChildRunN children dsn n mc bsC outsC S :=
  ⟨fun h => h.elim id (fun hc => absurd hclk hc.2.2.1), Or.inl⟩

end Tools.ShippingGen2
