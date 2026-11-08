import Tools.VedU1Contract
import Tools.ShippingFGCircuitS3rArtifact

/-!
# Checks for the U1 contract sketch (Tools/VedU1Contract.lean)

* a toy declaration, a module of the shape `synthesizeEntry` returns, its
  contract, and the expected statement with `src` built from the
  DECLARATION (`toySrc`); `ShapeStmt`/`WidthStmt` hold by `decide`;
* NEGATIVE: the same contract against mutated modules (init value, input
  width, an extra output, a register on another reset wire) fails
  `ShapeStmt` or `WidthStmt`;
* the real artifact `pilotB0` (FG pilot S3r, one `pilotEntry3` run): its
  `clk`, `rst` and output `out` have no wire declaration; the contract's
  `ShapeCore` and `WidthStmt` hold, the first draft's width clause does not;
  it has two child instances, so it is outside the v1 scope (`memInstFree`).
`OutputsStmt` is NOT proved here (that is the U1 work).
-/

namespace Tests.Ved.U1ContractCheck

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract

/-- The toy declaration: a one-cycle delay. -/
def toyDelay (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  Signal.register 0 x

/-- A module of the `synthesizeEntry` shape (data inputs, then clk, rst; no
wire for clk/rst/out). -/
def toyMod : Module :=
  { name := "toyDelay",
    inputs := [⟨"_gen_x", .bitVector 4⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩],
    outputs := [⟨"out", .bitVector 4⟩],
    wires := [⟨"_gen_x", .bitVector 4⟩, ⟨"_gen_r", .bitVector 4⟩],
    body := [.register "_gen_r" "clk" ("rst", .synchronous) (.ref "_gen_x") 0,
             .assign "out" (.ref "_gen_r")] }

def toyC : Contract := contractOf toyMod (some ("clk", "rst"))

/-- `src` built from the declaration `toyDelay` applied to the data input's
stream (the U1 entry generates this term; it is not an argument). -/
def toySrc : (Nat → String → Nat) → String → Nat → Nat :=
  fun ins o t => if o = "out" then obsBV (toyDelay (sigBV ins "_gen_x" 4)) t else 0

/-- The expected statement elaborates (it is what the entry would prove). -/
def toyExpected : Prop := U1Stmt toyC toyMod toySrc

example : toyC.inits = [("_gen_r", 0)] ∧ toyC.dataInputs = [⟨"_gen_x", .bitVector 4⟩] ∧
    toyC.clkRst = some ("clk", "rst") := by decide

example : ShapeStmt toyC toyMod := by decide
example : WidthStmt toyC toyMod := by decide
-- the first draft's width clause rejects even the toy (clk/rst/out have no wire)
example : ¬ WidthStmtDraft1 toyMod := by decide

/-! ## NEGATIVE: mutations of the module against the same contract -/

example : ¬ ShapeStmt toyC { toyMod with
    body := [.register "_gen_r" "clk" ("rst", .synchronous) (.ref "_gen_x") 1,
             .assign "out" (.ref "_gen_r")] } := by decide          -- init value
example : ¬ ShapeStmt toyC { toyMod with
    inputs := [⟨"_gen_x", .bitVector 5⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩] } := by decide  -- input width
example : ¬ ShapeStmt toyC { toyMod with
    outputs := [⟨"out", .bitVector 4⟩, ⟨"out2", .bit⟩] } := by decide   -- extra output
example : ¬ ShapeStmt toyC { toyMod with
    body := [.register "_gen_r" "clk" ("_gen_x", .synchronous) (.ref "_gen_x") 0,
             .assign "out" (.ref "_gen_r")] } := by decide          -- reset not the rst input
example : ¬ ShapeStmt toyC { toyMod with
    inputs := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"_gen_x", .bitVector 4⟩] } := by decide  -- input order
example : ¬ WidthStmt (contractOf { toyMod with wires := [⟨"_gen_x", .bitVector 4⟩] } (some ("clk", "rst")))
    { toyMod with wires := [⟨"_gen_x", .bitVector 4⟩] } := by decide  -- register output undeclared

/-! ## The real artifact shape -/

open Tools.ShippingFGCircuitS3rArtifact in
#guard (pilotB0.wires.find? (·.name == "clk")).isNone &&
       (pilotB0.wires.find? (·.name == "rst")).isNone &&
       (pilotB0.wires.find? (·.name == "out")).isNone

open Tools.ShippingFGCircuitS3rArtifact in
#guard decide (ShapeCore (contractOf pilotB0 (some ("clk", "rst"))) pilotB0)

-- pilotB0 has two child instances: outside the v1 scope (not a width rejection)
open Tools.ShippingFGCircuitS3rArtifact in
#guard (pilotB0.body.filter (fun s => match s with | .inst .. => true | _ => false)).length == 2 &&
       !memInstFree pilotB0.body

open Tools.ShippingFGCircuitS3rArtifact in
#guard decide (WidthStmt (contractOf pilotB0 (some ("clk", "rst"))) pilotB0)

open Tools.ShippingFGCircuitS3rArtifact in
#guard !decide (WidthStmtDraft1 pilotB0)

end Tests.Ved.U1ContractCheck
