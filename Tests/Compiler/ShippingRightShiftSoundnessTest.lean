import Tools.ShippingExecutionSoundness
import Tests.Compiler.ShippingEntrySoundnessTest

namespace Sparkle.Tests.Compiler.ShippingRightShiftSoundnessTest
open Lean Elab Command Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingScalarSoundness
open Tools.ShippingExecutionSoundness Tools.ShippingDeltaSemantics
open Sparkle.Tests.Compiler.ShippingEntrySoundnessTest (sigsOf evalOut)

def rightShift1 {dom : DomainConfig} (a b : Signal dom (BitVec 1)) : Signal dom (BitVec 1) := a >>> b
def rightShift8 {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a >>> b
def rightShift65 {dom : DomainConfig} (a b : Signal dom (BitVec 65)) : Signal dom (BitVec 65) := a >>> b

def nestedShift {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  ((a >>> b) + a) ^^^ ((b + a) >>> (Signal.pure (BitVec.ofNat 8 1) : Signal dom (BitVec 8)))

def feR : FExpr := .bin .shr (.inp 0) (.inp 1)
def feNested : FExpr := .bin .xor (.bin .add feR (.inp 0))
  (.bin .shr (.bin .add (.inp 1) (.inp 0)) (.lit 1))

#def_decl_value rightShiftValue of rightShift8
#def_decl_value nestedShiftValue of nestedShift
example : rightShiftValue = quoteDecl `dom [`a, `b] 8 feR := rfl
example : nestedShiftValue = quoteDecl `dom [`a, `b] 8 feNested := rfl
example {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    nestedShift a b = denoteFE 8 (sigsOf [a, b]) feNested := rfl

/-- General execution theorem instantiated at a real nested shift source.
The source equality is definitional; there is no per-circuit replay premise. -/
theorem nestedShift_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational ``nestedShift) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref ``nestedShift nestedShiftValue) :
    ∃ sv port pairs,
      Tools.SVParser.EmitAst.emitAstModule (Sparkle.IR.OptCheck.checkedOptimize m) = some sv ∧
      Tools.SVParser.ConcreteSyntax.Module sv (verilogOf m) ∧
      Tools.ShippingSVBridge.combItems sv.items = some pairs ∧
      ∀ {dom : DomainConfig} (a b : Signal dom (BitVec 8)) (t : Nat),
        SettlesTo sv pairs (Tools.ShippingSVBridge.inputEnv 2 port (fun j => (sigsOf [a, b] j).val t))
          ((nestedShift a b).val t).toNat := by
  have he : nestedShiftValue = quoteDecl `dom [`a, `b] 8 feNested := rfl
  rw [he] at henv
  obtain ⟨sv, port, pairs, ht, hsyntax, hi, _, _, _, _, _, hs⟩ :=
    compiledFragment_execution h henv (by simp [feNested, feR, FExpr.WF]) (by decide)
  exact ⟨sv, port, pairs, ht, hsyntax, hi, fun a b t => (hs (sigsOf [a, b]) t).2⟩

run_cmd liftTermElabM do
  for (decl, n, fe) in [( ``rightShift1, 1, feR), (``rightShift8, 8, feR),
      (``rightShift65, 65, feR), (``nestedShift, 8, feNested)] do
    let ci ← getConstInfo decl
    unless @decide (ci.value! = quoteDecl `dom [`a, `b] n fe)
        (Sparkle.Compiler.ExprDecEq.exprDecEq _ _) do
      throwError "{decl}: elaboration differs from quoted source"
    let (m, _) ← synthesizeCombinational decl
    let o := Sparkle.IR.OptCheck.checkedOptimize m
    unless Sparkle.IR.OptCheck.simpleBody m do throwError "{decl}: escaped checked optimizer route"
    unless Sparkle.IR.OptCheck.printDeclsCheck o && Sparkle.IR.PrintCheck.moduleCheck o do
      throwError "{decl}: printing invariants failed"
    unless Sparkle.Backend.Verilog.toVerilog o == Sparkle.Backend.Verilog.toVerilog m do
      throwError "{decl}: shift original must be retained by checked fallback"
    let ports := o.inputs.map (·.name)
    unless ports.length == 2 do throwError "{decl}: unexpected inputs"
    for a in [0, 1, 3, 2 ^ (n - 1), 2 ^ n - 1] do
      for b in [0, 1, n - 1, n, n + 1, 2 ^ n - 1] do
        let vals : Nat → BitVec n := fun j => BitVec.ofNat n (if j == 0 then a else b)
        let inputs := [(ports[0]!, (vals 0).toNat), (ports[1]!, (vals 1).toNat)]
        unless evalOut o inputs == some (evalFE n vals fe).toNat do
          throwError "{decl}: input {a}, amount {b}: wrong right shift"
    if decl == ``rightShift8 then
      let name := Sparkle.Backend.Verilog.sanitizeName o.name
      let text := verilogOf m
      IO.FS.writeFile "/tmp/sparkle_right_shift.sv" (text ++
        s!"\nmodule tb; reg [7:0] a,b; wire [7:0] out; integer i,j;\n{name} dut(.{ports[0]!}(a), .{ports[1]!}(b), .out(out));\n" ++
        "initial begin for(i=0;i<256;i=i+1) begin for(j=0;j<256;j=j+1) begin\n" ++
        "a=i; b=j; #1; if(out !== (a >> b)) $fatal(1, \"shift mismatch\");\n" ++
        "end end $display(\"RIGHT SHIFT RTL OK: 65536 pairs\"); $finish; end endmodule\n")

run_cmd do
  if (← get).messages.hasErrors then throwError "right-shift regression failed"
  for name in [``nestedShift_execution, ``compiledFragment_execution,
      ``Binary.rhs_correct, ``Tools.ShippingTranslateSoundness.library_shr,
      ``Tools.ShippingPrintSoundness.checkedOptimize_shr] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected right-shift axiom: {name}: {ax}"
  logInfo "SHIPPING RIGHT SHIFT OK: nested canonical Signal BitVec shifts reach full text syntax and delta execution; checked fallback, standard axioms only"

end Sparkle.Tests.Compiler.ShippingRightShiftSoundnessTest
