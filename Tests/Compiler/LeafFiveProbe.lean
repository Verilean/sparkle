import Tests.Compiler.LeafDeadInitTest

/-! # PROBE (not in AllTests): the five inner antecedents of `leaf_sat_design` on `dead7`'s compile

Evaluates, on the real compile (`synthesizeCombinationalCore` for `raw`, `synthesizeCombinational` for `b`),
with `o := checkedOptimize b`: (1) `o.body.all seqStmtOk`, (2) `simpleBody b = false`,
(3) `seqCheck (wofOf o) (weS o) o.body`, (4) `(seqNames o.body).all (declWidth o n == weS o n)`,
(5) every input of `dropZeroWidth raw` has `declWidth (drop raw) x ≤ weS o x`. Throws unless all hold. -/

namespace Sparkle.Tests.Compiler.LeafFiveProbe
open Lean Elab Command Meta Sparkle.Compiler.Elab

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  try
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}
    let (raw, _) ← synthesizeCombinationalCore ``Sparkle.Tests.Compiler.LeafDeadInitTest.dead7 [] false
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}
    let (b, _) ← synthesizeCombinational ``Sparkle.Tests.Compiler.LeafDeadInitTest.dead7
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let dr := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw
    let c1 := o.body.all Sparkle.IR.OptCheck.seqStmtOk
    let c2 := !(Sparkle.IR.OptCheck.simpleBody b)
    let c3 := Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf o) (Tools.ShippingDesignSV.weS o) o.body
    let c4 := (Tools.ShippingSeqSVSoundness.seqNames o.body).all fun n =>
      Sparkle.IR.RegDedup.declWidth o n == Tools.ShippingDesignSV.weS o n
    let c5 := dr.inputs.all fun p =>
      Nat.ble (Sparkle.IR.RegDedup.declWidth dr p.name) (Tools.ShippingDesignSV.weS o p.name)
    let bad5 := dr.inputs.filter fun p =>
      !Nat.ble (Sparkle.IR.RegDedup.declWidth dr p.name) (Tools.ShippingDesignSV.weS o p.name)
    logInfo m!"LEAF5 dead7: (1) seqStmtOk {c1}; (2) simpleBody=false {c2}; (3) seqCheck {c3}; (4) widths agree {c4}; (5) input widths {c5} (failing: {bad5.map fun p => (p.name, Sparkle.IR.RegDedup.declWidth dr p.name, Tools.ShippingDesignSV.weS o p.name)})"
    unless c1 && c2 && c3 && c4 && c5 do throwError "LEAF5: not all five hold on dead7"
  finally
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}

end Sparkle.Tests.Compiler.LeafFiveProbe
