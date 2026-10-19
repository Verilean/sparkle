import Tests.Compiler.MemNameCollisionGateCertGenTest
import Tools.ShippingGateCert2Command
-- BUILT as written: cf1 (exit 0, 665 jobs; round par/cert2).

/-! # The four gate-collision parents from DATA ONLY (round par/cert2)

`<p>_designClosedC` (`MemNameCollisionGateCertGenTest`) still took the hand-written kid facts
`<p>_kids` / `<p>_kidTyped` (and through them `<p>_entry`, the binder-position `decide`s,
`fakeSrc_width` / `fakeN_width`). Here the same four statements are re-derived as
`<p>_designClosedC2` by `Tools.ShippingGateCert2Command.generateCert2` from data:

| parent | memory origin | child const | gate source | tables | certificate |
|---|---|---|---|---|---|
| `collMixSame` | `.mem false 4 8` | `syncName` | `fakeSrc` | `outsG` / `insG` | inline (kernel) |
| `collMixDiff` | `.mem true 4 8` | `syncName` | `fakeSrc` | `outsG` / `insG` | `collMixDiff_cert` |
| `collMixArgs` | `.mem false 4 8` | `syncName` | `fakeSrc` | `outsG` / `insG` | `collMixArgs_cert` |
| `collWidth` | `.mem true 4 8` | `comboName` | `fakeN` | `outsFN` / `insFN` | inline (kernel) |

(both certificate routes are exercised: two parents reuse the `<p>_cert` theorem of
`MemNameCollisionGateCertGenTest`, two prove it inline.) The origin table, the binder positions
and the width ≠ 1 are ONE Bool (`memGateOk`) proved inline by `Eq.refl true` (kernel-evaluated).

STILL per parent (given to the generator): the closing `<p>_closesR`, the reflection binder `hR0`
(a premise of the result: `EntryDefines … childConst gateValue`), the value equation
(`syncGate_value` / `comboGate_value`), and the data above.

The audit asserts per parent: the type of `<p>_designClosedC2` is `Expr`-equal (`==`) to that
of `<p>_designClosedB`; standard axioms; the proof mentions none of `<p>_kids`, `<p>_kidTyped`,
`<p>_entry`, `<p>_runFacts`, `_outsG0`, `_designP0`, `_typedRun`, `_names`, `_callWidths`,
`_callArgs`, `_outChars`, `fakeSrc_width`, `fakeN_width` (and not `<p>_cert` for the inline
parents); it does mention `memGateOk`, `memGate_kidsS`, `memGate_kidTypedS` and the five
`gateParent_*`.

GLOBAL NAMES added: `Sparkle.Tests.Compiler.MemNameCollisionGateCert2Test.<p>_designClosedC2`
(new namespace; added by the generator). -/

/-! ## The endpoints, by the data generator (the kernel checks the results) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let an := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  let gn := `Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest
  let g2 := `Sparkle.Tests.Compiler.MemNameCollisionGateCert2Test
  -- (parent, child, source, value equation, closesR namespace, tables namespace, outs, ins, cb, cert?)
  for (p, cC, src, eqN, rN, tblN, oF, iF, cb, cert?) in
      [(`collMixSame, `syncName, `fakeSrc, `syncGate_value, ns, cn, `outsG, `insG, false,
          (none : Option Lean.Name)),
       (`collMixDiff, `syncName, `fakeSrc, `syncGate_value, an, cn, `outsG, `insG, true,
          some (gn ++ `collMixDiff_cert)),
       (`collMixArgs, `syncName, `fakeSrc, `syncGate_value, an, cn, `outsG, `insG, false,
          some (gn ++ `collMixArgs_cert)),
       (`collWidth, `comboName, `fakeN, `comboGate_value, an, an, `outsFN, `insFN, true,
          (none : Option Lean.Name))] do
    let n ← Tools.ShippingGateCert2Command.generateCert2Top
      { parent := ns ++ p, name := g2 ++ p.appendAfter "_designClosedC2",
        childConst := ns ++ cC, gateValue := ns ++ src ++ `gateValue,
        valueEq? := some (ns ++ eqN),
        closesR := rN ++ p.appendAfter "_closesR",
        src := ns ++ src, outsF := tblN ++ oF, insF := tblN ++ iF,
        cb := cb, aw := 4, dw := 8, nDecl := 3, cert? := cert? }
    Lean.logInfo m!"GATECERT2 [{n}]: from data (memory {cb} 4 8, child {cC}, source {src}); certificate {cert?.getD `inline}; kid facts by memGate_kidsS/kidTypedS on one memGateOk; closing {p}_closesR"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let bn := `Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let yn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
  let an := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  let gn := `Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest
  let g2 := `Sparkle.Tests.Compiler.MemNameCollisionGateCert2Test
  for n in [``Tools.ShippingGateCert2.memGateEntry_of_ok, ``Tools.ShippingGateCert2.memGate_kidsS,
      ``Tools.ShippingGateCert2.memGate_kidTypedS] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (parent, namespace of its hand-written lemmas, of its kidTyped, inline certificate?)
  for (p, hN, tN, inline) in [(`collMixSame, cn, yn, true), (`collMixDiff, an, an, false),
      (`collMixArgs, an, an, false), (`collWidth, an, an, true)] do
    let fin := g2 ++ p.appendAfter "_designClosedC2"
    let old := bn ++ p.appendAfter "_designClosedB"
    Tests.Compiler.NoPortsTest.stdAxioms fin
    let some (.thmInfo fi) := (← Lean.getEnv).find? fin | throwError "{fin}: not a theorem"
    let finT ← Lean.instantiateMVars fi.type
    let oldT ← Lean.instantiateMVars (← Lean.getConstInfo old).type
    -- (a) the same statement, as an `Expr`
    unless finT == oldT do
      throwError "{fin}: its type is not Expr-equal to {old}'s"
    -- (b) no hand-written per-parent piece except the closing (and the certificate, when given)
    let forbidden : List Lean.Name :=
      [hN ++ p.appendAfter "_kids", tN ++ p.appendAfter "_kidTyped", hN ++ p.appendAfter "_entry",
       hN ++ p.appendAfter "_runFacts", hN ++ p.appendAfter "_outsG0",
       hN ++ p.appendAfter "_designP0", tN ++ p.appendAfter "_typedRun",
       bn ++ p.appendAfter "_names", hN ++ p.appendAfter "_callWidths",
       hN ++ p.appendAfter "_callArgs", hN ++ p.appendAfter "_outChars",
       cn ++ `fakeSrc_width, an ++ `fakeN_width] ++
      (if inline then [gn ++ p.appendAfter "_cert"] else [])
    for k in forbidden do
      if (fi.value.find? (·.isConstOf k)).isSome then
        throwError "{fin}: the proof uses the hand-written {k}"
    for k in [``Tools.ShippingGateCert2.memGateOk, ``Tools.ShippingGateCert2.memGate_kidsS,
        ``Tools.ShippingGateCert2.memGate_kidTypedS, ``Tools.ShippingGateCert.gateParent_runFacts,
        ``Tools.ShippingGateCert.gateParent_outsG0, ``Tools.ShippingGateCert.gateParent_designP0,
        ``Tools.ShippingGateCert.gateParent_typedRun, ``Tools.ShippingGateCert.gateParent_names] do
      unless (fi.value.find? (·.isConstOf k)).isSome do
        throwError "{fin}: the proof does not use {k}"
    Lean.logInfo m!"GATECERT2 AUDIT {fin}: type Expr-equal to {old}; standard axioms; no hand-written kid/entry/run lemma in the proof (certificate {if inline then "inline" else "given"})"

#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateCert2Test.collMixSame_designClosedC2
#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateCert2Test.collMixDiff_designClosedC2
#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateCert2Test.collMixArgs_designClosedC2
#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateCert2Test.collWidth_designClosedC2
