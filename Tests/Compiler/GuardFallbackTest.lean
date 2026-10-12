import Tests.Compiler.OptFallbackTest
import Tests.Compiler.PrintGuardTest
import Tools.ShippingDesignSV
import Tools.ShippingMachineShipsDepth
import Tools.ShippingMachineLinked

/-! # Each guard on a minimal counterexample, with the fallback's guarantee

For every guard of the result-checked passes: a module on which it FIRES,
and — evaluated, an error otherwise — the endpoint-side checks of the module
that is then shipped. The endpoint-side check of a top module is
`Tools.ShippingDesignSV.textCheckI C s` (statement kinds, the emitted-text
check `seqCheck`, the width tables, `linkedWF`, distinct instance names,
`noSelfRead`, `portsMatchB`, every instance resolved) and, at depth 0,
`designCheck C 0 s` (the children's `leafCheck` too); `C` is the child map of
hand-built children. Where a guard refuses a candidate, the same check is
evaluated on the refused candidate.

## Real candidates (the optimizer's / the merge's own output)

* **print guard** (`printOk` in `keepGuarded`), `mMulNot`: an instance, a
  product `t = w * a` and `y = ~t`. `optimizeModule` inlines the single-use
  `t` (Phase 3, `inlineSingleUseWires`) as `~((w * a) & 8'd255)`: the NOT of
  an operand whose emitted width the emitter does not know (`exprWidthT` is
  `none` on a product), which the forward fragment refuses. The candidate
  passes G2 and G4; only `printOk` refuses it; `checkedOptimize` returns the
  input module, which passes `textCheckI` and `designCheck C 0`; the refused
  candidate fails the proof-side text check.
* **G2** (`linkedWFX`), `mChain`: an instance reading ANOTHER instance's
  output wire directly. `linkedWFX` reads "the wires an instance drives" as
  all its connected wires among the extracted inputs, so it refuses every
  candidate of such a module (an over-approximation: the real `linkedWF`
  accepts the candidate, evaluated and logged). The candidate passes G4 and
  `printOk`; `checkedOptimize` returns the input module unoptimized; it
  passes `textCheckI` and `designCheck C 0`.
* **masks guard** (`masksKept` in `mergeChecked`), `mMask`: `t` and the
  output `out` are the same slice of an input, and a register reads `t`.
  The merge (`mergeDuplicates`, the real one) turns `out` into the alias
  `out = t`; `refineCheck` ACCEPTS the merge (evaluated); `masksKept`
  refuses it; `mergeChecked` returns the input; every output of the shipped
  module is masked (`outsMaskedN`, the endpoint-side form), and the refused
  candidate's is not.
* **the check does not bind** (`hierGate` without `hierBinds` in
  `checkedOptimize`), `OptFallbackTest.mOutside`: returned unchanged; it
  passes `textCheckI`.

## Hand-made candidates

* **G4** (distinct instance names), `OptFallbackTest.oTwice`, and **G2** on a
  body out of the linked order, `OptFallbackTest.oReordered`: `keepGuarded`
  returns the input module `mGood`, which passes `textCheckI`; each refused
  candidate FAILS `textCheckI` (repeated instance name; `linkedWF` false).

  No input on which the optimizer itself produces such a candidate was found
  by reading `Sparkle/IR/Optimize.lean` and `HierCheck.deinlineParts`: the
  passes map and filter the statement list in order (`cseAndMergeInstances`
  drops duplicate instances, it adds none and renames none;
  `inlineSingleUseWires`, the dead-code filters and the reachability filter
  keep the order), and `deinlineParts` puts the assignment naming a
  connection immediately before its instance. So from an input with
  distinct instance names in the linked order the candidate keeps both.

Nothing here is a theorem: it is evaluation on fixed modules.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.GuardFallbackTest
open Sparkle.IR.AST Sparkle.IR.HierCheck

def b8 (n : String) : Port := { name := n, ty := .bitVector 8 }
def b16 (n : String) : Port := { name := n, ty := .bitVector 16 }
def b1 (n : String) : Port := { name := n, ty := .bit }

/-- A leaf child with one 8-bit output. -/
def childA : Module :=
  { name := "child", inputs := [], outputs := [b8 "o"], wires := [b8 "o"],
    body := [.assign "o" (.const 3 8)] }

/-- A leaf child with an 8-bit input and an 8-bit output. -/
def childB : Module :=
  { name := "childB", inputs := [b8 "i"], outputs := [b8 "o"], wires := [b8 "i", b8 "o"],
    body := [.assign "o" (.ref "i")] }

/-- The one-bit child of `OptFallbackTest`'s modules. -/
def childBit : Module :=
  { name := "child", inputs := [], outputs := [b1 "o"], wires := [b1 "o"],
    body := [.assign "o" (.const 1 1)] }

/-- The child map of the 8-bit modules. -/
def C8 : String → Option (Module × Sparkle.IR.Semantics.WEnv) :=
  Tools.ShippingMachineLinked.childMap [childA, childB]

/-- The child map of `OptFallbackTest`'s modules. -/
def C1 : String → Option (Module × Sparkle.IR.Semantics.WEnv) :=
  Tools.ShippingMachineLinked.childMap [childBit]

/-- Print guard, real candidate: `y = ~(w * a)` through a single-use wire. -/
def mMulNot : Module :=
  { name := "p1", inputs := [b8 "a"], outputs := [b8 "y"],
    wires := [b8 "a", b8 "w", b8 "t", b8 "y"],
    body := [.inst "child" "u0" [("o", .ref "w")],
             .assign "t" (.op .mul [.ref "w", .ref "a"]),
             .assign "y" (.op .not [.ref "t"])] }

/-- G2, real candidate: `u1` reads `u0`'s output wire `w` directly. -/
def mChain : Module :=
  { name := "p2", inputs := [], outputs := [b8 "y"],
    wires := [b8 "w", b8 "v", b8 "t", b8 "y"],
    body := [.inst "child" "u0" [("o", .ref "w")],
             .inst "childB" "u1" [("i", .ref "w"), ("o", .ref "v")],
             .assign "t" (.op .add [.ref "v", .ref "w"]),
             .assign "y" (.op .not [.ref "t"])] }

def sl : Expr := .slice (.ref "x") 7 0

/-- Masks guard, real merge: `t` and `out` are the same slice. -/
def mMask : Module :=
  { name := "pm", inputs := [b16 "x"], outputs := [b8 "out"],
    wires := [b16 "x", b8 "t", b8 "r"],
    body := [.assign "t" sl, .assign "out" sl,
             .register "r" "clk" ("rst", .synchronous) (.ref "t") 0] }

/-- The candidate of the optimizer after the connections are named again. -/
def cand (m : Module) : Module := deinlineRaw m (Sparkle.IR.Optimize.optimizeModule m)

/-- G2 and G4 on a candidate of `m`. -/
def g2 (m c : Module) : Bool := linkedWFX ((openIns m).map (·.name)) c.body
def g4 (c : Module) : Bool := decide (instNamesOf c.body).Nodup

/-- The endpoint-side check of a top module. -/
def top (C : String → Option (Module × Sparkle.IR.Semantics.WEnv)) (s : Module) : Bool :=
  Tools.ShippingDesignSV.textCheckI C s

/-- Its conjuncts, for the log. -/
def parts (C : String → Option (Module × Sparkle.IR.Semantics.WEnv)) (s : Module) : String :=
  s!"text={Tests.Compiler.PrintGuardTest.proofSide s} linkedWF={Tools.ShippingHierOpen.linkedWF C s.body} names={decide (Tools.ShippingHierState.instNames s.body).Nodup} noSelfRead={Tools.ShippingHierPremisesBase.noSelfRead C s.body} ports={Tools.ShippingDesignSV.portsMatchB C s} textCheckI={top C s}"

def note (name : String) (ok : Bool) (bad : Array String) : Array String :=
  if ok then bad else bad.push name

open Lean Elab Command in
run_cmd liftTermElabM do
  let mut bad : Array String := #[]
  let chk := Sparkle.IR.OptCheck.checkedOptimize
  -- ── print guard, real candidate ─────────────────────────────────────────
  let m := mMulNot
  let c := cand m
  let s := chk m
  logInfo m!"GUARDFALLBACK print/real: hierBinds={Sparkle.IR.RefineCheck.hierBinds m} candidate!=input={c != m} printOk(input)={Sparkle.IR.PrintGuard.printOk m} printOk(candidate)={Sparkle.IR.PrintGuard.printOk c} G2={g2 m c} G4={g4 c} hierRefineCheck(candidate)={Sparkle.IR.RefineCheck.hierRefineCheck m c} shipped==input={s == m}; shipped: {parts C8 s} designCheck0={Tools.ShippingDesignSV.designCheck C8 0 s}; candidate: {parts C8 c}"
  bad := note "print/real: hierBinds mMulNot" (Sparkle.IR.RefineCheck.hierBinds m) bad
  bad := note "print/real: the optimizer changes the module" (c != m) bad
  bad := note "print/real: printOk accepts the input" (Sparkle.IR.PrintGuard.printOk m) bad
  bad := note "print/real: printOk refuses the candidate" (!Sparkle.IR.PrintGuard.printOk c) bad
  bad := note "print/real: G2 accepts the candidate" (g2 m c) bad
  bad := note "print/real: G4 accepts the candidate" (g4 c) bad
  bad := note "print/real: keepGuarded falls back" (keepGuarded m c == m) bad
  bad := note "print/real: checkedOptimize returns the input" (s == m) bad
  bad := note "print/real: the shipped module passes textCheckI" (top C8 s) bad
  bad := note "print/real: the shipped module passes designCheck 0"
    (Tools.ShippingDesignSV.designCheck C8 0 s) bad
  bad := note "print/real: the refused candidate fails the proof-side text check"
    (!Tests.Compiler.PrintGuardTest.proofSide c) bad
  bad := note "print/real: the refused candidate fails textCheckI" (!top C8 c) bad
  -- ── G2, real candidate (over-approximation) ─────────────────────────────
  let m := mChain
  let c := cand m
  let s := chk m
  logInfo m!"GUARDFALLBACK G2/real: hierBinds={Sparkle.IR.RefineCheck.hierBinds m} candidate!=input={c != m} G2(input)={g2 m m} G2(candidate)={g2 m c} G4={g4 c} printOk(candidate)={Sparkle.IR.PrintGuard.printOk c} linkedWF(candidate)={Tools.ShippingHierOpen.linkedWF C8 c.body} hierRefineCheck(candidate)={Sparkle.IR.RefineCheck.hierRefineCheck m c} shipped==input={s == m}; shipped: {parts C8 s} designCheck0={Tools.ShippingDesignSV.designCheck C8 0 s}; candidate: {parts C8 c}"
  bad := note "G2/real: hierBinds mChain" (Sparkle.IR.RefineCheck.hierBinds m) bad
  bad := note "G2/real: the optimizer changes the module" (c != m) bad
  bad := note "G2/real: G2 refuses the candidate" (!g2 m c) bad
  bad := note "G2/real: G4 accepts the candidate" (g4 c) bad
  bad := note "G2/real: printOk accepts the candidate" (Sparkle.IR.PrintGuard.printOk c) bad
  bad := note "G2/real: keepGuarded falls back" (keepGuarded m c == m) bad
  bad := note "G2/real: checkedOptimize returns the input" (s == m) bad
  bad := note "G2/real: the shipped module passes textCheckI" (top C8 s) bad
  bad := note "G2/real: the shipped module passes designCheck 0"
    (Tools.ShippingDesignSV.designCheck C8 0 s) bad
  -- ── G4 and G2, hand-made candidates ─────────────────────────────────────
  let m := Tests.Compiler.OptFallbackTest.mGood
  let oT := Tests.Compiler.OptFallbackTest.oTwice
  let oR := Tests.Compiler.OptFallbackTest.oReordered
  logInfo m!"GUARDFALLBACK G4/hand: G4(candidate)={g4 oT}; shipped: {parts C1 (keepGuarded m oT)}; candidate: {parts C1 oT}"
  logInfo m!"GUARDFALLBACK G2/hand: G2(candidate)={g2 m oR}; shipped: {parts C1 (keepGuarded m oR)}; candidate: {parts C1 oR}"
  bad := note "G4/hand: G4 refuses the candidate" (!g4 oT) bad
  bad := note "G4/hand: keepGuarded falls back" (keepGuarded m oT == m) bad
  bad := note "G4/hand: the shipped module passes textCheckI" (top C1 (keepGuarded m oT)) bad
  bad := note "G4/hand: the refused candidate fails textCheckI" (!top C1 oT) bad
  bad := note "G2/hand: G2 refuses the candidate" (!g2 m oR) bad
  bad := note "G2/hand: keepGuarded falls back" (keepGuarded m oR == m) bad
  bad := note "G2/hand: the shipped module passes textCheckI" (top C1 (keepGuarded m oR)) bad
  bad := note "G2/hand: the refused candidate is not linkedWF"
    (!Tools.ShippingHierOpen.linkedWF C1 oR.body) bad
  bad := note "G2/hand: the refused candidate fails textCheckI" (!top C1 oR) bad
  -- ── the check does not bind ─────────────────────────────────────────────
  let m := Tests.Compiler.OptFallbackTest.mOutside
  let s := chk m
  logInfo m!"GUARDFALLBACK nobind: hierGate={Sparkle.IR.RefineCheck.hierGate m} hierBinds={Sparkle.IR.RefineCheck.hierBinds m} optimizeModule!=input={Sparkle.IR.Optimize.optimizeModule m != m} shipped==input={s == m}; shipped: {parts C1 s}"
  bad := note "nobind: hierGate" (Sparkle.IR.RefineCheck.hierGate m) bad
  bad := note "nobind: not hierBinds" (!Sparkle.IR.RefineCheck.hierBinds m) bad
  bad := note "nobind: checkedOptimize returns the input" (s == m) bad
  bad := note "nobind: the shipped module passes textCheckI" (top C1 s) bad
  -- ── masks guard, real merge ─────────────────────────────────────────────
  let m := mMask
  let r := Sparkle.IR.RegDedup.mergeDuplicates m
  let s := Sparkle.IR.RefineCheck.mergeChecked m
  let masked (x : Sparkle.IR.AST.Module) : Bool := x.outputs.all fun p =>
    Sparkle.IR.RefineCheck.outMaskedB (Sparkle.IR.RegDedup.declWidth x) x.body p
  logInfo m!"GUARDFALLBACK masks/real: merge!=input={r != m} refineCheck(merge)={Sparkle.IR.RefineCheck.refineCheck m r} masksKept(merge)={Sparkle.IR.RefineCheck.masksKept m r} printOk(input)={Sparkle.IR.PrintGuard.printOk m} printOk(merge)={Sparkle.IR.PrintGuard.printOk r} shipped==input={s == m}; outputs masked: shipped={masked s} merge={masked r}; outsMaskedN: shipped={Tools.ShippingMachineShipsDepth.outsMaskedN s} merge={Tools.ShippingMachineShipsDepth.outsMaskedN r}"
  bad := note "masks/real: the merge changes the module" (r != m) bad
  bad := note "masks/real: refineCheck accepts the merge" (Sparkle.IR.RefineCheck.refineCheck m r) bad
  bad := note "masks/real: masksKept refuses the merge" (!Sparkle.IR.RefineCheck.masksKept m r) bad
  bad := note "masks/real: mergeChecked returns the input" (s == m) bad
  bad := note "masks/real: every output of the shipped module is masked" (masked s) bad
  bad := note "masks/real: the shipped module passes outsMaskedN"
    (Tools.ShippingMachineShipsDepth.outsMaskedN s) bad
  bad := note "masks/real: the refused merge fails outsMaskedN"
    (!Tools.ShippingMachineShipsDepth.outsMaskedN r) bad
  bad := note "masks/real: the shipped module passes printOk" (Sparkle.IR.PrintGuard.printOk s) bad
  unless bad.isEmpty do
    throwError "GUARDFALLBACK FAILED ({bad.size}): {bad}"
  logInfo m!"GUARDFALLBACK: print guard and G2 fire on the optimizer's own candidate (mMulNot, mChain), the masks guard on the real merge (mMask), G4 and the linked order on hand-made candidates, the does-not-bind fallback on mOutside; in every case the shipped module is the input module and passes the endpoint-side check evaluated (textCheckI, designCheck 0, outsMaskedN); each refused candidate fails the check its guard stands for, G2/real apart (an over-approximation: its candidate is linkedWF)"

end Tests.Compiler.GuardFallbackTest
