import Tests.Compiler.HierBindsCensusTest
import Tools.ShippingPrintGuard

/-! # The print guard on hand-built modules, and its census (branch `fix/opt-fallback`)

Compiled checks (a failure throws):

* `mGood` (an instance, then an assignment reading its output, all names
  declared) passes `printOk`;
* `oUndecl` — the same module with the assignment reading an UNDECLARED
  name — fails `printOk` while passing G2 (`linkedWFX`) and G4 (distinct
  instance names): only the print guard refuses it, and
  `keepGuarded mGood oUndecl` is `mGood`;
* `keepGuarded mGood mGood` is `mGood` (an accepted candidate is kept);
* on both modules the compiler-side verdict equals the proof-side one
  (`seqCheck` and the width tables, evaluated) — compiled evidence of
  `printOk_sound`'s two sides, not a proof.

The census (`PRINTGUARD CENSUS`, logged; only the agreement is asserted):
over the candidates of `HierBindsCensusTest`, for the full entry's module
`b` and the raw candidate `c = deinlineRaw b (optimizeModule b)`:

* `printOk` false on `b`, on `c`, on the shipped module;
* "fires": `c` passes G2 and G4 and fails `printOk` (the print guard alone
  replaces the candidate by `b`);
* the width-table half alone false on `b` and on the shipped module (not
  aggregated by `DESIGNTEXT CENSUS`);
* disagreements between `printOk` and the proof-side check on `b`, `c` and
  the shipped module — an ERROR if any (the two are proved equal).

Expected: fires on 0 (`DESIGNTEXT CENSUS` has `seqCheck` true on every
shipped module of the branch before the guard).

Then an audit of `printOk_sound` and the equalities it rests on.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.PrintGuardTest
open Sparkle.IR.AST Sparkle.IR.HierCheck

def wBit (n : String) : Port := { name := n, ty := .bit }

def instSt : Stmt := .inst "child" "u0" [("o", .ref "w")]

/-- The input module: the instance, then the assignment reading its output. -/
def mGood : Module :=
  { name := "m", inputs := [], outputs := [wBit "y"], wires := [wBit "w", wBit "y"],
    body := [instSt, .assign "y" (.ref "w")] }

/-- A candidate in the linked order, with distinct instance names, reading an
undeclared name. -/
def oUndecl : Module := { mGood with body := [instSt, .assign "y" (.ref "nowhere")] }

/-- The width-table half alone. -/
def widthsHalf (m : Module) : Bool :=
  (Tools.ShippingSeqSVSoundness.seqNames m.body).all
    (fun x => Sparkle.IR.RegDedup.declWidth m x == Tools.ShippingDesignSV.weS m x)

/-- The proof-side verdict: `seqCheck` and the width tables. -/
def proofSide (m : Module) : Bool :=
  Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf m)
      (Tools.ShippingDesignSV.weS m) m.body && widthsHalf m

open Lean Elab Command in
run_cmd liftTermElabM do
  let X := (openIns mGood).map (·.name)
  unless Sparkle.IR.PrintGuard.printOk mGood do throwError "printOk refuses mGood"
  if Sparkle.IR.PrintGuard.printOk oUndecl then throwError "printOk accepts an undeclared read"
  unless linkedWFX X oUndecl.body do throwError "G2 refuses oUndecl (expected: only printOk does)"
  unless decide (instNamesOf oUndecl.body).Nodup do throwError "G4 refuses oUndecl"
  unless keepGuarded mGood oUndecl == mGood do
    throwError "keepGuarded keeps a candidate that fails the print guard"
  unless keepGuarded mGood mGood == mGood do throwError "keepGuarded changes an accepted candidate"
  for m in [mGood, oUndecl] do
    unless Sparkle.IR.PrintGuard.printOk m == proofSide m do
      throwError "printOk and the proof-side check disagree on a hand-built module"
  logInfo m!"PRINTGUARD: printOk accepts mGood, refuses an undeclared read that G2 and G4 accept; keepGuarded falls back to the input module; the compiler-side and proof-side verdicts agree on both"

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let mut total := 0
  let mut badB := 0
  let mut badC := 0
  let mut badO := 0
  let mut fires := 0
  let mut wB := 0
  let mut wO := 0
  let mut same := 0
  let mut disagree := 0
  for n in Tests.Compiler.HierBindsCensusTest.candidates do
    if env.contains n then
      try
        let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
        let c := deinlineRaw b (Sparkle.IR.Optimize.optimizeModule b)
        let o := Sparkle.IR.OptCheck.checkedOptimize b
        total := total + 1
        let pB := Sparkle.IR.PrintGuard.printOk b
        let pC := Sparkle.IR.PrintGuard.printOk c
        let pO := Sparkle.IR.PrintGuard.printOk o
        unless pB do badB := badB + 1
        unless pC do badC := badC + 1
        unless pO do badO := badO + 1
        let g24 := decide (instNamesOf c.body).Nodup &&
          linkedWFX ((openIns b).map (·.name)) c.body
        if g24 && !pC then fires := fires + 1
        unless widthsHalf b do wB := wB + 1
        unless widthsHalf o do wO := wO + 1
        if o == b then same := same + 1
        unless pB == proofSide b && pC == proofSide c && pO == proofSide o do
          disagree := disagree + 1
        logInfo m!"PRINTGUARD {n}: printOk b={pB} candidate={pC} shipped={pO}; G2&G4 on the candidate={g24}; shipped==b: {o == b}"
      catch e =>
        logInfo m!"PRINTGUARD {n}: COMPILE FAILED: {e.toMessageData}"
  logInfo m!"PRINTGUARD CENSUS: {total} declarations; printOk false on b: {badB}, on the raw candidate: {badC}, on the shipped module: {badO}; the print guard alone fires on {fires}; width tables false on b: {wB}, on the shipped module: {wO}; checkedOptimize b == b on {same}; compiler-side / proof-side disagreements: {disagree}"
  unless disagree == 0 do
    throwError "printOk and the proof-side check disagree on {disagree} census modules"

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingPrintGuard.widths_eq, ``Tools.ShippingPrintGuard.weOf_eq,
      ``Tools.ShippingPrintGuard.seqNames_eq, ``Tools.ShippingPrintGuard.immuneE_eq,
      ``Tools.ShippingPrintGuard.isShlLit_eq, ``Tools.ShippingPrintGuard.shlOperand_eq,
      ``Tools.ShippingPrintGuard.shlSideOK_eq, ``Tools.ShippingPrintGuard.ew_eq,
      ``Tools.ShippingPrintGuard.sf4_eq, ``Tools.ShippingPrintGuard.seqText_sound,
      ``Tools.ShippingPrintGuard.printOk_sound,
      ``Sparkle.IR.HierCheck.keepGuarded_cases, ``Sparkle.IR.HierCheck.keepGuarded_print,
      ``Sparkle.IR.HierCheck.deinline_print] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"PRINTGUARD AUDIT: widths_eq, weOf_eq, seqNames_eq, immuneE_eq, isShlLit_eq, shlOperand_eq, shlSideOK_eq, ew_eq, sf4_eq, seqText_sound, printOk_sound, keepGuarded_cases, keepGuarded_print, deinline_print — standard axioms only"

end Tests.Compiler.PrintGuardTest
