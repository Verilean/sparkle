import Tests.Compiler.HierBindsCensusTest
import Tools.ShippingSeqCheckTyped
import Tools.ShippingNamesStable

/-! # The text conjuncts of `designCheck`: audit and measurement (branch `fix/opt-fallback`)

1. A throwing axiom audit of the pure lemmas of round optfb-4
   (`Tools/ShippingWidthTables.lean`, `ShippingNamesStable.lean`,
   `ShippingSeqCheckTyped.lean`). (`Tools/ShippingNamesNext.lean` is audited
   in `Tests/Compiler/NamesNextTest.lean`, so that a failure of that file
   does not block this test.)
2. COMPILED EVIDENCE, logs only (prefix `DESIGNTEXT`): for every census
   candidate, on the full entry's module `b` and on the shipped module
   `o = checkedOptimize b`, the hypotheses of `core_text_same` that are
   decidable and the sub-conjuncts of `seqCheck`, one column each:
   * `wiresStable` — every wire name is sanitize-stable (`hwn`);
   * `portsStable` — every input / output port name is;
   * `readsWires` — every name of `seqNames` is a wire (`hread`);
   * `tgtStable` / `tgtDecl` — assignment targets sanitize-stable; assignment
     targets and register outputs declared in the emitter's map;
   * `widthEq` — `widthOf (weS m) rhs == weS m target` per assignment /
     register;
   * `sf4` — `sf4Check` of every right-hand side / register input;
   * `seqCheck`, `widths` — conjuncts 2 and 3 themselves;
   * `same` — `o == b`.
   Nothing is asserted about them. `TypedExpr` is a `Prop` and is not
   evaluated; `widthEq` and `sf4` are what it is used for.
3. `outNameOk` does not imply sanitize-stability: one name evaluated. -/
namespace Tests.Compiler.DesignTextTest
open Lean Meta

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingWidthTables.declWidth_eq_weS,
      ``Tools.ShippingWidthTables.moduleWof_wire,
      ``Tools.ShippingWidthTables.seqNames_widths,
      ``Tools.ShippingNamesStable.sanitizeName_of_cleanB,
      ``Tools.ShippingNamesStable.sanitizeName_of_allocated,
      ``Tools.ShippingSeqCheckTyped.seqCheck_of_stmts,
      ``Tools.ShippingSeqCheckTyped.seqCheck_of_typed,
      ``Tools.ShippingSeqCheckTyped.core_text_same,
      ``Tools.ShippingSeqCheckTyped.core_designCheck_same] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"DESIGNTEXT AUDIT: declWidth_eq_weS, moduleWof_wire, seqNames_widths, sanitizeName_of_cleanB, sanitizeName_of_allocated, seqCheck_of_stmts, seqCheck_of_typed, core_text_same, core_designCheck_same — standard axioms only"

def bs (b : Bool) : String := if b then "T" else "F"

/-- The columns of one module. -/
def cols (m : Sparkle.IR.AST.Module) : String :=
  let san (s : String) : Bool := Sparkle.Backend.Verilog.sanitizeName s == s
  let wof := Tools.ShippingDesignSV.wofOf m
  let we := Tools.ShippingDesignSV.weS m
  let names := Tools.ShippingSeqSVSoundness.seqNames m.body
  let wireNames := m.wires.map (·.name)
  let wiresStable := m.wires.all fun p => san p.name
  let portsStable := (m.inputs ++ m.outputs).all fun p => san p.name
  let readsWires := names.all fun x => wireNames.contains x
  let tgtStable := m.body.all fun st => match st with
    | .assign l _ => san l
    | _ => true
  let tgtDecl := m.body.all fun st => match st with
    | .assign l _ => (wof l).isSome
    | .register o _ _ _ _ => (wof o).isSome
    | _ => true
  let widthEq := m.body.all fun st => match st with
    | .assign l r => Sparkle.IR.Semantics.widthOf we r == we l
    | .register o _ _ i _ => Sparkle.IR.Semantics.widthOf we i == we o
    | _ => true
  let sf4 := m.body.all fun st => match st with
    | .assign _ r => Tools.SVParser.EmitSem.sf4Check wof we r
    | .register _ _ _ i _ => Tools.SVParser.EmitSem.sf4Check wof we i
    | _ => true
  let seqChk := Tools.SVParser.EmitSem.seqCheck wof we m.body
  let widths := names.all fun x => Sparkle.IR.RegDedup.declWidth m x == we x
  s!"wiresStable={bs wiresStable} portsStable={bs portsStable} readsWires={bs readsWires} " ++
  s!"tgtStable={bs tgtStable} tgtDecl={bs tgtDecl} widthEq={bs widthEq} sf4={bs sf4} " ++
  s!"seqCheck={bs seqChk} widths={bs widths}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut total := 0
  let mut same := 0
  let mut seqB := 0
  let mut seqO := 0
  for n in Tests.Compiler.HierBindsCensusTest.candidates do
    if env.contains n then
      try
        let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
        let o := Sparkle.IR.OptCheck.checkedOptimize b
        total := total + 1
        if o == b then same := same + 1
        if Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
            (Tools.ShippingDesignSV.weS b) b.body then seqB := seqB + 1
        if Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf o)
            (Tools.ShippingDesignSV.weS o) o.body then seqO := seqO + 1
        logInfo m!"DESIGNTEXT {n}: same={bs (o == b)}\n  b: {cols b}\n  o: {cols o}"
      catch e =>
        logInfo m!"DESIGNTEXT {n}: COMPILE FAILED: {e.toMessageData}"
  logInfo m!"DESIGNTEXT CENSUS: {total} declarations; checkedOptimize b == b on {same}; seqCheck true on b: {seqB}, on the shipped module: {seqO}"

#eval IO.println s!"DESIGNTEXT outNameOk \"a'b\" = {Sparkle.IR.Machine.outNameOk "a'b"}; sanitizeName \"a'b\" = {Sparkle.Backend.Verilog.sanitizeName "a'b"}; stable = {Sparkle.Backend.Verilog.sanitizeName "a'b" == "a'b"}"

end Tests.Compiler.DesignTextTest
