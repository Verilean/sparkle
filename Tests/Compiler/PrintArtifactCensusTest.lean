import Tests.Compiler.ShippingCallsCloseTest
import Tests.Compiler.ShippingMachineSeqLoopTest
import Tests.Compiler.ShippingDesignSVMemTest
import Tools.ShippingPremiseEval

/-! # A census of the PRINTED artifact against the endpoints' artifact (finding D)

Compiled evidence, LOGS ONLY — nothing here throws and nothing is a theorem.

The hierarchical commands (`#synthesizeVerilogDesign`, `#writeVerilogDesign`,
`#sim`, `#writeDesign`) print `toVerilogDesign (← synthesizeHierarchical n)`:

    toVerilogDesign d =
      "\n".intercalate (d.modules.map fun m => emitModule (optimizeModule m))

i.e. the UNCHECKED optimizer on every module (`#sim` applies
`optimizeDesign` to the design first, so each module is optimized twice).
The single-module commands print `verilogOf b = toVerilog (checkedOptimize b)`
for `b` the module of `synthesizeCombinational n`, and that — with the
children as the design's modules UNOPTIMIZED — is what the endpoints speak
about.

`toVerilog` vs `emitModule` (read in `Sparkle/Backend/Verilog.lean`):
`toVerilog m` is DEFINED as `emitModule m` — no header, nothing added — so
the two texts are compared like for like, and this file calls `emitModule`
on both sides.

`synthesizeHierarchical n` (read in `Sparkle/Compiler/Elab.lean`) is, in
`MetaM`:

    let (module, design) ← synthesizeCombinational n
    let design' := if design.modules.any (·.name == module.name) then design
                   else design.addModule module          -- appended LAST
    validateDesignNames design'                          -- identity or throws

For every candidate (the 30 declarations of `HierBindsCensusTest` plus leaf
declarations without an instance), with

* `dH` the design of `synthesizeHierarchical n` (called as the commands do),
* `(bC, dC)` a separate run of `synthesizeCombinational n` (`bC` is the
  endpoints' `b`),
* `bH` the module of `dH` named `bC.name` (the top),
* `(_, D)` the run of `synthesizeCombinationalCore n [] false`,

one line `PRINTARTIFACT <decl>: …` with the columns

* `mods` number of modules of `dH`; `kids` those not named `bC.name`;
* `topFound` `dH` has a module named `bC.name`; `topName` `bC.name` is
  `toString n` (what `#sim` looks up); `topField` `dH.topModule == bC.name`;
* `rerun` `dH == (the design the definition of synthesizeHierarchical gives
  from (bC, dC))` — the two runs agree (determinism of the entry);
* `top` `bH == bC`; when false a second line `… TOPDIFF` gives name,
  #inputs, #outputs, #wires, #stmts of both;
* `optH=optC` `optimizeModule bH == optimizeModule bC`;
* `unchk=chk` `optimizeModule bC == checkedOptimize bC` (on the endpoints'
  module: does the check/deinline change the optimizer's output);
* `chk=b` `checkedOptimize bC == bC`;
* `printed` `optimizeModule bH == checkedOptimize bC` (the design commands'
  top module against the endpoints' top module);
* `text` `emitModule (optimizeModule bH) == emitModule (checkedOptimize bC)`;
  when false a line `… TEXTDIFF` gives the lengths and the first differing
  line;
* children (modules of `dH` other than the top): `kOptChg` number with
  `optimizeModule c != c` (the endpoint takes `c`, the print takes
  `optimizeModule c`); `kTxtChg` number with
  `emitModule (optimizeModule c) != emitModule c`; `kUnchk=chk` number with
  `optimizeModule c == checkedOptimize c`; `kChk=c` number with
  `checkedOptimize c == c`; a line `… KIDS` names the children in each class;
* `setNames` the module names of `dH` are those of `D` plus the top (as
  lists, in order; `D ++ [top]` only when `D` has no module of that name);
  `setEq` number of modules of `dH` that are `==` to the module of that name
  in that reference (reference top: `D`'s own module of that name if any,
  else `bC`); extra / missing / unequal names are listed;
* `idem` number of modules `m` of `dH` with
  `optimizeModule (optimizeModule m) == optimizeModule m` (the `#sim` path);
  the others are listed.

Then the totals line `PRINTARTIFACT CENSUS: …`.

## The checked writer (isolated branch `fix/design-writer`)

On this branch `#synthesizeVerilogDesign`, `#writeVerilogDesign` and
`#writeDesign` print `toVerilogDesignChecked dH`
(`Sparkle/Backend/VerilogDesign.lean`): the module named `dH.topModule`
through `checkedOptimize`, every other module as it is (`designArtifact`).
`#sim` still prints `toVerilogDesign (optimizeDesign dH)`. A second line
`PRINTARTIFACT <decl>: WRITER …` per declaration, with `art` =
`designArtifact dH` and `(raw, D)` the core run:

* `wTop` the module of `art` named `bC.name` is `checkedOptimize bC`
  (expected T on every declaration); `wTopText` its emitted text is
  `emitModule (checkedOptimize bC)`;
* `wKids` number of the other modules of `art`; `wKidEq` those `==` to the
  module of that name in `D` (the endpoints' child, `childMap D.modules`);
  `wKidTxt` those whose emitted text is `emitModule` of that module (expected:
  all); the others are listed;
* `wList` `art == D.modules ++ [checkedOptimize bC]` and `wText`
  `toVerilogDesignChecked dH ==
  "\n".intercalate (D.modules.map emitModule ++ [emitModule (checkedOptimize bC)])`
  — the two equations `Tools.ShippingDesignWriterRun.writer_prints_endpoint_artifact`
  concludes, observed;
* `hno` no module of `D` is named `raw.name` and `htop`
  `D.topModule == raw.name` — that theorem's two data premises;
* `kZero` number of children `c` with `dropZeroWidthModule c != c` (a
  zero-width wire the optimizer's 0-bit pass would have removed is still
  there; expected 0 — the children come from their own full entry);
* the cost of printing the children as they are: `kLen` characters of their
  emitted texts, `kLenOpt` through `optimizeModule`, `kLenChk` through
  `checkedOptimize` (the variant `toVerilogDesignCheckedKids`, not used by
  any command).

Then `PRINTARTIFACT WRITER CENSUS: …` with the totals. -/
namespace Tests.Compiler.PrintArtifactCensusTest
open Lean Meta

def bs (b : Bool) : String := if b then "T" else "F"

/-- The candidates, by name (an absent name is logged, not an error): the 30
declarations of `HierBindsCensusTest`, then leaf declarations. -/
def candidates : List Name := [
  `Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
  `Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained,
  `Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid,
  `Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand,
  `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
  `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH,
  `Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2,
  `Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2,
  `Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1,
  `Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide,
  `Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter,
  `Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems,
  `Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems,
  `Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory,
  `Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent,
  `Sparkle.Tests.Compiler.MultiInstance.engineOnce,
  `Sparkle.Tests.Compiler.MultiInstance.twinCalls,
  `Sparkle.Tests.Compiler.MultiInstance.mesh2x2,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.caller,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner,
  `Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix,
  `Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL,
  `Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN,
  `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte,
  `Sparkle.Tests.Compiler.ShippingMachineTeleTest.divInLoop,
  `callerRep,
  `callerABA,
  -- leaf declarations (no instance expected): the single-module case
  `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
  `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH,
  `Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.pick,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.counter2,
  `Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH,
  `Sparkle.Tests.Compiler.ShippingMachineLinkedTest.counterB]

/-- name, #inputs, #outputs, #wires, #stmts. -/
def shape (m : Sparkle.IR.AST.Module) : String :=
  s!"name={m.name} in={m.inputs.length} out={m.outputs.length} " ++
  s!"wires={m.wires.length} stmts={m.body.length}"

def clip (s : String) : String := String.ofList (s.toList.take 160)

/-- The first differing line of two texts (index from 0). -/
def firstDiffAux : List String → List String → Nat → String
  | x :: xs, y :: ys, i =>
    if x == y then firstDiffAux xs ys (i + 1)
    else s!"line {i}: design [{clip x}] single [{clip y}]"
  | x :: _, [], i => s!"line {i}: design [{clip x}] single <end of text>"
  | [], y :: _, i => s!"line {i}: design <end of text> single [{clip y}]"
  | [], [], _ => "no differing line"

def firstDiff (a b : String) : String :=
  firstDiffAux (a.splitOn "\n") (b.splitOn "\n") 0

/-- One declaration's record. -/
structure Row where
  mods : Nat
  kids : Nat
  hasInst : Bool
  topFound : Bool
  topName : Bool
  topField : Bool
  rerun : Bool
  top : Bool
  topDiff : String
  optHC : Bool
  unchkChk : Bool
  chkSame : Bool
  printed : Bool
  text : Bool
  textDiff : String
  kOptChg : List String
  kTxtChg : List String
  kUnchkChk : List String
  kChkSame : List String
  setNames : Bool
  setExtra : List String
  setMissing : List String
  setEq : Nat
  setUnequal : List String
  idem : Nat
  notIdem : List String
  -- the checked writer
  wTop : Bool
  wTopText : Bool
  wKids : Nat
  wKidEq : Nat
  wKidTxt : Nat
  wKidDiff : List String
  wList : Bool
  wText : Bool
  hno : Bool
  htop : Bool
  kZero : List String
  kLen : Nat
  kLenOpt : Nat
  kLenChk : Nat

def Row.str (r : Row) : String :=
  s!"mods={r.mods} kids={r.kids} inst={bs r.hasInst} topFound={bs r.topFound} " ++
  s!"topName={bs r.topName} topField={bs r.topField} rerun={bs r.rerun} top={bs r.top} " ++
  s!"optH=optC={bs r.optHC} unchk=chk={bs r.unchkChk} chk=b={bs r.chkSame} " ++
  s!"printed={bs r.printed} text={bs r.text} " ++
  s!"kOptChg={r.kOptChg.length} kTxtChg={r.kTxtChg.length} " ++
  s!"kUnchk=chk={r.kUnchkChk.length} kChk=c={r.kChkSame.length} " ++
  s!"setNames={bs r.setNames} extra={r.setExtra} missing={r.setMissing} " ++
  s!"setEq={r.setEq}/{r.mods} unequal={r.setUnequal} " ++
  s!"idem={r.idem}/{r.mods} notIdem={r.notIdem}"

def Row.writerStr (r : Row) : String :=
  s!"wTop={bs r.wTop} wTopText={bs r.wTopText} wKids={r.wKids} wKidEq={r.wKidEq} " ++
  s!"wKidTxt={r.wKidTxt} wKidDiff={r.wKidDiff} wList={bs r.wList} wText={bs r.wText} " ++
  s!"hno={bs r.hno} htop={bs r.htop} kZero={r.kZero} " ++
  s!"kLen={r.kLen} kLenOpt={r.kLenOpt} kLenChk={r.kLenChk}"

def Row.kidsStr (r : Row) : String :=
  s!"optimizer changes {r.kOptChg}; optimizer changes the text {r.kTxtChg}; " ++
  s!"unchecked == checked {r.kUnchkChk}; checked == child {r.kChkSame}"

/-- The record of a declaration. -/
def census (n : Name) : MetaM Row := do
  -- the design the hierarchical commands print (called as they call it)
  let dH ← Sparkle.Compiler.Elab.synthesizeHierarchical n
  -- the endpoints' module: a separate run of the single-module entry
  let (bC, dC) ← Sparkle.Compiler.Elab.synthesizeCombinational n
  -- the core run's design
  let (raw, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
  let opt (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module := Sparkle.IR.Optimize.optimizeModule m
  let chk (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module := Sparkle.IR.OptCheck.checkedOptimize m
  let emit (m : Sparkle.IR.AST.Module) : String := Sparkle.Backend.Verilog.emitModule m
  let topN := bC.name
  -- the definition of `synthesizeHierarchical`, replayed on the second run
  let dH2 : Sparkle.IR.AST.Design :=
    if dC.modules.any (·.name == topN) then dC else dC.addModule bC
  let bH? := dH.modules.find? (·.name == topN)
  let bH := bH?.getD bC
  let kids := dH.modules.filter (fun m => !(m.name == topN))
  let oH := opt bH
  let oC := opt bC
  let cC := chk bC
  let tDesign := emit oH
  let tSingle := emit cC
  let textEq := tDesign == tSingle
  -- the reference set: the core design plus the top
  let refMods : List Sparkle.IR.AST.Module :=
    if D.modules.any (·.name == topN) then D.modules else D.modules ++ [bC]
  let namesH := dH.modules.map (·.name)
  let namesR := refMods.map (·.name)
  let eqByName (m : Sparkle.IR.AST.Module) : Bool :=
    match refMods.find? (·.name == m.name) with
    | some r => r == m
    | none => false
  let idemOf (m : Sparkle.IR.AST.Module) : Bool := opt (opt m) == opt m
  -- the checked writer's modules and text
  let art : List Sparkle.IR.AST.Module := Sparkle.Backend.Verilog.designArtifact dH
  let aTop? := art.find? (·.name == topN)
  let aKids := art.filter (fun m => !(m.name == topN))
  let kidRef (m : Sparkle.IR.AST.Module) : Option Sparkle.IR.AST.Module :=
    D.modules.find? (·.name == m.name)
  let kidEq (m : Sparkle.IR.AST.Module) : Bool :=
    match kidRef m with
    | some r => r == m
    | none => false
  let kidTxt (m : Sparkle.IR.AST.Module) : Bool :=
    match kidRef m with
    | some r => emit r == emit m
    | none => false
  let wTopB : Bool :=
    match aTop? with
    | some m => m == cC
    | none => false
  let wTopTextB : Bool :=
    match aTop? with
    | some m => emit m == tSingle
    | none => false
  let endpointMods : List Sparkle.IR.AST.Module := D.modules ++ [cC]
  let endpointText : String :=
    String.intercalate "\n" (D.modules.map emit ++ [emit cC])
  let len (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) : Nat :=
    kids.foldl (fun a c => a + (emit (f c)).length) 0
  return {
    mods := dH.modules.length
    kids := kids.length
    hasInst := bC.body.any Sparkle.IR.Machine.isInst
    topFound := bH?.isSome
    topName := topN == Sparkle.IR.ModuleName.ofDecl n
    topField := dH.topModule == topN
    rerun := dH == dH2
    top := bH == bC
    topDiff := s!"design top [{shape bH}] single [{shape bC}]"
    optHC := oH == oC
    unchkChk := oC == cC
    chkSame := cC == bC
    printed := oH == cC
    text := textEq
    textDiff :=
      if textEq then "" else
        s!"design text {tDesign.length} chars, single text {tSingle.length} chars; " ++
        s!"printed modules: design [{shape oH}] single [{shape cC}]; " ++
        s!"first difference at {firstDiff tDesign tSingle}"
    kOptChg := (kids.filter fun c => !(opt c == c)).map (·.name)
    kTxtChg := (kids.filter fun c => !(emit (opt c) == emit c)).map (·.name)
    kUnchkChk := (kids.filter fun c => opt c == chk c).map (·.name)
    kChkSame := (kids.filter fun c => chk c == c).map (·.name)
    setNames := namesH == namesR
    setExtra := namesH.filter fun x => !namesR.contains x
    setMissing := namesR.filter fun x => !namesH.contains x
    setEq := (dH.modules.filter eqByName).length
    setUnequal := (dH.modules.filter fun m => !eqByName m).map (·.name)
    idem := (dH.modules.filter idemOf).length
    notIdem := (dH.modules.filter fun m => !idemOf m).map (·.name)
    wTop := wTopB
    wTopText := wTopTextB
    wKids := aKids.length
    wKidEq := (aKids.filter kidEq).length
    wKidTxt := (aKids.filter kidTxt).length
    wKidDiff := (aKids.filter fun m => !kidTxt m).map (·.name)
    wList := art == endpointMods
    wText := Sparkle.Backend.Verilog.toVerilogDesignChecked dH == endpointText
    hno := D.modules.all fun x => !(x.name == raw.name)
    htop := D.topModule == raw.name
    kZero := (kids.filter fun c =>
      !(Sparkle.IR.ZeroWidth.dropZeroWidthModule c == c)).map (·.name)
    kLen := len id
    kLenOpt := len opt
    kLenChk := len chk }

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut rows : List (Name × Row) := []
  let mut absent : List Name := []
  let mut failed : List Name := []
  for n in candidates do
    if !env.contains n then
      absent := absent ++ [n]
      logInfo m!"PRINTARTIFACT {n}: ABSENT (no such declaration in this build)"
    else
      try
        let r ← census n
        rows := rows ++ [(n, r)]
        logInfo m!"PRINTARTIFACT {n}: {r.str}"
        logInfo m!"PRINTARTIFACT {n}: WRITER {r.writerStr}"
        unless r.top do
          logInfo m!"PRINTARTIFACT {n}: TOPDIFF {r.topDiff}"
        unless r.text do
          logInfo m!"PRINTARTIFACT {n}: TEXTDIFF {r.textDiff}"
        unless r.kids == 0 do
          logInfo m!"PRINTARTIFACT {n}: KIDS {r.kidsStr}"
      catch e =>
        failed := failed ++ [n]
        logInfo m!"PRINTARTIFACT {n}: COMPILE FAILED: {e.toMessageData}"
  let cnt (p : Row → Bool) : Nat := (rows.filter fun x => p x.2).length
  let names (p : Row → Bool) : List Name := (rows.filter fun x => p x.2).map (·.1)
  let sum (f : Row → Nat) : Nat := rows.foldl (fun a x => a + f x.2) 0
  let allIdem (r : Row) : Bool := r.idem == r.mods
  let allSet (r : Row) : Bool := r.setNames && r.setEq == r.mods
  let line : String :=
    s!"PRINTARTIFACT CENSUS: {rows.length} declarations " ++
    s!"({cnt (fun r => r.hasInst)} with an instance, {cnt (fun r => !r.hasInst)} without; " ++
    s!"{absent.length} absent {absent}); " ++
    s!"top found in the design {cnt (fun r => r.topFound)}; " ++
    s!"the two runs agree {cnt (fun r => r.rerun)}, not {names (fun r => !r.rerun)}; " ++
    s!"top module equal (bH == bC) {cnt (fun r => r.top)}, not {names (fun r => !r.top)}; " ++
    s!"optimizeModule bC == checkedOptimize bC {cnt (fun r => r.unchkChk)}; " ++
    s!"checkedOptimize bC == bC {cnt (fun r => r.chkSame)}; " ++
    s!"top printed module equal (optimizeModule bH == checkedOptimize bC) " ++
    s!"{cnt (fun r => r.printed)}, not {names (fun r => !r.printed)}; " ++
    s!"top text equal {cnt (fun r => r.text)}, not {names (fun r => !r.text)}; " ++
    s!"children: total {sum (fun r => r.kids)}, " ++
    s!"optimizer changes {sum (fun r => r.kOptChg.length)}, " ++
    s!"optimizer changes the text {sum (fun r => r.kTxtChg.length)}, " ++
    s!"unchecked == checked {sum (fun r => r.kUnchkChk.length)}, " ++
    s!"checked == child {sum (fun r => r.kChkSame.length)}; " ++
    s!"design module names equal {cnt (fun r => r.setNames)}; " ++
    s!"design module sets equal {cnt allSet}, not {names (fun r => !allSet r)}; " ++
    s!"optimizer idempotent on all modules {cnt allIdem}, not {names (fun r => !allIdem r)}; " ++
    s!"failures {failed}"
  logInfo m!"{line}"
  let wline : String :=
    s!"PRINTARTIFACT WRITER CENSUS: {rows.length} declarations; " ++
    s!"writer top module == checkedOptimize bC {cnt (fun r => r.wTop)}, " ++
    s!"not {names (fun r => !r.wTop)}; " ++
    s!"writer top text == emitModule (checkedOptimize bC) {cnt (fun r => r.wTopText)}, " ++
    s!"not {names (fun r => !r.wTopText)}; " ++
    s!"children printed: total {sum (fun r => r.wKids)}, " ++
    s!"== the core design's module {sum (fun r => r.wKidEq)}, " ++
    s!"text == emitModule of it {sum (fun r => r.wKidTxt)}, " ++
    s!"declarations with a differing child {names (fun r => !r.wKidDiff.isEmpty)}; " ++
    s!"module list == D.modules ++ [checkedOptimize bC] {cnt (fun r => r.wList)}, " ++
    s!"not {names (fun r => !r.wList)}; " ++
    s!"whole text == the endpoints' text {cnt (fun r => r.wText)}, " ++
    s!"not {names (fun r => !r.wText)}; " ++
    s!"premise hno {cnt (fun r => r.hno)}, not {names (fun r => !r.hno)}; " ++
    s!"premise htop {cnt (fun r => r.htop)}, not {names (fun r => !r.htop)}; " ++
    s!"children with a zero-width wire left {sum (fun r => r.kZero.length)} " ++
    s!"in {names (fun r => !r.kZero.isEmpty)}; " ++
    s!"children's text: as they are {sum (fun r => r.kLen)} characters, " ++
    s!"optimizeModule {sum (fun r => r.kLenOpt)}, " ++
    s!"checkedOptimize {sum (fun r => r.kLenChk)}"
  logInfo m!"{wline}"

end Tests.Compiler.PrintArtifactCensusTest
