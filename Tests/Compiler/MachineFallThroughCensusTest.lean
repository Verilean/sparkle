import Tests.Compiler.CallWidthHuntTest

/-! # A census of the machine arm DECLINING after it ran (finding E)

Compiled evidence, LOGS ONLY — nothing here throws and nothing is a theorem.

`synthesizeFromConst` (`Sparkle/Compiler/Elab.lean`): when no certified gate
accepts the entry constant and `machineShape?` returns a shape, the machine
arm `synthesizeMachineCertified` RUNS — the transition through the
combinational harness, then `closeLets`, then the calls' closing, which
synthesises every child. When it returns `none` (`closeLets` or the closing
refuses) the entry goes on to the legacy arm with a fresh `CircuitM.init`,
but the refs the wire naming reads (`sparkleLetWireCache`,
`sparkleLoopWireCache`, `sparkleWireCanon`, `sparkleSingleOutInstanceCache`,
`sparkleSubInstanceOutputs`, `sparkleFvarValueMap`, `sparkleWireWidthCache`)
keep what the harness run and the children's entries left.

Population: `PrintArtifactCensusTest.candidates` (37), the hunt's parents
and children (`CallWidthHuntTest`), and — when `envSweep` — every definition
of the environment from a user module whose result type is a Signal, a pair
or a user structure of Signals (at most `sweepCap`, in name order).

For each declaration the gates are evaluated on its entry constant; only a
declaration with NO gate and a machine shape is compiled. Its route is
`CallWidthHuntTest.routeOf`: the machine arm re-run from reset refs at depth
1; `fallthrough` when it returns `none`. For a fall-through:

    FALLTHROUGH <name>: lets=.. insts=.. oneOut=.. sameAsClean=<T/F/err> sameAsNoFrontEnd=<T/F/err>
      undeclared(real)=[..] undeclared(clean)=[..] undriven(real)=[..] undriven(clean)=[..]

* `sameAsClean`: the real module equals the LEGACY arm run on the SAME entry
  constant from reset refs (`synthesizeFromConst … certifiedFrontEnd := false`
  at depth 1) — `F` means the refs left by the declined machine arm changed
  the output;
* `sameAsNoFrontEnd`: the real module equals the entry's with
  `certifiedFrontEnd := false` (the ORIGINAL constant, not the unfolded one);
* `undeclared`: names a statement reads (assign right sides, register
  inputs / clocks / resets, memory ports, instance connections) that are
  not an input, output or wire of the module; `undriven`: read names that
  are neither an input nor written by a statement (every reference of an
  instance connection counts as written).

    FALLTHROUGH CENSUS: …

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.MachineFallThroughCensusTest
open Lean Meta
open Sparkle.Compiler.Elab
open Tests.Compiler.CallWidthHuntTest (Mod Dsn bs gatesOf routeOf resetRefs huntParents huntChildren)

/-- Sweep the environment too. Set to `false` to census the lists only. -/
def envSweep : Bool := true

/-- At most this many declarations of the sweep are examined. -/
def sweepCap : Nat := 300

/-- The result type (under its binders) is a Signal, a pair, or a user
structure of Signals. -/
def resultHead (env : Environment) : Lean.Expr → Bool
  | .forallE _ _ b _ => resultHead env b
  | e =>
    match e.getAppFn with
    | .const c _ =>
      c == ``Sparkle.Core.Signal.Signal || c == ``Prod || (userStructure? env c).isSome
    | _ => false

/-- The definitions of user modules with such a result type, in name order. -/
def sweepNames (env : Environment) : List Name :=
  let arr := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    match ci with
    | .defnInfo d =>
      if n.isInternal || n.hasMacroScopes || !inlUserModule env n then acc
      else if resultHead env d.type then acc.push n else acc
    | _ => acc
  (arr.qsort (fun a b => a.toString < b.toString)).toList

/-- Every name a statement reads. -/
def allReads : Sparkle.IR.AST.Stmt → List String
  | .assign _ r => Sparkle.IR.Reorder.refsOf r
  | .register _ c rst i _ => c :: rst.1 :: Sparkle.IR.Reorder.refsOf i
  | .memory _ _ _ c wa wd we ra _ _ ew er =>
    c :: (Sparkle.IR.Reorder.refsOf wa ++ Sparkle.IR.Reorder.refsOf wd ++
      Sparkle.IR.Reorder.refsOf we ++ Sparkle.IR.Reorder.refsOf ra ++
      ew.flatMap (fun p => Sparkle.IR.Reorder.refsOf p.1 ++ Sparkle.IR.Reorder.refsOf p.2.1 ++
        Sparkle.IR.Reorder.refsOf p.2.2) ++
      er.flatMap (fun p => Sparkle.IR.Reorder.refsOf p.1))
  | .inst _ _ conns => conns.flatMap fun c => Sparkle.IR.Reorder.refsOf c.2

/-- Every name a statement drives (an instance: every reference of its
connections — an over-approximation). -/
def allWrites : Sparkle.IR.AST.Stmt → List String
  | .assign l _ => [l]
  | .register o _ _ _ _ => [o]
  | .memory _ _ _ _ _ _ _ _ rd _ _ er => rd :: er.map (·.2)
  | .inst _ _ conns => conns.flatMap fun c => Sparkle.IR.Reorder.refsOf c.2

/-- Read names the module does not declare. -/
def undeclared (m : Mod) : List String :=
  let decl := m.inputs.map (·.name) ++ m.outputs.map (·.name) ++ m.wires.map (·.name)
  ((m.body.flatMap allReads).filter fun x => !decl.contains x).eraseDups

/-- Read names that are neither an input nor driven. -/
def undriven (m : Mod) : List String :=
  let drv := m.inputs.map (·.name) ++ m.body.flatMap allWrites
  ((m.body.flatMap allReads).filter fun x => !drv.contains x).eraseDups

/-- The legacy arm on the given entry constant, from reset refs, at depth 1. -/
def cleanLegacy (n : Name) (ec : ConstantInfo) : MetaM (Mod × Dsn) := do
  let env ← getEnv
  resetRefs
  sparkleSynthDepth.set 1
  try
    synthesizeFromConst (fun e hint top named => translateExprToWire e hint top named)
      (fun _ => pure ()) n [] false false ec (instancePredicate env)
  finally
    sparkleSynthDepth.set 0

/-- The entry without the certified front end (the original constant). -/
def noFrontEnd (n : Name) : MetaM (Mod × Dsn) :=
  synthesizeCombinationalCoreWith (fun e hint top named => translateExprToWire e hint top named)
    n [] false (certifiedFrontEnd := false)

/-- The class of a declaration, and for a fall-through its line and whether
it differs from the clean legacy run / reads an undeclared name. -/
structure Row where
  cls : String
  line : String := ""
  differs : Bool := false
  reads : Bool := false

def census (n : Name) : MetaM Row := do
  let g ← gatesOf n
  if g.gate then return { cls := "gate" }
  if g.mixed then return { cls := "mixed" }
  let some shape := g.shape | return { cls := "noshape" }
  let (raw, _) ← synthesizeCombinationalCore n [] false
  let (route, _, ec) ← routeOf n raw
  if route == "machine" then return { cls := "machine" }
  if route != "fallthrough" then return { cls := "undetermined", line := route }
  let clean? : Option Mod ←
    try
      let r ← cleanLegacy n ec
      pure (some r.1)
    catch _ => pure none
  let orig? : Option Mod ←
    try
      let r ← noFrontEnd n
      pure (some r.1)
    catch _ => pure none
  let same (x : Option Mod) : String := match x with
    | some m => bs (m == raw)
    | none => "err"
  let und := undeclared raw
  let undC := match clean? with
    | some m => undeclared m
    | none => []
  let drvC := match clean? with
    | some m => undriven m
    | none => []
  let differs := match clean? with
    | some m => !(m == raw)
    | none => false
  let line :=
    s!"lets={shape.layout.lets} insts={shape.insts.length} oneOut={bs shape.instFields.isEmpty} " ++
    s!"slots={shape.layout.slots.length} sameAsClean={same clean?} sameAsNoFrontEnd={same orig?} " ++
    s!"undeclared(real)={und} undeclared(clean)={undC} " ++
    s!"undriven(real)={undriven raw} undriven(clean)={drvC}"
  return { cls := "fallthrough", line := line, differs := differs, reads := !und.isEmpty }

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let lists := Tests.Compiler.PrintArtifactCensusTest.candidates ++ huntParents ++ huntChildren
  let swept := if envSweep then (sweepNames env).filter (fun n => !lists.contains n) else []
  let sweep := swept.take sweepCap
  let all := lists ++ sweep
  let mut absent : Nat := 0
  let mut gate : Nat := 0
  let mut mixed : Nat := 0
  let mut noshape : Nat := 0
  let mut machine : Nat := 0
  let mut falls : List Name := []
  let mut undet : List Name := []
  let mut failed : List Name := []
  let mut differ : List Name := []
  let mut reads : List Name := []
  for n in all do
    if !env.contains n then
      absent := absent + 1
    else
      let t0 ← IO.monoMsNow
      try
        let r ← census n
        let t1 ← IO.monoMsNow
        if r.cls == "gate" then gate := gate + 1
        else if r.cls == "mixed" then mixed := mixed + 1
        else if r.cls == "noshape" then noshape := noshape + 1
        else if r.cls == "machine" then
          machine := machine + 1
          logInfo m!"MACHINE {n}: machine route confirmed ({t1 - t0} ms)"
        else if r.cls == "fallthrough" then
          falls := falls ++ [n]
          if r.differs then differ := differ ++ [n]
          if r.reads then reads := reads ++ [n]
          logInfo m!"FALLTHROUGH {n}: {r.line} ({t1 - t0} ms)"
        else
          undet := undet ++ [n]
          logInfo m!"UNDETERMINED {n}: {r.line} ({t1 - t0} ms)"
      catch e =>
        failed := failed ++ [n]
        logInfo m!"FALLTHROUGH-CENSUS {n}: COMPILE FAILED: {e.toMessageData}"
  logInfo m!"FALLTHROUGH CENSUS: population {all.length} (lists {lists.length}, environment sweep {sweep.length} of {swept.length}, cap {sweepCap}); absent {absent}; gate {gate}; mixed {mixed}; no gate and no machine shape {noshape}; machine shape without a gate {machine + falls.length + undet.length + failed.length}: machine route confirmed {machine}, FALL-THROUGH {falls.length} {falls}, undetermined {undet.length} {undet}, compile failed {failed.length} {failed}; fall-through differing from the clean legacy run {differ.length} {differ}; fall-through reading an undeclared name {reads.length} {reads}"

end Tests.Compiler.MachineFallThroughCensusTest
