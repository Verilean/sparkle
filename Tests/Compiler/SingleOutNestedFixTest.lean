import Lean.Elab.Command
import Tests.Compiler.MachineFallThroughCensusTest

/-! # A nested entry and the single-output instance map (finding I): the regression test of the fix

WRITTEN, NOT BUILT (`fix/singleout-nested`). Target-only; not in
`Tests.AllTests`. Uses no declaration of the candidate, so it builds on poc
(`e6f68394`) and on the candidate; whether the entry is the FIXED one is
MEASURED (§0) and the assertions are made only when it is. Every "PREDICTED"
is from reading `Sparkle/Compiler/Elab.lean`, not an observation. The file
compares compiled `Module` VALUES returned by the entry (no reflected data).

Finding I (`docs/parallel/I-singleout-stale.md`; measured on poc by
`Tests/Compiler/SingleOutStaleProbe.lean`: `A insts=1 stmts=3`,
`B insts=0 stmts=2`, `equal=F`): the legacy handler returns a hit of
`sparkleSingleOutInstanceCache` without validation, and a nested entry did
not reset that map. `SingleOutStaleProbe` ASSERTS THE DIFFERENCE and is the
record of the finding: on the candidate it throws ("the two modules are
EQUAL"), which is the expected outcome there. This file is that probe
turned around.

## §0 Is the entry fixed?

The map is seeded with one foreign entry, the depth pre-set to 1, one nested
entry is run (`synthesizeCombinational pTop`), and the map is read again.

    SINGLEOUTFIX FIXED: nested entry ran=<T/F> restores single-out=<T/F> => fixed=<T/F>

PREDICTED: poc `fixed=F` (the seed AND the entry of `pTop` are there), the
candidate `fixed=T` (exactly the seed).

## §1 The probe turned around (a CONSTRUCTED state, as in the probe)

Run A: the full entry on `pTop` from reset refs at depth 0. Run B: the full
entry again with the depth pre-set to 1 and the refs as A left them, the
legacy memo emptied (as in the probe).

    SINGLEOUTFIX A: returned=<T/F> hIrr insts=<n> stmts=<n>
    SINGLEOUTFIX B: returned=<T/F> hIrr insts=<n> stmts=<n>
    SINGLEOUTFIX RESULT: equal=<T/F>

PREDICTED: poc `A 1/3`, `B 0/2`, `equal=F` (the finding); the candidate
`A 1/3`, `B 1/3`, `equal=T`.

## §2 REAL commands only (no pre-set depth, no emptied memo)

* `pOuter` calls the tagged `pMid`, whose body instantiates `hIrr` through
  the legacy handler: the nested module of `pMid` in the design of the real
  entry on `pOuter`, against the module the real entry builds for `pMid`
  alone.

      SINGLEOUTFIX pOuter: returned=<T/F> pMid nested found=<T/F> hIrr insts nested=<n> alone=<n> nested==alone=<T or F or ->

  PREDICTED on BOTH trees: `nested==alone=T`, one instance each (no stale
  entry exists in a real run; the fix changes nothing here).

* `pMach`: a register machine with `hIrr` in its body — the one hole the
  reading left ("the legacy arm after a declined machine arm builds a
  second time under the same module name"). The machine gate's verdict and,
  the real entry against the clean legacy arm, the `hIrr` instance counts.

      SINGLEOUTFIX pMach: machine shape=<T/F> real=<returned T/F> hIrr insts real=<n> cold=<n> => stale hit on a real command=<T or F or ->

  PREDICTED on both trees: `machine shape=F` (the transition is not in the
  unified fragment: `unifiedGateRoot` refuses a call of an unknown head), so
  no harness runs and `stale hit=F`. A `T` here would be a finding on a REAL
  command, on either tree: the command throws in that case WHATEVER §0 says.

## What is ASSERTED

Always: no stale hit on the real command `pMach`. When `fixed=T`: run A
returns with at least one `hIrr` instance, run B returns, the two modules
are EQUAL; `pOuter` returns, the nested `pMid` is found and equals the alone
one. When `fixed=F` the rows are logged and nothing else is asserted. -/
namespace Tests.Compiler.SingleOutNestedFixTest
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tests.Compiler.CallWidthHuntTest (Mod Dsn bs gatesOf resetRefs)
open Tests.Compiler.MachineFallThroughCensusTest (cleanLegacy)

/-- An untagged helper that default-transparency unfolding leaves alone (the
helper of `SingleOutStaleProbe`). -/
@[irreducible]
def hIrr {dom : DomainConfig} (y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  y + (Signal.pure 1#8 : Signal dom (BitVec 8))

def pTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  hIrr x + x

/-- A tagged child whose body instantiates `hIrr` through the legacy handler. -/
@[hardware_module]
def pMid (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  hIrr x + x

def pOuter (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  pMid x - x

/-- A register machine with the helper in its body. -/
def pMach (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let h := hIrr x
    r <~ h + rs
    return rs

def hIrrMod : String := Sparkle.IR.ModuleName.ofDecl ``hIrr
def pMidMod : String := Sparkle.IR.ModuleName.ofDecl ``pMid

def emit (s : String) : MetaM Unit := do
  IO.eprintln s
  (← IO.getStderr).flush
  logInfo m!"{s}"

/-- The instance statements of the helper's module. -/
def hInsts (m : Mod) : Nat :=
  (m.body.filter fun s => match s with
    | .inst mn _ _ => mn == hIrrMod
    | _ => false).length

/-- One run of the full entry on `pTop` at the given pre-set depth; the refs
are NOT reset here. -/
def runOnce (label : String) (depth : Nat) : MetaM (Option Mod) := do
  sparkleSynthDepth.set depth
  let r : Option Mod ←
    try
      let res ← Sparkle.Compiler.Elab.synthesizeCombinational ``pTop
      pure (some res.1)
    catch _ => pure none
  sparkleSynthDepth.set 0
  match r with
  | some m => emit s!"SINGLEOUTFIX {label}: returned=T hIrr insts={hInsts m} stmts={m.body.length}"
  | none => emit s!"SINGLEOUTFIX {label}: returned=F hIrr insts=0 stmts=0"
  return r

def optBs : Option Bool → String
  | some b => bs b
  | none => "-"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let mut failures : Array String := #[]
  -- §0 is the entry fixed?
  emit "SINGLEOUTFIX START §0 (seeded map, depth 1, one nested entry)"
  resetRefs
  sparkleSingleOutInstanceCache.set
    (({} : Std.HashMap String String).insert "seed#single#out" "seed_single_out_wire")
  sparkleSynthDepth.set 1
  let nestedRan : Bool ←
    try
      let _ ← Sparkle.Compiler.Elab.synthesizeCombinational ``pTop
      pure true
    catch _ => pure false
  sparkleSynthDepth.set 0
  let after := (← (sparkleSingleOutInstanceCache.get : IO _)).toList
  let restored : Bool := after == [("seed#single#out", "seed_single_out_wire")]
  let fixed : Bool := nestedRan && restored
  resetRefs
  emit s!"SINGLEOUTFIX FIXED: nested entry ran={bs nestedRan} restores single-out={bs restored} => fixed={bs fixed} (the §1 and pOuter assertions are made only when it is T)"
  -- §1 the probe turned around
  emit "SINGLEOUTFIX START A (depth 0, reset refs)"
  resetRefs
  let a ← runOnce "A" 0
  emit "SINGLEOUTFIX START B (depth 1, refs as A left them, the sub-module memo emptied)"
  sparkleSubModuleCache.set {}
  let b ← runOnce "B" 1
  resetRefs
  sparkleSynthDepth.set 0
  match a, b with
  | some ma, some mb =>
    let eq : Bool := ma == mb
    emit s!"SINGLEOUTFIX RESULT: equal={bs eq}"
    if hInsts ma == 0 then failures := failures.push "run A has no hIrr instance (the legacy single-output path is not exercised)"
    if !eq then failures := failures.push "run A and run B differ"
  | _, _ =>
    emit "SINGLEOUTFIX RESULT: a run did not return"
    failures := failures.push "a run of §1 did not return"
  -- §2 real commands: pOuter
  emit "SINGLEOUTFIX START pOuter (real entry, depth 0)"
  let outer? : Option (Mod × Dsn) ←
    try
      let res ← Sparkle.Compiler.Elab.synthesizeCombinational ``pOuter
      pure (some res)
    catch _ => pure none
  sparkleSynthDepth.set 0
  emit "SINGLEOUTFIX START pMid alone (real entry, depth 0)"
  let alone? : Option Mod ←
    try
      let res ← Sparkle.Compiler.Elab.synthesizeCombinational ``pMid
      pure (some res.1)
    catch _ => pure none
  sparkleSynthDepth.set 0
  resetRefs
  let nested? : Option Mod := outer?.bind fun r => r.2.modules.find? fun m => m.name == pMidMod
  let same? : Option Bool := match nested?, alone? with
    | some x, some y => some (x == y)
    | _, _ => none
  emit s!"SINGLEOUTFIX pOuter: returned={bs outer?.isSome} pMid nested found={bs nested?.isSome} hIrr insts nested={(nested?.map hInsts).getD 0} alone={(alone?.map hInsts).getD 0} nested==alone={optBs same?}"
  if same? != some true then failures := failures.push "pOuter: the nested pMid is missing or differs from the alone one"
  -- §2 real commands: pMach
  emit "SINGLEOUTFIX START pMach (gates, real entry at depth 0, clean legacy arm)"
  let shape : Bool ←
    try
      let g ← gatesOf ``pMach
      pure g.shape.isSome
    catch _ => pure false
  resetRefs
  sparkleSynthDepth.set 0
  let real? : Option Mod ←
    try
      let res ← synthesizeCombinationalCore ``pMach [] false
      pure (some res.1)
    catch _ => pure none
  sparkleSynthDepth.set 0
  resetRefs
  let cold? : Option Mod ←
    try
      let g ← gatesOf ``pMach
      let res ← cleanLegacy ``pMach g.ec
      pure (some res.1)
    catch _ => pure none
  sparkleSynthDepth.set 0
  resetRefs
  let stale? : Option Bool := match real?, cold? with
    | some r, some c => some (hInsts r != hInsts c)
    | _, _ => none
  emit s!"SINGLEOUTFIX pMach: machine shape={bs shape} real={bs real?.isSome} hIrr insts real={(real?.map hInsts).getD 0} cold={(cold?.map hInsts).getD 0} => stale hit on a real command={optBs stale?}"
  emit s!"SINGLEOUTFIX: fixed={bs fixed}; rows not as expected {failures.toList}"
  if stale? == some true then
    throwError "SINGLEOUTFIX: a REAL command (pMach) took a stale single-output hit — a finding on real commands, whatever the entry"
  if fixed then
    if !failures.isEmpty then
      throwError "SINGLEOUTFIX: the nested entry resets and restores the single-output map, but these rows are not as expected: {failures.toList}"

end Tests.Compiler.SingleOutNestedFixTest
