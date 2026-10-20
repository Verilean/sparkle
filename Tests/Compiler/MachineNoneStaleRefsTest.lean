import Tests.Compiler.MachineFallThroughCensusTest

/-! # The refs a declined machine arm leaves to the legacy arm (finding E)

Compiled evidence, LOGS ONLY — nothing here throws and nothing is a theorem.

For a declaration whose machine arm RUNS and returns `none`
(`synthesizeMachineCertified`: the harness, `closeLets`, the calls'
closing with its nested child entries), the real entry then runs the legacy
arm without touching the wire-naming refs. This file looks at that moment:

1. reset the refs, depth 1, run the machine arm (`CallWidthHuntTest.machineArm`
   does both) — it returns `none`;
2. READ the refs as the legacy arm would find them: the sizes of
   `sparkleWireWidthCache`, `sparkleLetWireCache`, `sparkleLoopWireCache`,
   `sparkleWireCanon`, `sparkleFvarValueMap`, `sparkleSingleOutInstanceCache`,
   `sparkleSubInstanceOutputs`, and the entries of the first two;
3. WITHOUT a reset, run the legacy arm on the same entry constant
   (`dirty`); then from reset refs (`clean`);
4. compare: `dirty == clean`; the stale width entries whose NAME is
   declared in the clean module with ANOTHER width (`clash` — a
   `getWireWidth` of that name before the legacy arm re-declares it would
   read the stale width); the stale width entries whose name the clean
   module does not declare at all (`orphan`); the stale `let`-wire entries
   whose wire the clean module does not declare (`letOrphan` — a hit of
   that key would name a wire that does not exist).

    STALEREFS <name>: arm=<none|some|threw> width=<n> let=<n> loop=<n> canon=<n> fvar=<n> single=<n> sub=<n>
      clash=<n> […] orphan=<n> letOrphan=<n> dirty==clean=<T/F/err> real==clean=<T/F/err>

Declarations: `pCount` (the one fall-through of the census) and three more
constructed ones whose parent has wires of other widths than its
transition's. A `dirty==clean=F` row is a declaration on which the stale
refs change the output; `T` with `clash` / `letOrphan` > 0 says the hazard
is present and was not read on this declaration.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.MachineNoneStaleRefsTest
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tests.Compiler.CallWidthHuntTest (Mod Dsn bs gatesOf machineArm resetRefs kCount tyW)

/-- A wide parent of the one-output sequential child `kCount`. -/
def eWide (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let k := kCount en
    let t := rs + x
    let u := t ^^^ x
    r <~ Signal.mux (k === (Signal.pure 3#5 : Signal defaultDomain (BitVec 5))) u t
    return rs

/-- Two calls of the one-output sequential child, a Bool and a narrow `let`. -/
def eTwo (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 5)) :
    Signal defaultDomain (BitVec 5) :=
  circuit do
    let r ← Signal.reg 0#5
    let rs := (r : Signal defaultDomain (BitVec 5))
    let k := kCount en
    let h := k === x
    let k2 := kCount h
    r <~ Signal.mux h (rs + k2) (rs ^^^ k)
    return rs

/-- A `let` over two INPUTS (the same port names in the harness run and in
the legacy run), used after the call. -/
def eIn (en : Signal defaultDomain Bool) (x y : Signal defaultDomain (BitVec 5)) :
    Signal defaultDomain (BitVec 5) :=
  circuit do
    let r ← Signal.reg 0#5
    let rs := (r : Signal defaultDomain (BitVec 5))
    let t := x + y
    let k := kCount en
    r <~ Signal.mux en (t + k) rs
    return t

def subjects : List Name := [
  `Tests.Compiler.CallWidthHuntTest.pCount,
  `Tests.Compiler.MachineNoneStaleRefsTest.eWide,
  `Tests.Compiler.MachineNoneStaleRefsTest.eTwo,
  `Tests.Compiler.MachineNoneStaleRefsTest.eIn]

/-- The declared width of a name in a module (wires, inputs, outputs). -/
def declW (m : Mod) (x : String) : Option Nat :=
  ((m.wires ++ m.inputs ++ m.outputs).find? fun p => p.name == x).map fun p => tyW p.ty

/-- The legacy arm on the entry constant with the refs AS THEY ARE, depth 1. -/
def legacyAsIs (n : Name) (ec : ConstantInfo) : MetaM (Mod × Dsn) := do
  let tenv ← Lean.getEnv
  let env ← getEnv
  sparkleSynthDepth.set 1
  try
    synthesizeFromConst (fun e hint top named => translateExprToWire tenv e hint top named)
      (fun _ => pure ()) n [] false false ec (instancePredicate env)
  finally
    sparkleSynthDepth.set 0

def look (n : Name) : MetaM String := do
  let g ← gatesOf n
  let some shape := g.shape | return "no machine shape"
  if g.gate || g.mixed then return "a gate accepts the entry constant"
  let (real, _) ← synthesizeCombinationalCore n [] false
  -- 1. the machine arm, from reset refs
  let arm? : Option (Option (Mod × Dsn)) ←
    try
      let r ← machineArm n shape
      pure (some r)
    catch _ => pure none
  let armStr := match arm? with
    | none => "threw"
    | some none => "none"
    | some (some _) => "some"
  -- 2. the refs as the legacy arm would find them
  let width := (← sparkleWireWidthCache.get).toList
  let letW := (← sparkleLetWireCache.get).toList
  let loopN := (← sparkleLoopWireCache.get).size
  let canonN := (← sparkleWireCanon.get).size
  let fvarN := (← sparkleFvarValueMap.get).size
  let singleN := (← sparkleSingleOutInstanceCache.get).size
  let subN := (← sparkleSubInstanceOutputs.get).size
  -- 3. the legacy arm on these refs, then from reset refs
  let dirty? : Option Mod ←
    try
      let r ← legacyAsIs n g.ec
      pure (some r.1)
    catch _ => pure none
  let clean? : Option Mod ←
    try
      let r ← Tests.Compiler.MachineFallThroughCensusTest.cleanLegacy n g.ec
      pure (some r.1)
    catch _ => pure none
  -- 4. the comparison
  let clash : List String := match clean? with
    | some c => width.filterMap fun (x, w) =>
        (declW c x).bind fun w' => if w' != w then some s!"{x}:{w}/{w'}" else none
    | none => []
  let orphan : Nat := match clean? with
    | some c => (width.filter fun (x, _) => (declW c x).isNone).length
    | none => 0
  let letOrphan : Nat := match clean? with
    | some c => (letW.filter fun (_, x) => (declW c x).isNone).length
    | none => 0
  let eqS (a b : Option Mod) : String := match a, b with
    | some x, some y => bs (x == y)
    | _, _ => "err"
  return s!"arm={armStr} width={width.length} let={letW.length} loop={loopN} canon={canonN} " ++
    s!"fvar={fvarN} single={singleN} sub={subN} clash={clash.length} {clash.take 8} " ++
    s!"orphan={orphan} letOrphan={letOrphan} dirty==clean={eqS dirty? clean?} " ++
    s!"real==clean={eqS (some real) clean?}"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  for n in subjects do
    if !env.contains n then
      logInfo m!"STALEREFS {n}: ABSENT"
    else
      try
        let line ← look n
        logInfo m!"STALEREFS {n}: {line}"
      catch e =>
        logInfo m!"STALEREFS {n}: FAILED: {e.toMessageData}"
      -- leave the refs as a fresh top-level entry expects them
      resetRefs

end Tests.Compiler.MachineNoneStaleRefsTest
