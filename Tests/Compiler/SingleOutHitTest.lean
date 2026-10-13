import Tests.Compiler.NestedLetCacheTest

/-! # The one-output instance dedupe hit of the legacy handler, and the zeta marks

Uses NO declaration of a candidate: it is meant to build on poc (`85ebb9fd`)
and on the isolated `fix/nested-let-cache-build`. LOGS ONLY — nothing here
asserts, nothing throws. Not in `Tests.AllTests`. WRITTEN, NOT BUILT: every
"expected" below is a PREDICTION from reading `Sparkle/Compiler/Elab.lean`
at `85ebb9fd` (`docs/parallel/B-cache-keys.md` §2, §3).

## What is read from the code

`sparkleSingleOutInstanceCache : String ↦ String`, key
`<module being built>#<child module>#<port>=<connection>;…`, value the
instance's output wire. Two readers:

* the certified arm (`translateInstanceUncachedWith`, every call whose head
  is tagged `@[hardware_module]` and whose child has one output): a hit is
  honoured only if the builder's own `translateRecord` says the wire was
  made for this expression (`instHitValid`);
* the legacy handler (`Rec.handleDefinitionUnfold`, the `[singleOut]`
  branch): a hit is returned as it is. By reading, a one-output child
  reaches this branch only when it is NOT tagged and the inline attempt did
  not produce a wire — e.g. an `@[irreducible]` helper, which
  `unfoldDefinition?` does not unfold at default transparency.

## §1 SEEDED rows (an injected state, NOT a finding)

For `sIrr` (calls the irreducible `hIrr`) and `sTag` (calls the tagged
`hTag`, the same function): the real entry at depth 0; then the keys this
run left for the parent are mapped to the wire name `seed_single_out_wire`
and the entry is run again at depth 1 (a nested entry does not clear this
ref).

    SINGLEOUT <decl> real: route=<…> stmts=<n> insts=[…] undeclared=[…] own single-out entries=[<key> -> <wire>, …] zeta marks left=<n>
    SINGLEOUT <decl> real STMT <i>: <statement>
    SINGLEOUT <decl> seeded: stmts=<n> insts=[…] undeclared=[…] readsSeed=<T/F> => unvalidated hit honoured=<T/F>
    SINGLEOUT <decl> seeded STMT <i>: <statement>
    SINGLEOUT <decl> seeded: NOT APPLICABLE (…)

PREDICTED: `sIrr … honoured=T` (no instance, the module reads the seed
name), `sTag … honoured=F` (the instance is emitted again). If `sIrr real`
shows no instance of `hIrr` the helper was inlined after all and the reading
"an irreducible helper reaches the legacy branch" is wrong: the seeded row
then says NOT APPLICABLE.

This shows which reader validates. It does NOT show that a real entry run
can hold such an entry: the key carries the module name, and by reading the
only second builder of one module name inside one top-level run is the
legacy arm after a declined machine arm.

## §2 The constructed parent for that hole

`sMach`: the shape of `NestedLetCacheTest.fTop` (a register machine whose
machine arm declines: it calls the sequential one-output `fMid`) with the
`let` replaced by a call of `hIrr`.

    SINGLEOUT sMach real: route=<…> … hIrr instances=<n> selfAssign=[…] undeclared=[…] undriven=[…]
    SINGLEOUT sMach cold: …
    SINGLEOUT sMach real==cold <T/F/err>
    SINGLEOUT sMach DETECT: machine shape=<T/F> hIrr instances real=<n> cold=<n> undeclared real=[…] => stale single-out hit=<T/F>

`cold`: `cleanLegacy` (everything reset, the legacy arm alone). NOT
established which way it goes: if `machine shape=F` the machine arm never
runs a harness on this body and the hole is closed for this form. CONFOUNDER
on poc: finding F (the parent's `let rs` against `fMid`'s) can put
self-assignments or undeclared names into BOTH rows; the line of interest is
the `hIrr` instance count of `real` against `cold`.

## §3 Zeta marks

`zeta marks left`: the size of `sparkleFvarZetaVisited` after each run (the
ref is cleared at no entry). Expected 0 after every run that returned. -/
namespace Tests.Compiler.SingleOutHitTest
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tests.Compiler.CallWidthHuntTest (Mod Dsn bs gatesOf resetRefs)
open Tests.Compiler.MachineFallThroughCensusTest (cleanLegacy allReads undeclared undriven)
open Tests.Compiler.NestedLetCacheTest (stmtStr instNames selfAssigned routeStr fMid)

/-- An untagged helper that default-transparency unfolding leaves alone. -/
@[irreducible]
def hIrr (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  x + y

/-- The same function, tagged. -/
@[hardware_module]
def hTag (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  x + y

def sIrr (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  hIrr x y - x

def sTag (x y : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  hTag x y - x

/-- `NestedLetCacheTest.fTop` with `hIrr x y` in the place of `x + y`. -/
def sMach (en : Signal defaultDomain Bool) (x y : Signal defaultDomain (BitVec 5)) :
    Signal defaultDomain (BitVec 5) :=
  circuit do
    let r ← Signal.reg 0#5
    let rs := (r : Signal defaultDomain (BitVec 5))
    let h := hIrr x y
    let m := fMid en x y
    r <~ Signal.mux en (h + m) rs
    return rs

def hIrrName : Name := `Tests.Compiler.SingleOutHitTest.hIrr
def sIrrName : Name := `Tests.Compiler.SingleOutHitTest.sIrr
def sTagName : Name := `Tests.Compiler.SingleOutHitTest.sTag
def sMachName : Name := `Tests.Compiler.SingleOutHitTest.sMach

def seedWire : String := "seed_single_out_wire"

def instOf (m : Mod) (child : String) : Nat :=
  ((instNames m).filter fun x => x == child).length

def zetaLeft : MetaM Nat := do
  let z ← (sparkleFvarZetaVisited.get : IO _)
  pure z.size

/-- The real entry from reset refs at depth 0, and the one-output instance
cache as the run left it. -/
def realRun (n : Name) : MetaM (Option (Mod × Dsn) × List (String × String)) := do
  resetRefs
  sparkleSynthDepth.set 0
  let r : Option (Mod × Dsn) ←
    try
      let res ← synthesizeCombinationalCore n [] false
      pure (some res)
    catch _ => pure none
  sparkleSynthDepth.set 0
  let c := (← (sparkleSingleOutInstanceCache.get : IO _)).toList
  pure (r, c)

/-- The entry as a NESTED entry (depth 1: the one-output instance cache is
not cleared), the given keys mapped to the seed wire. -/
def seededRun (n : Name) (keys : List String) : MetaM (Option (Mod × Dsn)) := do
  resetRefs
  sparkleSingleOutInstanceCache.set
    (keys.foldl (fun (m : Std.HashMap String String) k => m.insert k seedWire) {})
  sparkleSynthDepth.set 1
  let r : Option (Mod × Dsn) ←
    try
      let res ← synthesizeCombinationalCore n [] false
      pure (some res)
    catch _ => pure none
  sparkleSynthDepth.set 0
  resetRefs
  pure r

def stmtRows (tag : String) (m : Mod) : MetaM Unit := do
  let mut i : Nat := 0
  for s in m.body do
    logInfo m!"SINGLEOUT {tag} STMT {i}: {stmtStr s}"
    i := i + 1

/-- §1: the real run, then the seeded one. Returns whether the seeded hit
was honoured (`none`: not applicable or a run threw). -/
def seedRow (n : Name) : MetaM (Option Bool) := do
  let route ← routeStr n
  let (r?, cache) ← realRun n
  let zl ← zetaLeft
  let pre : String := toString n ++ "#"
  let own : List (String × String) := cache.filter fun p => p.1.startsWith pre
  let ownS : List String := own.map fun p => p.1 ++ " -> " ++ p.2
  match r? with
  | none =>
    logInfo m!"SINGLEOUT {n} real: route={route} the run threw; zeta marks left={zl}"
    resetRefs
    pure none
  | some r =>
    let m := r.1
    logInfo m!"SINGLEOUT {n} real: route={route} stmts={m.body.length} insts={instNames m} undeclared={undeclared m} own single-out entries={ownS} zeta marks left={zl}"
    stmtRows (toString n ++ " real") m
    if own.isEmpty then
      logInfo m!"SINGLEOUT {n} seeded: NOT APPLICABLE (the real run left no one-output instance entry of this parent)"
      resetRefs
      pure none
    else
      let s? ← seededRun n (own.map fun p => p.1)
      match s? with
      | none =>
        logInfo m!"SINGLEOUT {n} seeded: the run threw"
        pure none
      | some s =>
        let ms := s.1
        let reads : Bool := (ms.body.flatMap allReads).contains seedWire
        logInfo m!"SINGLEOUT {n} seeded: stmts={ms.body.length} insts={instNames ms} undeclared={undeclared ms} readsSeed={bs reads} => unvalidated hit honoured={bs reads}"
        stmtRows (toString n ++ " seeded") ms
        pure (some reads)

def optStr : Option Bool → String
  | some b => bs b
  | none => "-"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- §1
  let a ← seedRow sIrrName
  let b ← seedRow sTagName
  logInfo m!"SINGLEOUT SEEDED: legacy handler (sIrr) honoured={optStr a}; certified arm (sTag) honoured={optStr b} (an injected state, not a finding)"
  -- §2
  let child : String := Sparkle.IR.ModuleName.ofDecl hIrrName
  let shape : Bool ←
    try
      let g ← gatesOf sMachName
      pure g.shape.isSome
    catch _ => pure false
  let route ← routeStr sMachName
  let (real?, _) ← realRun sMachName
  let zl ← zetaLeft
  resetRefs
  let cold? : Option (Mod × Dsn) ←
    try
      let g ← gatesOf sMachName
      let res ← cleanLegacy sMachName g.ec
      pure (some res)
    catch _ => pure none
  sparkleSynthDepth.set 0
  resetRefs
  match real? with
  | some r =>
    let m := r.1
    logInfo m!"SINGLEOUT sMach real: route={route} stmts={m.body.length} insts={instNames m} hIrr instances={instOf m child} selfAssign={selfAssigned m} undeclared={undeclared m} undriven={undriven m} zeta marks left={zl}"
    stmtRows "sMach real" m
  | none => logInfo m!"SINGLEOUT sMach real: route={route} the run threw; zeta marks left={zl}"
  match cold? with
  | some r =>
    let m := r.1
    logInfo m!"SINGLEOUT sMach cold: stmts={m.body.length} insts={instNames m} hIrr instances={instOf m child} selfAssign={selfAssigned m} undeclared={undeclared m} undriven={undriven m}"
    stmtRows "sMach cold" m
  | none => logInfo m!"SINGLEOUT sMach cold: the run threw"
  match real?, cold? with
  | some r, some c =>
    let same : Bool := r.1 == c.1
    let nr : Nat := instOf r.1 child
    let nc : Nat := instOf c.1 child
    let stale : Bool := nr != nc
    logInfo m!"SINGLEOUT sMach real==cold {bs same}"
    logInfo m!"SINGLEOUT sMach DETECT: machine shape={bs shape} hIrr instances real={nr} cold={nc} undeclared real={undeclared r.1} => stale single-out hit={bs stale} (logged only)"
  | _, _ =>
    logInfo m!"SINGLEOUT sMach real==cold err"
    logInfo m!"SINGLEOUT sMach DETECT: machine shape={bs shape}; a run threw, nothing to compare"

end Tests.Compiler.SingleOutHitTest
