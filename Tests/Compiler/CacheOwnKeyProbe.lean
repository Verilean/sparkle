import Lean.Elab.Command
import Tests.Compiler.CallWidthHuntTest

/-! # The child cache: does a run of the entry insert its OWN key? (H3 probe)

WRITTEN, NOT BUILT (par/a-33). Target-only; not in `Tests.AllTests`.
Every "PREDICTED" is a prediction from reading `Sparkle/Compiler/Elab.lean`
at b7dc0ec4 (`docs/parallel/A-cache-coherence-2.md` §1.3), not an observation.

## The claim that is probed

`Tools.ShippingCacheCoherentRun.CoreFresh` contains: "a returning run of the
entry of `c` from a cache that does not hold `c` ends in a cache that does
not hold `c`" (H3: the insert `sparkleChildCache.modify (·.insert n r)` of
`synthesizeChild` is never an OVERWRITE). The cache gets `c` during the run
of `c`'s entry only if `c`'s entry is re-entered and that inner run RETURNS:
`c` must reach itself. A kernel-checked definition does not; an `unsafe`
one can (`unsafe def` is a `defnInfo` whose value mentions itself).

What stops such a cycle is the depth limit (`sparkleSynthDepthLimit`, the
entry throws when the depth reads 1024). PREDICTED: every run on the cycle
then throws — the one `catch` that goes on translating
(`Rec.tryInlineUnfold`) retries the SAME expression — so no run on a cycle
returns and no entry is ever overwritten.

## What is run

Each top is run by the full entry `synthesizeCombinational` from reset refs
with the synthesis depth PRE-SET to `startDepth` (so a cycle meets the limit
after a few levels instead of 1024, and the entry does not clear the cache).
Then the cache is read.

* `ctlTop` (control, no cycle): `ctlKid x + x`.
* `cyc1`: `@[hardware_module] unsafe def`, calls itself.
* `cyc2` / `cycHelp`: a tagged `unsafe def` calling itself through an
  untagged helper (the inline attempt, its `catch`, the retry as a module).
* `cyc3`: a tagged `unsafe def` that mentions itself only in an argument its
  untagged callee drops.

## The lines (each also on standard error, flushed, BEFORE the operation)

    CACHEOWN START <label> <decl> depth=<d>
    CACHEOWN <label>: returned=<T/F> ownKey=<T/F> depthAfter=<d> keys=[<names>] <message>
    CACHEOWN RESULT: <n> violations

## What is ASSERTED (the command throws otherwise)

* for every top: NOT (`returned=T` and `ownKey=T`) — the claim above;
* for every top: `depthAfter` = the start depth (the entry's `finally`);
* `ctlTop`: `returned=T`, and the cache holds `ctlKid` (the harness works at
  a pre-set depth, so a `returned=F` below is not an artefact of it).

PREDICTED: `ctlTop` `returned=T ownKey=F keys=[…ctlKid]`; `cyc1`, `cyc2`
`returned=F ownKey=F`; `cyc3` EITHER `returned=T ownKey=F` (the inline
unfolding of `dropArg` drops the self-call before anything translates it)
OR `returned=F`. A line `returned=T ownKey=T` is a COUNTEREXAMPLE to H3:
the entry it names was inserted during its own run, and the insert that
follows overwrites it.

NOT established: all of the above. Unknown before the first run: whether
`@[hardware_module] unsafe def` elaborates; whether the entry accepts an
`unsafe` definition at all (then `returned=F` says nothing about cycles —
read the message); the run time of `cyc2` (each level tries the helper
inline and then as a module: up to 2^(1024 - startDepth) attempts). -/
namespace Tests.Compiler.CacheOwnKeyProbe
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tests.Compiler.CallWidthHuntTest (bs resetRefs)

/-! ### Control -/

@[hardware_module]
def ctlKid {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal dom (BitVec 8))

@[hardware_module]
def ctlTop {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  ctlKid x + x

/-! ### Cycles (`unsafe`: the kernel accepts no other) -/

@[hardware_module]
unsafe def cyc1 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  cyc1 x + (Signal.pure 1#8 : Signal dom (BitVec 8))

mutual
@[hardware_module]
unsafe def cyc2 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  cycHelp x + x

unsafe def cycHelp {dom : DomainConfig} (y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  cyc2 y + (Signal.pure 1#8 : Signal dom (BitVec 8))
end

def dropArg {dom : DomainConfig} (_z : Signal dom (BitVec 8)) (y : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) :=
  y + (Signal.pure 1#8 : Signal dom (BitVec 8))

@[hardware_module]
unsafe def cyc3 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  dropArg (cyc3 x) x

/-- Six levels below the limit: a cycle meets the limit quickly. -/
def startDepth : Nat := sparkleSynthDepthLimit - 6

/-- A line on standard error (flushed: it survives a crash of what follows)
and in the message log. -/
def emit (s : String) : MetaM Unit := do
  IO.eprintln s
  (← IO.getStderr).flush
  logInfo m!"{s}"

structure Outcome where
  returned : Bool
  ownKey : Bool
  depthAfter : Nat
  keys : List Name
  msg : String

/-- One run of the full entry on `n` from reset refs, the depth pre-set. -/
def runAt (label : String) (n : Name) : MetaM Outcome := do
  emit s!"CACHEOWN START {label} {n} depth={startDepth}"
  resetRefs
  sparkleSynthDepth.set startDepth
  let r : Bool × String ←
    try
      let _ ← Sparkle.Compiler.Elab.synthesizeCombinational n
      pure (true, "")
    catch e =>
      let msg ← e.toMessageData.toString
      pure (false, msg)
  let keys : List Name := (← (sparkleChildCache.get : IO _)).toList.map (·.1)
  let depthAfter : Nat ← (sparkleSynthDepth.get : IO Nat)
  resetRefs
  sparkleSynthDepth.set 0
  let o : Outcome :=
    { returned := r.1, ownKey := keys.contains n, depthAfter := depthAfter, keys := keys,
      msg := r.2 }
  emit s!"CACHEOWN {label}: returned={bs o.returned} ownKey={bs o.ownKey} depthAfter={o.depthAfter} keys={o.keys} {o.msg}"
  return o

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let tops : List (String × Name) :=
    [("ctl", ``ctlTop), ("cyc1", ``cyc1), ("cyc2", ``cyc2), ("cyc3", ``cyc3)]
  let mut bad : List String := []
  for (label, n) in tops do
    let o ← runAt label n
    if o.returned && o.ownKey then
      bad := bad ++ [s!"{label}: the entry returned and the cache holds its own key (H3 fails)"]
    if o.depthAfter != startDepth then
      bad := bad ++ [s!"{label}: depth after the run is {o.depthAfter}, not {startDepth}"]
    if label == "ctl" then
      if !o.returned then
        bad := bad ++ ["ctl: the control did not return (the harness does not work)"]
      if !o.keys.contains ``ctlKid then
        bad := bad ++ ["ctl: the cache does not hold ctlKid"]
  resetRefs
  sparkleSynthDepth.set 0
  emit s!"CACHEOWN RESULT: {bad.length} violations"
  if !bad.isEmpty then
    throwError "CACHEOWN: {bad}"

end Tests.Compiler.CacheOwnKeyProbe
