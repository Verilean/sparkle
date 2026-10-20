import Lean.Elab.Command
import Tests.Compiler.CallWidthHuntTest

/-! # The child cache: does a run of the entry insert its OWN key? (H3 probe)

Target-only; not in `Tests.AllTests`. First version (par/a-33) BUILT and run
by the integrator at bfa5f5fe: `ctl` T/F, `cyc1` F/F (depth limit), `cyc3`
T/F with `keys=[]`, 0 violations; `cyc2` ended with `Cannot synthesise
cycHelp: not inlinable and not a hardware module`. THIS revision (par/a-34)
is WRITTEN, NOT BUILT; every "PREDICTED" is a prediction from reading
`Sparkle/Compiler/Elab.lean`, not an observation.

## The claim that is probed

"A returning run of the entry of `c` from a cache that does not hold `c`
ends in a cache that does not hold `c`" (H3: the insert of `synthesizeChild`
is never an overwrite). It can fail only if `c` reaches itself and the inner
run returns; an `unsafe def` can reach itself. What stops the cycle is the
depth limit; the one `catch` that goes on translating is
`Rec.tryInlineUnfold` (inline attempt → `catch` → retry under reducible
transparency → the helper as a MODULE, `Rec.handleDefinitionUnfold`).

## About `cyc2`'s message, and how this revision decides it

`Cannot synthesise <h>: not inlinable and not a hardware module` is thrown
at ONE place: after `tryInlineUnfold` returned no wire AND the module
synthesis of `<h>` threw. `tryInlineUnfold` returns no wire in two ways:
the unfolding was a no-op (no attempt, no `catch`; the message then has NO
`Inline expansion failed with:` part), or the inline attempt threw and was
CAUGHT (the message then carries that part). So the message alone does not
say the `catch` was not reached. The line now prints `detail=<T/F>` (the
part is present), and two more cycles are added whose helper's module
synthesis SUCCEEDS, so that the retry leaves a trace in the cache:

* `cyc4`: `help4 (cyc4 x) x`, `help4` an untagged non-recursive `unsafe def`
  (the front end does not unfold `unsafe` definitions);
* `cyc5`: `help5.{0} PUnit.unit (cyc5 x) x`, `help5` a safe untagged
  definition with a universe parameter (the front end does not unfold a
  definition with level parameters; `unfoldDefinition?` does).

With the controls `ctl4` / `ctl5` (the same helper over `ctlKid`, no cycle):
if the control returns and its cache does NOT hold the helper (the helper
was inlined), and the cycle's cache DOES hold the helper, then in the cycle
the inline attempt was made, failed, was caught, and the helper was
synthesised as a module — the catch-and-retry path, on a cycle.

## What is run

Each top is run by the full entry from reset refs with the synthesis depth
PRE-SET to `startDepth` (a cycle meets the limit after six levels; each
level may try the helper inline and then as a module, so the number of
attempts doubles per level).

## The lines (each also on standard error, flushed, BEFORE the operation)

    CACHEOWN START <label> <decl> depth=<d>
    CACHEOWN <label>: returned=<T/F> ownKey=<T/F> detail=<T/F> depthAfter=<d> keys=[<names>] <message>
    CACHEOWN RETRY <label>: control returned=<T/F> helper in control=<T/F> helper in cycle=<T/F> exercised=<T/F>
    CACHEOWN RESULT: <n> violations

## What is ASSERTED (the command throws otherwise)

* every top: NOT (`returned=T` and `ownKey=T`) — H3;
* every top: `depthAfter` = the start depth;
* `ctl`: `returned=T` and the cache holds `ctlKid`;
* the catch-and-retry path was exercised on a cycle by AT LEAST ONE of
  `cyc2`, `cyc4`, `cyc5` (`exercised=T`: the cache evidence above, or
  `returned=F` with `detail=T` — the final message carries the caught
  inline failure). If none, the probe does not test what it is for, and says so
  by throwing.

PREDICTED: `ctl`, `ctl4`, `ctl5`: `returned=T ownKey=F`, keys `[ctlKid]`;
`cyc1`: `returned=F` (depth limit); `cyc2`: `returned=F detail=T`;
`cyc3`: `returned=T ownKey=F keys=[]`; `cyc4`, `cyc5`: `returned=F ownKey=F`,
keys holding the helper, `exercised=T`; `CACHEOWN RESULT: 0 violations`.
LEAST CERTAIN: `ctl4` / `cyc4` (whether `unfoldDefinition?` unfolds an
`unsafe` helper — if not, `helper in control=T` and `cyc4` is not evidence;
that would also explain a `cyc2` line with `detail=F`), and whether the
entry accepts `help5.{0} PUnit.unit …`. A line `returned=T ownKey=T` is a
COUNTEREXAMPLE to H3. -/
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

/-! ### Cycles through a helper whose own module synthesis succeeds -/

/-- Untagged, non-recursive, `unsafe`: not unfolded by the front end. -/
unsafe def help4 {dom : DomainConfig} (z y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  z + y

@[hardware_module]
unsafe def ctl4 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  help4 (ctlKid x) x

@[hardware_module]
unsafe def cyc4 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  help4 (cyc4 x) x

/-- Untagged, safe, with a universe parameter: not unfolded by the front end. -/
def help5.{u} {dom : DomainConfig} (_u : PUnit.{u + 1}) (z y : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) :=
  z + y

@[hardware_module]
def ctl5 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  help5.{0} PUnit.unit (ctlKid x) x

@[hardware_module]
unsafe def cyc5 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  help5.{0} PUnit.unit (cyc5 x) x

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
  detail : Bool
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
    { returned := r.1, ownKey := keys.contains n,
      detail := decide ((r.2.splitOn "Inline expansion failed with").length > 1),
      depthAfter := depthAfter, keys := keys, msg := r.2 }
  emit s!"CACHEOWN {label}: returned={bs o.returned} ownKey={bs o.ownKey} detail={bs o.detail} depthAfter={o.depthAfter} keys={o.keys} {o.msg}"
  return o

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let mut bad : List String := []
  let check (label : String) (o : Outcome) : List String :=
    (if o.returned && o.ownKey then
      [s!"{label}: the entry returned and the cache holds its own key (H3 fails)"] else []) ++
    (if o.depthAfter != startDepth then
      [s!"{label}: depth after the run is {o.depthAfter}, not {startDepth}"] else [])
  -- the control
  let oc ← runAt "ctl" ``ctlTop
  bad := bad ++ check "ctl" oc
  if !oc.returned then
    bad := bad ++ ["ctl: the control did not return (the harness does not work)"]
  if !oc.keys.contains ``ctlKid then
    bad := bad ++ ["ctl: the cache does not hold ctlKid"]
  -- the cycles of the first version
  let o1 ← runAt "cyc1" ``cyc1
  bad := bad ++ check "cyc1" o1
  let o2 ← runAt "cyc2" ``cyc2
  bad := bad ++ check "cyc2" o2
  let o3 ← runAt "cyc3" ``cyc3
  bad := bad ++ check "cyc3" o3
  -- the cycles whose helper can be synthesised as a module
  let c4 ← runAt "ctl4" ``ctl4
  bad := bad ++ check "ctl4" c4
  let o4 ← runAt "cyc4" ``cyc4
  bad := bad ++ check "cyc4" o4
  let ex4 : Bool := (c4.returned && !c4.keys.contains ``help4 && o4.keys.contains ``help4) ||
    (!o4.returned && o4.detail)
  emit s!"CACHEOWN RETRY cyc4: control returned={bs c4.returned} helper in control={bs (c4.keys.contains ``help4)} helper in cycle={bs (o4.keys.contains ``help4)} exercised={bs ex4}"
  let c5 ← runAt "ctl5" ``ctl5
  bad := bad ++ check "ctl5" c5
  let o5 ← runAt "cyc5" ``cyc5
  bad := bad ++ check "cyc5" o5
  let ex5 : Bool := (c5.returned && !c5.keys.contains ``help5 && o5.keys.contains ``help5) ||
    (!o5.returned && o5.detail)
  emit s!"CACHEOWN RETRY cyc5: control returned={bs c5.returned} helper in control={bs (c5.keys.contains ``help5)} helper in cycle={bs (o5.keys.contains ``help5)} exercised={bs ex5}"
  let ex2 : Bool := !o2.returned && o2.detail
  emit s!"CACHEOWN RETRY cyc2: returned={bs o2.returned} detail={bs o2.detail} exercised={bs ex2}"
  if !(ex4 || ex5 || ex2) then
    bad := bad ++ ["no cycle exercised the inline catch-and-retry path (cyc2, cyc4, cyc5)"]
  resetRefs
  sparkleSynthDepth.set 0
  emit s!"CACHEOWN RESULT: {bad.length} violations"
  if !bad.isEmpty then
    throwError "CACHEOWN: {bad}"

end Tests.Compiler.CacheOwnKeyProbe
