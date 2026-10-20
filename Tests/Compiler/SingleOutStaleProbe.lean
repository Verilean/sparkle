import Lean.Elab.Command
import Tests.Compiler.CallWidthHuntTest

/-! # Two compiles of ONE declaration, two modules: the legacy single-output instance cache at a nested entry (probe)

WRITTEN, NOT BUILT (par/a-39). Target-only; not in `Tests.AllTests`. Every
"PREDICTED" is from reading `Sparkle/Compiler/Elab.lean` at 11a2ee8f, not an
observation. The probe compares compiled `Module` VALUES returned by the
entry (not reflected data).

## The claim that is probed

"Two real compiles of one declaration return the same module" (`DetN`,
`Tools/ShippingDetReduce.lean`) is FALSE in general for an invariant world
of positive depth, for a declaration on the LEGACY route that instantiates
an untagged helper compiled as a module:

* the legacy handler (`Rec.handleDefinitionUnfold`, 6638–6647) looks the
  instance up in `sparkleSingleOutInstanceCache` under
  `parent#child#connections` and, on a hit, RETURNS THE CACHED WIRE — no
  validation against the builder's record, no wire declared, no instance
  emitted;
* that cache is cleared at depth 0 only (5500); a nested entry resets the
  other wire caches (5511–5516) but not this one.

So a second compile of the same parent, entered at a positive depth with
the cache as the first compile left it, takes the hit for the helper's
instance and returns a module WITHOUT the instance statement. (The legacy
arm's memo `sparkleSubModuleCache`, 5311–5315, is not reset at a nested
entry either and would return the first result unchanged; the probe empties
it — both are side refs of the world, on which the invariant says nothing.)

In a real compile this does not happen: within one outermost synthesis a
declaration is compiled once (the child cache), and the catches that retry
restore this cache (`WireCaches.singleOut`, 5613–5655). The probe builds the
situation by hand (a pre-set depth), which is exactly the kind of world
`RealChild` / `MachineClosesAt` quantify over.

## The declarations

* `hIrr`: an untagged `@[irreducible]` helper (`y + 1`). `unfoldDefinition?`
  does not unfold it, the front end does not inline it
  (`userDefinition?`, 3327–3339), so the legacy handler synthesises it as a
  module (6551–6553) and instantiates it through the single-output path.
* `pTop x := hIrr x + x`.

## The lines (each START also on standard error, flushed, before the run)

    SINGLEOUT START A (depth 0, reset refs)
    SINGLEOUT A: returned=<T/F> insts=<n> stmts=<n> <message>
    SINGLEOUT START B (depth 1, refs as A left them, the sub-module memo emptied)
    SINGLEOUT B: returned=<T/F> insts=<n> stmts=<n> <message>
    SINGLEOUT RESULT: equal=<T/F>

## What is ASSERTED (the command throws otherwise)

* run A returns and its module has at least one instance statement (else
  the probe does not exercise the path, and says so);
* run B returns;
* the two modules DIFFER.

PREDICTED: `A: returned=T insts=1`, `B: returned=T insts=0`, `equal=F`.
If `equal=T` the reading is wrong (the hit is validated somewhere, or the
cache is reset at the nested entry) and the command throws with that
message: then `DetN` is not refuted by this mechanism. -/
namespace Tests.Compiler.SingleOutStaleProbe
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tests.Compiler.CallWidthHuntTest (Mod Dsn bs resetRefs)

@[irreducible]
def hIrr {dom : DomainConfig} (y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  y + (Signal.pure 1#8 : Signal dom (BitVec 8))

def pTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  hIrr x + x

def emit (s : String) : MetaM Unit := do
  IO.eprintln s
  (← IO.getStderr).flush
  logInfo m!"{s}"

def instCount (m : Mod) : Nat :=
  (m.body.filter fun s => match s with
    | .inst .. => true
    | _ => false).length

/-- One run of the full entry on `pTop` at the given pre-set depth. The refs
are NOT reset here. -/
def runOnce (label : String) (depth : Nat) : MetaM (Option Mod) := do
  sparkleSynthDepth.set depth
  let r : Option Mod × String ←
    try
      let res ← Sparkle.Compiler.Elab.synthesizeCombinational ``pTop
      pure (some res.1, "")
    catch e =>
      let msg ← e.toMessageData.toString
      pure (none, msg)
  sparkleSynthDepth.set 0
  match r.1 with
  | some m => emit s!"SINGLEOUT {label}: returned=T insts={instCount m} stmts={m.body.length} {r.2}"
  | none => emit s!"SINGLEOUT {label}: returned=F insts=0 stmts=0 {r.2}"
  return r.1

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  emit "SINGLEOUT START A (depth 0, reset refs)"
  resetRefs
  let a ← runOnce "A" 0
  emit "SINGLEOUT START B (depth 1, refs as A left them, the sub-module memo emptied)"
  -- the legacy arm's memo (`sparkleSubModuleCache`, Elab 5311–5315) would hand
  -- run A's result back without translating anything: it is emptied, the
  -- single-output instance cache is NOT (a side ref of the world, like it)
  sparkleSubModuleCache.set {}
  let b ← runOnce "B" 1
  resetRefs
  sparkleSynthDepth.set 0
  match a, b with
  | some ma, some mb =>
    let eq : Bool := ma == mb
    emit s!"SINGLEOUT RESULT: equal={bs eq}"
    if instCount ma == 0 then
      throwError "SINGLEOUT: run A has no instance statement — the probe does not exercise the legacy single-output path"
    if eq then
      throwError "SINGLEOUT: the two modules are EQUAL — the prediction is wrong (DetN is not refuted by this mechanism)"
  | _, _ =>
    throwError "SINGLEOUT: a run did not return — the probe shows nothing"

end Tests.Compiler.SingleOutStaleProbe
