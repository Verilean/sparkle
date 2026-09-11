/-
  Minimal reproduction: a value parameter used as a register's INITIAL
  VALUE.

  Status at the time of writing (2026-09-11): `initCirc7` FAILS on the
  deep route with `unknown free variable '_fvar.NNNN'` — an internal
  elaboration error rather than a designed refusal.  `accK9`, the
  control, passes.  This file therefore does NOT `#verify_elab_deep`
  the failing circuit: it pins the parts that must keep working, and
  documents the failing one so the next session starts from the same
  experiment rather than rebuilding it in `/tmp`.

  Reproduce the failure:

      lake env lean Tests/Verification/ValueParamInitRepro.lean
      -- then uncomment the marked line below

  Observed facts (measured, not inferred):

  * the EMITTER is correct — `synthesizeHierarchical` succeeds and the
    IR carries `register … init=7` (pinned by `initIsSeven` below);
  * the control `accK9` (same value parameter, used in the BODY rather
    than as an init) proves on the deep route;
  * with `SPARKLE_DEEP_DEBUG=1` the failing circuit logs
    `STAGE ok: helpers collected` and then dies BEFORE any loop node is
    reported — i.e. inside loop-node discovery;
  * the expressions `openLams` collects inside its `withLocalDecl`
    scope carry free variables OUT of that scope (`hasFVar = true`),
    which is the leading candidate for the leak.

  Corrected record: an earlier note claimed the failure happened
  "before any definition is emitted", on the grounds that it fails
  under `SPARKLE_DEEP_NOTHM=1`.  That inference was WRONG — the
  generator emits definitions and theorems from well before the
  `NOTHM` check, so that flag does not bound the failure.
-/
import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Tools.DeepElab

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core

namespace Sparkle.Tests.ValueParamInitRepro

/-- CONTROL: the value parameter is used in the BODY.  This shape
    proves on the deep route and must keep doing so. -/
def accK (k : BitVec 8) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg (0#8)
    let a := (acc : Signal defaultDomain (BitVec 8))
    acc <~ a + d + (Signal.pure k : Signal defaultDomain (BitVec 8))
    return a

def accK9 (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  accK 9#8 d

#verify_elab_deep accK9

/-- CONTROL: a direct literal initial value, no parameter at all. -/
def litInit (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (7#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + d
    return a

#verify_elab_deep litInit

/-- THE FAILING SHAPE: the value parameter is the register's INIT. -/
def initCirc (k : BitVec 8) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg k
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + d
    return a

def initCirc7 (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  initCirc 7#8 d

-- UNCOMMENT to reproduce the defect (expected: `unknown free variable`):
-- #verify_elab_deep initCirc7

-- The EMITTER is correct for the failing shape: the wrapper resolves
-- the parameter and the IR carries the literal initial value.  This is
-- the half that must not regress while the deep route is repaired, and
-- it is also the completion criterion "initCirc7's IR init is 7".
open Lean Elab Command in
run_cmd do
  let d ← liftTermElabM
    (Sparkle.Compiler.Elab.synthesizeHierarchical
      ``Sparkle.Tests.ValueParamInitRepro.initCirc7)
  let mut inits : List Int := []
  for m in d.modules do
    for st in m.body do
      match st with
      | .register _ _ _ _ init => inits := init :: inits
      | _ => pure ()
  unless inits == [7] do
    throwError "initCirc7: expected exactly one register with init 7, got {inits}"

-- The control's deep-route theorems exist and are clean.
#print axioms accK9_deep_trace
#print axioms litInit_deep_trace

end Sparkle.Tests.ValueParamInitRepro
