/-
  Minimal reproduction: a value parameter used as a register's INITIAL
  VALUE.

  History.  On 2026-09-11 `initCirc7` FAILED on the deep route with
  `unknown free variable '_fvar.NNNN'` — an internal elaboration error
  rather than a designed refusal — while `accK9` (the same parameter
  used in the BODY) and `litInit` (a literal init) passed.  Fixed on
  2026-09-12; every circuit in this file now proves, and the CI gate
  (`bench/xiangshan/ci_check.sh`) requires exactly 5 PROVEN lines here.

  Cause (observed before the change, confirmed by the change):

  * with `SPARKLE_DEEP_DEBUG=1` the failing circuit logged
    `STAGE ok: helpers collected` and then died before any loop node
    was reported — inside loop-node discovery;
  * `openLams`/`openLams'` open a definition's lambdas with
    `withLocalDecl` and, at both the root and the helper site, RETURNED
    the collected `runCircuitH` applications out of that scope;
    `nodeOf` then analysed them outside the local context they mention
    (measured: the collected body has `hasFVar = true`).  A value
    parameter used as an init is exactly the case where the collected
    expression still refers to one of those fvars.

  Fix: analyse inside the callback.  Only validated `LoopNode`s (closed
  literal widths/inits + delaborated types) cross the scope boundary
  now.  No change to the traversal (`headChain`/`findRC`) was needed
  for any shape in this file, including the two-level wrapper chain.

  Before the change:  `#verify_elab_deep initCirc7` → unknown free variable
  After the change:   PROVEN; `initCirc7_deep_trace` and
                      `initCirc7_deep_signal_run` both exist.

  Axiom dependencies (checked by the `run_cmd` at the end of this file,
  and CORRECTED from an earlier note that claimed "standard axioms only"
  for both — that was read off a truncated line):

  * `{f}_deep_trace` (capstone): `propext`, `Classical.choice`,
    `Quot.sound` only.
  * `{f}_deep_signal_run` (IR replay): the three above PLUS
    `native_decide`-generated axioms (`{lemma}._native.native_decide.ax_N`,
    23 of them for `initCirc7`, from 7 replay lemmas: `coneEval_out`,
    `coneEval_r0`, `regstep`, `seed_bounded`, `step_*`, and the run
    itself).  These ride `Lean.ofReduceBool`, i.e. they trust the Lean
    compiler's evaluation of the checker, not the kernel.  This is the
    documented trust boundary of the replay chain — see
    `docs/CertifiedRoundtrip-design.md` ("`native_decide` in the
    obligations") and TODO item F2, which tracks moving these to kernel
    `decide`.  No `sorryAx` on either theorem.

  Corrected record: an earlier note claimed the failure happened
  "before any definition is emitted", because it failed under
  `SPARKLE_DEEP_NOTHM=1`.  That was wrong — emission starts well before
  the `NOTHM` check, so the flag never bounded the failure.
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

-- FIXED 2026-09-12 (see the header): this now proves.
#verify_elab_deep initCirc7

/-- Completion criterion: an initial value computed FROM a `Nat`
    parameter (not a `BitVec` literal handed straight through). -/
def natInit (n : Nat) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (BitVec.ofNat 8 n)
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + d
    return a

def natInit5 (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  natInit 5 d

#verify_elab_deep natInit5

/-- Completion criterion: a CHAIN of specialized wrappers, the init
    resolved two definitions away from the `circuit do`. -/
def initCirc7Again (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  initCirc7 d

#verify_elab_deep initCirc7Again

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

-- For EVERY circuit above: the capstone `_deep_trace` and the IR replay
-- `_deep_signal_run` both exist; the capstone depends on the three
-- standard axioms only; the replay depends on those plus
-- `native_decide`-generated axioms and NOTHING else (in particular no
-- `sorryAx`).  One `VPI OK:` line per circuit — the CI gate greps for
-- them by name, so a missing theorem, a stray axiom, or a silently
-- skipped circuit fails the build rather than lowering a count.
open Lean Elab Command in
run_cmd do
  let circuits : List Name := [`accK9, `litInit, `initCirc7, `natInit5, `initCirc7Again]
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let isNativeDecide (a : Name) : Bool :=
    a == ``Lean.ofReduceBool || (a.toString.splitOn "native_decide").length > 1
  let ns := `Sparkle.Tests.ValueParamInitRepro
  for c in circuits do
    let tr := ns ++ c.appendAfter "_deep_trace"
    let rp := ns ++ c.appendAfter "_deep_signal_run"
    for thm in [tr, rp] do
      unless (← getEnv).contains thm do
        throwError "VPI: missing theorem {thm}"
    let axT ← collectAxioms tr
    for a in axT do
      unless std.contains a do
        throwError "VPI: {tr} depends on unexpected axiom {a}"
    let mut nNative : Nat := 0
    for a in (← collectAxioms rp) do
      if std.contains a then pure ()
      else if isNativeDecide a then nNative := nNative + 1
      else throwError "VPI: {rp} depends on unexpected axiom {a}"
    logInfo m!"VPI OK: {c} trace=[std] replay=[std + {nNative} native_decide]"

end Sparkle.Tests.ValueParamInitRepro
