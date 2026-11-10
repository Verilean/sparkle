import Tools.VedU1Deep
import Tools.VedU1HierEntry
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# H2 unit 1: the open parent (design docs/VED-HIER-H2-DESIGN.md §2.2, §12, Q8)

`parTwo` is a register-free parent with two instances of the register-carrying
child `accMod` on different inputs, combined asymmetrically (`p - q + a`).

What is fixed here:
1. Baseline: `#verify_elab_deep parTwo` on the WHOLE parent is refused
   (single-module designs only), and `#ved_u1_hier parTwo` is refused by the
   H1 shape check (child with a register).
2. `parentOpen a p q := p - q + a` has the child calls as free signals `p q`.
   `#verify_elab_deep` refuses it (it requires registers), but the
   combinational entry `#ved_u1` accepts it (`parentOpen.ved_u1`).
3. `parTwo_eq_open : parTwo a b = parentOpen a (accMod a) (accMod b)`, a theorem
   whose proof term is `rfl`, added to the environment by the kernel, with no
   axioms at all.
4. Controls: the swapped / replaced / mis-connected equations are rejected by
   the kernel (`addDecl` of an `Eq.refl` proof), and nothing is left behind.
-/

namespace Tests.Ved.H2OpenParentProbe

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Deep

/-- Child with one register: an accumulator with an input. -/
@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + x
    return a

/-- Another register function (init 1), used only by a control. -/
def accModOther (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (1#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + x
    return a

/-- Register-free parent: two instances of `accMod` on different inputs,
combined asymmetrically. -/
@[hardware_module]
def parTwo (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accMod a
  let q := accMod b
  p - q + a

/-- The open parent: the child calls are free signals `p q`. -/
def parentOpen (a p q : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  p - q + a

/-! ## 1. Baseline: the whole parent -/

/-- error: #verify_elab_deep: single-module designs only -/
#guard_msgs in
#verify_elab_deep parTwo

/-- error: VED U1 REFUSED Tests.Ved.H2OpenParentProbe.parTwo [hier-shape]: instance _tmp_inst_Tests.Ved.H2OpenParentProbe.accMod_0: child Tests.Ved.H2OpenParentProbe.accMod is not a combinational leaf (register, memory or instance in its body: H2) -/
#guard_msgs in
#ved_u1_hier parTwo

/-! ## 2. The open parent -/

/-- error: #verify_elab_deep: no registers -/
#guard_msgs in
#verify_elab_deep parentOpen

/-- error: Tests.Ved.H2OpenParentProbe.parentOpen.ved_mod missing (run #verify_elab_deep Tests.Ved.H2OpenParentProbe.parentOpen first) -/
#guard_msgs in
#ved_u1_deep parentOpen

#guard_msgs (drop info) in
#ved_u1 parentOpen

example : U1Stmt parentOpen.ved_contract parentOpen.ved_mod parentOpen := parentOpen.ved_u1

/-! ## 3. The equation, checked by the kernel -/

theorem parTwo_eq_open (a b : Signal defaultDomain (BitVec 8)) :
    parTwo a b = parentOpen a (accMod a) (accMod b) := rfl

/-- info: 'Tests.Ved.H2OpenParentProbe.parTwo_eq_open' does not depend on any axioms -/
#guard_msgs in
#print axioms parTwo_eq_open

/-- info: 'Tests.Ved.H2OpenParentProbe.parentOpen.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parentOpen.ved_u1

/-! ## 4. Controls: the kernel refuses a wrong equation, nothing is left -/

/-- Elaborate `stmt` (a closed `∀ a b, l = r`), submit `fun a b => Eq.refl l`
as the proof of a theorem named `nm` to the kernel; it must be refused, and
`nm` must not exist afterwards.  With `expectOk := true` it must be accepted
(then the name is dropped from the check by using a throwaway environment). -/
def kernelVerdict (nm : Name) (stmt : Syntax) : TermElabM Bool := do
  let ty ← instantiateMVars (← Term.elabTerm stmt none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let value ← forallTelescope ty fun xs body => do
    let some (_, l, _) := body.eq? | throwError "not an equation"
    let pf ← mkEqRefl l
    mkLambdaFVars xs pf
  let before ← getEnv
  let ok ← try
      addDecl (.thmDecl { name := nm, levelParams := [], type := ty, value })
      pure true
    catch _ => pure false
  unless ok do
    if (← getEnv).contains nm then throwError "{nm} left in the environment"
  setEnv before
  return ok

elab "#kernel_refuses " nm:ident ty:term : command => do
  liftTermElabM do
    if (← kernelVerdict nm.getId ty) then throwError "kernel accepted {nm.getId}"
    logInfo m!"refused: {nm.getId}"

elab "#kernel_accepts " nm:ident ty:term : command => do
  liftTermElabM do
    unless (← kernelVerdict nm.getId ty) do throwError "kernel refused {nm.getId}"
    logInfo m!"accepted: {nm.getId}"

/-- info: accepted: ctl_ok -/
#guard_msgs in
#kernel_accepts ctl_ok (∀ a b : Signal defaultDomain (BitVec 8),
  parTwo a b = parentOpen a (accMod a) (accMod b))

/-- info: refused: ctl_swapped_calls -/
#guard_msgs in
#kernel_refuses ctl_swapped_calls (∀ a b : Signal defaultDomain (BitVec 8),
  parTwo a b = parentOpen a (accMod b) (accMod a))

/-- info: refused: ctl_other_function -/
#guard_msgs in
#kernel_refuses ctl_other_function (∀ a b : Signal defaultDomain (BitVec 8),
  parTwo a b = parentOpen a (accMod a) (accModOther b))

/-- info: refused: ctl_swapped_connections -/
#guard_msgs in
#kernel_refuses ctl_swapped_connections (∀ a b : Signal defaultDomain (BitVec 8),
  parTwo b a = parentOpen a (accMod a) (accMod b))

/-- info: refused: ctl_shared_connection -/
#guard_msgs in
#kernel_refuses ctl_shared_connection (∀ a b : Signal defaultDomain (BitVec 8),
  parTwo a b = parentOpen a (accMod a) (accMod a))

/-- info: ok -/
#guard_msgs in
run_cmd do
  for n in [`ctl_ok, `ctl_swapped_calls, `ctl_other_function, `ctl_swapped_connections,
            `ctl_shared_connection] do
    if (← getEnv).contains n then throwError "{n} left in the environment"
  logInfo "ok"

end Tests.Ved.H2OpenParentProbe
