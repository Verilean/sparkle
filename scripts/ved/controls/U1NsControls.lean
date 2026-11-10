/-
U1 measurement controls for the namespace-assisted route `u1_deep_ns`
(MEASUREMENT ONLY, never for main; reviewer ruling 2026-11-10).

Run (after `kjob lake build Tools.VedU1Deep Tools.VedStrictAudit Sparkle`):
  kjob lake env lean scripts/ved/controls/U1NsControls.lean
The file elaborates without error iff every control holds; each prints
`VED U1CTL <id> PASS`.

  C0  the harness wrapper `#vedu1_in_declns` (copied from u1_gen.py) gives a
      strict `VedCtlA.cnt.ved_u1` (theorem, std3 closure) for a command written
      outside the declaration's namespace;
  C1  same short name in another namespace: a wrapper that opens the WRONG
      namespace (VedCtlB) while the original scope resolves `cnt` to VedCtlA.cnt
      must not run the command (no facts, no theorem for either constant);
  C2  preparation facts missing: `#ved_u1_deep` on VedCtlC.cnt with no
      `#verify_elab_deep` refuses, no theorem;
  C3  another declaration's facts: VedCtlA's facts exist (C0), and
      `#ved_u1_deep VedCtlB.cnt` refuses, no theorem for VedCtlB.cnt.
-/
import Sparkle
import Sparkle.Core.CircuitDo
import Sparkle.Compiler.Elab
import Tools.VedU1Deep
import Tools.VedStrictAudit

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace VedCtlA
def cnt : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    c <~ c + 1#8
    return c
end VedCtlA

namespace VedCtlB
def cnt : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    c <~ c + 2#8
    return c
end VedCtlB

namespace VedCtlC
def cnt : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    c <~ c + 3#8
    return c
end VedCtlC

-- the harness wrapper, verbatim from u1_gen.py (IN_DECLNS)
open Lean Elab Command in
elab "#vedu1_in_declns " id:ident c:command : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  withNamespace n.getPrefix do
    -- withNamespace also changes how the bare identifier resolves: run the
    -- command only if it still names the SAME constant inside the namespace
    let n' ← liftCoreM <| realizeGlobalConstNoOverload id
    logInfo m!"VED U1N scope={n.getPrefix} outer={n} inner={n'} {if n == n' then "same" else "differs"}"
    if n == n' then elabCommand c
    else logError m!"VED U1N REFUSED {id}: resolves to {n'} inside {n.getPrefix}, not {n}"

-- a deliberately WRONG wrapper for C1: opens the namespace it is given, with
-- the same same-constant check as the harness wrapper
open Lean Elab Command in
elab "#vedu1_in_ns " ns:ident id:ident c:command : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  withNamespace ns.getId do
    let n' ← try liftCoreM <| realizeGlobalConstNoOverload id
      catch e => do logError m!"VED U1N REFUSED {id}: {← e.toMessageData.toString}"; return Name.anonymous
    logInfo m!"VED U1N scope={ns.getId} outer={n} inner={n'} {if n == n' then "same" else "differs"}"
    if n == n' then elabCommand c
    else logError m!"VED U1N REFUSED {id}: resolves to {n'} inside {ns.getId}, not {n}"

open Lean Elab Command in
elab "#vedu1_ctl " id:str thm:ident want:ident : command => do
  -- want: `present` (theorem with std3 closure) or `absent`
  let env ← getEnv
  let ok ← match env.find? thm.getId, want.getId with
    | some (.thmInfo _), `present => do
        let ax ← liftCoreM <| Lean.collectAxioms thm.getId
        pure (ax.all fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
    | none, `absent => pure true
    | _, _ => pure false
  if ok then logInfo m!"VED U1CTL {id.getString} PASS"
  else throwError m!"VED U1CTL {id.getString} FAIL: {thm.getId} expected {want.getId}"

open Lean Elab Command in
elab "#vedu1_absent " id:str n:ident : command => do
  if (← getEnv).contains n.getId then throwError m!"VED U1CTL {id.getString} FAIL: {n.getId} exists"
  logInfo m!"VED U1CTL {id.getString} absent {n.getId}"

/-! C0: positive, command outside the namespace (like CircuitDoTest's section) -/
section C0
open VedCtlA
set_option Elab.async false in
#vedu1_in_declns cnt
set_option Elab.async false in
#verify_elab_deep cnt
set_option Elab.async false in
#vedu1_in_declns cnt
set_option Elab.async false in
#ved_u1_deep cnt
end C0
#vedu1_ctl "C0" VedCtlA.cnt.ved_u1 present

/-! C1: same short name elsewhere; the wrong namespace must not run the command -/
section C1
open VedCtlA
#guard_msgs (drop all) in
set_option Elab.async false in
#vedu1_in_ns VedCtlB cnt
set_option Elab.async false in
#verify_elab_deep cnt
#guard_msgs (drop all) in
set_option Elab.async false in
#vedu1_in_ns VedCtlB cnt
set_option Elab.async false in
#ved_u1_deep cnt
end C1
#vedu1_absent "C1" VedCtlB.cnt_deep_trace
#vedu1_ctl "C1" VedCtlB.cnt.ved_u1 absent

/-! C2: no preparation facts -/
namespace VedCtlC
#guard_msgs (drop all) in
set_option Elab.async false in
#ved_u1_deep cnt
end VedCtlC
#vedu1_absent "C2" VedCtlC.cnt_deep_trace
#vedu1_ctl "C2" VedCtlC.cnt.ved_u1 absent

/-! C3: another declaration's facts (VedCtlA's, from C0) are not used for VedCtlB -/
namespace VedCtlB
#guard_msgs (drop all) in
set_option Elab.async false in
#ved_u1_deep cnt
end VedCtlB
#vedu1_ctl "C3" VedCtlB.cnt.ved_u1 absent
