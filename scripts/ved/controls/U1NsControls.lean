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
      `#ved_u1_deep VedCtlB.cnt` refuses, no theorem for VedCtlB.cnt;
  C4  a ROOT-level declaration (no namespace; 150 inventory rows failed with
      `invalid scope` before): the wrapper elaborates the command as is in the
      original scope (mode=root) and gives a strict `vedCtlRootCnt.ved_u1`;
  C5  a PRIVATE declaration inside a namespace (3 rows failed the same way):
      the wrapper opens the user-facing namespace and the bare name still
      resolves to the same private constant (mode=ns, same); `#ved_u1_deep`
      then refuses (`pcnt_deep missing`: a U1 tool limit on private names, see
      below), and no theorem exists.
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

def vedCtlRootCnt : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    c <~ c + 5#8
    return c

namespace VedCtlP
private def pcnt : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    c <~ c + 7#8
    return c
end VedCtlP

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
  -- a private constant's namespace is that of its user-facing name
  let scope := ((privateToUserName? n).getD n).getPrefix
  if scope.isAnonymous then
    -- a root-level declaration: no namespace to open, so the command is
    -- elaborated as is in the original scope (the u1_deep command)
    logInfo m!"VED U1N scope=_root_ outer={n} inner={n} same mode=root"
    elabCommand c
  else
    let r : Option String ← try
        withNamespace scope do
          -- withNamespace also changes how the bare identifier resolves: run
          -- the command only if it still names the SAME constant inside
          let n' ← liftCoreM <| realizeGlobalConstNoOverload id
          logInfo m!"VED U1N scope={scope} outer={n} inner={n'} {if n == n' then "same" else "differs"} mode=ns"
          if n == n' then elabCommand c
          else logError m!"VED U1N REFUSED {id}: resolves to {n'} inside {scope}, not {n}"
        pure none
      catch e => pure (some (← e.toMessageData.toString))
    if let some msg := r then
      logError m!"VED U1N HARNESS-FAIL {id} scope={scope}: {msg}"

-- a deliberately WRONG wrapper for C1: opens the namespace it is given, with
-- the same same-constant check as the harness wrapper
open Lean Elab Command in
elab "#vedu1_in_ns " ns:ident id:ident c:command : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  withNamespace ns.getId do
    let n' ← try liftCoreM <| realizeGlobalConstNoOverload id
      catch e => do logError m!"VED U1N REFUSED {id}: {← e.toMessageData.toString}"; pure Name.anonymous
    logInfo m!"VED U1N scope={ns.getId} outer={n} inner={n'} {if n == n' then "same" else "differs"}"
    if n == n' then elabCommand c
    else logError m!"VED U1N REFUSED {id}: resolves to {n'} inside {ns.getId}, not {n}"

open Lean Elab Command in
/-- Elaborate `c`; require an error from the namespace wrapper itself
(`VED U1N REFUSED ...`), whatever the resolution failure was (another constant
or an ambiguous name), and drop the captured messages. -/
elab "#vedu1_expect_refused " id:str c:command : command => do
  let saved := (← get).messages
  modify fun s => { s with messages := MessageLog.empty }
  elabCommand c
  let errs ← (← get).messages.toList.filterMapM fun m => do
    if m.severity == .error then pure (some (← m.data.toString)) else pure none
  modify fun s => { s with messages := saved }
  match errs.find? (·.startsWith "VED U1N REFUSED") with
  | some e => logInfo m!"VED U1CTL {id.getString} refused by the wrapper: {e}"
  | none => throwError m!"VED U1CTL {id.getString} FAIL: not refused by the wrapper; errors: {errs}"

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

/-! C1: same short name elsewhere; the wrong namespace must not run the command.
The wrapper's own refusal is required (#vedu1_expect_refused), so C1 can not
pass because the wrapper is missing or never ran. -/
section C1
open VedCtlA
#vedu1_expect_refused "C1-prep"
#vedu1_in_ns VedCtlB cnt
set_option Elab.async false in
#verify_elab_deep cnt
#vedu1_expect_refused "C1-u1"
#vedu1_in_ns VedCtlB cnt
set_option Elab.async false in
#ved_u1_deep cnt
end C1
#vedu1_absent "C1" VedCtlB.cnt_deep_trace
#vedu1_absent "C1" cnt_deep_trace
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

/-! C4: root-level declaration through the wrapper (mode=root) -/
section C4
set_option Elab.async false in
#vedu1_in_declns vedCtlRootCnt
set_option Elab.async false in
#verify_elab_deep vedCtlRootCnt
set_option Elab.async false in
#vedu1_in_declns vedCtlRootCnt
set_option Elab.async false in
#ved_u1_deep vedCtlRootCnt
end C4
#vedu1_ctl "C4" vedCtlRootCnt.ved_u1 present

/-! C5: private declaration inside a namespace, command written outside it.
The wrapper must resolve the same private constant and run both commands
(mode=ns).  U1 then REFUSES: `#verify_elab_deep` names the facts in the current
namespace by the user-facing name (`VedCtlP.pcnt_deep...`) while `#ved_u1_deep`
looks them up under the private name (`_private...VedCtlP.pcnt_deep`).  That is
a U1 tool limit (deepName on private names), recorded here as the expected
refusal; it is not a harness failure and never a success. -/
open Lean Elab Command in
elab "#vedu1_expect_error " id:str pat:str c:command : command => do
  let saved := (← get).messages
  modify fun s => { s with messages := MessageLog.empty }
  elabCommand c
  let msgs ← (← get).messages.toList.mapM fun m => do pure (m.severity, ← m.data.toString)
  modify fun s => { s with messages := saved }
  let errs := msgs.filter (·.1 == .error) |>.map (·.2)
  let infos := msgs.filter (·.1 == .information) |>.map (·.2)
  unless infos.any (fun t => t.startsWith "VED U1N" && (t.splitOn " same mode=ns").length > 1) do
    throwError m!"VED U1CTL {id.getString} FAIL: wrapper did not run the command (mode=ns, same): {infos}"
  match errs.find? (fun e => (e.splitOn pat.getString).length > 1) with
  | some e => logInfo m!"VED U1CTL {id.getString} expected refusal: {e}"
  | none => throwError m!"VED U1CTL {id.getString} FAIL: no error containing {pat.getString}; errors: {errs}"
section C5
open VedCtlP
set_option Elab.async false in
#vedu1_in_declns pcnt
set_option Elab.async false in
#verify_elab_deep pcnt
#vedu1_expect_error "C5-u1" "pcnt_deep missing"
set_option Elab.async false in
#vedu1_in_declns pcnt
set_option Elab.async false in
#ved_u1_deep pcnt
open Lean Elab Command in
run_cmd do
  let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent `pcnt)
  if (← getEnv).contains (n ++ `ved_u1) then
    throwError m!"VED U1CTL C5 FAIL: {n ++ `ved_u1} exists"
  -- where the preparation put the facts (this module's constants only)
  let facts := (← getEnv).constants.map₂.foldl (init := #[]) fun acc k _ =>
    if (toString k).endsWith "pcnt_deep" then acc.push k else acc
  logInfo m!"VED U1CTL C5 facts at {facts}; U1 looked under {n}_deep"
  logInfo m!"VED U1CTL C5 PASS (expected tool refusal on a private name, no theorem)"
end C5
