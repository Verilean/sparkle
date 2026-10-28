import Tests.Compiler.SeqDeepGenDiffTest
import Tests.Compiler.SeqDeepGenDiffConclTest
import Tests.Compiler.SeqDeepGrandEndpointTest
import Tests.Compiler.ChildVertAuditTest
import Tools.ShippingSeqOldPieces
import Tools.ShippingSeqChildDeepRunA
import Tools.ShippingSeqParentGenD2MS
-- UNBUILT (unit SR19): written before the first build; the run names and exits are in REPORT-SR19.md.
-- SCOPE (binding, ledger L8ay): the FALLBACK of the opt-in shared-leaf generator (`sparkle.sharedLeafCandidate`, default false).  When a command of the generic-lemma path fails, the generator
-- logs `SR18: the generic-lemma path FAILED …`, restores the whole command state, and runs the SR13 path (pasted per-callee blocks).  Two fresh copies of the shared-leaf example `topshare`
-- are generated with the TEST HOOK `sparkle.sharedLeafInject` (default empty = off): `decl` appends the deliberately failing declaration `epD2M_injected : 1 = 2 := by decide` to the generic text
-- (after the generated facts, so earlier generic declarations exist when it fails), `audit` makes the generic path's audit fail after the endpoint was added.  For each the test asserts:
--   * the failure is LOGGED (the message names the failing declaration / the audit failure) and no error message is produced (nothing is refused);
--   * the state is RESTORED: none of the generic-only declarations (`epD2M_injected`, `epD2M_quadAll`, `epD2M_genP`, `epD2M_leafRun`, `epD2M{i}_C_hF`, `epD2M_hFP`, `epD2M_hPoint0`) exists, the scope stack
--     has the depth it had before;
--   * the SR13 path was USED: the pasted per-callee blocks exist, `epD2M_endpoint` exists, `SR13 AUDIT OK` was logged;
--   * no declaration containing `injected` exists anywhere.
-- NOT claimed: that every failure mode of the generic path falls back (the hook injects two); the facts of the fallback path are those of unit SR13.
namespace Tests.Compiler.SharedLeafGenFallbackTest
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

structure AccOutF (dom : DomainConfig) where
  s : Signal dom (BitVec 8)
  odd : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (AccOutF dom) dom := ⟨⟩

@[hardware_module] def accF1 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : AccOutF dom :=
  circuit do
    let a ← Signal.reg 0#8
    let as := (a : Signal dom (BitVec 8))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 1#8 : Signal dom (BitVec 8)) } : AccOutF dom)

@[hardware_module] def wrapF1 {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : AccOutF dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := accF1 y
    r <~ a.s + x
    return ({ s := rs, odd := a.odd } : AccOutF dom)

@[hardware_module] def wrapBF1 {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : AccOutF dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := accF1 x
    r <~ a.s + y
    return ({ s := rs, odd := a.odd } : AccOutF dom)

def topF1 (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrapF1 v w
    let m2 := wrapBF1 w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topF1

#machine_design_svNR Tests.Compiler.SharedLeafGenFallbackTest.topF1 2

@[hardware_module] def accF2 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : AccOutF dom :=
  circuit do
    let a ← Signal.reg 0#8
    let as := (a : Signal dom (BitVec 8))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 1#8 : Signal dom (BitVec 8)) } : AccOutF dom)

@[hardware_module] def wrapF2 {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : AccOutF dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := accF2 y
    r <~ a.s + x
    return ({ s := rs, odd := a.odd } : AccOutF dom)

@[hardware_module] def wrapBF2 {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : AccOutF dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := accF2 x
    r <~ a.s + y
    return ({ s := rs, odd := a.odd } : AccOutF dom)

def topF2 (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrapF2 v w
    let m2 := wrapBF2 w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topF2

#machine_design_svNR Tests.Compiler.SharedLeafGenFallbackTest.topF2 2

open Lean Elab Command in
/-- generate `decl` with the shared-leaf candidate ON and the failure injected as `inj`; assert logged failure, restored state, SR13 path used, nothing refused -/
def fallbackCheck (decl : Name) (inj : String) (needle : String) : CommandElabM Unit := do
  let env0 ← getEnv
  let pre := env0.constants.fold (init := (0 : Nat)) fun n c _ => if decl.isPrefixOf c && (c.toString.splitOn ".epD2M").length > 1 then n + 1 else n
  unless pre == 0 do throwError "SR19 AUDIT FAILED: {pre} epD2M declaration(s) of {decl} exist before generation"
  let depth0 := (← get).scopes.length
  let saved := (← get).messages.toList.length
  elabCommand (← `(command| set_option sparkle.sharedLeafCandidate true in set_option sparkle.sharedLeafInject $(Syntax.mkStrLit inj) in
    #machine_seq_parent_endpoint $(mkIdent decl)))
  let ms := (← get).messages.toList.drop saved
  let txts ← ms.mapM fun m => m.data.toString
  let has := fun (n : String) => txts.any fun t => (t.splitOn n).length > 1
  -- nothing refused: no error message at all
  unless (ms.filter (·.severity == .error)).isEmpty do throwError "SR19 AUDIT FAILED: error message(s) for {decl} ({inj}): {(txts.map (·.take 300)).take 3}"
  -- the failure is logged, and names its cause
  unless has "generic-lemma path FAILED" do throwError "SR19 AUDIT FAILED: no log of the generic path's failure ({inj})"
  unless has needle do throwError "SR19 AUDIT FAILED: the log of the failure does not mention `{needle}` ({inj})"
  -- the SR13 path ran and passed its own audit
  unless has "SR13 AUDIT OK" do throwError "SR19 AUDIT FAILED: the SR13 audit was not logged ({inj})"
  let env ← getEnv
  for must in [`epD2M_endpoint, `epD2M_returned, `epD2M_wired, `epD2M0_C_composedA, `epD2M1_C_composedA] do
    unless env.contains (decl ++ must) do throwError "SR19 AUDIT FAILED: {decl ++ must} missing: the SR13 path did not run ({inj})"
  -- state restored: nothing of the generic attempt survives
  for no in [`epD2M_injected, `epD2M_quadAll, `epD2M_genP, `epD2M_leafRun, `epD2M0_C_hF, `epD2M1_C_hF, `epD2M_hFP, `epD2M_hPoint0, `epD2M0_C_gen, `epD2M0_C_hext] do
    if env.contains (decl ++ no) then throwError "SR19 AUDIT FAILED: {decl ++ no} survived the failed generic attempt ({inj})"
  let injected := env.constants.fold (init := (0 : Nat)) fun n c _ => if (c.toString.splitOn "injected").length > 1 then n + 1 else n
  unless injected == 0 do throwError "SR19 AUDIT FAILED: {injected} declaration(s) named `injected` exist ({inj})"
  unless (← get).scopes.length == depth0 do throwError "SR19 AUDIT FAILED: the scope stack changed ({inj})"
  logInfo m!"SR19 FALLBACK OK ({inj}): {decl}: the generic path's failure was logged, nothing of it kept, the SR13 path produced the endpoint, no error message (nothing refused)"

open Lean Elab Command in
run_cmd do
  fallbackCheck ``Tests.Compiler.SharedLeafGenFallbackTest.topF1 "decl" "epD2M_injected"
  fallbackCheck ``Tests.Compiler.SharedLeafGenFallbackTest.topF2 "audit" "injected audit failure"

end Tests.Compiler.SharedLeafGenFallbackTest
