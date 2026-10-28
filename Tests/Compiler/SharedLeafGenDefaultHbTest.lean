import Tests.Compiler.SeqDeepGenDiffTest
import Tests.Compiler.SeqDeepGenDiffConclTest
import Tests.Compiler.SeqDeepGrandEndpointTest
import Tests.Compiler.ChildVertAuditTest
import Tools.ShippingSeqOldPieces
import Tools.ShippingSeqChildDeepRunA
import Tools.ShippingSeqParentGenD2MS
-- BUILT (unit SR19): a8 exit 0 (dev run; 850 jobs); the final-SHA rebuild is in REPORT-SR19.md.
-- SCOPE (binding, ledger L8ay): the generic-lemma path of the opt-in shared-leaf generator (`sparkle.sharedLeafCandidate`, default false) on FRESH copies of the two accepted examples
-- (`topshare2d`: callees `wrapQ`/`wrapP`, leaf `leaf16`; `topshared`: callees `wrapD`/`wrap3D`, leaf `accD`), in a file with NO `maxHeartbeats` option anywhere (default 200000):
-- neither around the old chain `#machine_design_svNR` nor around the generating command `#machine_seq_parent_endpoint`; the generic path's text no longer carries the shared header's
-- `set_option maxHeartbeats 4000000`.  `sparkle.sharedLeafTiming` (measurement only) logs, per generated declaration, heartbeats / ms / peak RSS.  The test ASSERTS that the generic path
-- (not the logged SR13 fallback) produced the declarations: no `FAILED` message, `epD2M_hFP` exists, no pasted per-callee block exists.
-- NOT claimed: anything about parents outside the explicitly stated class; the facts are per-declaration kernel-checked, not a class theorem.
namespace Tests.Compiler.SharedLeafGenDefaultHbTest
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

structure Acc16Out (dom : DomainConfig) where
  s : Signal dom (BitVec 16)
  odd : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Acc16Out dom) dom := ⟨⟩

@[hardware_module] def leaf16 {dom : DomainConfig} (x : Signal dom (BitVec 16)) : Acc16Out dom :=
  circuit do
    let a ← Signal.reg 0#16
    let as := (a : Signal dom (BitVec 16))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 5#16 : Signal dom (BitVec 16)) } : Acc16Out dom)

@[hardware_module] def wrapQ {dom : DomainConfig} (x y : Signal dom (BitVec 16)) : Acc16Out dom :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal dom (BitVec 16))
    let a := leaf16 (x + y)
    r <~ a.s + x
    return ({ s := rs, odd := a.odd } : Acc16Out dom)

@[hardware_module] def wrapP {dom : DomainConfig} (x y : Signal dom (BitVec 16)) : Acc16Out dom :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal dom (BitVec 16))
    let a := leaf16 x
    let b := leaf16 y
    r <~ a.s + b.s
    return ({ s := rs, odd := a.odd &&& b.odd } : Acc16Out dom)

def topshare2d (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapQ v w
    let m2 := wrapP w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topshare2d

structure AccOutD (dom : DomainConfig) where
  s : Signal dom (BitVec 8)
  odd : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (AccOutD dom) dom := ⟨⟩

@[hardware_module] def accD {dom : DomainConfig} (x : Signal dom (BitVec 8)) : AccOutD dom :=
  circuit do
    let a ← Signal.reg 0#8
    let as := (a : Signal dom (BitVec 8))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 1#8 : Signal dom (BitVec 8)) } : AccOutD dom)

@[hardware_module] def wrapD {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : AccOutD dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := accD y
    r <~ a.s + x
    return ({ s := rs, odd := a.odd } : AccOutD dom)

@[hardware_module] def wrap3D {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : AccOutD dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := accD x
    r <~ a.s + y
    return ({ s := rs, odd := a.odd } : AccOutD dom)

def topshared (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrapD v w
    let m2 := wrap3D w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topshared

-- the old chains, at the DEFAULT heartbeat limit
#machine_design_svNR Tests.Compiler.SharedLeafGenDefaultHbTest.topshare2d 2
#machine_design_svNR Tests.Compiler.SharedLeafGenDefaultHbTest.topshared 2

open Lean Elab Command in
/-- run the generator (option ON, timing ON, NO heartbeat option) on `decl` and assert the GENERIC path produced the declarations -/
def genGeneric (decl : Name) : CommandElabM Unit := do
  -- the text of the generic path has NO heartbeat option; the text of the SR13 path (the shared header) still carries `set_option maxHeartbeats 4000000`
  let some p ← Tools.ShippingSeqParentGenD2MS.analyseS decl | throwError "SR19 AUDIT FAILED: {decl} is not in the class"
  let gi ← Tools.ShippingSeqParentGenD2MS.genInfoS p
  let hasHb := fun (t : String) => (t.splitOn "maxHeartbeats").length > 1
  if hasHb (Tools.ShippingSeqParentGenD2MS.assembleMS p (some gi)) then throwError "SR19 AUDIT FAILED: the generic path's text contains a maxHeartbeats option"
  unless hasHb (Tools.ShippingSeqParentGenD2MS.assembleMS p none) do throwError "SR19 AUDIT FAILED: the SR13 text no longer contains the header's option (the check would discriminate nothing)"
  -- (item 3) the generic path's text does not extract anything from the old generated chain
  let gtxt := Tools.ShippingSeqParentGenD2MS.assembleMS p (some gi)
  for bad in ["oldGroupFact%", "oldInst%", "oldNamed%", "machine_composedNR", "seq_child_runN_ofR"] do
    if (gtxt.splitOn bad).length > 1 then throwError "SR19 AUDIT FAILED: the generic path's text mentions `{bad}`"
  unless ((Tools.ShippingSeqParentGenD2MS.assembleMS p none).splitOn "oldGroupFact%").length > 1 do
    throwError "SR19 AUDIT FAILED: the SR13 text no longer mentions oldGroupFact% (the check would discriminate nothing)"
  let saved := (← get).messages.toList.length
  elabCommand (← `(command| set_option sparkle.sharedLeafCandidate true in set_option sparkle.sharedLeafTiming true in
    #machine_seq_parent_endpoint $(mkIdent decl)))
  let ms := (← get).messages.toList.drop saved
  let txts ← ms.mapM fun m => m.data.toString
  let errs := (ms.filter (·.severity == .error)).length
  unless errs == 0 do throwError "SR19 AUDIT FAILED: {errs} error(s) while generating {decl}"
  for t in txts do
    if (t.splitOn "generic-lemma path FAILED").length > 1 then throwError "SR19 AUDIT FAILED: the generic path fell back for {decl}: {t.take 600}"
  let env ← getEnv
  for must in [`epD2M_endpoint, `epD2M_hFP, `epD2M0_C_hF, `epD2M1_C_hF, `epD2M_hPoint0, `epD2M_returned, `epD2M_wired] do
    unless env.contains (decl ++ must) do throwError "SR19 AUDIT FAILED: {decl ++ must} missing"
  for no in [`epD2M0_C_composedA, `epD2M1_C_composedA] do
    if env.contains (decl ++ no) then throwError "SR19 AUDIT FAILED: the pasted block {decl ++ no} exists (SR13 fallback ran)"
  let timing := txts.filter fun t => (t.splitOn "SR19 TIMING").length > 1
  unless timing.length > 20 do throwError "SR19 AUDIT FAILED: only {timing.length} timing lines for {decl}"
  let mut maxHb := 0
  for t in timing do
    let n := ((t.drop ((t.splitOn "heartbeats ").head!.length + 11)).takeWhile Char.isDigit).toString.toNat!
    if n > maxHb then maxHb := n
  logInfo m!"SR19: {decl}: generic path, {timing.length} generated declarations timed, max {maxHb} heartbeat units of the default limit 200000 (no maxHeartbeats option anywhere)"

open Lean Elab Command in
run_cmd do
  unless (maxHeartbeats.get (← getOptions)) == 200000 do throwError "SR19 AUDIT FAILED: the ambient maxHeartbeats is not the default"
  genGeneric ``Tests.Compiler.SharedLeafGenDefaultHbTest.topshare2d
  genGeneric ``Tests.Compiler.SharedLeafGenDefaultHbTest.topshared

#print axioms Tests.Compiler.SharedLeafGenDefaultHbTest.topshare2d.epD2M_endpoint
#print axioms Tests.Compiler.SharedLeafGenDefaultHbTest.topshared.epD2M_endpoint
#print axioms Tests.Compiler.SharedLeafGenDefaultHbTest.topshare2d.epD2M_hFP
#print axioms Tests.Compiler.SharedLeafGenDefaultHbTest.topshared.epD2M_hFP

end Tests.Compiler.SharedLeafGenDefaultHbTest
