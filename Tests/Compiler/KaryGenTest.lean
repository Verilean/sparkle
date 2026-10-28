import Tests.Compiler.KaryThreeReturnedTest
import Tools.ShippingSeqParentGenD2MSK
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit SR22): g2 exit 0 (dev run, default heartbeats, no raise); the final-SHA rebuild is in REPORT-SR22.md.
-- SCOPE (binding, ledger L8bb): the OPT-IN K-ary generator `Tools/ShippingSeqParentGenD2MSK.lean` (`set_option sparkle.karyCandidate true`, default false; K != 2) run by `#machine_seq_parent_endpoint` on a FRESH
-- copy of the SR21 three-callee example (`topshare3`: callees `wrapA`, `wrapB`, `wrapC`, leaf `leafK`), in a file with NO `maxHeartbeats` option anywhere (default 200000), with `sparkle.sharedLeafTiming` logging
-- heartbeats / ms / peak RSS per generated declaration.  Checked here:
--   (1) the generated `epK_endpoint` / `epK_returned` / `epK_wired` have FULL forall-types `isDefEq` to (a) the hand-applied declarations of SR21 / `Tests/Compiler/KaryThreeReturnedTest.lean` and (b) the HAND-WRITTEN
--       statements `Share3Full` / `Share3Ret` / `Share3Wired`, in both cases with the constants of `Tests.Compiler.KaryThreeTest` renamed to those of this file (the two copies are different declarations with
--       the same source text); type-correct mutations are REJECTED; closure audit;
--   (2) with the option OFF the existing refusal of the same parent is unchanged and nothing is generated; with the option ON a `K = 2` parent is NOT taken (same refusal);
--   (3) FALLBACK: an injected failing declaration / a failing audit makes the generator LOG `the K-ary path FAILED`, restore the state (no `epK*` / `epD2M*` constant survives) and run the existing
--       elaborators, whose refusal text is identical to the option-off text (no new refusal, nothing kept);
--   (4) a K = 1 parent (`topone`, one callee, one call) is accepted by the generator (smoke example: endpoint / returned / wired exist, standard axioms, closure audit; its full type is NOT compared with a
--       hand-written statement).
-- The generated facts are per-declaration kernel-checked facts about these declarations, not a class theorem; four examples do NOT make the class complete.  `RealChildA` / `JQC` are histories.
-- No `sorry`, no `axiom`, no `native_decide`, NO heartbeat raise.
set_option Elab.async false
section
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
namespace Tests.Compiler.KaryGenTest

abbrev N := `Tests.Compiler.KaryGenTest

structure KOut (dom : DomainConfig) where
  s : Signal dom (BitVec 16)
  odd : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (KOut dom) dom := ⟨⟩

/-- the shared 16-bit leaf -/
@[hardware_module] def leafK {dom : DomainConfig} (x : Signal dom (BitVec 16)) : KOut dom :=
  circuit do
    let a ← Signal.reg 0#16
    let as := (a : Signal dom (BitVec 16))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 5#16 : Signal dom (BitVec 16)) } : KOut dom)

/-- a callee with ONE call of the leaf (argument `x + y`) -/
@[hardware_module] def wrapA {dom : DomainConfig} (x y : Signal dom (BitVec 16)) : KOut dom :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal dom (BitVec 16))
    let a := leafK (x + y)
    r <~ a.s + x
    return ({ s := rs, odd := a.odd } : KOut dom)

/-- a callee with TWO calls of the leaf (arguments `x`, `y`) -/
@[hardware_module] def wrapB {dom : DomainConfig} (x y : Signal dom (BitVec 16)) : KOut dom :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal dom (BitVec 16))
    let a := leafK x
    let b := leafK y
    r <~ a.s + b.s
    return ({ s := rs, odd := a.odd &&& b.odd } : KOut dom)

/-- a callee with ONE call of the leaf (argument `x + x`) -/
@[hardware_module] def wrapC {dom : DomainConfig} (x y : Signal dom (BitVec 16)) : KOut dom :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal dom (BitVec 16))
    let a := leafK (x + x)
    r <~ a.s + y
    return ({ s := rs, odd := a.odd } : KOut dom)

/-- the parent: THREE different callees sharing the leaf -/
def topshare3 (en : Signal defaultDomain Bool) (u v w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapA u v
    let m2 := wrapB v w
    let m3 := wrapC w u
    r <~ Signal.mux (m.odd &&& m2.odd &&& m3.odd &&& en) (rs + u) rs
    return rs

#machine_endpoint topshare3

/-- the parent of the SECOND copy (option OFF: the existing refusal; same shape as `topshare3`) -/
def topshare3off (en : Signal defaultDomain Bool) (u v w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapA u v
    let m2 := wrapB v w
    let m3 := wrapC w u
    r <~ Signal.mux (m.odd &&& m2.odd &&& m3.odd &&& en) (rs + u) rs
    return rs
#machine_endpoint topshare3off

/-- fallback copies -/
def topshare3inj (en : Signal defaultDomain Bool) (u v w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapA u v
    let m2 := wrapB v w
    let m3 := wrapC w u
    r <~ Signal.mux (m.odd &&& m2.odd &&& m3.odd &&& en) (rs + u) rs
    return rs
#machine_endpoint topshare3inj

def topshare3aud (en : Signal defaultDomain Bool) (u v w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapA u v
    let m2 := wrapB v w
    let m3 := wrapC w u
    r <~ Signal.mux (m.odd &&& m2.odd &&& m3.odd &&& en) (rs + u) rs
    return rs
#machine_endpoint topshare3aud

/-- K = 2 parent (outside the generator's class `K != 2`) -/
def toptwo (en : Signal defaultDomain Bool) (u v : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapA u v
    let m2 := wrapB v u
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + u) rs
    return rs
#machine_endpoint toptwo

/-- K = 1 parent: one callee, ONE call (the machine data lists the two instances `[wrapA, wrapA]` of that call, as for every callee of `topshare3`) -/
def topone (en : Signal defaultDomain Bool) (u v : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapA u v
    r <~ Signal.mux (m.odd &&& en) (rs + u) rs
    return rs
#machine_endpoint topone

theorem toptwo_callees : toptwo.machineData.shape.insts.map (·.1) = [``wrapA, ``wrapA, ``wrapB, ``wrapB] := by decide
theorem topone_callees : topone.machineData.shape.insts.map (·.1) = [``wrapA, ``wrapA] := by decide


/-! ## the generation, at the default heartbeats -/

open Lean Elab Command in
def refusalOf (decl : Name) : CommandElabM (List String × List String) := do
  let saved := (← get).messages
  let n0 := saved.toList.length
  elabCommand (← `(command| #machine_seq_parent_endpoint $(mkIdent decl)))
  let ms := ((← get).messages.toList).drop n0
  let errs ← (ms.filter (·.severity == .error)).mapM fun m => m.data.toString
  let infos ← (ms.filter (·.severity == .information)).mapM fun m => m.data.toString
  modify fun s => { s with messages := saved }
  return (errs, infos)

open Lean Elab Command in
def countDecls (decl : Name) : CommandElabM Nat := do
  return (← getEnv).constants.fold (init := (0 : Nat)) fun (n : Nat) c _ =>
    if decl.isPrefixOf c && ((c.toString.splitOn ".epK").length > 1 || (c.toString.splitOn ".epD2M").length > 1 || (c.toString.splitOn ".epD2_").length > 1) then n + 1 else n

open Lean Elab Command in
run_cmd do
  unless (maxHeartbeats.get (← getOptions)) == 200000 do throwError "SR22 AUDIT FAILED: the ambient maxHeartbeats is not the default"
  for d in [`topshare3, `topshare3off, `topshare3inj, `topshare3aud, `toptwo, `topone] do
    unless (← countDecls (N ++ d)) == 0 do throwError "SR22 AUDIT FAILED: generated declarations of {d} exist before generation"

-- (2) option OFF: the existing refusal, nothing generated; recorded for the comparison below
open Lean Elab Command in
run_cmd do
  let (errs, _) ← refusalOf (N ++ `topshare3off)
  unless errs.length == 1 do throwError "SR22 AUDIT FAILED: expected exactly one (existing) refusal of topshare3off with the option off, got {errs}"
  unless (errs.head!.splitOn "REFUSED").length > 1 do throwError "SR22 AUDIT FAILED: the existing refusal is not a REFUSED text: {errs}"
  unless (← countDecls (N ++ `topshare3off)) == 0 do throwError "SR22 AUDIT FAILED: declarations were generated with the option off"
  logInfo m!"SR22: with sparkle.karyCandidate OFF the existing elaborators REFUSE topshare3off as before: {errs.head!.take 300}…"

-- (3) the generation with the option ON (K = 3), timing logged
set_option sparkle.karyCandidate true in
set_option sparkle.sharedLeafTiming true in
open Lean Elab Command in
run_cmd do
  let t0 ← IO.monoMsNow
  let saved := (← get).messages.toList.length
  elabCommand (← `(command| #machine_seq_parent_endpoint topshare3))
  let t1 ← IO.monoMsNow
  let ms := ((← get).messages.toList).drop saved
  let txts ← ms.mapM fun m => m.data.toString
  unless (ms.filter (·.severity == .error)).isEmpty do throwError "SR22 AUDIT FAILED: error message(s) for topshare3: {(txts.take 3).map (·.take 400)}"
  unless txts.any (fun t => (t.splitOn "FAILED").length > 1 && (t.splitOn "K-ary path").length > 1) == false do throwError "SR22 AUDIT FAILED: the K-ary path FAILED for topshare3"
  let env ← getEnv
  for must in [`epK_endpoint, `epK_returned, `epK_wired, `epK_all, `epK_cs, `epK_gens, `epK_hFP, `epD2M_genP, `epD2M_leafRun] do
    unless env.contains (N ++ `topshare3 ++ must) do throwError "SR22 AUDIT FAILED: {N ++ `topshare3 ++ must} was not generated"
  for no in [`epD2M0_C_composedA, `epD2M0_C_seqChildRunN2, `epD2M_quadAll, `epD2M_endpoint] do
    if env.contains (N ++ `topshare3 ++ no) then throwError "SR22 AUDIT FAILED: {no} exists (the QUAD / pasted-block path ran)"
  logInfo m!"SR22: topshare3 generated by the K-ary path at the DEFAULT heartbeats in {t1 - t0} ms wall, peak RSS {(← Tools.ShippingSeqParentGenD2MS.peakRssKb) / 1024} MB (per-declaration heartbeats in the SR19 TIMING lines above)"

/-! ## (1) the generated types against the hand-applied declarations of SR21 and the hand-written statements -/

section
open Lean Meta Elab Command
open Tests.Compiler.KaryThreeReturnedTest (Share3Ret Share3Wired Share3Cs)
open Tests.Compiler.KaryThreeTest (Share3Full)

/-- the constants (and name literals) of the SR21 copy renamed to this file's copy -/
def renameE (e : Expr) : Expr := e.replace fun x =>
  match x with
  | .const n ls =>
    if `Tests.Compiler.KaryThreeTest |>.isPrefixOf n then
      some (.const (n.replacePrefix `Tests.Compiler.KaryThreeTest `Tests.Compiler.KaryGenTest) ls) else none
  | .lit (.strVal "KaryThreeTest") => some (.lit (.strVal "KaryGenTest"))
  | _ => none

/-- the hand-written statement definitions (to be unfolded before renaming) -/
def isShare3 (n : Name) : Bool :=
  (n.toString.startsWith "Tests.Compiler.KaryThreeTest.Share3") || (n.toString.startsWith "Tests.Compiler.KaryThreeReturnedTest.Share3")

run_cmd liftTermElabM do
  let top := N ++ `topshare3
  let top3 := ``Tests.Compiler.KaryThreeTest.topshare3
  let gen := fun (nm : Name) => do instantiateMVars (← getConstInfo (top ++ nm)).type
  let hand := fun (nm : Name) => do instantiateMVars (← getConstInfo (top3 ++ nm)).type
  let ty := mkConst ``Sparkle.IR.AST.Design
  let eqReal ← withLocalDeclD `a ty fun a => withLocalDeclD `b ty fun b => do mkLambdaFVars #[a, b] (← mkEq a b)
  let pickA ← withLocalDeclD `a ty fun a => withLocalDeclD `b ty fun b => mkLambdaFVars #[a, b] a
  let pickB ← withLocalDeclD `a ty fun a => withLocalDeclD `b ty fun b => mkLambdaFVars #[a, b] b
  let wrapC := ``Tests.Compiler.KaryThreeTest.wrapC
  let cs := mkConst ``Share3Cs
  let writtenRet := mkAppN (mkConst ``Share3Ret) #[cs, mkNatLit 0, toExpr top3, toExpr wrapC, eqReal, pickA, mkNatLit 2, mkNatLit 4]
  let writtenWired := mkAppN (mkConst ``Share3Wired) #[cs, mkNatLit 0, toExpr top3, toExpr wrapC, pickB, mkNatLit 2, mkNatLit 4]
  let writtenEp := mkConst ``Share3Full
  let ex := fun (e : Expr) => do pure (renameE (← deltaExpand e isShare3))
  for (nm, written, what) in [(`epK_endpoint, writtenEp, "endpoint"), (`epK_returned, writtenRet, "returned"), (`epK_wired, writtenWired, "wired")] do
    let g ← gen nm
    if g.hasMVar || g.hasFVar then throwError "SR22 AUDIT FAILED: metavariables / free variables in the generated {what} type"
    let h ← hand nm
    unless (← isDefEq g (renameE h)) do throwError "SR22 AUDIT FAILED: the GENERATED {what} type is not isDefEq to the (renamed) hand-applied SR21 declaration"
    unless (← isDefEq g (← ex written)) do throwError "SR22 AUDIT FAILED: the GENERATED {what} type is not isDefEq to the (renamed) hand-written statement"
  -- mutations of the endpoint's hand-written statement are rejected
  let g ← gen `epK_endpoint
  for (c, w) in [(``Tests.Compiler.KaryThreeTest.Share3FullBndTwo, "boundary: two callees"), (``Tests.Compiler.KaryThreeTest.Share3FullBndNoC, "boundary: third callee missing"),
      (``Tests.Compiler.KaryThreeTest.Share3FullBndD1, "boundary: JQC O 1"), (``Tests.Compiler.KaryThreeTest.Share3FullDepth3, "depth 3"),
      (``Tests.Compiler.KaryThreeTest.Share3FullKP3, "kP = 3"), (``Tests.Compiler.KaryThreeTest.Share3FullHrDecl, "hr synthesizes wrapA")] do
    let m ← deltaExpand (mkConst c) isShare3
    if (← isDefEq g (renameE m)) then throwError "SR22 AUDIT FAILED: the mutated endpoint type ({w}) was ACCEPTED"
  -- returned / wired mutations
  let gr ← gen `epK_returned
  let gw ← gen `epK_wired
  let csTwo ← mkAppM ``List.take #[mkNatLit 2, cs]
  for (e, w) in [(mkAppN (mkConst ``Share3Ret) #[cs, mkNatLit 1, toExpr top3, toExpr wrapC, eqReal, pickA, mkNatLit 2, mkNatLit 4], "start world JQC O 1 w"),
      (mkAppN (mkConst ``Share3Ret) #[csTwo, mkNatLit 0, toExpr top3, toExpr wrapC, eqReal, pickA, mkNatLit 2, mkNatLit 4], "callee list shortened"),
      (mkAppN (mkConst ``Share3Ret) #[cs, mkNatLit 0, toExpr top3, toExpr wrapC, eqReal, pickB, mkNatLit 2, mkNatLit 4], "DesignSemConcl of Dg")] do
    if (← isDefEq gr (← ex e)) then throwError "SR22 AUDIT FAILED: the mutated returned type ({w}) was ACCEPTED"
  for (e, w) in [(mkAppN (mkConst ``Share3Wired) #[cs, mkNatLit 1, toExpr top3, toExpr wrapC, pickB, mkNatLit 2, mkNatLit 4], "start world JQC O 1 w"),
      (mkAppN (mkConst ``Share3Wired) #[csTwo, mkNatLit 0, toExpr top3, toExpr wrapC, pickB, mkNatLit 2, mkNatLit 4], "callee list shortened"),
      (mkAppN (mkConst ``Share3Wired) #[cs, mkNatLit 0, toExpr top3, toExpr wrapC, pickA, mkNatLit 2, mkNatLit 4], "DesignSemConcl of y.2")] do
    if (← isDefEq gw (← ex e)) then throwError "SR22 AUDIT FAILED: the mutated wired type ({w}) was ACCEPTED"
  logInfo m!"SR22: the GENERATED topshare3.epK_endpoint / epK_returned / epK_wired (fresh copy) have full forall-types isDefEq to the hand-applied SR21 declarations and to the hand-written Share3Full / Share3Ret / Share3Wired (constants renamed to this copy); 6 endpoint and 3 + 3 returned / wired type-correct mutations are REJECTED"

open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  for (d, nms) in [(`topshare3, [`epK_endpoint, `epK_returned, `epK_wired])] do
    for nm in nms do
      let c := N ++ d ++ nm
      stdAxioms c
      let cl ← depClosure c
      let quadLemmas : List Name :=
        [``Tools.ShippingQuadLeafGeneric.quad_closes0, ``Tools.ShippingQuadLeafGeneric.quad_machineRun, ``Tools.ShippingQuadLeafGeneric.quad_entry_run_ret_np,
         ``Tools.ShippingQuadComposed.quad_ranA, ``Tools.ShippingQuadComposed.quad_hkid, ``Tools.ShippingQuadComposed.quad_runFacts,
         ``Tools.ShippingQuadComposed.quad_outsCheck, ``Tools.ShippingQuadComposed.quad_kidsMasked, ``Tools.ShippingQuadComposed.quad_designCheck,
         ``Tools.ShippingQuadComposed.quad_traceXA, ``Tools.ShippingQuadComposed.quad_soundLA, ``Tools.ShippingQuadCalls.quad_composed_split,
         ``Tools.ShippingQuadReturned.quad_returned, ``Tools.ShippingQuadReturned.quad_wired, ``Tools.ShippingTopShareNoParent.topshare_entry_run4_ret_np]
      for q in quadLemmas do
        if cl.contains q then throwError "SR22 AUDIT FAILED: the two-callee lemma {q} is in the closure of {c}"
      for m in [``Tools.ShippingKaryComposed.kary_soundLA, ``Tools.ShippingKaryCalls.kary_composed_split, ``Tools.ShippingKaryComposed.kary_runFacts,
          ``Tools.ShippingKaryComposed.kary_outsCheck, ``Tools.ShippingKaryComposed.kary_kidsMasked, ``Tools.ShippingKaryComposed.kary_designCheck,
          N ++ d ++ `epK_all, N ++ d ++ `epK_hFP, N ++ d ++ `epD2M_genP] do
        unless cl.contains m do throwError "SR22 AUDIT FAILED: {m} not in the closure of {c}"
      Tools.ShippingSeqParentGenD2MSK.auditK c (if nm == `epK_returned then ``Tools.ShippingKaryReturned.kary_returned
        else if nm == `epK_wired then ``Tools.ShippingKaryReturned.kary_wired else ``Tools.ShippingKaryComposed.kary_soundLA)
      logInfo m!"SR22 CLOSURE AUDIT: {c}: standard axioms, closure {cl.size} constants, none of the {quadLemmas.length} two-callee lemmas, the K-ary lemmas and the generated per-declaration facts are in it"
end

/-! ## (2) a K = 2 parent is not taken, (3) the fallback -/

open Lean Elab Command in
def norm (d : Name) (s : String) : String := s.replace d.toString "<DECL>"

-- K = 2 with the option ON: the same refusal as with the option OFF, nothing generated
open Lean Elab Command in
run_cmd do
  let (off, _) ← refusalOf (N ++ `toptwo)
  let (on, _) ← withScope (fun sc => { sc with opts := Tools.ShippingSeqParentGenD2MSK.sparkle.karyCandidate.set sc.opts true }) (refusalOf (N ++ `toptwo))
  unless off.length == 1 && (off.head!.splitOn "REFUSED").length > 1 do throwError "SR22 AUDIT FAILED: expected the existing refusal of toptwo with the option off, got {off}"
  unless on == off do throwError "SR22 AUDIT FAILED: toptwo (K = 2) was handled differently with sparkle.karyCandidate on: {on} vs {off}"
  unless (← countDecls (N ++ `toptwo)) == 0 do throwError "SR22 AUDIT FAILED: declarations were generated for the K = 2 parent"
  logInfo m!"SR22: a K = 2 parent (toptwo) is NOT taken by the K-ary generator: with the option ON the refusal is the existing one, unchanged: {off.head!.take 200}…"

-- fallback: injected failures
open Lean Elab Command in
def fallbackK (decl : Name) (inj : String) (needle : String) : CommandElabM Unit := do
  let (off, _) ← refusalOf (N ++ `topshare3off)
  let (errs, infos) ← withScope (fun sc => { sc with opts := (Tools.ShippingSeqParentGenD2MSK.sparkle.karyInject.set (Tools.ShippingSeqParentGenD2MSK.sparkle.karyCandidate.set sc.opts true) inj) }) (refusalOf (N ++ decl))
  unless infos.any (fun t => (t.splitOn "the K-ary path FAILED").length > 1) do throwError "SR22 AUDIT FAILED: no log of the K-ary path's failure ({inj}): {infos.map (·.take 200)}"
  unless infos.any (fun t => (t.splitOn needle).length > 1) do throwError "SR22 AUDIT FAILED: the log of the failure does not mention `{needle}` ({inj})"
  unless errs.length == 1 && (errs.head!.splitOn "REFUSED").length > 1 do throwError "SR22 AUDIT FAILED: expected the existing refusal after the failure ({inj}), got {errs}"
  unless errs.map (norm (N ++ decl)) == off.map (norm (N ++ `topshare3off)) do
    throwError "SR22 AUDIT FAILED: the refusal after the failure ({inj}) differs from the option-off refusal"
  unless (← countDecls (N ++ decl)) == 0 do throwError "SR22 AUDIT FAILED: declarations of {decl} survived the failed K-ary attempt ({inj})"
  logInfo m!"SR22: injected {inj} failure for {decl}: logged (`the K-ary path FAILED … {needle}`), state restored (no epK*/epD2M* constant), the existing refusal text runs, identical to the option-off text"

run_cmd do
  fallbackK `topshare3inj "decl" "epK_injected"
  fallbackK `topshare3aud "audit" "injected audit failure"

/-! ## (4) K = 1 (smoke example) -/

set_option sparkle.karyCandidate true in
open Lean Elab Command in
run_cmd do
  let saved := (← get).messages.toList.length
  elabCommand (← `(command| #machine_seq_parent_endpoint topone))
  let ms := ((← get).messages.toList).drop saved
  let txts ← ms.mapM fun m => m.data.toString
  unless (ms.filter (·.severity == .error)).isEmpty do throwError "SR22 AUDIT FAILED: error message(s) for topone: {(txts.take 3).map (·.take 400)}"
  if txts.any (fun t => (t.splitOn "K-ary path FAILED").length > 1) then throwError "SR22 AUDIT FAILED: the K-ary path FAILED for topone"
  let env ← getEnv
  for must in [`epK_endpoint, `epK_returned, `epK_wired] do
    unless env.contains (N ++ `topone ++ must) do throwError "SR22 AUDIT FAILED: topone.{must} was not generated"

theorem topone_cs : (Tests.Compiler.KaryGenTest.topone.epK_cs).map (·.c) = [``Tests.Compiler.KaryGenTest.wrapA] := by decide

open Tests.Compiler.ChildVertAuditTest in
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for (nm, lem) in [(`epK_endpoint, ``Tools.ShippingKaryComposed.kary_soundLA), (`epK_returned, ``Tools.ShippingKaryReturned.kary_returned),
      (`epK_wired, ``Tools.ShippingKaryReturned.kary_wired)] do
    let c := N ++ `topone ++ nm
    stdAxioms c
    Tools.ShippingSeqParentGenD2MSK.auditK c lem
  logInfo m!"SR22: the K = 1 parent topone: endpoint / returned / wired generated, standard axioms, closure audit (smoke example, not compared with a hand-written statement)"

end Tests.Compiler.KaryGenTest
end
