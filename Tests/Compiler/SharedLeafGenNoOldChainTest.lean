import Tests.Compiler.QuadCallsTest
import Tests.Compiler.SharedLeafGenTest
import Tests.Compiler.SharedLeafGenTopshareTest
import Tests.Compiler.ChildVertAuditTest
import Tools.ShippingSeqParentGenD2MS
-- BUILT (unit SR20): n5 exit 0 (dev run on the dirty tree); the final-SHA rebuild is in REPORT-SR20.md.
-- SCOPE (binding, ledger L8az): the generic-lemma path of the opt-in shared-leaf generator (`sparkle.sharedLeafCandidate`, default false) on FRESH copies of the two accepted examples
-- (`topshare2`: callees `wrapQ`/`wrapP`, leaf `leaf16`; `topshare`: callees `wrap`/`wrap3`, leaf `acc`) in a file where the old chain `#machine_design_svNR` is NEVER run: no
-- `machine_composedNR*` / `seq_child_runN_ofR1` exists for any of them (asserted).  Only `#machine_endpoint` (which produces the machine data, `machine_ok`, `machine_body`, …) runs before the
-- generating command.  No `maxHeartbeats` option anywhere (default 200000).  The instance → group partition is computed by the generator from the generated `machineExt`/`machineExtB`.
-- Checked: (1) the generic path (not a fallback) produced the declarations; (2) the generated facts are `isDefEq` to the independent HAND-WRITTEN statements of `QuadCallsTest` /
-- `QuadComposedTest` / `SharedLeafGenTest` (which speak about the ORIGINAL declarations), transported to the fresh copies by renaming the declaration names (constants and `Name`
-- literals) — the copies are textually the same definitions; type-correct mismatched pairs are rejected; (3) the FULL forall-type of both endpoints against the hand-written
-- `ShareFull` / `topshare_noShips_noBd_dc` (renamed) with type-correct mutations; (4) closure audit; (5) a fresh parent with an INJECTED failing declaration and no old chain: the
-- failure is logged, nothing is kept, and the pre-existing elaborators then run (their own shared-leaf refusal).
-- NOT claimed: anything about parents outside the stated class; the facts are per-declaration kernel-checked, not a class theorem.  Two examples do not make the class complete.
section
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
namespace Tests.Compiler.SharedLeafGenNoOldChainTest

abbrev N := `Tests.Compiler.SharedLeafGenNoOldChainTest

/-! ## fresh copies (definitions textually equal to the originals) -/

@[hardware_module] def leaf16 {dom : DomainConfig} (x : Signal dom (BitVec 16)) : Tests.Compiler.SharedLeafGenTest.Acc16Out dom :=
  circuit do
    let a ← Signal.reg 0#16
    let as := (a : Signal dom (BitVec 16))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 5#16 : Signal dom (BitVec 16)) } : Tests.Compiler.SharedLeafGenTest.Acc16Out dom)

@[hardware_module] def wrapQ {dom : DomainConfig} (x y : Signal dom (BitVec 16)) : Tests.Compiler.SharedLeafGenTest.Acc16Out dom :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal dom (BitVec 16))
    let a := leaf16 (x + y)
    r <~ a.s + x
    return ({ s := rs, odd := a.odd } : Tests.Compiler.SharedLeafGenTest.Acc16Out dom)

@[hardware_module] def wrapP {dom : DomainConfig} (x y : Signal dom (BitVec 16)) : Tests.Compiler.SharedLeafGenTest.Acc16Out dom :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal dom (BitVec 16))
    let a := leaf16 x
    let b := leaf16 y
    r <~ a.s + b.s
    return ({ s := rs, odd := a.odd &&& b.odd } : Tests.Compiler.SharedLeafGenTest.Acc16Out dom)

def topshare2 (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapQ v w
    let m2 := wrapP w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topshare2

@[hardware_module] def acc {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut dom :=
  circuit do
    let a ← Signal.reg 0#8
    let as := (a : Signal dom (BitVec 8))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 1#8 : Signal dom (BitVec 8)) } : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut dom)

@[hardware_module] def wrap {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := acc y
    r <~ a.s + x
    return ({ s := rs, odd := a.odd } : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut dom)

@[hardware_module] def wrap3 {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := acc x
    r <~ a.s + y
    return ({ s := rs, odd := a.odd } : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut dom)

def topshare (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrap v w
    let m2 := wrap3 w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topshare

-- a third parent over the copies of topshare2's callees, for the injected-failure check (5)
def topshare2x (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapQ v w
    let m2 := wrapP w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topshare2x

/-! ## (0) NO old generated chain exists for any of them -/

run_cmd liftTermElabM do
  let env ← getEnv
  for n in [`topshare2, `topshare, `topshare2x] do
    if env.contains (N ++ n ++ `machine_composedNR2) then throwError "SR20 AUDIT FAILED: the old chain exists for {n}"
  for n in [`wrapQ, `wrapP, `wrap, `wrap3] do
    if env.contains (N ++ n ++ `machine_composedNR1) || env.contains (N ++ n ++ `seq_child_runN_ofR1) then throwError "SR20 AUDIT FAILED: the old chain exists for {n}"
  -- the pieces the machine route reads exist
  for n in [`topshare2, `topshare, `wrapQ, `wrapP, `wrap, `wrap3] do
    for s in [`machineData, `machineExt, `machineExtB, `machine_ok, `machine_body] do
      unless env.contains (N ++ n ++ s) do throwError "SR20 AUDIT FAILED: {N ++ n ++ s} missing (the machine route needs it)"
  for n in [`leaf16, `acc] do
    for s in [`machineData, `machine_ok, `machine_body, `machine_closes] do
      unless env.contains (N ++ n ++ s) do throwError "SR20 AUDIT FAILED: {N ++ n ++ s} missing (the machine route needs it)"
  for n in [`leaf16, `acc] do
    if env.contains (N ++ n ++ `seq_child_runN) then throwError "SR20 AUDIT FAILED: {n}.seq_child_runN exists before the generation (the generator must create it)"
  logInfo m!"SR20: no old chain (machine_composedNR*, seq_child_runN_ofR1) exists for the fresh copies"

/-! ## the generation (no old chain, no heartbeat option) -/

open Lean Elab Command in
def genNoOld (decl : Name) : CommandElabM Unit := do
  let some p ← Tools.ShippingSeqParentGenD2MS.analyseG decl | throwError "SR20 AUDIT FAILED: {decl} is not in the class"
  let gi ← Tools.ShippingSeqParentGenD2MS.genInfoS p
  let gtxt := Tools.ShippingSeqParentGenD2MS.assembleMS p (some gi)
  for bad in ["maxHeartbeats", "oldGroupFact%", "oldInst%", "oldNamed%", "machine_composedNR", "seq_child_runN_ofR"] do
    if (gtxt.splitOn bad).length > 1 then throwError "SR20 AUDIT FAILED: the generic path's text mentions `{bad}`"
  -- the analysis without the old chain must refuse nothing here, and the old-chain analysis must not apply (no chain)
  let old ← try (pure (some (← Tools.ShippingSeqParentGenD2MS.analyseS decl))) catch _ => pure none
  if old.isSome then throwError "SR20 AUDIT FAILED: the old-chain analysis succeeded without an old chain"
  let saved := (← get).messages.toList.length
  elabCommand (← `(command| set_option sparkle.sharedLeafCandidate true in set_option sparkle.sharedLeafTiming true in
    #machine_seq_parent_endpoint $(mkIdent decl)))
  let ms := (← get).messages.toList.drop saved
  let txts ← ms.mapM fun m => m.data.toString
  for t in txts do
    if (t.splitOn "generic-lemma path FAILED").length > 1 then throwError "SR20 AUDIT FAILED: the generic path fell back / failed for {decl}: {t.take 3000}"
  unless (ms.filter (·.severity == .error)).isEmpty do throwError "SR20 AUDIT FAILED: error(s) while generating {decl}: {(txts.map (·.take 300)).take 3}"
  unless txts.any (fun t => (t.splitOn "old chain absent or unusable").length > 1) do throwError "SR20 AUDIT FAILED: the generator did not report the absent old chain"
  let env ← getEnv
  for must in [`epD2M_endpoint, `epD2M_hFP, `epD2M0_C_hF, `epD2M1_C_hF, `epD2M_hPoint0, `epD2M_returned, `epD2M_wired] do
    unless env.contains (decl ++ must) do throwError "SR20 AUDIT FAILED: {decl ++ must} missing"
  for no in [`epD2M0_C_composedA, `epD2M1_C_composedA] do
    if env.contains (decl ++ no) then throwError "SR20 AUDIT FAILED: the pasted block {decl ++ no} exists"
  let timing := txts.filter fun t => (t.splitOn "SR19 TIMING").length > 1
  unless timing.length > 20 do throwError "SR20 AUDIT FAILED: only {timing.length} timing lines for {decl}"
  let mut maxHb := 0
  for t in timing do
    let n := ((t.drop ((t.splitOn "heartbeats ").head!.length + 11)).takeWhile Char.isDigit).toString.toNat!
    if n > maxHb then maxHb := n
  logInfo m!"SR20: {decl}: generic path WITHOUT the old chain, {timing.length} generated declarations timed, max {maxHb} heartbeat units of the default limit 200000 (no maxHeartbeats option); partition {p.instGroup}: {p.partitionNote}"

run_cmd do
  unless (maxHeartbeats.get (← getOptions)) == 200000 do throwError "SR20 AUDIT FAILED: the ambient maxHeartbeats is not the default"
  genNoOld ``Tests.Compiler.SharedLeafGenNoOldChainTest.topshare2
  genNoOld ``Tests.Compiler.SharedLeafGenNoOldChainTest.topshare

/-! ## (2) the generated facts equal the hand-written statements of the originals, transported by renaming -/

/-- (old, new) roots of the renaming: the original declarations and their fresh copies -/
def renMap : List (Name × Name) :=
  [(`Tests.Compiler.SharedLeafGenTest.leaf16, N ++ `leaf16), (`Tests.Compiler.SharedLeafGenTest.wrapQ, N ++ `wrapQ),
   (`Tests.Compiler.SharedLeafGenTest.wrapP, N ++ `wrapP), (`Tests.Compiler.SharedLeafGenTest.topshare2, N ++ `topshare2),
   (`Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc, N ++ `acc), (`Tests.Compiler.SeqDeepGenInstTest.wrap, N ++ `wrap),
   (`Tests.Compiler.SeqDeepGenDiffTest.wrap3, N ++ `wrap3), (`Tests.Compiler.SeqDeepGenDiffTest.topshare, N ++ `topshare)]

def renName (n : Name) : Name :=
  match renMap.find? (·.1.isPrefixOf n) with
  | some (o, nw) => n.replacePrefix o nw
  | none => n

/-- read a closed `Name` literal as elaborated by ``` `` ``` -/
partial def readNameLit : Expr → Option Name
  | .const ``Lean.Name.anonymous _ => some .anonymous
  | e =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n _ =>
      if n == ``Lean.Name.str && args.size == 2 then
        match readNameLit args[0]!, args[1]! with
        | some p, .lit (.strVal s) => some (.str p s)
        | _, _ => none
      else if (n.getPrefix == `Lean.Name) && (n.getString!.startsWith "mkStr") && args.size > 0 && args.size ≤ 8 then
        args.foldlM (fun p a => match a with | .lit (.strVal s) => some (Name.str p s) | _ => none) Name.anonymous
      else none
    | _ => none

def renExpr (e : Expr) : Expr :=
  e.replace fun x =>
    match x with
    | .const n ls => if renName n != n then some (.const (renName n) ls) else none
    | .app .. =>
      match readNameLit x with
      | some n => if renName n != n then some (toExpr (renName n)) else none
      | none => none
    | _ => none

/-- does the term mention a renamed declaration (as a constant or as a `Name` literal)? -/
def mentionsRen (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .const n _ => renMap.any (·.1.isPrefixOf n)
    | .app .. => (readNameLit x).any fun n => renName n != n
    | _ => false).isSome

/-- the `Tests.*` definitions reachable from `e` that (transitively) mention a renamed declaration in their bodies: the hand-written statements are built from such helper
definitions (`ShareBnd`, …), which speak about the ORIGINAL declarations and must be unfolded before the renaming -/
partial def helpersToUnfold (e : Expr) : MetaM (List Name) := do
  let env ← getEnv
  let mut reach : Array Name := #[]
  let mut todo : List Name := e.getUsedConstants.toList.filter (`Tests).isPrefixOf
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if reach.contains c || renMap.any (·.1.isPrefixOf c) then continue
    reach := reach.push c
    if let some (.defnInfo d) := env.find? c then
      todo := todo ++ d.value.getUsedConstants.toList.filter (`Tests).isPrefixOf
  let mut S : List Name := []
  let mut changed := true
  while changed do
    changed := false
    for c in reach do
      if S.contains c then continue
      if let some (.defnInfo d) := env.find? c then
        if mentionsRen d.value || d.value.getUsedConstants.any S.contains then
          S := c :: S
          changed := true
  return S

/-- rename AFTER unfolding the helper definitions that mention the renamed declarations -/
def renDeep (e : Expr) : MetaM Expr := do
  let mut e ← instantiateMVars e
  for _ in List.range 30 do
    let S ← helpersToUnfold e
    if S.isEmpty then break
    e ← Meta.deltaExpand e S.contains
  pure (renExpr e)

def tyOf (n : Name) : MetaM Expr := do pure (← getConstInfo n).type
def hand (n : Name) : MetaM Expr := do renDeep (← getConstInfo n).type

def T2 := N ++ `topshare2
def T1 := N ++ `topshare
def QC := `Tests.Compiler.QuadCallsTest
def QD := `Tests.Compiler.QuadComposedTest

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let ok : List (Name × Name) :=
    [(T2 ++ `epD2M0_C_hF, QC ++ `b_wrapQ_hF), (T2 ++ `epD2M1_C_hF, QC ++ `b_wrapP_hF), (T2 ++ `epD2M_hFP, QC ++ `b_topshare2_hFP),
     (T2 ++ `epD2M0_C_hextB, QC ++ `b_wrapQ_hextB), (T2 ++ `epD2M0_C_hext, QC ++ `b_wrapQ_hext),
     (T2 ++ `epD2M1_C_hextB, QC ++ `b_wrapP_hextB), (T2 ++ `epD2M1_C_hext, QC ++ `b_wrapP_hext),
     (T2 ++ `epD2M_genP, QC ++ `b_gen), (T2 ++ `epD2M0_C_gen, QC ++ `b_wrapQ_gen), (T2 ++ `epD2M1_C_gen, QC ++ `b_wrapP_gen),
     (T2 ++ `epD2M_leafRun, QC ++ `b_leaf_run), (T2 ++ `epD2M_quadAll, QC ++ `b_quadAll),
     (T1 ++ `epD2M0_C_hF, QC ++ `a_wrap_hF), (T1 ++ `epD2M1_C_hF, QC ++ `a_wrap3_hF), (T1 ++ `epD2M_hFP, QC ++ `a_topshare_hFP),
     (T1 ++ `epD2M0_C_hextB, QD ++ `wrap_hextB), (T1 ++ `epD2M0_C_hext, QD ++ `wrap_hext),
     (T1 ++ `epD2M1_C_hextB, QD ++ `wrap3_hextB), (T1 ++ `epD2M1_C_hext, QD ++ `wrap3_hext),
     (T1 ++ `epD2M_genP, QD ++ `topshare_gen), (T1 ++ `epD2M0_C_gen, QD ++ `wrap_gen), (T1 ++ `epD2M1_C_gen, QD ++ `wrap3_gen),
     (T1 ++ `epD2M_leafRun, QC ++ `a_acc_run), (T1 ++ `epD2M_quadAll, QD ++ `topshare_quadAll)]
  for (g, h) in ok do
    unless (← getEnv).contains g do throwError "SR20 AUDIT FAILED: the generator did not emit {g}"
    unless (← isDefEq (← tyOf g) (← hand h)) do throwError "SR20 AUDIT FAILED: the generated {g} differs from the (renamed) hand-written {h}"
  -- the renaming is not vacuous: the un-renamed hand-written statement is about the ORIGINAL declarations and is not defeq
  for (g, h) in [(T2 ++ `epD2M_hFP, QC ++ `b_topshare2_hFP), (T1 ++ `epD2M0_C_hF, QC ++ `a_wrap_hF)] do
    if (← isDefEq (← tyOf g) (← instantiateMVars (← getConstInfo h).type)) then throwError "SR20 AUDIT FAILED: {g} ≡ the un-renamed {h} (the renaming would prove nothing)"
  let bad : List (Name × Name) :=
    [(T2 ++ `epD2M0_C_hF, QC ++ `b_wrapP_hF), (T2 ++ `epD2M1_C_hF, QC ++ `b_wrapQ_hF), (T2 ++ `epD2M_hFP, QC ++ `b_wrapQ_hF),
     (T2 ++ `epD2M0_C_hext, QC ++ `b_wrapP_hext), (T2 ++ `epD2M1_C_hextB, QC ++ `b_wrapQ_hextB),
     (T2 ++ `epD2M0_C_hext, QC ++ `b_wrapQ_hextB), (T2 ++ `epD2M_genP, QC ++ `b_wrapQ_gen), (T2 ++ `epD2M0_C_gen, QC ++ `b_wrapP_gen),
     (T1 ++ `epD2M0_C_hF, QC ++ `a_wrap3_hF), (T1 ++ `epD2M1_C_hF, QC ++ `a_wrap_hF), (T1 ++ `epD2M_hFP, QC ++ `a_wrap_hF),
     (T1 ++ `epD2M0_C_hext, QD ++ `wrap3_hext), (T1 ++ `epD2M1_C_hextB, QD ++ `wrap_hextB), (T1 ++ `epD2M_genP, QD ++ `wrap_gen),
     (T1 ++ `epD2M_quadAll, QC ++ `b_quadAll), (T2 ++ `epD2M_quadAll, QD ++ `topshare_quadAll)]
  for (g, h) in bad do
    if (← isDefEq (← tyOf g) (← hand h)) then throwError "SR20 AUDIT FAILED: the statements of {g} and {h} were judged equal (the audit would not discriminate)"
  logInfo m!"SR20: {ok.length} GENERATED facts of the no-old-chain topshare / topshare2 copies are isDefEq to the (renamed) hand-written statements; {bad.length} type-correct mismatched pairs are REJECTED"

/-! ## (3) FULL forall-types of both endpoints, mutations -/

def modDom (e : Expr) : Nat → (Expr → Expr) → Expr
  | 0, f => match e with | .forallE nm t b bi => .forallE nm (f t) b bi | e => e
  | n+1, f => match e with | .forallE nm t b bi => .forallE nm t (modDom b n f) bi | e => e

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  -- topshare: against the hand-pasted `topshare_noShips_noBd_dc`
  let gt ← instantiateMVars (← getConstInfo (T1 ++ `epD2M_endpoint)).type
  let old ← hand ``Tests.Compiler.TopShareComposedTest.topshare_noShips_noBd_dc
  unless (← isDefEq gt old) do throwError "SR20 AUDIT FAILED: the FULL type of the generated topshare endpoint differs from the (renamed) hand-pasted topshare_noShips_noBd_dc"
  let nm := toExpr T1
  let other := toExpr (N ++ `wrap)
  let swap := fun (e : Expr) => e.replace fun x => if x == nm then some other else none
  let names ← forallTelescope gt fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
  unless names == ["mctx", "mref", "cctx", "cref", "w", "w'", "b", "design", "hr", "entry", "closes"] do throwError "SR20 AUDIT FAILED: binder names {names}"
  let muts : List (Expr × String) :=
    [(modDom gt 8 swap, "hr synthesizes wrap"), (modDom gt 9 swap, "entry is for wrap"),
     (modDom gt 10 (fun _ => mkConst ``False), "closes : False"),
     ((← getConstInfo (T2 ++ `epD2M_endpoint)).type, "the endpoint of topshare2")]
  for (m, w) in muts do
    if m.hasMVar || m.hasFVar then throwError "SR20 AUDIT FAILED: mvars/fvars in mutation {w}"
    Meta.check m
    unless (← Meta.isProp m) do throwError "SR20 AUDIT FAILED: mutation {w} is not a Prop"
    if (← isDefEq gt m) then throwError "SR20 AUDIT FAILED: the mutated full type ({w}) was ACCEPTED"
  -- topshare2: against the hand-written `ShareFull` (+ its mutations), renamed
  let g2 ← instantiateMVars (← getConstInfo (T2 ++ `epD2M_endpoint)).type
  let unfold (n : Name) : MetaM Expr := do
    let some v := (← getConstInfo n).value? | throwError "{n} has no value"
    pure v
  let sf ← unfold ``Tests.Compiler.SharedLeafGenTest.ShareFull
  let sfR ← renDeep sf
  unless (← isDefEq g2 sfR) do throwError "SR20 AUDIT FAILED: the FULL type of the generated topshare2 endpoint differs from the (renamed) hand-written ShareFull"
  let mut cnt := 0
  for mn in [``Tests.Compiler.SharedLeafGenTest.ShareFullHrDecl, ``Tests.Compiler.SharedLeafGenTest.ShareFullEnDecl] do
    let m ← renDeep (← unfold mn)
    if (← isDefEq g2 m) then throwError "SR20 AUDIT FAILED: the mutation {mn} was ACCEPTED"
    cnt := cnt + 1
  for (m, w) in [(modDom g2 8 (fun _ => mkConst ``False), "hr : False"), (modDom g2 9 (fun _ => mkConst ``False), "entry : False"),
                 (modDom g2 10 (fun _ => mkConst ``False), "closes : False"), (gt, "the endpoint of topshare")] do
    Meta.check m
    if (← isDefEq g2 m) then throwError "SR20 AUDIT FAILED: the mutated full type ({w}) was ACCEPTED"
    cnt := cnt + 1
  logInfo m!"SR20: the FULL forall-types of BOTH generated endpoints (no old chain) are isDefEq to the (renamed) hand-written ones; {muts.length + cnt} type-correct mutations REJECTED"

/-! ## (4) closure audit -/

open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  for (P, Cs) in [(T2, [N ++ `wrapQ, N ++ `wrapP]), (T1, [N ++ `wrap, N ++ `wrap3])] do
    let ep := P ++ `epD2M_endpoint
    stdAxioms ep
    let cl ← depClosure ep
    let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
      `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
    let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad.isEmpty do throwError "SR20 AUDIT FAILED: old boundary / old child predicate in the closure of {ep}: {bad}"
    -- no constant of the closure is an old generated chain theorem (none exists)
    let oldish := cl.toList.filter fun c => (c.toString.splitOn "machine_composedNR").length > 1 || (c.toString.splitOn "seq_child_runN_ofR").length > 1
    unless oldish.isEmpty do throwError "SR20 AUDIT FAILED: old generated chain theorem(s) in the closure of {ep}: {oldish}"
    let pasted : List Name := (List.range 2).flatMap fun i =>
      [P ++ Name.mkSimple s!"epD2M{i}_C_composedA", P ++ Name.mkSimple s!"epD2M{i}_C_seqChildRunN2", P ++ Name.mkSimple s!"epD2M{i}_C_kidFactsA",
       P ++ Name.mkSimple s!"epD2M{i}_C_closesA", P ++ Name.mkSimple s!"epD2M{i}_C_hcalls", P ++ Name.mkSimple s!"epD2M{i}_C_traceXA",
       P ++ Name.mkSimple s!"epD2M{i}_G_kidFactsA"] ++ [P ++ `epD2M_closesA, P ++ `epD2M_disj]
    for n in pasted do
      if (← getEnv).contains n then throwError "SR20 AUDIT FAILED: the pasted block {n} exists"
    let must : List Name :=
      [``Tools.ShippingQuadCalls.quad_composed_split, ``Tools.ShippingQuadCalls.leafCallee_hcalls, ``Tools.ShippingQuadHPoint.callFactF_of_hPointAt,
       ``Tools.ShippingQuadCallFacts.callFactF_of_fam, ``Tools.ShippingQuadComposed.quad_ranA,
       ``Tools.ShippingQuadComposed.quad_runFacts, ``Tools.ShippingQuadLeafGeneric.quad_closes0, ``Tools.ShippingTopShareRan.machineRanA_start0,
       P ++ `epD2M_quadAll, P ++ `epD2M_genP, P ++ `epD2M_leafRun, P ++ `epD2M_hFP, P ++ `epD2M0_C_hF, P ++ `epD2M1_C_hF,
       P ++ `epD2M0_C_hextB, P ++ `epD2M1_C_hext, P ++ `epD2M0_C_hPoint0, P ++ `epD2M_hPoint0, P ++ `epD2M_composedA, P ++ `epD2M_soundLA]
    for m in must do
      unless cl.contains m do throwError "SR20 AUDIT FAILED: {m} not in the closure of {ep}"
    logInfo m!"SR20 CLOSURE AUDIT: {ep}: standard axioms; closure {cl.size} constants; no old boundary / child predicate; no old generated chain theorem; no pasted per-callee block; the generic lemmas and the generated per-declaration facts are in it; callees {Cs}"

/-! ## (5) no old chain AND a failing generated declaration: logged, nothing kept, then the pre-existing elaborators run -/

open Lean Elab Command in
run_cmd do
  let decl := N ++ `topshare2x
  let saved := (← get).messages
  elabCommand (← `(command| set_option sparkle.sharedLeafCandidate true in set_option sparkle.sharedLeafInject "decl" in
    #machine_seq_parent_endpoint $(mkIdent decl)))
  let ms := (← get).messages.toList.drop saved.toList.length
  let txts ← ms.mapM fun m => m.data.toString
  modify fun s => { s with messages := saved }
  let has := fun (n : String) => txts.any fun t => (t.splitOn n).length > 1
  -- the failure of the generic path is LOGGED (as info), and says that there is no SR13 fallback
  unless ms.any (fun m => m.severity == .information) && has "generic-lemma path FAILED" && has "epD2M_injected" && has "NO old chain: no SR13 fallback" do
    throwError "SR20 AUDIT FAILED: the failure of the generic path was not logged as expected: {(txts.map (·.take 300))}"
  -- this elaborator itself refuses nothing: the only error is the PRE-EXISTING elaborators' shared-leaf refusal (unit SR3x text), reached by `unsupportedSyntax`
  let errs ← ms.filterM fun m => pure (m.severity == .error)
  let etxt ← errs.mapM fun m => m.data.toString
  unless etxt.length == 1 && (etxt.head!.splitOn "unit SR3w").length > 1 && (etxt.head!.splitOn "SAME leaf").length > 1 && (etxt.head!.splitOn "SHARED-LEAF CANDIDATE").length == 1 do
    throwError "SR20 AUDIT FAILED: expected exactly the pre-existing path's refusal, got {etxt}"
  -- nothing of the failed attempt is kept
  let env ← getEnv
  let n := env.constants.fold (init := (0 : Nat)) fun n c _ => if decl.isPrefixOf c && (c.toString.splitOn ".epD2M").length > 1 then n + 1 else n
  unless n == 0 do throwError "SR20 AUDIT FAILED: {n} epD2M declaration(s) of {decl} survived"
  let inj := env.constants.fold (init := (0 : Nat)) fun n c _ => if (c.toString.splitOn "injected").length > 1 then n + 1 else n
  unless inj == 0 do throwError "SR20 AUDIT FAILED: {inj} declaration(s) named `injected` exist"
  logInfo m!"SR20: no old chain + failing generic path: the failure is logged (no SR13 fallback exists), nothing is kept, the pre-existing elaborators then ran (their shared-leaf refusal); the new elaborator itself raised no error"

end Tests.Compiler.SharedLeafGenNoOldChainTest
end
