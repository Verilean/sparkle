import Tests.Compiler.QuadCallsTest
import Tests.Compiler.SharedLeafGenTopshareTest
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit SR18): h7 exit 0 (dev run; includes the rebuilt QuadCallsTest); the final-SHA rebuild is in REPORT-SR18.md.
-- SCOPE (binding, ledger L8ax): what the opt-in shared-leaf generator (`sparkle.sharedLeafCandidate`, default false) now EMITS for the two accepted declarations `topshare` (callees `wrap`,
-- `wrap3`, leaf `acc`) and `topshare2` (callees `wrapQ`, `wrapP`, leaf `leaf16`): per-call `HPointAt` theorems, `hF` / `hFP` (`callFactF_of_hPointAt`), `hext` / `hextB`, `GenFacts`, the leaf run,
-- the data bundle `QuadAll`, and an endpoint whose proof is the generic lemmas (`quad_composed_split` …).  Every one of these is a theorem checked by the KERNEL when the generator elaborates it;
-- they are facts about THESE declarations, produced per declaration — NOT a theorem over the class.  Here: (1) each generated statement is `isDefEq` to the HAND-WRITTEN statement of
-- `QuadCallsTest` / `QuadComposedTest` (written independently of the generator), with type-correct mismatch pairs that are REJECTED; (2) the `HPointAt` statement of three calls is `isDefEq` to a
-- hand-written unfolded statement; (3) the exact number of per-call theorems; (4) FULL forall-type audit of the topshare endpoint against the hand-pasted `topshare_noShips_noBd_dc` with
-- mutations (the topshare2 full-type audit with 7 mutations is in `SharedLeafGenTest`); (5) closure audit of BOTH endpoints: the generic lemmas and the generated facts are in the closure, no
-- pasted per-callee block exists or is in the closure, no old generated `machine_composedNR*` / `seq_child_runN_ofR1`.  RealChildA / ServedRealA are histories of past synthesis results.
-- No sorry / axiom / native_decide; no heartbeat raise beyond the scoped `set_option … in` of the audit commands below (never 0 on a proof).
section
open Tools.ShippingQuadCalls Tools.ShippingQuadComposed Tools.ShippingQuadCallFacts
open Tools.ShippingMachineCausal Tools.ShippingMachineSource Tools.ShippingMachineAuto
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Lean Elab Command Meta
namespace Tests.Compiler.SharedLeafGenFactsTest

/-! ## (1) generated statements = hand-written statements -/

def T2 := `Tests.Compiler.SharedLeafGenTest.topshare2
def T1 := `Tests.Compiler.SeqDeepGenDiffTest.topshare
def QC := `Tests.Compiler.QuadCallsTest
def QD := `Tests.Compiler.QuadComposedTest

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let ty (n : Name) : MetaM Expr := do pure (← getConstInfo n).type
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
    unless (← getEnv).contains g do throwError "SR18 AUDIT FAILED: the generator did not emit {g}"
    unless (← isDefEq (← ty g) (← ty h)) do throwError "SR18 AUDIT FAILED: the generated {g} differs from the hand-written {h}"
  -- mismatches (type-correct, different callee / instance): must NOT be defeq
  let bad : List (Name × Name) :=
    [(T2 ++ `epD2M0_C_hF, QC ++ `b_wrapP_hF), (T2 ++ `epD2M1_C_hF, QC ++ `b_wrapQ_hF), (T2 ++ `epD2M_hFP, QC ++ `b_wrapQ_hF),
     (T2 ++ `epD2M0_C_hext, QC ++ `b_wrapP_hext), (T2 ++ `epD2M1_C_hextB, QC ++ `b_wrapQ_hextB),
     (T2 ++ `epD2M0_C_hext, QC ++ `b_wrapQ_hextB), (T2 ++ `epD2M_genP, QC ++ `b_wrapQ_gen), (T2 ++ `epD2M0_C_gen, QC ++ `b_wrapP_gen),
     (T1 ++ `epD2M0_C_hF, QC ++ `a_wrap3_hF), (T1 ++ `epD2M1_C_hF, QC ++ `a_wrap_hF), (T1 ++ `epD2M_hFP, QC ++ `a_wrap_hF),
     (T1 ++ `epD2M0_C_hext, QD ++ `wrap3_hext), (T1 ++ `epD2M1_C_hextB, QD ++ `wrap_hextB), (T1 ++ `epD2M_genP, QD ++ `wrap_gen),
     (T1 ++ `epD2M_quadAll, QC ++ `b_quadAll), (T2 ++ `epD2M_quadAll, QD ++ `topshare_quadAll)]
  for (g, h) in bad do
    if (← isDefEq (← ty g) (← ty h)) then throwError "SR18 AUDIT FAILED: the statements of {g} and {h} were judged equal (the audit would not discriminate)"
  logInfo m!"SR18: {ok.length} GENERATED facts (hF, hFP, hext, hextB, GenFacts, leaf run, QuadAll) of topshare and topshare2 are isDefEq to the hand-written statements; {bad.length} type-correct mismatched pairs are REJECTED"

/-! ## (2) the per-call `HPointAt` statement, hand-written unfolded, for three calls -/

open Tests.Compiler.SharedLeafGenTest in
def hpWrapQ1 : Prop :=
  ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n))
    (hk : 1 < wrapQ.machineData.shape.insts.length),
    ∃ (A : Nat → Signal i Bool) (B : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
      Tools.ShippingMachineChild.boolsOf (D := i) leaf16.machineData.bsIn
        (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB wrapQ.machineData (fun i : DomainConfig => i) wrapQ.machineInits wrapQ.machineBody wrapQ.machineExt wrapQ.machineExtB i bools bits)
          (wrapQ.machineData.shape.insts[1]).2.1) = A ∧
      Tools.ShippingMachineChild.bitsOf (D := i) leaf16.machineData.bsIn
        (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB wrapQ.machineData (fun i : DomainConfig => i) wrapQ.machineInits wrapQ.machineBody wrapQ.machineExt wrapQ.machineExtB i bools bits)
          (wrapQ.machineData.shape.insts[1]).2.1) = B ∧
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
        (leafOutsC ``leaf16 leaf16.machineData (wrapQ.machineData.shape.insts[1]).1)[k']? = some o ∧
        o.name = wrapQ.machineData.shape.instFields.getD 1 "" ∧
        (leafSrcA ``leaf16 leaf16.machineSource i (wrapQ.machineData.shape.insts[1]).1 A B)[k']? = some f ∧
        ∀ τ, Tools.ShippingMachineEntry.posEnc
          (fun p => ((wrapQ.machineExtB i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits))) p).val τ)
          (fun p n => ((wrapQ.machineExt i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits))) p n).val τ)
          (3 + 1) (((wrapQ.machineData.bsIn.drop 3)[1]?.map (·.2)).getD .domain) = f τ

open Tests.Compiler.SharedLeafGenTest in
def hpTop2_3 : Prop :=
  ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool) (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
    (hk : 3 < topshare2.machineData.shape.insts.length),
    ∃ (A : Nat → Signal defaultDomain Bool) (B : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n)),
      Tools.ShippingMachineChild.boolsOf (D := defaultDomain)
        (quadBsOf ``wrapQ ``wrapP wrapQ.machineData wrapP.machineData 3 3 (topshare2.machineData.shape.insts[3]).1)
        (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB topshare2.machineData (fun _ : Unit => defaultDomain) topshare2.machineInits topshare2.machineBody topshare2.machineExt topshare2.machineExtB i bools bits)
          (topshare2.machineData.shape.insts[3]).2.1) = A ∧
      Tools.ShippingMachineChild.bitsOf (D := defaultDomain)
        (quadBsOf ``wrapQ ``wrapP wrapQ.machineData wrapP.machineData 3 3 (topshare2.machineData.shape.insts[3]).1)
        (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB topshare2.machineData (fun _ : Unit => defaultDomain) topshare2.machineInits topshare2.machineBody topshare2.machineExt topshare2.machineExtB i bools bits)
          (topshare2.machineData.shape.insts[3]).2.1) = B ∧
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
        (quadOutsOf ``wrapQ ``wrapP wrapQ.machineData wrapP.machineData (topshare2.machineData.shape.insts[3]).1)[k']? = some o ∧
        o.name = topshare2.machineData.shape.instFields.getD 3 "" ∧
        (quadSrcA ``wrapQ ``wrapP wrapQ.machineSource wrapP.machineSource i (topshare2.machineData.shape.insts[3]).1 A B)[k']? = some f ∧
        ∀ τ, Tools.ShippingMachineEntry.posEnc
          (fun p => ((topshare2.machineExtB i bools bits (stateLoop topshare2.machineInits (topshare2.machineBody i bools bits))) p).val τ)
          (fun p n => ((topshare2.machineExt i bools bits (stateLoop topshare2.machineInits (topshare2.machineBody i bools bits))) p n).val τ)
          (3 + 3) (((topshare2.machineData.bsIn.drop 3)[3]?.map (·.2)).getD .domain) = f τ

run_cmd liftTermElabM do
  let ty (n : Name) : MetaM Expr := do pure (← getConstInfo n).type
  unless (← isDefEq (← ty (T2 ++ `epD2M0_C_hPoint1)) (mkConst ``hpWrapQ1)) do
    throwError "SR18 AUDIT FAILED: the generated epD2M0_C_hPoint1 differs from the hand-written unfolded statement"
  unless (← isDefEq (← ty (T2 ++ `epD2M_hPoint3)) (mkConst ``hpTop2_3)) do
    throwError "SR18 AUDIT FAILED: the generated epD2M_hPoint3 differs from the hand-written unfolded statement"
  -- mismatches: another call / another callee of the same shape
  if (← isDefEq (← ty (T2 ++ `epD2M0_C_hPoint0)) (mkConst ``hpWrapQ1)) then throwError "SR18 AUDIT FAILED: call 0 ≡ call 1"
  if (← isDefEq (← ty (T2 ++ `epD2M1_C_hPoint1)) (mkConst ``hpWrapQ1)) then throwError "SR18 AUDIT FAILED: wrapP call 1 ≡ wrapQ call 1"
  if (← isDefEq (← ty (T2 ++ `epD2M_hPoint2)) (mkConst ``hpTop2_3)) then throwError "SR18 AUDIT FAILED: parent call 2 ≡ call 3"
  logInfo m!"SR18: the generated per-call HPointAt statements (wrapQ call 1, topshare2 call 3) are isDefEq to hand-written unfolded statements; 3 mismatched pairs are REJECTED"

/-! ## (3) exactly one `HPointAt` theorem per call -/

run_cmd liftTermElabM do
  let env ← getEnv
  for (P, mC0, mC1, mP) in [(T2, 2, 4, 4), (T1, 2, 2, 4)] do
    for k in List.range mC0 do unless env.contains (P ++ Name.mkSimple s!"epD2M0_C_hPoint{k}") do throwError "SR18 AUDIT FAILED: missing {P}.epD2M0_C_hPoint{k}"
    for k in List.range mC1 do unless env.contains (P ++ Name.mkSimple s!"epD2M1_C_hPoint{k}") do throwError "SR18 AUDIT FAILED: missing {P}.epD2M1_C_hPoint{k}"
    for k in List.range mP do unless env.contains (P ++ Name.mkSimple s!"epD2M_hPoint{k}") do throwError "SR18 AUDIT FAILED: missing {P}.epD2M_hPoint{k}"
    if env.contains (P ++ Name.mkSimple s!"epD2M0_C_hPoint{mC0}") || env.contains (P ++ Name.mkSimple s!"epD2M1_C_hPoint{mC1}") || env.contains (P ++ Name.mkSimple s!"epD2M_hPoint{mP}") then
      throwError "SR18 AUDIT FAILED: more HPointAt theorems than calls for {P}"
  logInfo m!"SR18: one HPointAt theorem per call: topshare2 (wrapQ 2, wrapP 4, parent 4), topshare (wrap 2, wrap3 2, parent 4); no extra"

/-! ## (4) FULL forall-type of the topshare endpoint, mutations -/

def modDom (e : Expr) : Nat → (Expr → Expr) → Expr
  | 0, f => match e with | .forallE nm t b bi => .forallE nm (f t) b bi | e => e
  | n+1, f => match e with | .forallE nm t b bi => .forallE nm t (modDom b n f) bi | e => e

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let gt ← instantiateMVars (← getConstInfo (T1 ++ `epD2M_endpoint)).type
  let old ← instantiateMVars (← getConstInfo ``Tests.Compiler.TopShareComposedTest.topshare_noShips_noBd_dc).type
  unless (← isDefEq gt old) do throwError "SR18 AUDIT FAILED: the FULL type of the generated topshare endpoint differs from the hand-pasted topshare_noShips_noBd_dc"
  let nm := toExpr T1
  let other := toExpr ``Tests.Compiler.SeqDeepGenInstTest.wrap
  let swap := fun (e : Expr) => e.replace fun x => if x == nm then some other else none
  let names ← forallTelescope gt fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
  unless names == ["mctx", "mref", "cctx", "cref", "w", "w'", "b", "design", "hr", "entry", "closes"] do throwError "SR18 AUDIT FAILED: binder names {names}"
  let muts : List (Expr × String) :=
    [(modDom gt 8 swap, "hr synthesizes wrap"), (modDom gt 9 swap, "entry is for wrap"),
     (modDom gt 10 (fun _ => mkConst ``False), "closes : False"),
     (← getConstInfo (T2 ++ `epD2M_endpoint)).type |> fun t => (t, "the endpoint of topshare2")]
  for (m, w) in muts do
    if m.hasMVar || m.hasFVar then throwError "SR18 AUDIT FAILED: mvars/fvars in mutation {w}"
    Meta.check m
    unless (← Meta.isProp m) do throwError "SR18 AUDIT FAILED: mutation {w} is not a Prop"
    if (← isDefEq gt m) then throwError "SR18 AUDIT FAILED: the mutated full type ({w}) was ACCEPTED"
  logInfo m!"SR18: the FULL forall-type of the GENERATED topshare.epD2M_endpoint is isDefEq to the hand-pasted topshare_noShips_noBd_dc; {muts.length} type-correct mutations (hr's declaration, entry's declaration, closes : False, the topshare2 endpoint) are REJECTED"

/-! ## (5) closure audit of both generated endpoints -/

open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  for (P, Cs, G) in [(T2, [`Tests.Compiler.SharedLeafGenTest.wrapQ, `Tests.Compiler.SharedLeafGenTest.wrapP], `Tests.Compiler.SharedLeafGenTest.leaf16),
                     (T1, [`Tests.Compiler.SeqDeepGenInstTest.wrap, `Tests.Compiler.SeqDeepGenDiffTest.wrap3], `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc)] do
    let ep := P ++ `epD2M_endpoint
    stdAxioms ep
    let cl ← depClosure ep
    let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
      `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
    let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad.isEmpty do throwError "SR18 AUDIT FAILED: old boundary / old child predicate in the closure of {ep}: {bad}"
    -- no old generated chain, no pasted per-callee block (these names must not exist: the generic path does not emit them)
    let pasted : List Name := (List.range 2).flatMap fun i =>
      [P ++ Name.mkSimple s!"epD2M{i}_C_composedA", P ++ Name.mkSimple s!"epD2M{i}_C_seqChildRunN2", P ++ Name.mkSimple s!"epD2M{i}_C_kidFactsA",
       P ++ Name.mkSimple s!"epD2M{i}_C_closesA", P ++ Name.mkSimple s!"epD2M{i}_C_hcalls", P ++ Name.mkSimple s!"epD2M{i}_C_traceXA",
       P ++ Name.mkSimple s!"epD2M{i}_G_kidFactsA"] ++ [P ++ `epD2M_closesA, P ++ `epD2M_disj]
    for n in pasted do
      if (← getEnv).contains n then throwError "SR18 AUDIT FAILED: the pasted block {n} exists (the generic path must not emit it)"
    let oldGen := [P ++ `machine_composedNR2] ++ Cs.map (· ++ `machine_composedNR1) ++ Cs.map (· ++ `seq_child_runN_ofR1)
    for f in oldGen do
      unless (← getEnv).contains f do throwError "SR18 AUDIT FAILED: the old generated name {f} does not exist (the audit would check nothing)"
      if cl.contains f then throwError "SR18 AUDIT FAILED: the old generated theorem {f} is in the closure of {ep}"
    let must : List Name :=
      [``Tools.ShippingQuadCalls.quad_composed_split, ``Tools.ShippingQuadCalls.leafCallee_hcalls, ``Tools.ShippingQuadHPoint.callFactF_of_hPointAt,
       ``Tools.ShippingQuadCallFacts.callFactF_of_fam, ``Tools.ShippingQuadCallFacts.extendBits_of_ne, ``Tools.ShippingQuadComposed.quad_ranA,
       ``Tools.ShippingQuadComposed.quad_runFacts, ``Tools.ShippingQuadLeafGeneric.quad_closes0, ``Tools.ShippingTopShareRan.machineRanA_start0,
       P ++ `epD2M_quadAll, P ++ `epD2M_genP, P ++ `epD2M_leafRun, P ++ `epD2M_hFP, P ++ `epD2M0_C_hF, P ++ `epD2M1_C_hF,
       P ++ `epD2M0_C_hextB, P ++ `epD2M1_C_hext, P ++ `epD2M0_C_hPoint0, P ++ `epD2M_hPoint0, P ++ `epD2M_composedA, P ++ `epD2M_soundLA]
    for m in must do
      unless cl.contains m do throwError "SR18 AUDIT FAILED: {m} not in the closure of {ep}"
    logInfo m!"SR18 CLOSURE AUDIT: {ep}: standard axioms; closure {cl.size} constants; no old boundary / child predicate; no pasted per-callee block exists; the old generated chain {oldGen.length} theorems is not in it; the generic lemmas and the generated per-declaration facts (GenFacts, hext/hextB, hPoint, hF, QuadAll, leaf run) are in it"

end Tests.Compiler.SharedLeafGenFactsTest
end
