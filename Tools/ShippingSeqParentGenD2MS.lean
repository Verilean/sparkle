import Tools.ShippingSeqParentGenD2M
import Tools.ShippingQuadLeafGeneric
import Tools.ShippingTopShareRan
-- BUILT (unit SR13): s4 exit 0 (module), s5 exit 0 (Tests.Compiler.SharedLeafGenTest), s6 exit 0 (Tests.Compiler.SharedLeafGenTopshareTest) (dev runs); the final-SHA rebuild is in REPORT-SR13.md.
/-! # `#machine_seq_parent_endpoint P` — a LIMITED shared-leaf CANDIDATE (unit SR13, ledger L8as)

STATUS (binding): a CANDIDATE, opt-in.  `set_option sparkle.sharedLeafCandidate true` (default `false`) lets THIS elaborator take over a declaration `P` of the explicitly
stated class QUAD below; with the option off, or for every declaration outside the class, it throws `unsupportedSyntax` and the elaborators of
`Tools/ShippingSeqParentGen*.lean` (UNCHANGED files) run exactly as before (including the SR3x refusal of `topshare` with its text).  Outside the class the shared-leaf
refusal is NOT lifted: this module refuses with a reason that NAMES the failed condition.

## The class QUAD (each condition is checked before any text is generated)
* (Q0) `P` calls TWO different callees `C₀`, `C₁` and EACH callee has exactly ONE distinct grandchild, the SAME non-memory leaf `G` for both (otherwise this elaborator
  does not apply and the existing path runs / refuses with its own reason; a callee that is a leaf, has memory, several grandchildren, or a grandchild with calls of
  its own — depth 3 — is refused there, before the shared-leaf test, exactly as before);
* (Q1) exactly two different callees (three callees sharing a leaf are refused here);
* (Q2) the call list of `P` is exactly `[C₀, C₀, C₁, C₁]` (first-occurrence order; interleaved / repeated-differently lists are refused here);
* (Q3) `G ∉ {C₀, C₁, P}`; `P` has no call that is a memory; `G` has no call instances (depth 2) — as in the existing path;
* every other condition of the depth-2 several-callee path (domain polymorphic callees, `instFields ≠ []`, `Unit`-indexed parent, the old chain
  `#machine_design_svNR P 2` present, group numbering read from the old term) is kept.
The decidable DATA facts (`LeafData`, `LeafCalleeData`, `QuadParentData` of `Tools/ShippingQuadLeafGeneric.lean`) are discharged by `decide` in the generated text; a
failure there is an elaboration error of the generated declaration, not a refusal.
Two tested examples (`topshare`, `topshare2`) do NOT make the class complete: besides (Q0)–(Q3) the DATA conditions (`decide` on the stored `machineData`) and the NAME conditions
(`epD2M_*`, the group numbering read from the old chain term) must hold, otherwise generation fails with an elaboration error; `sparkle.sharedLeafCandidate` stays `false` by default (unit SR14 wording).

## What the candidate generates
The text of the existing depth-2 several-callee template (`Tools/ShippingSeqParentGenD2M.lean`, UNCHANGED) with: the same-leaf-incompatible parent declarations `epD2M_disj` and
`epD2M_closesA` REMOVED (their library lemma needs `hdisjD`, false for a shared leaf); the generic QUAD data facts and `epD2M_closes0` (= `quad_closes0`, the START-world
no-fallback of the parent, DERIVED), `epD2M_machineRun` (= `quad_machineRun`); the start world `JQC O 0 w` (the outermost entry) instead of `JQ … ∧ (D₀ = 0 ∨ CacheInvA …)`;
`machineRanA_start0` instead of `machineRanA_main`.  The per-callee blocks are the existing ones.
The conclusion object is the same as that of the existing path (the endpoint `machine_design_noShips_noBd_dc`); `O`, `T`, `MachineDefines`, inputs / reset / bounds stay
conditional (inside `epD2M_Bnd` / the conclusion).  `RealChildA` is a history of past synthesis results. -/
namespace Tools.ShippingSeqParentGenD2MS
open Lean Elab Command Meta Term
open Tools.ShippingSeqParentGen (runCmds elabText readNames readName reduceNat openBlock)
open Tools.ShippingSeqParentGenD2 (openBlock2 readNats readNatLists sourceIndex isMemName memWhy oldGroupCount groupFactsTmpl)
open Tools.ShippingSeqParentGenD2M

register_option sparkle.sharedLeafCandidate : Bool := {
  defValue := false
  descr := "SR13: let `#machine_seq_parent_endpoint` take over the explicitly stated shared-leaf class QUAD (candidate; default off: the shared-leaf refusal is unchanged)" }

def refuseS {α : Type} (fn : Name) (cond : String) (why : String) : CommandElabM α :=
  throwError "#machine_seq_parent_endpoint (unit SR13, SHARED-LEAF CANDIDATE, class QUAD): REFUSED `{fn}`: condition {cond} FAILED: {why}"

/-- remove the text from the unique occurrence of `a` up to (not including) the first `b` after it -/
def cutBetween (s a b : String) : String :=
  match s.splitOn a with
  | [pre, rest] =>
    match rest.splitOn b with
    | _ :: tl@(_ :: _) => pre ++ b ++ b.intercalate tl
    | _ => panic! s!"cutBetween: end marker {b} not found"
  | _ => panic! s!"cutBetween: start marker {a} not unique"

/-- the class test: `none` = this elaborator does not apply (the existing path decides); `some p` = a QUAD instance (conditions checked) -/
def analyseS (fn : Name) : CommandElabM (Option D2MParams) := do
  let env ← getEnv
  let calleesOf := fun (n : Name) => liftTermElabM do readNames (← elabText (s!"({n}.machineData.shape.insts.map (·.1))"))
  let nat := fun (s : String) (n : Name) => liftTermElabM do reduceNat (← elabText (s.replace "@F@" n.toString))
  let pc ← calleesOf fn
  if pc.isEmpty || pc.any isMemName then return none
  let Cs := pc.eraseDups
  -- (Q0) the same preliminary checks, in the same order, as the existing path; any failure there is the existing path's refusal
  let mut Gs : Array Name := #[]
  for C in Cs do
    unless env.contains (C ++ `machineData) do return none
    let cc ← calleesOf C
    if cc.isEmpty || cc.any isMemName then return none
    let ccs := cc.eraseDups
    unless ccs.length == 1 do return none
    let G := ccs.head!
    unless env.contains (G ++ `machineData) do return none
    let gc ← calleesOf G
    if gc.any isMemName then return none
    let gi ← nat "@F@.machineData.shape.insts.length" G
    unless gi == 0 do return none
    Gs := Gs.push G
  -- from here on the declaration has the shape of the shared-leaf case iff some leaf occurs twice
  unless Gs.toList.any (fun G => Gs.toList.count G > 1) do return none
  let G := Gs[0]!
  -- (Q1)
  unless Cs.length == 2 do
    refuseS fn "Q1 (exactly two different callees)" s!"{fn} calls {Cs.length} different callees {Cs}; the candidate takes exactly two. The shared-leaf refusal of the existing path stays for this declaration (OPEN)"
  unless Gs.toList.all (· == G) do
    refuseS fn "Q0 (one shared leaf for both callees)" s!"the callees {Cs} call the leaves {Gs}; only the case of ONE shared leaf is in the class"
  -- (Q2)
  let want := [Cs[0]!, Cs[0]!, Cs[1]!, Cs[1]!]
  unless pc == want do
    refuseS fn "Q2 (call list [C₀, C₀, C₁, C₁])" s!"the call list of {fn} is {pc}, the class requires {want}. The shared-leaf refusal of the existing path stays for this declaration (OPEN)"
  -- (Q3)
  if Cs.contains G then refuseS fn "Q3 (leaf ∉ callees)" s!"the leaf {G} is also a callee of the parent"
  if G == fn then refuseS fn "Q3 (leaf ≠ parent)" s!"the leaf {G} is the parent itself"
  -- the remaining conditions and the partition are those of the existing path
  let al ← liftTermElabM do readNatLists (← elabText s!"({fn}.machineData.shape.insts.map (·.2.1))")
  let kP ← nat "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)" fn
  let oldThm := fn ++ `machine_composedNR2
  unless env.contains oldThm do
    refuseS fn "old chain present" s!"{oldThm} not found (the class needs the old generated chain: `#machine_design_svNR {fn} 2`)"
  let instGroup ← match ← liftTermElabM <| Tools.ShippingSeqParentGenD2.oldInstGroups oldThm with
    | .ok og => pure og
    | .error why => refuseS fn "group numbering" s!"the partition of the instances into groups cannot be read from the old generated {oldThm}: {why}"
  unless instGroup.length == al.length do
    refuseS fn "group numbering" s!"the old generated {oldThm} has {instGroup.length} call entries but {fn} has {al.length} call instances"
  let some groups := Tools.ShippingSeqParentGenD2.groupKeysOf instGroup (pc.map Cs.idxOf |>.zip al)
    | refuseS fn "group numbering" s!"the old generated {oldThm} groups the instances as {instGroup}, but the instances of one group do not have one (callee, argument list)"
  let partitionNote : String ← match ← liftTermElabM <| oldGroupKeysM fn pc kP al with
    | .ok (inst, _) => pure (if inst == instGroup then "the recomputed call-argument approximation of the old key gives the same partition" else s!"the recomputed call-argument approximation of the old key gives a DIFFERENT partition {inst} (the old term's numbering is used)")
    | .error why => pure s!"the call-argument approximation of the old key was not computed ({why})"
  for (n, ss) in [(fn, [`machine_composedNR2, `machine_ok, `machine_body, `machine_inits, `machine_writes, `machine_result, `machine_source,
        `machine_ext_causal, `machineSource, `machineInits, `machineBody, `machineResult, `machineExt, `machineExtB, `machineData])] ++
      Cs.map (fun C => (C, [`machine_composedNR1, `machine_ok, `machine_body, `machine_inits, `machine_writes, `machine_result, `machine_source,
        `machine_ext_causal, `machineSource, `machineInits, `machineBody, `machineResult, `machineExt, `machineExtB, `machineData,
        `seq_child_runN_ofR1])) ++
      [(G, [`machine_ok, `machine_body, `machine_closes, `machineSource, `machineData])] do
    for s in ss do
      unless env.contains (n ++ s) do
        refuseS fn "old chain present" s!"{n ++ s} not found (the class needs the old generated chain: `#machine_design_svNR {fn} 2`)"
  let nOld ← liftTermElabM <| Tools.ShippingSeqParentGenD2.oldGroupCount oldThm
  unless nOld == groups.length do
    refuseS fn "group numbering" s!"the old generated {oldThm} has {nOld} group(s) of facts but its entries use {groups.length} group(s)"
  let ip ← liftTermElabM <| sourceIndex fn
  unless ip == ``Unit || ip == ``PUnit do refuseS fn "top-level parent" s!"the parent's machineSource is indexed by {ip}, expected Unit"
  let mut kCs : Array Nat := #[]
  let mut gws : Array (List Nat) := #[]
  let mut nOuts : Array Nat := #[]
  for C in Cs do
    let ic ← liftTermElabM <| sourceIndex C
    unless ic == `Sparkle.Core.Domain.DomainConfig do
      refuseS fn "domain polymorphic callees" s!"the callee {C}'s machineSource is indexed by {ic}, expected DomainConfig"
    for n in [fn, C] do
      let nf ← nat "@F@.machineData.shape.instFields.length" n
      if nf == 0 then refuseS fn "instFields ≠ []" s!"{n} has no instField"
    kCs := kCs.push (← nat "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)" C)
    nOuts := nOuts.push (← nat "@F@.machineData.shape.layout.outs.length" C)
    gws := gws.push (← liftTermElabM do readNats (← elabText s!"(Tools.ShippingPortWidthsPure.declWidths {G}.machineData)"))
  let mP ← nat "@F@.machineData.shape.insts.length" fn
  return some { P := fn, Cs := Cs, Gs := Gs.toList, kCs := kCs.toList, gws := gws.toList, nOutsCs := nOuts.toList, kP := kP, mP := mP,
                groups := groups, instGroup := instGroup, instCallee := pc.map Cs.idxOf, partitionNote := partitionNote }

/-! ## text -/

/-- the QUAD data facts and the START-world closing of the parent (the generic lemmas of `Tools/ShippingQuadLeafGeneric.lean`); `@C0@ @C1@ @G@ @K0@ @K1@` -/
def quadExtra : String := r#"
theorem _root_.@P@.epD2M_leafData : Tools.ShippingQuadLeafGeneric.LeafData @G@.machineData :=
  ⟨@G@.machine_ok, @G@.machine_body, by first | decide | decide +kernel, by first | decide | decide +kernel⟩

theorem _root_.@P@.epD2M0_calleeData :
    Tools.ShippingQuadLeafGeneric.LeafCalleeData @C0@.machineData @G@.machineData ``@C0@ ``@G@ @K0@ := by
  refine ⟨@C0@.machine_ok, @C0@.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem _root_.@P@.epD2M1_calleeData :
    Tools.ShippingQuadLeafGeneric.LeafCalleeData @C1@.machineData @G@.machineData ``@C1@ ``@G@ @K1@ := by
  refine ⟨@C1@.machine_ok, @C1@.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem _root_.@P@.epD2M_quadData :
    Tools.ShippingQuadLeafGeneric.QuadParentData @P@.machineData @C0@.machineData @C1@.machineData ``@P@ ``@C0@ ``@C1@ ``@G@ @KP@ := by
  refine ⟨@P@.machine_ok, @P@.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

/-- the parent's no-fallback at the entry's START world, DERIVED (`Tools.ShippingQuadLeafGeneric.quad_closes0`) -/
theorem _root_.@P@.epD2M_closes0 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    :
    Tools.ShippingTopShareRun.MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx
      ``@P@ @P@.machineData.shape :=
  Tools.ShippingQuadLeafGeneric.quad_closes0 O T hA @P@.epD2M_quadData @P@.epD2M_leafData @P@.epD2M0_calleeData
    @P@.epD2M1_calleeData hM0 hM1 hR0 (fun mc cc => @G@.machine_closes mc _ cc _)

theorem _root_.@P@.epD2M_machineRun (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``@P@ [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape) :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``@P@ @P@.machineData.shape m design :=
  Tools.ShippingQuadLeafGeneric.quad_machineRun O T hA @P@.epD2M_quadData @P@.epD2M_leafData @P@.epD2M0_calleeData
    @P@.epD2M1_calleeData entry hM0 hM1 hR0 (fun mc cc => @G@.machine_closes mc _ cc _) hw hcore
"#

/-- the parent text of the shared-leaf candidate: the existing templates with the shared-leaf-incompatible pieces replaced -/
def parentTextS : String :=
  let h := cutBetween pHead "theorem _root_.@P@.epD2M_disj" "theorem _root_.@P@.epD2M_callArgs"
  let h := cutBetween h "theorem _root_.@P@.epD2M_closesA" "theorem _root_.@P@.epD2M_hkid"
  let t := pMid ++ pTail
  -- order matters: the " hw hc" rewrite must not see the text of `quadExtra` (which contains `hw hcore`) nor produce it
  let reps : List (String × String) :=
    [("{D₀ : Nat} {w w1 : Void IO.RealWorld}", "{w w1 : Void IO.RealWorld}"),
     ("{D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))", "(hw : JQC O 0 w)"),
     ("(hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))", "(hw : JQC O 0 w)"),
     (" hw hc", " hw"),
     ("Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (@P@.epD2M_closesA O T hA @HA@) hw",
      "Tools.ShippingTopShareRan.machineRanA_start0 O hA T hcore entry (@P@.epD2M_closes0 O T hA @HA@) hw"),
     ("(machineRunJQC_of_closesA O hA hcore entry (@P@.epD2M_closesA O T hA @HA@) hw)",
      "(@P@.epD2M_machineRun O T hA @HA@ hw hcore entry)"),
     ("(n := D₀ + 1) (htr_of_tele O hA T D₀)", "(n := 0 + 1) (htr_of_tele O hA T 0)"),
     ("∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))", "JQC O 0 w")]
  h ++ quadExtra ++ reps.foldl (fun s (a, b) => s.replace a b) t

def assembleMS (p : D2MParams) : String :=
  let tcs := "\n".intercalate ((rangeR p).map fun i => sub1 p i tcTmpl)
  let pat := "".intercalate ((List.range p.mP).map fun _ => "_ | ") ++ "k"
  let ptxt := parentTextS
  let ptxt := ptxt.replace "@DISPDEFS@" (dispDefs p)
  let ptxt := ptxt.replace "@KIDBRANCHES@" (kidBranches p)
  let ptxt := ptxt.replace "@HKIDBRANCHES@" (hkidBranches p)
  let ptxt := ptxt.replace "@RUNBRANCHES@" (runBranches p)
  let ptxt := ptxt.replace "@GROUPFACTS@" (groupFacts p)
  let ptxt := ptxt.replace "@CASES@" (composedCases p)
  let ptxt := ptxt.replace "@BNDDEFS@" (bndDefs p)
  let ptxt := ptxt.replace "@HB@" (hypBinders p)
  let ptxt := ptxt.replace "@HA@" (hypArgs p)
  let ptxt := ptxt.replace "@HNPAT@" (patOf p "hn")
  let ptxt := ptxt.replace "@CPAT@" (patOf p "rfl")
  let ptxt := ptxt.replace "@ORC@" (orOf p "c")
  let ptxt := ptxt.replace "@ORK@" (orOf p "(@P@.machineData.shape.insts[k]).1")
  let ptxt := ptxt.replace "@CALLEES@" (calleesLit p)
  let ptxt := ptxt.replace "@KO@" "(fun k => @P@.epD2M_outsOf (@P@.epD2M_calleeAt k))"
  let ptxt := ptxt.replace "@KI@" "(fun k => @P@.epD2M_widthsOf (@P@.epD2M_calleeAt k))"
  let ptxt := ptxt.replace "@MPAT@" pat
  let ptxt := ptxt.replace "@MP@" (toString p.mP)
  let ptxt := ptxt.replace "@C0@" (p.Cs.getD 0 .anonymous).toString
  let ptxt := ptxt.replace "@C1@" (p.Cs.getD 1 .anonymous).toString
  let ptxt := ptxt.replace "@K0@" (toString (p.kCs.getD 0 0))
  let ptxt := ptxt.replace "@K1@" (toString (p.kCs.getD 1 0))
  let ptxt := ptxt.replace "@G@" (p.Gs.getD 0 .anonymous).toString
  let src := Tools.ShippingSeqParentGenD2.openBlock2 ++ tcs ++ ptxt
  (src.replace "@P@" p.P.toString).replace "@KP@" (toString p.kP)

def obtainPatS (p : D2MParams) : String :=
  "⟨O, T, hA, " ++ ", ".intercalate ((rangeR p).map fun i => s!"hM{i}, hR{i}") ++ ", hw⟩"

def endpointSrcS (p : D2MParams) : String :=
  ((((endpointTermM.replace " hw hc" " hw").replace "@OBT@" (obtainPatS p)).replace "@HA@" (hypArgs p)).replace "@P@" p.P.toString).replace "@KP@" (toString p.kP)

/-! ## audit of the generated endpoint -/

open Tests.Compiler.ChildVertAuditTest in
def auditS (p : D2MParams) (ep : Name) : MetaM Unit := do
  stdAxioms ep
  let ty := (← getConstInfo ep).type
  let premises ← forallTelescope ty fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← inferType x
      if (← isProp t) then ps := ps.push s!"{(← x.fvarId!.getUserName)} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let expected := ["hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines", "closes : True"]
  unless premises.toList == expected do throwError "SR13 AUDIT FAILED: outer Prop premises are {premises}, expected {expected}"
  let cl ← depClosure ep
  let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
    `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
    `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SR13 AUDIT FAILED: the forbidden name {f} does not exist (the audit would check nothing)"
  let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR13 AUDIT FAILED: {ep}: old boundary / old child predicate in closure: {bad}"
  let pe := fun (s : String) => p.P ++ Name.mkSimple s
  let perCallee := (rangeR p).foldr (fun i acc => acc ++ [pe s!"epD2M{i}_C_composedA", pe s!"epD2M{i}_C_seqChildRunN2",
      pe s!"epD2M{i}_C_kidFactsA", pe s!"epD2M{i}_C_closesA", pe s!"epD2M{i}_calleeData"]) []
  for must in [pe "epD2M_soundLA", pe "epD2M_composedA", pe "epD2M_traceXA", pe "epD2M_designCheck", pe "epD2M_runFacts", pe "epD2M_outsCheck",
      pe "epD2M_kidsMasked", pe "epD2M_closes0", pe "epD2M_machineRun", pe "epD2M_quadData", pe "epD2M_leafData", pe "epD2M_hkid",
      ``Tools.ShippingQuadLeafGeneric.quad_closes0, ``Tools.ShippingQuadLeafGeneric.quad_machineRun,
      ``Tools.ShippingQuadLeafGeneric.leafCallee_ifaceP, ``Tools.ShippingQuadLeafGeneric.leafCallee_calleeOK,
      ``Tools.ShippingTopShareRan.machineRanA_start0,
      ``Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA, ``Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA,
      ``Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main, ``Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA,
      ``Tools.ShippingMachineShipsDepth.composedG_of_NW,
      ``Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc] ++ perCallee do
    unless cl.contains must do throwError "SR13 AUDIT FAILED: {must} not in the closure of {ep}"
  -- the pieces that need `hdisjD` (false for a shared leaf) must NOT be in the closure
  for no in [pe "epD2M_closesA", pe "epD2M_disj"] do
    if cl.contains no then throwError "SR13 AUDIT FAILED: {no} is in the closure of {ep}"
  for old in [p.P ++ `machine_composedNR2] ++ p.Cs.map (· ++ `machine_composedNR1) ++ p.Cs.map (· ++ `seq_child_runN_ofR1) do
    if cl.contains old then throwError "SR13 AUDIT FAILED: the old generated theorem {old} is in the closure of {ep}"
  let (_, concl) ← forallTelescope ty fun _ c => pure ((), c)
  let bnd := pe "epD2M_Bnd"
  unless (concl.find? (·.isConstOf bnd)).isSome do throwError "SR13 AUDIT FAILED: {bnd} not in the conclusion"
  let some bv := (← getConstInfo bnd).value? | throwError "SR13 AUDIT FAILED: {bnd} has no value"
  let mut defs : Array Name := #[]
  let mut hasJQC := false
  let mut todo : Array Expr := #[bv]
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if e.getAppFn.isConstOf ``Tools.ShippingMachineEntry.MachineDefines && e.getAppNumArgs == 6 then
      if let some a := e.getAppArgs[4]? then
        defs := defs.push (← Tools.ShippingSeqParentGen.readName a)
    if e.getAppFn.isConstOf ``Tools.ShippingChildCacheA.JQC then hasJQC := true
    match e with
    | .app f a => todo := todo.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b => todo := todo.push b
    | _ => pure ()
  unless hasJQC do throwError "SR13 AUDIT FAILED: {bnd} does not ask for a start world in JQC O 0"
  let want := (p.Cs ++ [p.Gs.getD 0 .anonymous, p.Gs.getD 1 .anonymous]).toArray
  unless defs.qsort (·.toString < ·.toString) == want.qsort (·.toString < ·.toString) do
    throwError "SR13 AUDIT FAILED: {bnd} asks MachineDefines for {defs}, expected exactly {want}"
  logInfo m!"SR13 AUDIT OK: {ep}: standard axioms; outer Prop premises ASSERTED {premises}; closure {cl.size} constants, none of ChildBnd/StartV/GenKid/old KidFacts/MachineRunNC/machineRunNC_of_real/seqChildRunN_of_composedC; neither {pe "epD2M_closesA"} nor {pe "epD2M_disj"} (they need hdisjD) is in the closure; the old generated theorems are not in the closure; {bnd} (an EXISTENTIAL over O/T/AdmCtx/MachineDefines of {p.Cs} and the shared leaf {p.Gs.getD 0 .anonymous}/start world JQC O 0, not a proof that it holds) stays in the conclusion; chains {p.Cs.zip p.Gs}"

/-! ## the command (a fourth elaborator; tried FIRST, defers to the existing ones) -/

open Tools.ShippingSeqParentGen in
@[command_elab Tools.ShippingSeqParentGen.«command#machine_seq_parent_endpoint_»]
def elabEndpointD2MS : CommandElab := fun stx => do
  unless sparkle.sharedLeafCandidate.get (← getOptions) do throwUnsupportedSyntax
  let f : Ident := ⟨stx[1]⟩
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  unless (← getEnv).contains (fn ++ `machineData) do throwUnsupportedSyntax
  let pc ← liftTermElabM do readNames (← elabText (s!"({fn}.machineData.shape.insts.map (·.1))"))
  unless pc.eraseDups.length ≥ 2 do throwUnsupportedSyntax
  let some p ← analyseS fn | throwUnsupportedSyntax
  logInfo m!"SR13 shared-leaf candidate (class QUAD): {p.P} calls {p.Cs} (call list {pc}), all of which call the SAME leaf {p.Gs.getD 0 .anonymous} (kP {p.kP}, kC {p.kCs}); {p.mP} call instance(s), groups {p.groups} (instance -> group {p.instGroup}; numbering READ from the old term: {p.partitionNote}); leaf argument widths {p.gws}"
  let src := assembleMS p
  try
    Tools.ShippingSeqParentGen.runCmds src
  catch e =>
    try Tools.ShippingSeqParentGen.runCmds "end" catch _ => pure ()
    throw e
  let ep := fn ++ `epD2M_endpoint
  try
    liftTermElabM do
      let some stx := (Parser.runParserCategory (← getEnv) `term (endpointSrcS p)).toOption
        | throwError "endpoint term: parse error"
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let ty ← instantiateMVars (← inferType e)
      if e.hasMVar || ty.hasMVar then throwError "#machine_seq_parent_endpoint (SR13 candidate): unassigned mvars in the endpoint term"
      addAndCompile <| .thmDecl { name := ep, levelParams := [], type := ty, value := e }
    liftTermElabM <| auditS p ep
  finally
    Tools.ShippingSeqParentGen.runCmds "end"

end Tools.ShippingSeqParentGenD2MS
