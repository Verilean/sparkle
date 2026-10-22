import Tools.ShippingSeqParentGenD2M
import Tools.ShippingQuadLeafGeneric
import Tools.ShippingTopShareRan
import Tools.ShippingQuadReturned
import Tools.ShippingSeqParentGenD2MSG
import Tools.ShippingSeqParentGenD2MSD
-- BUILT (unit SR20): n5 exit 0 (Tests.Compiler.SharedLeafGenNoOldChainTest; dev run on the dirty tree); the final-SHA rebuild is in REPORT-SR20.md.
-- BUILT (unit SR19): a8 exit 0 (Tests.Compiler.SharedLeafGenDefaultHbTest), f1 exit 0 (Tests.Compiler.SharedLeafGenFallbackTest) (dev runs); final-SHA rebuild in REPORT-SR19.md.
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

## Unit SR18 (ledger L8ax): the generic-lemma path (default behaviour of the candidate when it is enabled)
With `sparkle.sharedLeafCandidate true` the generator FIRST tries the generic-lemma path (`Tools/ShippingSeqParentGenD2MSG.lean`): for each accepted parent it elaborates, one command at a time and
each checked by the kernel, the decided data bundles (`epD2M_quadAll` …), `GenFacts` of the parent and of each callee (`epD2M_genP`, `epD2M{i}_C_gen`), the leaf run (`epD2M_leafRun := G.seq_child_runN`),
`epD2M{i}_C_hextB` / `_hext`, the PER-CALL residues `epD2M{i}_C_hPoint{k}` / `epD2M_hPoint{k}` (`Tools.ShippingQuadHPoint.HPointAt`) and `epD2M{i}_C_hF` / `epD2M_hFP` (`callFactF_of_hPointAt`), and the template
theorems `epD2M_hkid / ranA / runFacts / outsCheck / kidsMasked / designCheck / traceXA / soundLA / composedA` with the STATEMENTS of the SR13 template and the generic lemmas (`quad_*`,
`quad_composed_split`) as bodies; the per-callee pasted blocks (`epD2M{i}_C_composedA` …) are NOT emitted.  The endpoint statement is unchanged.  If one of these commands fails, or the audit fails, the
failing command and its errors are LOGGED (`SR18: the generic-lemma path FAILED …`), NOTHING of the attempt is kept, and the SR13 path (pasted blocks) runs instead; no input is refused by this.
What is generated is kernel-checked per declaration, instance-specific facts about the accepted declarations — NOT a theorem over the class.  What stays a PREMISE of a generated endpoint: the conclusion's
existential `O`/`T`/`AdmCtx`/`MachineDefines`/`JQC O 0 w` (inside `epD2M_Bnd`), the run `hr`, `entry`, and the leaf's `MachineCloses` (`G.machine_closes`); the generated `GenFacts`, `LeafSeqRunN`
(`G.seq_child_runN`), `hPoint`, `hext`/`hextB` are THEOREMS of the generated declarations.
(Unit SR19, ledger L8ay) The decoding equations `Hb0`/`Hv0` of every call are NO LONGER extracted from the old chain (`oldGroupFact%`): they are stated and proved per call as `have`s inside each generated `hPoint`, the
families being read from the generated `machineExt`/`machineExtB` (`Tools/ShippingSeqParentGenD2MSD.lean`, text only; a wrong reading makes that theorem fail and triggers the logged fallback); the `Inhabited` instances are
`⟨defaultHList _⟩` (not `oldInst%`); the generic path runs under the AMBIENT `maxHeartbeats` (the shared header's `set_option maxHeartbeats 4000000` is dropped from its text; `Tests/Compiler/SharedLeafGenDefaultHbTest.lean`).
(Unit SR20, ledger L8az) The ANALYSIS of the generic path (`analyseG`) no longer needs the old chain: the instance → group partition is the first-occurrence partition of the call keys read from the generated
`machineExt`/`machineExtB` (`oldGroupKeysM`, a reading of the generated terms, not trusted: every generated declaration built on it is kernel-checked and a wrong partition makes one fail), and the leaf's run theorem
`G.seq_child_runN` is generated on demand by `Tools.ShippingMachineDepthCommand.generateSeqChildN` (from `G.machine_sound`).  Nothing of `#machine_design_svNR` is required: no `machine_composedNR*`, `seq_child_runN_ofR1`.
The old chain is still used for the SR13 FALLBACK only: if `fn.machine_composedNR2` exists, `analyseS` (old-chain analysis, numbering read from the old term) is run as before and the SR13 path is the fallback of a failed generic attempt.
If there is NO old chain and the generic attempt fails, the failure is logged (`SR18: … FAILED … NO old chain: no SR13 fallback`), the state is restored, and the pre-existing elaborators for the command are run (`runOtherElabs`; for a
shared-leaf parent: their own shared-leaf refusal text).  This elaborator itself raises no error and keeps nothing of the failed attempt.  `Tests/Compiler/SharedLeafGenNoOldChainTest.lean`.
STILL needed: `#machine_endpoint P` (the machine data of the parent and of its callees/leaf, `machine_ok`, `machine_body`, `machine_closes` of the leaf).  Test hooks (default off): `sparkle.sharedLeafTiming`, `sparkle.sharedLeafInject`.
`RealChildA` / `ServedRealA` are histories of past synthesis results.

## What the candidate generates
(unit SR14, L8at) In addition to `epD2M_endpoint`, the RETURNED theorem `epD2M_returned` (= `Tools.ShippingQuadReturned.quad_returned` applied to the generated data facts and
per-callee blocks: the same `M`, `Dg`, `y.2 = Dg`, `DesignSemConcl … y.1 M y.2`) and the WIRED theorem `epD2M_wired` (`quad_wired`) are generated; their FULL types are checked in
`Tests/Compiler/SharedLeafGenReturnedTest.lean` on `topshare2` only (hand-written statements, type-correct mutations, closure audit).  Their premises are those of the endpoint
(`O`, `T`, `AdmCtx`, `MachineDefines`, `JQC O 0 w`, the run `h`).
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
def analyseCore (fn : Name) (old : Bool) : CommandElabM (Option D2MParams) := do
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
  -- (unit SR20) `old = false`: NO old chain is read or required.  The instance → group partition is the first-occurrence partition of the call keys read from the generated
  -- `machineExt`/`machineExtB` (`oldGroupKeysM`); it is not trusted: the generated declarations built on it are kernel-checked, and a wrong partition makes one of them fail.
  let instGroup ← if old then do
      unless env.contains oldThm do
        refuseS fn "old chain present" s!"{oldThm} not found (the class needs the old generated chain: `#machine_design_svNR {fn} 2`)"
      match ← liftTermElabM <| Tools.ShippingSeqParentGenD2.oldInstGroups oldThm with
      | .ok og => pure og
      | .error why => refuseS fn "group numbering" s!"the partition of the instances into groups cannot be read from the old generated {oldThm}: {why}"
    else match ← liftTermElabM <| oldGroupKeysM fn pc kP al with
      | .ok (inst, _) => pure inst
      | .error why => refuseS fn "group numbering (machine route)" s!"the partition of the instances into groups cannot be computed from the generated machineExt of {fn}: {why}"
  unless instGroup.length == al.length do
    refuseS fn "group numbering" s!"the partition has {instGroup.length} call entries but {fn} has {al.length} call instances"
  let some groups := Tools.ShippingSeqParentGenD2.groupKeysOf instGroup (pc.map Cs.idxOf |>.zip al)
    | refuseS fn "group numbering" s!"the partition groups the instances as {instGroup}, but the instances of one group do not have one (callee, argument list)"
  let partitionNote : String ← if !old then pure "machine route: first-occurrence partition of the call keys read from the generated machineExt/machineExtB (no old chain)" else
    match ← liftTermElabM <| oldGroupKeysM fn pc kP al with
    | .ok (inst, _) => pure (if inst == instGroup then "the recomputed call-argument approximation of the old key gives the same partition" else s!"the recomputed call-argument approximation of the old key gives a DIFFERENT partition {inst} (the old term's numbering is used)")
    | .error why => pure s!"the call-argument approximation of the old key was not computed ({why})"
  if old then
   for (n, ss) in [(fn, [`machine_composedNR2, `machine_ok, `machine_body, `machine_inits, `machine_writes, `machine_result, `machine_source,
        `machine_ext_causal, `machineSource, `machineInits, `machineBody, `machineResult, `machineExt, `machineExtB, `machineData])] ++
      Cs.map (fun C => (C, [`machine_composedNR1, `machine_ok, `machine_body, `machine_inits, `machine_writes, `machine_result, `machine_source,
        `machine_ext_causal, `machineSource, `machineInits, `machineBody, `machineResult, `machineExt, `machineExtB, `machineData,
        `seq_child_runN_ofR1])) ++
      [(G, [`machine_ok, `machine_body, `machine_closes, `machineSource, `machineData])] do
    for s in ss do
      unless env.contains (n ++ s) do
        refuseS fn "old chain present" s!"{n ++ s} not found (the class needs the old generated chain: `#machine_design_svNR {fn} 2`)"
  if old then
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

/-- the class test with the OLD CHAIN (SR13 fallback and its group numbering read from the old term); behaviour unchanged -/
def analyseS (fn : Name) : CommandElabM (Option D2MParams) := analyseCore fn true

/-- (unit SR20) the class test for the GENERIC path: no old chain read or required -/
def analyseG (fn : Name) : CommandElabM (Option D2MParams) := analyseCore fn false

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
def parentTextS (gen : Option (String × String) := none) : String :=
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
  let t := reps.foldl (fun s (a, b) => s.replace a b) t
  match gen with
  | none => h ++ quadExtra ++ t
  | some (ga, gb) =>
    -- (unit SR18) the GENERIC-lemma path: the bodies of the template theorems are the generic lemmas (statements untouched), the generated facts come first
    let (hpre, hk) := match h.splitOn "theorem _root_.@P@.epD2M_hkid" with
      | [a, b] => (a, b)
      | _ => panic! "parentTextS: epD2M_hkid marker not unique"
    -- (unit SR19) the parent's `Inhabited` instance by instance search (the old chain's term is `instInhabitedProd`), not extracted from the old chain
    let t := t.replace "instance _root_.@P@.epD2M_inhab" "noncomputable instance _root_.@P@.epD2M_inhab"
    let t := t.replace "  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys @P@.machineData.ss))) @P@.machine_composedNR2\n    Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA\n" "  ⟨Tools.ShippingSeqParentGenD2MSD.defaultHList _⟩\n"
    let t := t.replace "theorem _root_.@P@.epD2M_hcausal" (gb ++ "\ntheorem _root_.@P@.epD2M_hcausal")
    let full := hpre ++ quadExtra ++ ga ++ "theorem _root_.@P@.epD2M_hkid" ++ hk ++ t
    Tools.ShippingSeqParentGenD2MSG.bodies.foldl (fun s (m, b) => Tools.ShippingSeqParentGenD2MSG.replaceBody s m b) full

def assembleMS (p : D2MParams) (g : Option Tools.ShippingSeqParentGenD2MSG.GenInfo := none) : String :=
  let tcs := if g.isSome then "" else "\n".intercalate ((rangeR p).map fun i => sub1 p i tcTmpl)
  let pat := "".intercalate ((List.range p.mP).map fun _ => "_ | ") ++ "k"
  let ptxt := parentTextS (g.map fun gi => (Tools.ShippingSeqParentGenD2MSG.genA p, Tools.ShippingSeqParentGenD2MSG.genB p gi))
  -- generic path: the dispatch families `epD2M_bsF / srcF / PC` belong to the pasted per-callee blocks and are not emitted
  let ptxt := ptxt.replace "@DISPDEFS@" (if g.isSome then ((dispDefs p).splitOn "noncomputable def _root_.@P@.epD2M_bsF").head! else dispDefs p)
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
  -- (unit SR19) the generic path runs under the AMBIENT heartbeat limit: the pre-existing `set_option maxHeartbeats 4000000` of the shared header is dropped from its text
  let hdr := if g.isSome then Tools.ShippingSeqParentGenD2.openBlock2.replace "set_option maxHeartbeats 4000000\n" "" else Tools.ShippingSeqParentGenD2.openBlock2
  let src := hdr ++ tcs ++ ptxt
  (src.replace "@P@" p.P.toString).replace "@KP@" (toString p.kP)

def obtainPatS (p : D2MParams) : String :=
  "⟨O, T, hA, " ++ ", ".intercalate ((rangeR p).map fun i => s!"hM{i}, hR{i}") ++ ", hw⟩"

def endpointSrcS (p : D2MParams) : String :=
  ((((endpointTermM.replace " hw hc" " hw").replace "@OBT@" (obtainPatS p)).replace "@HA@" (hypArgs p)).replace "@P@" p.P.toString).replace "@KP@" (toString p.kP)

/-- (unit SR14, ledger L8at) the term of the RETURNED / WIRED theorem: the generic `Tools.ShippingQuadReturned.quad_returned` / `quad_wired` applied to the generated data facts and
the generated per-callee blocks of the candidate (`epD2M_soundLA` … `epD2M_designCheck`).  `@QR@` is the generic theorem. -/
def returnedTermS : String := r#"(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryP : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape)
    (entry0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C0@ @C0@.machineData.shape)
    (entry1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C1@ @C1@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Tools.ShippingChildInv.Res} (hw : JQC O 0 w)
    (h : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``@P@) mctx mref cctx cref w y w') =>
    @Tools.ShippingQuadReturned.@QR@ _ _ _ _ @P@.machineData @C0@.machineData @C1@.machineData @G@.machineData
      ``@P@ ``@C0@ ``@C1@ ``@G@ @KP@ @K0@ @K1@ 2 @KP@ Unit (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      @P@.machineSource
      (fun i bools bits => @P@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
      (fun i bools bits => @P@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits
        @P@.machineBody @P@.machineExt @P@.machineExtB)
      @P@.machineSource
      (fun i bools bits => @P@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
      (fun i bools bits => @P@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
      (fun hcore entry hB => by
        obtain @OBT@ := hB
        exact @P@.epD2M_soundLA O T hA @HA@ hw hcore entry)
      (fun hcore entry hB => by
        obtain @OBT@ := hB
        exact @P@.epD2M_composedA O T hA @HA@ hw hcore entry)
      @P@.epD2M_houtTy
      (fun hcore hpost entry hB => by
        obtain @OBT@ := hB
        exact @P@.epD2M_runFacts O T 1 hA @HA@ hcore hpost entry hw)
      (fun hcore hpost entry _ hB => by
        obtain @OBT@ := hB
        exact @P@.epD2M_outsCheck O T 1 hA @HA@ hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        obtain @OBT@ := hB
        exact @P@.epD2M_kidsMasked O T 1 hA @HA@ hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        obtain @OBT@ := hB
        exact @P@.epD2M_designCheck O T 1 hA @HA@ hcore hpost entry hw)
      O T hA @P@.epD2M_quadData @P@.epD2M_leafData @P@.epD2M0_calleeData @P@.epD2M1_calleeData entryP entry0 entry1 hR0
      (fun mc cc => @G@.machine_closes mc _ cc _) w w' y hw h)"#

def returnedSrcS (p : D2MParams) (qr : String) : String :=
  let t := ((returnedTermS.replace "@QR@" qr).replace "@OBT@" (obtainPatS p)).replace "@HA@" (hypArgs p)
  let t := t.replace "@C0@" (p.Cs.getD 0 .anonymous).toString |>.replace "@C1@" (p.Cs.getD 1 .anonymous).toString
  let t := t.replace "@G@" (p.Gs.getD 0 .anonymous).toString |>.replace "@K0@" (toString (p.kCs.getD 0 0)) |>.replace "@K1@" (toString (p.kCs.getD 1 0))
  (t.replace "@P@" p.P.toString).replace "@KP@" (toString p.kP)

/-! ## audit of the generated endpoint -/

open Tests.Compiler.ChildVertAuditTest in
def auditS (p : D2MParams) (ep : Name) (generic : Bool := false) : MetaM Unit := do
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
  let common : List Name := [pe "epD2M_soundLA", pe "epD2M_composedA", pe "epD2M_traceXA", pe "epD2M_designCheck", pe "epD2M_runFacts", pe "epD2M_outsCheck",
      pe "epD2M_kidsMasked", pe "epD2M_closes0", pe "epD2M_machineRun", pe "epD2M_quadData", pe "epD2M_leafData", pe "epD2M_hkid",
      ``Tools.ShippingQuadLeafGeneric.quad_closes0, ``Tools.ShippingQuadLeafGeneric.quad_machineRun,
      ``Tools.ShippingQuadLeafGeneric.leafCallee_ifaceP, ``Tools.ShippingQuadLeafGeneric.leafCallee_calleeOK,
      ``Tools.ShippingTopShareRan.machineRanA_start0,
      ``Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA, ``Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA,
      ``Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main, ``Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA,
      ``Tools.ShippingMachineShipsDepth.composedG_of_NW,
      ``Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc]
  -- (unit SR18) the generic path: the emitted proof uses the generic lemmas and the GENERATED per-declaration facts, and none of the pasted per-callee blocks
  let genericMust : List Name := [pe "epD2M_quadAll", pe "epD2M_genP", pe "epD2M_leafRun", pe "epD2M_hFP", pe "epD2M_hPoint0",
      pe "epD2M0_C_gen", pe "epD2M1_C_gen", pe "epD2M0_C_hF", pe "epD2M1_C_hF", pe "epD2M0_C_hextB", pe "epD2M0_C_hext", pe "epD2M1_C_hextB", pe "epD2M1_C_hext",
      pe "epD2M0_C_hPoint0", pe "epD2M1_C_hPoint0",
      ``Tools.ShippingQuadCalls.quad_composed_split, ``Tools.ShippingQuadCalls.leafCallee_hcalls, ``Tools.ShippingQuadComposed.quad_composed,
      ``Tools.ShippingQuadHPoint.callFactF_of_hPointAt, ``Tools.ShippingQuadCallFacts.callFactF_of_fam, ``Tools.ShippingQuadCallFacts.quadSrcF_eq,
      ``Tools.ShippingQuadCallFacts.leafSrcC_eq, ``Tools.ShippingQuadCallFacts.extendBits_of_ne, ``Tools.ShippingQuadCallFacts.extendBools_of_ne,
      ``Tools.ShippingQuadComposed.quad_hkid, ``Tools.ShippingQuadComposed.quad_ranA, ``Tools.ShippingQuadComposed.quad_runFacts,
      ``Tools.ShippingQuadComposed.quad_traceXA, ``Tools.ShippingQuadComposed.quad_soundLA]
  -- generic path: `epD2M_traceXA / hkid / closes0 / machineRun` are emitted (statements of the template) but the generic lemmas are used directly by the endpoint's proof, so they are required through the lemmas
  let wrappersNotUsed := [pe "epD2M_traceXA", pe "epD2M_hkid", pe "epD2M_closes0", pe "epD2M_machineRun"]
  let missing := (if generic then (common.filter (!wrappersNotUsed.contains ·)) ++ genericMust else common ++ perCallee).filter fun must => !cl.contains must
  unless missing.isEmpty do throwError "SR13 AUDIT FAILED: {missing} not in the closure of {ep}"
  if generic then
    for no in perCallee do
      if !(no.toString.endsWith "calleeData") && cl.contains no then throwError "SR18 AUDIT FAILED: the pasted per-callee block {no} is in the closure of {ep}"
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
  logInfo m!"SR13 AUDIT OK: {ep}: standard axioms; outer Prop premises ASSERTED {premises}; closure {cl.size} constants, none of ChildBnd/StartV/GenKid/old KidFacts/MachineRunNC/machineRunNC_of_real/seqChildRunN_of_composedC; neither {pe "epD2M_closesA"} nor {pe "epD2M_disj"} (they need hdisjD) is in the closure; the old generated theorems are not in the closure; {bnd} (an EXISTENTIAL over O/T/AdmCtx/MachineDefines of {p.Cs} and the shared leaf {p.Gs.getD 0 .anonymous}/start world JQC O 0, not a proof that it holds) stays in the conclusion; chains {p.Cs.zip p.Gs}{if generic then "; [SR18 generic-lemma path: the proof uses quad_composed_split / callFactF_of_hPointAt / quad_* and the generated per-declaration facts, no pasted per-callee block]" else ""}"

/-! ## the command (a fourth elaborator; tried FIRST, defers to the existing ones) -/

register_option sparkle.sharedLeafTiming : Bool := {
  defValue := false
  descr := "SR19: log, for every command of the generic-lemma path, its heartbeats (in the unit of `maxHeartbeats`: raw count / 1000) and the process peak RSS (measurement only; default off)" }

register_option sparkle.sharedLeafInject : String := {
  defValue := ""
  descr := "SR19 TEST HOOK (default empty = off): `decl` appends a deliberately failing declaration to the generic path's text, `audit` makes the generic path's audit fail; either way the generic path must fall back to the SR13 path" }

/-- peak resident set size of this process in kB (`VmHWM`), `0` if unreadable -/
def peakRssKb : IO Nat := do
  try
    let t ← IO.FS.readFile "/proc/self/status"
    for l in t.splitOn "\n" do
      if l.startsWith "VmHWM:" then
        return ((l.drop 6).trimAscii.takeWhile Char.isDigit).toString.toNat!
    return 0
  catch _ => return 0

/-- `Tools.ShippingSeqParentGen.runCmds` with the elaboration errors of the failing command in the thrown message (unit SR18: the generic path logs WHICH generated declaration failed and why) -/
def runCmdsDiag (src : String) : CommandElabM Unit := do
  let inputCtx := Parser.mkInputContext src "<seq-parent-gen>"
  let mut pstate : Parser.ModuleParserState := {}
  let mut msgs : MessageLog := {}
  repeat
    let scope ← getScope
    let pmctx : Parser.ParserModuleContext :=
      { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps', msgs') := Parser.parseCommand inputCtx pmctx pstate msgs
    pstate := ps'; msgs := msgs'
    if Parser.isTerminalCommand cmd then break
    if msgs.hasErrors then
      throwError "template parse error: {← msgs.toList.mapM (·.toString)}"
    let msgs0 := (← get).messages
    modify fun s => { s with messages := {} }
    let hb0 ← IO.getNumHeartbeats
    let t0 ← IO.monoMsNow
    elabCommand cmd
    let hb1 ← IO.getNumHeartbeats
    let t1 ← IO.monoMsNow
    let ms := (← get).messages
    modify fun s => { s with messages := msgs0 ++ ms }
    let txt : String := match cmd.getPos?, cmd.getTailPos? with
      | some a, some b => (Substring.Raw.toString ⟨src, a, b⟩).take 160 |>.toString
      | _, _ => ""
    if sparkle.sharedLeafTiming.get (← getOptions) && (txt.startsWith "theorem" || txt.startsWith "instance" || txt.startsWith "noncomputable") then
      logInfo m!"SR19 TIMING: heartbeats {(hb1 - hb0) / 1000} (the unit of maxHeartbeats, default limit 200000), {t1 - t0} ms, peak RSS {(← peakRssKb) / 1024} MB, errors {ms.hasErrors}: {(txt.splitOn " :=").head!.take 110}"
    if ms.hasErrors then
      let errs ← (ms.toList.filter (·.severity == .error)).mapM fun m => m.data.toString
      throwError "the generated command failed: {txt} … ERRORS: {errs.take 2}"

/-- facts read from the environment for the generic path -/
def genInfoS (p : D2MParams) : CommandElabM Tools.ShippingSeqParentGenD2MSG.GenInfo := do
  let nat := fun (s : String) (n : Name) => liftTermElabM do reduceNat (← elabText (s.replace "@F@" n.toString))
  let mCs ← p.Cs.mapM (nat "@F@.machineData.shape.insts.length")
  let nOutsG ← nat "@F@.machineData.shape.layout.outs.length" (p.Gs.getD 0 .anonymous)
  -- (unit SR19) the decoding data of every call, read from the generated `machineExt` / `machineExtB` (no old chain)
  let argLists := fun (n : Name) => liftTermElabM do readNatLists (← elabText (s!"({n}.machineData.shape.insts.map (·.2.1))"))
  let mut calleeCalls := []
  for (C, i) in p.Cs.zipIdx do
    let G := p.Gs.getD i .anonymous
    let al ← argLists C
    let kC := p.kCs.getD i 0
    let cds ← (List.range (mCs.getD i 0)).mapM fun k =>
      liftTermElabM <| Tools.ShippingSeqParentGenD2MSD.callDecOf C G kC k none (al.getD k [])
    calleeCalls := calleeCalls ++ [cds]
  let alP ← argLists p.P
  let parentCalls ← (List.range p.mP).mapM fun k => do
    let ci := p.instCallee.getD k 0
    liftTermElabM <| Tools.ShippingSeqParentGenD2MSD.callDecOf p.P (p.Cs.getD ci .anonymous) p.kP k (some (p.kCs.getD ci 0)) (alP.getD k [])
  return { mCs := mCs, nOutsG := nOutsG, calleeCalls := calleeCalls, parentCalls := parentCalls }

/-- generate, audit and register `fn.epD2M_endpoint` (+ returned / wired); `gen = some _`: the generic-lemma path of unit SR18 -/
def runPathS (fn : Name) (p : D2MParams) (gen : Option Tools.ShippingSeqParentGenD2MSG.GenInfo) : CommandElabM Unit := do
  let src := assembleMS p gen
  -- (unit SR19, test hook) a deliberately failing generated declaration, placed AFTER the generated facts so that earlier declarations exist when it fails
  let inj := sparkle.sharedLeafInject.get (← getOptions)
  let src := if gen.isSome && inj == "decl" then
      src.replace ("theorem _root_.@P@.epD2M_composedA".replace "@P@" p.P.toString)
        (s!"theorem _root_.{p.P}.epD2M_injected : (1 : Nat) = 2 := by decide\n\n" ++ "theorem _root_.@P@.epD2M_composedA".replace "@P@" p.P.toString)
    else src
  try
    if gen.isSome then runCmdsDiag src else Tools.ShippingSeqParentGen.runCmds src
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
    if gen.isSome && inj == "audit" then throwError "SR19 injected audit failure"
    liftTermElabM <| auditS p ep gen.isSome
    -- unit SR14 (L8at): the RETURNED (`y.2 = Dg`) and WIRED theorems, from the generic theorems
    for (nm, qr) in [(`epD2M_returned, "quad_returned"), (`epD2M_wired, "quad_wired")] do
      liftTermElabM do
        let some stx := (Parser.runParserCategory (← getEnv) `term (returnedSrcS p qr)).toOption
          | throwError "{nm} term: parse error"
        let e ← elabTerm stx none
        synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        let ty ← instantiateMVars (← inferType e)
        if e.hasMVar || ty.hasMVar then throwError "#machine_seq_parent_endpoint (SR14 candidate): unassigned mvars in the {nm} term"
        addAndCompile <| .thmDecl { name := fn ++ nm, levelParams := [], type := ty, value := e }
        Tests.Compiler.ChildVertAuditTest.stdAxioms (fn ++ nm)
  finally
    Tools.ShippingSeqParentGen.runCmds "end"



/-- (unit SR20) run the elaborators registered for `stx` OTHER than this one, in registration order of precedence, exactly as `elabCommand` would after `unsupportedSyntax` -- but WITHOUT
the state rollback that `unsupportedSyntax` performs (it would discard the log of the failure of the generic path).  The first one that does not defer decides (its own errors propagate). -/
def runOtherElabs (stx : Syntax) : CommandElabM Unit := do
  let ents := (Lean.Elab.Command.commandElabAttribute.getEntries (← getEnv) stx.getKind).filter (·.declName != `Tools.ShippingSeqParentGenD2MS.elabEndpointD2MS)
  for e in ents do
    try
      e.value stx
      return
    catch ex =>
      match ex with
      | .internal id _ => if id == Lean.Elab.unsupportedSyntaxExceptionId then continue else throw ex
      | _ => throw ex
  throwError "#machine_seq_parent_endpoint: no other elaborator accepted the declaration"

open Tools.ShippingSeqParentGen in
@[command_elab Tools.ShippingSeqParentGen.«command#machine_seq_parent_endpoint_»]
def elabEndpointD2MS : CommandElab := fun stx => do
  unless sparkle.sharedLeafCandidate.get (← getOptions) do throwUnsupportedSyntax
  let f : Ident := ⟨stx[1]⟩
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  unless (← getEnv).contains (fn ++ `machineData) do throwUnsupportedSyntax
  let pc ← liftTermElabM do readNames (← elabText (s!"({fn}.machineData.shape.insts.map (·.1))"))
  unless pc.eraseDups.length ≥ 2 do throwUnsupportedSyntax
  -- (unit SR20) the GENERIC path is analysed WITHOUT the old chain (partition from the generated machineExt); the SR13 fallback needs the old chain and is available only if it exists
  let some pg ← analyseG fn | throwUnsupportedSyntax
  let oldThm := fn ++ `machine_composedNR2
  let pOld? : Option D2MParams ← if (← getEnv).contains oldThm then
      (try analyseS fn catch e =>
        logInfo m!"SR20: the old chain of {fn} is present but unusable for the SR13 fallback: {e.toMessageData}"; pure none)
    else pure none
  logInfo m!"SR13 shared-leaf candidate (class QUAD): {pg.P} calls {pg.Cs} (call list {pc}), all of which call the SAME leaf {pg.Gs.getD 0 .anonymous} (kP {pg.kP}, kC {pg.kCs}); {pg.mP} call instance(s), groups {pg.groups} (instance -> group {pg.instGroup}; numbering: {pg.partitionNote}); leaf argument widths {pg.gws}; old chain {if pOld?.isSome then "present (SR13 fallback available)" else "absent or unusable (no SR13 fallback)"}"
  -- (unit SR18, L8ax) first the GENERIC-lemma path; if one of its generated declarations fails to check (or the audit fails) nothing of it is kept, the failure is logged and
  -- the SR13 path (pasted per-callee blocks) runs instead.
  -- (unit SR20) WITHOUT an old chain there is no SR13 path: the failure is logged, the state restored, and the command throws `unsupportedSyntax`, i.e. the pre-existing elaborators
  -- run (for a shared-leaf parent: their own SR3x refusal, which names the old chain).  This elaborator itself refuses nothing and keeps nothing of the failed attempt.
  let saved ← get
  let generic ← try
      -- (unit SR20) without the old chain nobody has generated the leaf's run theorem: the machine-route generator of the old chain's first step is called for the leaf alone
      -- (`Tools.ShippingMachineDepthCommand.generateSeqChildN`: a theorem built from the leaf's `machine_sound`, kernel-checked, nothing of the old chain's composed theorems)
      for G in pg.Gs.eraseDups do
        unless (← getEnv).contains (G ++ `seq_child_runN) do
          discard <| liftTermElabM <| withOptions (fun o => Lean.Elab.async.set o false) (Tools.ShippingMachineDepthCommand.generateSeqChildN G)
      let gi ← genInfoS pg
      runPathS fn pg (some gi)
      pure true
    catch e =>
      set saved
      logInfo m!"SR18: the generic-lemma path FAILED for {fn} (a generated declaration did not check, or the audit failed): {e.toMessageData}; nothing of it is kept{if pOld?.isSome then ", falling back to the SR13 path" else ", NO old chain: no SR13 fallback; the pre-existing elaborators run"}"
      pure false
  unless generic do
    match pOld? with
    | some p => runPathS fn p none
    | none => runOtherElabs stx

end Tools.ShippingSeqParentGenD2MS
