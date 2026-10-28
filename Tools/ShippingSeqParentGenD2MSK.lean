import Tools.ShippingSeqParentGenD2MS
import Tools.ShippingKaryBridge
import Tools.ShippingKaryReturned
import Tools.ShippingKaryFacts
-- BUILT (unit SR22): g2 exit 0 (Tests.Compiler.KaryGenTest, dev run; this module and its injection hook); the final-SHA rebuild is in REPORT-SR22.md.
/-! # `#machine_seq_parent_endpoint P` — the K-ary shared-leaf CANDIDATE (unit SR22, ledger L8bb)

STATUS (binding): a CANDIDATE, opt-in.  `set_option sparkle.karyCandidate true` (default `false`) lets THIS elaborator (registered after `Tools.ShippingSeqParentGenD2MS`, so tried first) take over a
declaration `P` of the K-ary class stated below; with the option off, for `K = 2`, or for every declaration outside the class it throws `unsupportedSyntax` and the elaborators registered earlier
(`Tools/ShippingSeqParentGenD2MS.lean` and the `ShippingSeqParentGen*` ones) run exactly as before.  `K = 2` is deliberately NOT taken: the existing QUAD path (SR13–SR20) keeps producing its (unchanged)
statements, so the existing `SharedLeafGen*` audits are unaffected under every setting of this option.

## The K-ary class used by this generator (read from the stored `machineData` before any text is generated; each condition is only a PRE-FILTER, the kernel-checked declarations decide)
* (K0) the instance list of `P` (`machineData.shape.insts`, which carries the TWO instances of each source call, consecutively) is `[C₀, C₀, C₁, C₁, …, C_{K-1}, C_{K-1}]`, `K ≥ 1`, `K ≠ 2`, the `C_i` pairwise different (so each callee has ONE source call), none a memory;
* (K1) every callee has call instances, none a memory, all to ONE leaf `G` (the same for every callee; each callee may call it one or more times); `G` is not a memory and has no call instances;
  `G ∉ {C_i, P}`;
* (K2) the decidable data facts (`KaryParentData`, `KaryParentExtra`, `LeafCalleeData`, `LeafCalleeExtra`, `LeafData`, `LeafKidData` of `Tools/ShippingKary*.lean` and `ShippingQuad*.lean`) are discharged by `decide` in the generated
  text, the per-call decoding equations (`HPointAt`) and `GenFacts` by the templates of `Tools/ShippingSeqParentGenD2MSG.lean` / `…D2MSD.lean`.
The generated declarations are per-declaration facts about `P`, its callees and its leaf (instance-specific, each kernel-checked), NOT a class theorem; three examples (`topshare`, `topshare2` through the QUAD
path, `topshare3` here) do not make the class complete.  Whatever fails (a data fact, a decoding equation, the audit) makes the command LOG the failing declaration, restore the state and run the
pre-existing elaborators (`runOtherElabs`): this elaborator itself refuses nothing.  Everything is generated under the AMBIENT `maxHeartbeats` (no raise in the text).
What stays a PREMISE of a generated endpoint: the existential `O` / `T` / `AdmCtx` / `MachineDefines` of the callees and the leaf / `JQC O 0 w` (inside `KaryBnd`), the run `hr`, `entry`, the leaf's `MachineCloses`
(`G.machine_closes`); `RealChildA` / `ServedRealA` / `JQC` are histories of past synthesis results, not semantic correctness in the current environment. -/
namespace Tools.ShippingSeqParentGenD2MSK
open Lean Elab Command Meta Term
open Tools.ShippingSeqParentGen (runCmds elabText readNames readName reduceNat)
open Tools.ShippingSeqParentGenD2 (readNatLists)
open Tools.ShippingSeqParentGenD2MSG (calleeGenTmpl calleePointTmpl calleeHFTmpl calleeFam parentGenTmpl decHaves pointAlts)
open Tools.ShippingSeqParentGenD2MSD (callDecOf CallDec)

register_option sparkle.karyCandidate : Bool := {
  defValue := false
  descr := "SR22: let `#machine_seq_parent_endpoint` take over the K-ary shared-leaf class (K callees, one source call each (two consecutive instances), one shared leaf; K != 2) (candidate; default off)" }

def patK (m : Nat) : String := "".intercalate ((List.range m).map fun _ => "_ | ") ++ "k"

/-- the callee template placeholders -/
def subC (P C G : Name) (i kC : Nat) (s : String) : String :=
  (((((s.replace "@P@" P.toString).replace "@I@" (toString i)).replace "@C@" C.toString).replace "@G@" G.toString).replace "@KC@" (toString kC))

def dataTmpl : String := r#"
theorem _root_.@P@.epK_leafData : Tools.ShippingQuadLeafGeneric.LeafData @G@.machineData :=
  ⟨@G@.machine_ok, @G@.machine_body, by first | decide | decide +kernel, by first | decide | decide +kernel⟩

theorem _root_.@P@.epK_leafKid : Tools.ShippingQuadComposed.LeafKidData @G@.machineData := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel | exact fun h0 => absurd (congrArg List.length h0) (by decide)

noncomputable abbrev _root_.@P@.epK_cs : List Tools.ShippingKaryRun.KCal := @CSLIT@

theorem _root_.@P@.epK_parentData :
    Tools.ShippingKaryLeafGeneric.KaryParentData @P@.machineData @P@.epK_cs ``@P@ ``@G@ @KP@ := by
  refine ⟨@P@.machine_ok, @P@.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem _root_.@P@.epK_parentExtra : Tools.ShippingKaryComposed.KaryParentExtra @P@.machineData @P@.epK_cs @KP@ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel | exact fun h0 => absurd (congrArg List.length h0) (by decide)
"#

def calleeDataTmpl : String := r#"
theorem _root_.@P@.epK@I@_calleeData :
    Tools.ShippingQuadLeafGeneric.LeafCalleeData @C@.machineData @G@.machineData ``@C@ ``@G@ @KC@ := by
  refine ⟨@C@.machine_ok, @C@.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem _root_.@P@.epK@I@_calleeExtra : Tools.ShippingQuadComposed.LeafCalleeExtra @C@.machineData @G@.machineData @KC@ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | decide +kernel
"#

def allTmpl : String := r#"
theorem _root_.@P@.epK_callees : Tools.ShippingKaryLeafGeneric.KaryCallees @P@.epK_cs @G@.machineData ``@G@ :=
  Tools.ShippingKaryComposed.kandk_forall (r := True) (p := fun e : Tools.ShippingKaryRun.KCal => Tools.ShippingQuadLeafGeneric.LeafCalleeData e.d @G@.machineData e.c ``@G@ e.n)
    (l := @P@.epK_cs) (@CALLEEPROOF@) |>.1

theorem _root_.@P@.epK_all : Tools.ShippingKaryComposed.KaryAll @P@.machineData @G@.machineData @P@.epK_cs ``@P@ ``@G@ @KP@ :=
  ⟨@P@.epK_parentData, @P@.epK_parentExtra, @P@.epK_leafData, @P@.epK_leafKid, @P@.epK_callees,
   (Tools.ShippingKaryComposed.kandk_forall (r := True) (p := fun e : Tools.ShippingKaryRun.KCal => Tools.ShippingQuadComposed.LeafCalleeExtra e.d @G@.machineData e.n)
    (l := @P@.epK_cs) (@EXTRAPROOF@)).1⟩

noncomputable instance _root_.@P@.epK_inhab : Inhabited (HList (Tools.ShippingMachineDenote.tys @P@.machineData.ss)) :=
  ⟨Tools.ShippingSeqParentGenD2MSD.defaultHList _⟩
"#

def parentPointTmpl : String := r#"
theorem _root_.@P@.epK_hPoint@CK@ : Tools.ShippingQuadHPoint.HPointAt @P@.machineData @KP@ (ι := Unit) (dom := fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
    (fun _ => Sparkle.Core.Domain.defaultDomain) @FAM@
    (Tools.ShippingKaryComposed.kBsF @P@.epK_cs) (Tools.ShippingKaryFacts.kSrcA @P@.epK_cs) @CK@ := by
  intro i bools bits hk
@HBHV@
@ALTS@
"#

def parentFamK : String := r#"(Tools.ShippingMachineCausal.letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineExt @P@.machineExtB)
    (fun i bools bits => @P@.machineExt i bools bits (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
    (fun i bools bits => @P@.machineExtB i bools bits (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
    (Tools.ShippingKaryComposed.kOutsOf @P@.epK_cs)"#

def parentHFTmplK : String := r#"
theorem _root_.@P@.epK_hFP : Tools.ShippingQuadCalls.CallFactF @P@.machineData @KP@
    @FAM@
    (Tools.ShippingKaryComposed.kSrcF @P@.epK_cs) :=
  Tools.ShippingQuadHPoint.callFactF_of_hPointAt _ _ (fun _ => Sparkle.Core.Domain.defaultDomain)
    (Tools.ShippingKaryComposed.kBsF @P@.epK_cs) (Tools.ShippingKaryFacts.kSrcA @P@.epK_cs)
    (fun i n v => Tools.ShippingKaryFacts.kSrcF_eq _ i n v)
    (fun k hk => by
      have hl : @P@.machineData.shape.insts.length = @MC@ := by decide
      rcases k with @MPAT@
      all_goals first
        | omega
@EXACTS@)
"#

def kgenTmpl : String := r#"
noncomputable def _root_.@P@.epK@I@_kgen : Tools.ShippingKaryCalls.KaryGen ⟨``@C@, @C@.machineData, @KC@, @C@.machineSource⟩ ``@G@ @G@.machineData @G@.machineSource :=
  { inh := @P@.epD2M@I@_C_inhab, ρ := _, inits := @C@.machineInits, body := @C@.machineBody, obsR := @C@.machineResult, ext := @C@.machineExt,
    extB := @C@.machineExtB, gen := @P@.epD2M@I@_C_gen, hF := @P@.epD2M@I@_C_hF, hextB := @P@.epD2M@I@_C_hextB, hext := @P@.epD2M@I@_C_hext }
"#

/-- the text of every declaration for `P` with callees `Cs` (own inputs `kCs`) sharing the leaf `G` -/
def genText (P : Name) (Cs : List Name) (kCs : List Nat) (G : Name) (kP mP : Nat) (mCs : List Nat) (nOutsG : Nat)
    (calleeCalls : List (List CallDec)) (parentCalls : List CallDec) (parentCallee : List Nat) : String := Id.run do
  let cslit := "[" ++ ", ".intercalate ((Cs.zip kCs).map fun (C, kC) => s!"⟨``{C}, {C}.machineData, {kC}, {C}.machineSource⟩") ++ "]"
  let rep := fun (s : String) => ((s.replace "@P@" P.toString).replace "@G@" G.toString).replace "@KP@" (toString kP)
  let mut out := (rep dataTmpl).replace "@CSLIT@" cslit
  for (C, i) in Cs.zipIdx do
    out := out ++ subC P C G i (kCs.getD i 0) calleeDataTmpl
  let cp := "⟨" ++ ", ".intercalate ((Cs.zipIdx).map fun (_, i) => s!"{P}.epK{i}_calleeData") ++ ", trivial⟩"
  let xp := "⟨" ++ ", ".intercalate ((Cs.zipIdx).map fun (_, i) => s!"{P}.epK{i}_calleeExtra") ++ ", trivial⟩"
  out := out ++ (rep allTmpl).replace "@CALLEEPROOF@" cp |>.replace "@EXTRAPROOF@" xp
  -- the callees' own facts (generator templates)
  for (C, i) in Cs.zipIdx do
    let kC := kCs.getD i 0
    out := out ++ subC P C G i kC calleeGenTmpl
  out := out ++ rep parentGenTmpl
  for (C, i) in Cs.zipIdx do
    let kC := kCs.getD i 0
    let mC := mCs.getD i 0
    let lsrcC := s!"(Tools.ShippingMachineCausal.letObsB {C}.machineData (fun i : Sparkle.Core.Domain.DomainConfig => i) {C}.machineInits {C}.machineBody {C}.machineExt {C}.machineExtB i bools bits)"
    for k in List.range mC do
      let some cd := (calleeCalls.getD i [])[k]? | panic! s!"no decoding data for call {k} of {C}"
      out := out ++ ((subC P C G i kC (calleePointTmpl.replace "@FAM@" calleeFam)).replace "@CK@" (toString k)
        |>.replace "@HBHV@" (decHaves "i" s!"{G}.machineData.bsIn" lsrcC cd)
        |>.replace "@ALTS@" (pointAlts [(0, nOutsG)]))
    out := out ++ ((subC P C G i kC (calleeHFTmpl.replace "@FAM@" calleeFam)).replace "@MC@" (toString mC) |>.replace "@MPAT@" (patK mC)).replace "@EXACTS@"
      ("\n".intercalate ((List.range mC).map fun k => s!"        | exact {P}.epD2M{i}_C_hPoint{k}"))
  let lsrcP := s!"(Tools.ShippingMachineCausal.letObsB {P}.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) {P}.machineInits {P}.machineBody {P}.machineExt {P}.machineExtB i bools bits)"
  for k in List.range mP do
    let some cd := parentCalls[k]? | panic! s!"no decoding data for call {k} of {P}"
    let ci := parentCallee.getD k 0
    out := out ++ (((rep parentPointTmpl).replace "@FAM@" (rep parentFamK)).replace "@CK@" (toString k)
      |>.replace "@HBHV@" (decHaves "Sparkle.Core.Domain.defaultDomain" s!"(List.take {kCs.getD ci 0} {Cs.getD ci .anonymous}.machineData.bsIn)" lsrcP cd)
      |>.replace "@ALTS@" (pointAlts [(0, nOutsG)]))
  out := out ++ ((((rep parentHFTmplK).replace "@FAM@" (rep parentFamK)).replace "@MC@" (toString mP)).replace "@MPAT@" (patK mP)).replace "@EXACTS@"
    ("\n".intercalate ((List.range mP).map fun k => s!"        | exact {P}.epK_hPoint{k}"))
  for (C, i) in Cs.zipIdx do
    out := out ++ subC P C G i (kCs.getD i 0) kgenTmpl
  out := out ++ s!"
noncomputable def _root_.{P}.epK_gens : ∀ (j : Nat) (hj : j < {P}.epK_cs.length), Tools.ShippingKaryCalls.KaryGen ({P}.epK_cs[j]) ``{G} {G}.machineData {G}.machineSource :=
  fun j hj => match j, hj with
" ++ "\n".intercalate ((Cs.zipIdx).map fun (_, i) => s!"  | {i}, _ => {P}.epK{i}_kgen") ++ s!"
  | n + {Cs.length}, h => absurd h (by simp [{P}.epK_cs])
"
  return out

/-! ## the endpoint / returned / wired terms (text) -/

def hclTxt (G : Name) : String := s!"(fun mc cc => {G}.machine_closes mc _ cc _)"
def obtTxt (indent : Nat := 6) : String :=
  "obtain ⟨O, T, hA, hB'⟩ := hB\n" ++ "".pushn ' ' indent ++ "obtain ⟨hent, hR0, hw⟩ := Tools.ShippingKaryComposed.kandk_forall hB'"

/-- the endpoint term: `machine_design_noShips_noBd_dc` applied to the K-ary blocks (no pasted per-callee block, no old chain) -/
def endpointK (P G : Name) (kP : Nat) : String :=
  let hcl := hclTxt G
  let obt := obtTxt
  s!"(@Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc 2 (Tools.ShippingKaryComposed.KaryBnd {P}.epK_cs ``{G} {G}.machineData) (fun _ _ _ _ => True)
    ``{P} {P}.machineData {kP} Unit (fun _ => Sparkle.Core.Domain.defaultDomain) _ _ _ _ _ _ _
    (fun hcore entry _ hB => by
      {obt}
      exact Tools.ShippingKaryComposed.kary_soundLA O T hA {P}.epK_all {P}.epD2M_genP entry hent hR0 {hcl} hw hcore)
    (fun hcore entry _ hB _ => by
      exact Tools.ShippingKaryCalls.kary_composed_split {P}.epK_all {P}.epD2M_genP {P}.epK_gens {P}.epD2M_leafRun {P}.epK_hFP {hcl} hcore entry hB)
    {P}.epK_all.hPX.outTy
    (fun hcore hpost entry hB => by
      {obt}
      exact Tools.ShippingKaryComposed.kary_runFacts O T 1 hA {P}.epK_all hent hR0 {hcl} hcore hpost entry hw)
    (fun hcore hpost entry _ hB => by
      {obt}
      exact Tools.ShippingKaryComposed.kary_outsCheck O T 1 hA {P}.epK_all hent hR0 {hcl} hcore hpost entry hw)
    (fun hcore hpost entry hB => by
      {obt}
      exact Tools.ShippingKaryComposed.kary_kidsMasked O T 1 hA {P}.epK_all hent hR0 {hcl} hcore hpost entry hw)
    (fun hcore hpost entry hB => by
      {obt}
      exact Tools.ShippingKaryComposed.kary_designCheck O T 1 hA {P}.epK_all hent hR0 {hcl} hcore hpost entry hw))"

/-- the RETURNED / WIRED term: `Tools.ShippingKaryReturned.kary_returned` / `kary_wired` (`qr`) applied to the generated data facts and the K-ary blocks.  The callees' `MachineDefines` are
`entry0 … entry{K-1}`; `hent` is built from them. -/
def returnedK (P G : Name) (Cs : List Name) (kP : Nat) (qr : String) : String :=
  let hcl := hclTxt G
  let obt := obtTxt 8
  let entryBinders := " ".intercalate ((Cs.zipIdx).map fun (C, i) =>
    s!"(entry{i} : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``{C} {C}.machineData.shape)")
  let entriesTuple := "⟨" ++ ", ".intercalate ((Cs.zipIdx).map fun (_, i) => s!"entry{i}") ++ ", trivial⟩"
  s!"(fun \{mctx : Lean.Meta.Context} \{mref : ST.Ref IO.RealWorld Lean.Meta.State}
    \{cctx : Lean.Core.Context} \{cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (T : Tools.ShippingChildInvA.RefLawsATele O.quiet mref cref) (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx)
    (entryP : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``{P} {P}.machineData.shape)
    {entryBinders}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``{G} {G}.machineData.shape)
    \{w w' : Void IO.RealWorld} \{y : Tools.ShippingChildInv.Res} (hw : Tools.ShippingChildCacheA.JQC O 0 w)
    (h : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``{P}) mctx mref cctx cref w y w') =>
    Tools.ShippingKaryReturned.{qr} (dP := {P}.machineData) (dG := {G}.machineData) (cs := {P}.epK_cs) (c := ``{P}) (G := ``{G}) (nP := {kP})
      (n := 2) (kD := {kP}) (ι := Unit) (dom := fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      (src := {P}.machineSource)
      (ext := fun i bools bits => {P}.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop {P}.machineInits ({P}.machineBody i bools bits)))
      (extB := fun i bools bits => {P}.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop {P}.machineInits ({P}.machineBody i bools bits)))
      (lsrc := Tools.ShippingMachineCausal.letObsB {P}.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) {P}.machineInits
        {P}.machineBody {P}.machineExt {P}.machineExtB)
      (srcL := {P}.machineSource)
      (extL := fun i bools bits => {P}.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop {P}.machineInits ({P}.machineBody i bools bits)))
      (extBL := fun i bools bits => {P}.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop {P}.machineInits ({P}.machineBody i bools bits)))
      (fun hcore entry hB => by
        {obt}
        exact Tools.ShippingKaryComposed.kary_soundLA O T hA {P}.epK_all {P}.epD2M_genP entry hent hR0 {hcl} hw hcore)
      (fun hcore entry hB => by
        exact Tools.ShippingKaryCalls.kary_composed_split {P}.epK_all {P}.epD2M_genP {P}.epK_gens {P}.epD2M_leafRun {P}.epK_hFP {hcl} hcore entry hB)
      {P}.epK_all.hPX.outTy
      (fun hcore hpost entry hB => by
        {obt}
        exact Tools.ShippingKaryComposed.kary_runFacts O T 1 hA {P}.epK_all hent hR0 {hcl} hcore hpost entry hw)
      (fun hcore hpost entry _ hB => by
        {obt}
        exact Tools.ShippingKaryComposed.kary_outsCheck O T 1 hA {P}.epK_all hent hR0 {hcl} hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        {obt}
        exact Tools.ShippingKaryComposed.kary_kidsMasked O T 1 hA {P}.epK_all hent hR0 {hcl} hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        {obt}
        exact Tools.ShippingKaryComposed.kary_designCheck O T 1 hA {P}.epK_all hent hR0 {hcl} hcore hpost entry hw)
      O T hA {P}.epK_all.hP {P}.epK_all.hG {P}.epK_callees
      (Tools.ShippingKaryComposed.kandk_forall (p := fun e : Tools.ShippingKaryRun.KCal => Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref e.c e.d.shape)
        (r := True) (l := {P}.epK_cs) {entriesTuple}).1
      entryP hR0 {hcl} hw h)"

/-! ## the audit of the generated declarations -/

open Tests.Compiler.ChildVertAuditTest in
def auditK (ep : Name) (lemma : Name) : MetaM Unit := do
  stdAxioms ep
  let ty ← instantiateMVars (← getConstInfo ep).type
  if ty.hasMVar || ty.hasFVar then throwError "SR22 AUDIT FAILED: metavariables / free variables in the type of {ep}"
  Meta.check ty
  let cl ← depClosure ep
  let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
    `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
    `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
  let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR22 AUDIT FAILED: old boundary / old child predicate in the closure of {ep}: {bad}"
  let oldish := cl.toList.filter fun c => (c.toString.splitOn "machine_composedNR").length > 1 || (c.toString.splitOn "seq_child_runN_ofR").length > 1
  unless oldish.isEmpty do throwError "SR22 AUDIT FAILED: old generated chain theorem(s) in the closure of {ep}: {oldish}"
  unless cl.contains lemma do throwError "SR22 AUDIT FAILED: {lemma} is not in the closure of {ep}"

/-! ## the command -/

register_option sparkle.karyInject : String := {
  defValue := ""
  descr := "SR22 TEST HOOK (default empty = off): `decl` appends a deliberately failing declaration to the K-ary path's text, `audit` makes its audit fail; either way the K-ary path must be undone and the existing elaborators run" }

/-- the facts read for the K-ary class -/
structure KParams where
  P : Name
  Cs : List Name
  G : Name
  kP : Nat
  mP : Nat
  kCs : List Nat
  mCs : List Nat
  nOutsG : Nat

def isPairs : List Name → Option (List Name)
  | [] => some []
  | a :: b :: rest => if a == b then (isPairs rest).map (a :: ·) else none
  | _ => none

/-- the class test (a pre-filter): `none` = this elaborator does not apply -/
def analyseK (fn : Name) : CommandElabM (Option KParams) := do
  let env ← getEnv
  let calleesOf := fun (n : Name) => liftTermElabM do readNames (← elabText (s!"({n}.machineData.shape.insts.map (·.1))"))
  let nat := fun (s : String) (n : Name) => liftTermElabM do reduceNat (← elabText (s.replace "@F@" n.toString))
  let pc ← calleesOf fn
  if pc.isEmpty || pc.any Tools.ShippingSeqParentGenD2.isMemName then return none
  let some Cs := isPairs pc | return none
  if Cs.length == 2 || Cs.length == 0 || !(Cs.eraseDups.length == Cs.length) then return none
  let mut Gs : List Name := []
  for C in Cs do
    unless env.contains (C ++ `machineData) do return none
    let cc ← calleesOf C
    if cc.isEmpty || cc.any Tools.ShippingSeqParentGenD2.isMemName then return none
    let ccs := cc.eraseDups
    unless ccs.length == 1 do return none
    Gs := Gs ++ [ccs.head!]
  let some G := Gs.head? | return none
  unless Gs.all (· == G) do return none
  unless env.contains (G ++ `machineData) do return none
  if Cs.contains G || G == fn then return none
  let gc ← calleesOf G
  if gc.any Tools.ShippingSeqParentGenD2.isMemName then return none
  unless (← nat "@F@.machineData.shape.insts.length" G) == 0 do return none
  let bsMinus := "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)"
  let kP ← nat bsMinus fn
  let kCs ← Cs.mapM (nat bsMinus)
  let mP ← nat "@F@.machineData.shape.insts.length" fn
  let mCs ← Cs.mapM (nat "@F@.machineData.shape.insts.length")
  let nOutsG ← nat "@F@.machineData.shape.layout.outs.length" G
  return some { P := fn, Cs := Cs, G := G, kP := kP, mP := mP, kCs := kCs, mCs := mCs, nOutsG := nOutsG }

/-- generate and register `fn.epK_endpoint`, `fn.epK_returned`, `fn.epK_wired` (every command kernel-checked; the audits run) -/
def runPathK (p : KParams) : CommandElabM Unit := do
  let argLists := fun (n : Name) => liftTermElabM do
    readNatLists (← elabText s!"({n}.machineData.shape.insts.map (·.2.1))")
  let mut calleeCalls : List (List CallDec) := []
  for (C, i) in p.Cs.zipIdx do
    let al ← argLists C
    let cds ← (List.range (p.mCs.getD i 0)).mapM fun k =>
      liftTermElabM <| callDecOf C p.G (p.kCs.getD i 0) k none (al.getD k [])
    calleeCalls := calleeCalls ++ [cds]
  let alP ← argLists p.P
  let parentCallee := (List.range p.mP).map (· / 2)
  let parentCalls ← (List.range p.mP).mapM fun k => do
    let ci := parentCallee.getD k 0
    liftTermElabM <| callDecOf p.P (p.Cs.getD ci .anonymous) p.kP k (some (p.kCs.getD ci 0)) (alP.getD k [])
  unless (← getEnv).contains (p.G ++ `seq_child_runN) do
    discard <| liftTermElabM <| withOptions (fun o => Lean.Elab.async.set o false) (Tools.ShippingMachineDepthCommand.generateSeqChildN p.G)
  let txt := Tools.ShippingSeqParentGenD2.openBlock2.replace "set_option maxHeartbeats 4000000\n" "" ++
    genText p.P p.Cs p.kCs p.G p.kP p.mP p.mCs p.nOutsG calleeCalls parentCalls parentCallee
  for bad in ["maxHeartbeats", "oldGroupFact%", "oldInst%", "oldNamed%", "machine_composedNR", "seq_child_runN_ofR"] do
    if (txt.splitOn bad).length > 1 then throwError "SR22 AUDIT FAILED: the generated text mentions `{bad}`"
  -- (test hook, default off) a deliberately failing generated declaration, placed AFTER the generated facts so that earlier declarations exist when it fails
  let inj := sparkle.karyInject.get (← getOptions)
  let txt := if inj == "decl" then txt ++ s!"\ntheorem _root_.{p.P}.epK_injected : (1 : Nat) = 2 := by decide\n" else txt
  try Tools.ShippingSeqParentGenD2MS.runCmdsDiag txt
  catch e =>
    try Tools.ShippingSeqParentGen.runCmds "end" catch _ => pure ()
    throw e
  try
    for (nm, src, lem) in [(`epK_endpoint, endpointK p.P p.G p.kP, ``Tools.ShippingKaryComposed.kary_soundLA),
        (`epK_returned, returnedK p.P p.G p.Cs p.kP "kary_returned", ``Tools.ShippingKaryReturned.kary_returned),
        (`epK_wired, returnedK p.P p.G p.Cs p.kP "kary_wired", ``Tools.ShippingKaryReturned.kary_wired)] do
      liftTermElabM do
        let stx ← match Parser.runParserCategory (← getEnv) `term src with
          | .ok stx => pure stx
          | .error err => throwError "{nm} term: parse error: {err}"
        let e ← elabTerm stx none
        synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        let ty ← instantiateMVars (← inferType e)
        if e.hasMVar || ty.hasMVar then throwError "SR22: unassigned metavariables in the {nm} term"
        addAndCompile <| .thmDecl { name := p.P ++ nm, levelParams := [], type := ty, value := e }
        auditK (p.P ++ nm) lem
    if inj == "audit" then throwError "SR22 injected audit failure"
  finally
    Tools.ShippingSeqParentGen.runCmds "end"

/-- run the elaborators registered for `stx` OTHER than this one (as `elabCommand` would after `unsupportedSyntax`, but without the state rollback of `unsupportedSyntax`, so the log of the
failure stays); the first one that does not defer decides -/
def runOtherElabsK (stx : Syntax) : CommandElabM Unit := do
  let ents := (Lean.Elab.Command.commandElabAttribute.getEntries (← getEnv) stx.getKind).filter (·.declName != `Tools.ShippingSeqParentGenD2MSK.elabEndpointK)
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
def elabEndpointK : CommandElab := fun stx => do
  unless sparkle.karyCandidate.get (← getOptions) do throwUnsupportedSyntax
  let f : Ident := ⟨stx[1]⟩
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  unless (← getEnv).contains (fn ++ `machineData) do throwUnsupportedSyntax
  let some p ← analyseK fn | throwUnsupportedSyntax
  logInfo m!"SR22 K-ary candidate: {p.P} calls {p.Cs} (two consecutive instances each, one source call each; K = {p.Cs.length}), all of which call the SAME leaf {p.G} (kP {p.kP}, kC {p.kCs}); {p.mP} call instance(s)"
  let saved ← get
  let ok ← try
      runPathK p
      pure true
    catch e =>
      set saved
      logInfo m!"SR22: the K-ary path FAILED for {fn} (a generated declaration did not check, or the audit failed): {e.toMessageData}; nothing of it is kept; the pre-existing elaborators run"
      pure false
  unless ok do runOtherElabsK stx

end Tools.ShippingSeqParentGenD2MSK
