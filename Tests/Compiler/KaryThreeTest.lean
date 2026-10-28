import Tools.ShippingKaryBridge
import Tools.ShippingKaryFacts
import Tools.ShippingSeqParentGenD2MS
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit SR21): k12 exit 0 (dev run); the final-SHA rebuild is in REPORT-SR21.md.
-- SCOPE (binding, ledger L8ba): a NEW example OUTSIDE the two-callee QUAD class, handled by the K-ary lemmas of `Tools/ShippingKary*.lean`: the parent `topshare3` calls THREE different callees
-- `wrapA` (one call of the leaf, argument `x + y`), `wrapB` (two calls, arguments `x`, `y`), `wrapC` (one call, argument `x + x`), all of which call the SAME 16-bit leaf `leafK`; the call list is
-- `[wrapA, wrapA, wrapB, wrapB, wrapC, wrapC]` (asserted).  The generator is NOT used and NOT changed (the three-callee parent is outside its class); the endpoint is hand-applied:
--   * the decidable data facts (`KaryParentData`, `KaryParentExtra`, `LeafCalleeData`, `LeafCalleeExtra`, `LeafData`, `LeafKidData`) are `decide`d on the stored `machineData`;
--   * the per-declaration facts about GENERATED definitions (`GenFacts`, `hextB`, `hext`, the per-call `HPointAt` decoding equations + output defeq, `hF`, `hFP`) are produced by the TEMPLATES and the
--     decoding-data readers of the existing generator modules (`Tools.ShippingSeqParentGenD2MSG` / `…D2MSD`: `calleeGenTmpl`, `calleePointTmpl`, `calleeHFTmpl`, `decHaves`, `callDecOf`), instantiated for
--     the three callees; every produced declaration is checked by the kernel at default heartbeats (per-declaration heartbeats / ms / RSS are logged); the parent's `HPointAt` / `CallFactF` use the
--     K-ary tables (`kBsF`, `kOutsOf`, `kSrcF`, `kSrcA`); the leaf's `seq_child_runN` is built by `generateSeqChildN` (from `leafK.machine_sound`);
--   * the endpoint `topshare3.epK_endpoint` is `machine_design_noShips_noBd_dc` applied to `kary_soundLA` / `kary_composed_split` / `kary_runFacts` / `kary_outsCheck` / `kary_kidsMasked` /
--     `kary_designCheck` (no pasted per-callee block, no old generated chain: `#machine_design_svNR` is never run).
-- Then: a hand-written statement of the endpoint (`Share3Full`) is compared by `isDefEq` with the FULL forall-type of the endpoint, with type-correct mutations REJECTED, and a closure audit.
-- THREE examples (topshare, topshare2, topshare3) do NOT make the class complete.  `O`, `T`, `hA`, `MachineDefines` of the parent / callees / leaf and `JQC O 0 w` stay premises / inside the boundary;
-- `RealChildA` / `ServedRealA` / `JQC` / `MachineRunNCA` are histories of past synthesis results, not semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`.
set_option Elab.async false
section
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
namespace Tests.Compiler.KaryThreeTest

abbrev N := `Tests.Compiler.KaryThreeTest

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

/-- the call structure is ASSERTED by kernel-checked equations -/
theorem topshare3_callees : topshare3.machineData.shape.insts.map (·.1) = [``wrapA, ``wrapA, ``wrapB, ``wrapB, ``wrapC, ``wrapC] := by decide
theorem wrapA_leaf : wrapA.machineData.shape.insts.map (·.1) = [``leafK, ``leafK] := by decide
theorem wrapB_leaf : wrapB.machineData.shape.insts.map (·.1) = [``leafK, ``leafK, ``leafK, ``leafK] := by decide
theorem wrapC_leaf : wrapC.machineData.shape.insts.map (·.1) = [``leafK, ``leafK] := by decide
theorem leafK_nocalls : leafK.machineData.shape.insts = [] := by decide

/-! ## generation of the per-declaration facts (templates of the existing generator modules, instantiated for THREE callees) -/

open Tools.ShippingSeqParentGenD2MSG (calleeGenTmpl calleePointTmpl calleeHFTmpl calleeFam parentGenTmpl decHaves pointAlts)
open Tools.ShippingSeqParentGenD2MSD (callDecOf CallDec)

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


open Lean Elab Command in
def genThree : CommandElabM Unit := do
  let P := N ++ `topshare3
  let Cs := [N ++ `wrapA, N ++ `wrapB, N ++ `wrapC]
  let G := N ++ `leafK
  let nat := fun (s : String) (n : Name) => liftTermElabM do
    Tools.ShippingSeqParentGen.reduceNat (← Tools.ShippingSeqParentGen.elabText (s.replace "@F@" n.toString))
  let kP ← nat "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)" P
  let kCs ← Cs.mapM (nat "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)")
  let mP ← nat "@F@.machineData.shape.insts.length" P
  let mCs ← Cs.mapM (nat "@F@.machineData.shape.insts.length")
  let nOutsG ← nat "@F@.machineData.shape.layout.outs.length" G
  -- the leaf's generated run theorem (from `leafK.machine_sound`; nothing of an old chain)
  unless (← getEnv).contains (G ++ `seq_child_runN) do
    discard <| liftTermElabM <| withOptions (fun o => Lean.Elab.async.set o false) (Tools.ShippingMachineDepthCommand.generateSeqChildN G)
  let argLists := fun (n : Name) => liftTermElabM do
    Tools.ShippingSeqParentGenD2.readNatLists (← Tools.ShippingSeqParentGen.elabText s!"({n}.machineData.shape.insts.map (·.2.1))")
  let mut calleeCalls : List (List CallDec) := []
  for (C, i) in Cs.zipIdx do
    let al ← argLists C
    let cds ← (List.range (mCs.getD i 0)).mapM fun k =>
      liftTermElabM <| Tools.ShippingSeqParentGenD2MSD.callDecOf C G (kCs.getD i 0) k none (al.getD k [])
    calleeCalls := calleeCalls ++ [cds]
  let alP ← argLists P
  -- call `k` of the parent belongs to callee `k / 2` (asserted above by `topshare3_callees`, and re-checked by `KaryParentData.names`)
  let parentCallee := (List.range mP).map (· / 2)
  let parentCalls ← (List.range mP).mapM fun k => do
    let ci := parentCallee.getD k 0
    liftTermElabM <| Tools.ShippingSeqParentGenD2MSD.callDecOf P (Cs.getD ci .anonymous) kP k (some (kCs.getD ci 0)) (alP.getD k [])
  let txt := Tools.ShippingSeqParentGenD2.openBlock2.replace "set_option maxHeartbeats 4000000\n" "" ++
    genText P Cs kCs G kP mP mCs nOutsG calleeCalls parentCalls parentCallee
  for bad in ["maxHeartbeats", "oldGroupFact%", "oldInst%", "oldNamed%", "machine_composedNR", "seq_child_runN_ofR"] do
    if (txt.splitOn bad).length > 1 then throwError "SR21 AUDIT FAILED: the generated text mentions `{bad}`"
  try Tools.ShippingSeqParentGenD2MS.runCmdsDiag txt
  catch e =>
    try Tools.ShippingSeqParentGen.runCmds "end" catch _ => pure ()
    throw e
  Tools.ShippingSeqParentGen.runCmds "end"

set_option sparkle.sharedLeafTiming true in
run_cmd do
  unless (maxHeartbeats.get (← getOptions)) == 200000 do throwError "SR21 AUDIT FAILED: the ambient maxHeartbeats is not the default"
  genThree


/-! ## the endpoint: `machine_design_noShips_noBd_dc` applied to the K-ary blocks (no pasted per-callee block, no old chain) -/

def endpointK (P G : Name) (kP : Nat) : String :=
  let hcl := s!"(fun mc cc => {G}.machine_closes mc _ cc _)"
  let obt := "obtain ⟨O, T, hA, hB'⟩ := hB\n      obtain ⟨hent, hR0, hw⟩ := Tools.ShippingKaryComposed.kandk_forall hB'"
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

open Lean Elab Command Meta Term in
run_cmd do
  let P := N ++ `topshare3
  let G := N ++ `leafK
  liftTermElabM do
    let some stx := (Parser.runParserCategory (← getEnv) `term (endpointK P G 4)).toOption | throwError "endpoint term: parse error"
    let e ← elabTerm stx none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← instantiateMVars (← inferType e)
    if e.hasMVar || ty.hasMVar then throwError "SR21: unassigned metavariables in the endpoint term"
    addAndCompile <| .thmDecl { name := P ++ `epK_endpoint, levelParams := [], type := ty, value := e }

#print axioms Tests.Compiler.KaryThreeTest.topshare3.epK_endpoint

/-! ## the expected WHOLE statement of the endpoint, written by hand (independent of the lemmas), compared by `isDefEq` -/

section
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- The expected run boundary, written by hand: laws `O`, `T` (PREMISES), the admissible contexts, `MachineDefines` of the THREE callees and of the shared leaf, and a start world `JQC O 0 w`. -/
def Share3Bnd : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``wrapA wrapA.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapB wrapB.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapC wrapC.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leafK leafK.machineData.shape ∧
    JQC O 0 w

/-- ALTERED boundary: only TWO callees -/
def Share3BndTwo : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``wrapA wrapA.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapB wrapB.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leafK leafK.machineData.shape ∧
    JQC O 0 w

/-- ALTERED boundary: the start world of the non-shared class (`JQ …` with a cache invariant) -/
def Share3BndJQ : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``wrapA wrapA.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapB wrapB.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapC wrapC.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leafK leafK.machineData.shape ∧
    ∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))

/-- ALTERED boundary: start world `JQC O 1 w` -/
def Share3BndD1 : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``wrapA wrapA.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapB wrapB.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapC wrapC.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leafK leafK.machineData.shape ∧
    JQC O 1 w

/-- ALTERED boundary: the callee `wrapC` replaced by `wrapA` (the third callee's `MachineDefines` missing) -/
def Share3BndNoC : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``wrapA wrapA.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapB wrapB.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapA wrapA.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leafK leafK.machineData.shape ∧
    JQC O 0 w

/-- The expected conclusion of the depth-`n` endpoint of `topshare3` (`kP` own inputs read by the source), written out by hand. -/
def Share3ConclWith (B : Tools.ShippingMachineShipsHier.CtxBnd) (n kP : Nat) (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State)
    (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State) (w : Void IO.RealWorld)
    (b : Sparkle.IR.AST.Module) (design : Design) : Prop :=
  ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (B mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = topshare3.machineData.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = topshare3.machineData.ss.length ∧
          ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
            (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT n),
            (∀ t st, t < T → SourceInputs ``Tests.Compiler.KaryThreeTest.topshare3 (topshare3.machineData.bsIn.take kP) ids cache
              (fun j => ((fun i bools bits => topshare3.machineExtB i bools bits
                (Tools.ShippingMachineSource.stateLoop topshare3.machineInits (topshare3.machineBody i bools bits))) i bools bits j).val (T - 1 - t))
              (fun j n => ((fun i bools bits => topshare3.machineExt i bools bits
                (Tools.ShippingMachineSource.stateLoop topshare3.machineInits (topshare3.machineBody i bools bits))) i bools bits j n).val (T - 1 - t))
              (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              topshare3.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
            ResetNk n raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
            Bounded (weS (checkedOptimize b)) st0 →
            (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
              childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) n gc (kids iname)) →
            (∃ envsO,
              DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                topshare3.machineData.shape.layout.outs[k]? = some o → (topshare3.machineSource i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)
            ∧ ∀ envs', DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  topshare3.machineData.shape.layout.outs[k]? = some o → (topshare3.machineSource i bools bits)[k]? = some f →
                  (envs'[j]'hj) o.name = f j)

/-- The expected FULL type of the endpoint `topshare3.epD2M_endpoint` (outer binders included), written by hand.  `dHr` = the declaration `hr` synthesizes, `dEn` = the
declaration of `entry`'s `MachineDefines` (the real ones are both `topshare3`). -/
def Share3FullWith (B : Tools.ShippingMachineShipsHier.CtxBnd) (n kP : Nat) (dHr dEn : Lean.Name) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design},
    RunsTo (synthesizeCombinational dHr) mctx mref cctx cref w (b, design) w' →
    MachineDefines mctx mref cctx cref dEn topshare3.machineData.shape → True →
    Share3ConclWith B n kP mctx mref cctx cref w b design

/-- the expected full type -/
def Share3Full : Prop := Share3FullWith Share3Bnd 2 4 ``topshare3 ``topshare3

/-- MUTATION of `hr`'s declaration: `hr` synthesizes `wrapA` (type-correct) -/
def Share3FullHrDecl : Prop := Share3FullWith Share3Bnd 2 4 ``wrapA ``topshare3
/-- MUTATION of `entry`'s declaration -/
def Share3FullEnDecl : Prop := Share3FullWith Share3Bnd 2 4 ``topshare3 ``wrapA
/-- MUTATION of `hr`'s form: the core synthesis `synthesizeCombinationalCore … [] false` instead of `synthesizeCombinational` -/
def Share3FullHrCore : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design},
    RunsTo (synthesizeCombinationalCore ``topshare3 [] false) mctx mref cctx cref w (b, design) w' →
    MachineDefines mctx mref cctx cref ``topshare3 topshare3.machineData.shape → True →
    Share3ConclWith Share3Bnd 2 4 mctx mref cctx cref w b design
/-- MUTATION of `hr`'s world: it ends in `w` itself -/
def Share3FullHrWorld : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design},
    RunsTo (synthesizeCombinational ``topshare3) mctx mref cctx cref w (b, design) w →
    MachineDefines mctx mref cctx cref ``topshare3 topshare3.machineData.shape → True →
    Share3ConclWith Share3Bnd 2 4 mctx mref cctx cref w b design
/-- MUTATION of `hr`'s world: it STARTS in `w'` -/
def Share3FullHrStart : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design},
    RunsTo (synthesizeCombinational ``topshare3) mctx mref cctx cref w' (b, design) w →
    MachineDefines mctx mref cctx cref ``topshare3 topshare3.machineData.shape → True →
    Share3ConclWith Share3Bnd 2 4 mctx mref cctx cref w b design
/-- MUTATION of `closes`: `False` instead of `True` -/
def Share3FullClosesFalse : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design},
    RunsTo (synthesizeCombinational ``topshare3) mctx mref cctx cref w (b, design) w' →
    MachineDefines mctx mref cctx cref ``topshare3 topshare3.machineData.shape → False →
    Share3ConclWith Share3Bnd 2 4 mctx mref cctx cref w b design
/-- MUTATION: the `entry` premise dropped -/
def Share3FullNoEntry : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design},
    RunsTo (synthesizeCombinational ``topshare3) mctx mref cctx cref w (b, design) w' → True →
    Share3ConclWith Share3Bnd 2 4 mctx mref cctx cref w b design


/-- MUTATION: the boundary lists only two callees -/
def Share3FullBndTwo : Prop := Share3FullWith Share3BndTwo 2 4 ``topshare3 ``topshare3
/-- MUTATION: the start world of the boundary is `JQ …` with a cache invariant -/
def Share3FullBndJQ : Prop := Share3FullWith Share3BndJQ 2 4 ``topshare3 ``topshare3
/-- MUTATION: the start world of the boundary is `JQC O 1 w` -/
def Share3FullBndD1 : Prop := Share3FullWith Share3BndD1 2 4 ``topshare3 ``topshare3
/-- MUTATION: the third callee is missing from the boundary -/
def Share3FullBndNoC : Prop := Share3FullWith Share3BndNoC 2 4 ``topshare3 ``topshare3
/-- MUTATION: depth 3 instead of 2 -/
def Share3FullDepth3 : Prop := Share3FullWith Share3Bnd 3 4 ``topshare3 ``topshare3
/-- MUTATION: three instead of four own inputs read by the source -/
def Share3FullKP3 : Prop := Share3FullWith Share3Bnd 2 3 ``topshare3 ``topshare3

end

open Tests.Compiler.ChildVertAuditTest in
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let ep := N ++ `topshare3 ++ `epK_endpoint
  let gt ← instantiateMVars (← getConstInfo ep).type
  let muts : List (Name × String) :=
    [(``Share3FullHrDecl, "hr synthesizes wrapA"), (``Share3FullEnDecl, "entry is for wrapA"),
     (``Share3FullHrCore, "hr is the core synthesis"), (``Share3FullHrWorld, "hr ends in w"), (``Share3FullHrStart, "hr starts in w'"),
     (``Share3FullClosesFalse, "closes : False"), (``Share3FullNoEntry, "entry dropped"),
     (``Share3FullBndTwo, "boundary: two callees"), (``Share3FullBndJQ, "boundary: JQ start world"), (``Share3FullBndD1, "boundary: JQC O 1"),
     (``Share3FullBndNoC, "boundary: third callee missing"), (``Share3FullDepth3, "depth 3"), (``Share3FullKP3, "kP = 3")]
  let allC : List (Expr × String) := [(gt, "the endpoint's type"), (mkConst ``Share3Full, "the expected full type")] ++ muts.map fun (c, w) => (mkConst c, s!"mutation {w}")
  for (e, what) in allC do
    if e.hasMVar || e.hasFVar then throwError "SR21 AUDIT FAILED: metavariables / free variables in {what}"
    Meta.check e
    unless (← Meta.isProp e) do throwError "SR21 AUDIT FAILED: {what} is not a Prop"
  unless (← isDefEq gt (mkConst ``Share3Full)) do
    throwError "SR21 AUDIT FAILED: the FULL type of the endpoint is not definitionally the hand-written Share3Full"
  for (c, w) in muts do
    if (← isDefEq gt (mkConst c)) then throwError "SR21 AUDIT FAILED: the mutated full type ({w}) was ACCEPTED"
  -- binder names of the endpoint
  let names ← forallTelescope gt fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
  unless names == ["mctx", "mref", "cctx", "cref", "w", "w'", "b", "design", "hr", "entry", "closes"] do throwError "SR21 AUDIT FAILED: binder names {names}"
  logInfo m!"SR21: the FULL forall-type of the three-callee endpoint {ep} (outer binders, hr : RunsTo (synthesizeCombinational topshare3) … w (b, design) w', entry : MachineDefines … topshare3, closes : True, and the conclusion) is isDefEq to the hand-written Share3Full; {muts.length} type-correct mutations (hr / entry declaration and form, closes, boundary: two callees / JQ / JQC O 1 / third callee missing, depth, kP) are REJECTED"

/-! ## data-fact mismatches are REJECTED by `decide` (the bundles are not vacuous) -/

theorem neg_order : topshare3.machineData.shape.instTagged.map (·.1) ≠ [``wrapB, ``wrapB, ``wrapA, ``wrapA, ``wrapC, ``wrapC] := by decide
theorem neg_two : topshare3.machineData.shape.instTagged.map (·.1) ≠ [``wrapA, ``wrapA, ``wrapB, ``wrapB] := by decide
theorem neg_single : topshare3.machineData.shape.instTagged.map (·.1) ≠ [``wrapA, ``wrapB, ``wrapC] := by decide
theorem neg_dup : ¬ (([``wrapA, ``wrapB, ``wrapA] : List Lean.Name).Nodup) := by decide
theorem neg_leaf : wrapB.machineData.shape.insts.map (·.1) ≠ [``leafK, ``leafK] := by decide

/-! ## closure audit -/

open Tests.Compiler.ChildVertAuditTest in
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let P := N ++ `topshare3
  let ep := P ++ `epK_endpoint
  stdAxioms ep
  let cl ← depClosure ep
  let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
    `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
    `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
  let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR21 AUDIT FAILED: old boundary / old child predicate in the closure of {ep}: {bad}"
  let oldish := cl.toList.filter fun c => (c.toString.splitOn "machine_composedNR").length > 1 || (c.toString.splitOn "seq_child_runN_ofR").length > 1
  unless oldish.isEmpty do throwError "SR21 AUDIT FAILED: old generated chain theorem(s) in the closure of {ep}: {oldish}"
  -- the TWO-callee lemmas are NOT used: the endpoint goes through the K-ary lemmas
  let quadLemmas : List Name :=
    [``Tools.ShippingQuadLeafGeneric.quad_closes0, ``Tools.ShippingQuadLeafGeneric.quad_machineRun, ``Tools.ShippingQuadLeafGeneric.quad_entry_run_ret_np,
     ``Tools.ShippingQuadComposed.quad_ranA, ``Tools.ShippingQuadComposed.quad_hkid, ``Tools.ShippingQuadComposed.quad_runFacts,
     ``Tools.ShippingQuadComposed.quad_outsCheck, ``Tools.ShippingQuadComposed.quad_kidsMasked, ``Tools.ShippingQuadComposed.quad_designCheck,
     ``Tools.ShippingQuadComposed.quad_traceXA, ``Tools.ShippingQuadComposed.quad_soundLA, ``Tools.ShippingQuadComposed.quad_composed,
     ``Tools.ShippingQuadCalls.quad_composed_split, ``Tools.ShippingQuadCalls.quad_inRange, ``Tools.ShippingQuadReturned.quad_returned,
     ``Tools.ShippingTopShareRun.machineSynth_ne_none4, ``Tools.ShippingTopShareRun.topshare_quad, ``Tools.ShippingTopShareRun.topshare_closing4,
     ``Tools.ShippingTopShareNoParent.topshare_entry_run4_ret_np]
  for q in quadLemmas do
    if cl.contains q then throwError "SR21 AUDIT FAILED: the two-callee lemma {q} is in the closure of {ep}"
  -- no pasted per-callee block exists
  for n in (List.range 3).flatMap fun i =>
      [P ++ Name.mkSimple s!"epD2M{i}_C_composedA", P ++ Name.mkSimple s!"epD2M{i}_C_seqChildRunN2", P ++ Name.mkSimple s!"epD2M{i}_C_kidFactsA",
       P ++ Name.mkSimple s!"epD2M{i}_C_closesA", P ++ Name.mkSimple s!"epD2M{i}_C_hcalls", P ++ Name.mkSimple s!"epD2M{i}_C_traceXA"] do
    if (← getEnv).contains n then throwError "SR21 AUDIT FAILED: the pasted block {n} exists"
  let must : List Name :=
    [``Tools.ShippingKaryCalls.kary_composed_split, ``Tools.ShippingKaryComposed.kary_inRange, ``Tools.ShippingKaryComposed.kary_hkid,
     ``Tools.ShippingKaryComposed.kary_ranA, ``Tools.ShippingKaryComposed.kary_runFacts, ``Tools.ShippingKaryComposed.kary_outsCheck,
     ``Tools.ShippingKaryComposed.kary_kidsMasked, ``Tools.ShippingKaryComposed.kary_designCheck, ``Tools.ShippingKaryComposed.kary_soundLA,
     ``Tools.ShippingKaryComposed.kary_traceXA, ``Tools.ShippingKaryLeafGeneric.kary_closes0, ``Tools.ShippingKaryLeafGeneric.kary_machineRun,
     ``Tools.ShippingKaryEntry.kary_machineSynth_ne_none, ``Tools.ShippingKaryRun.kary_closing, ``Tools.ShippingKaryRun.kary_loop,
     ``Tools.ShippingQuadCalls.leafCallee_hcalls, ``Tools.ShippingQuadHPoint.callFactF_of_hPointAt, ``Tools.ShippingKaryFacts.kSrcF_eq,
     ``Tools.ShippingTopShareRan.machineRanA_start0,
     P ++ `epK_all, P ++ `epK_parentData, P ++ `epK_parentExtra, P ++ `epK_gens, P ++ `epK0_kgen, P ++ `epK1_kgen, P ++ `epK2_kgen,
     P ++ `epD2M_genP, P ++ `epD2M_leafRun, P ++ `epK_hFP, P ++ `epK_hPoint0, P ++ `epK_hPoint5, P ++ `epD2M0_C_hF, P ++ `epD2M1_C_hF, P ++ `epD2M2_C_hF,
     P ++ `epD2M0_C_hextB, P ++ `epD2M1_C_hext, P ++ `epD2M2_C_gen]
  for m in must do
    unless cl.contains m do throwError "SR21 AUDIT FAILED: {m} not in the closure of {ep}"
  logInfo m!"SR21 CLOSURE AUDIT: {ep}: standard axioms; closure {cl.size} constants; no old boundary / child predicate; no old generated chain theorem; none of the {quadLemmas.length} two-callee lemmas; no pasted per-callee block; the K-ary lemmas and the generated per-declaration facts of the three callees are in it"

#print axioms Tests.Compiler.KaryThreeTest.topshare3.epK_endpoint

end Tests.Compiler.KaryThreeTest
end
