import Tools.ShippingKaryBridge
import Tools.ShippingKaryFacts
import Tools.ShippingSeqParentGenD2MS
import Tests.Compiler.ChildVertAuditTest
-- UNBUILT (unit SR21): see STATUS-SR21.md for the run names.
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

end Tests.Compiler.KaryThreeTest
end
