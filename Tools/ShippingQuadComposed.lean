import Tools.ShippingQuadReturned
import Tools.ShippingSeqChildDeepKidFactsA
import Tools.ShippingSeqChildDeepRunA
import Tools.ShippingSeqParentKidFactsA
import Tools.ShippingParentSeqComposedA
import Tools.ShippingMachineDepthRunRA
import Tools.ShippingMachineCallsLinkedTNR
import Tools.ShippingTopShareRan
import Tools.ShippingSeqParentLemmas
-- BUILT (unit SR15): c9 exit 0 (dev run, with the #print axioms below: standard axioms); the final-SHA rebuild is in REPORT-SR15.md.
-- SCOPE (binding, ledger L8au): the PER-CALLEE and PER-PARENT blocks of the shared-leaf class QUAD (`QuadParentData` / `LeafCalleeData` / `LeafData`),
-- stated and proved GENERICALLY (no `topshare` / `wrap` / `wrap3` / `acc` / `wrap`-text in any statement): the leaf's `KidFactsA`, the callee's
-- `KidFactsA`, trace, `ComposedNW`, `SeqChildRunN` at depth 2 (via `seqChildRunN_of_composedCA`), the `MachineRunNCA` of a served callee run
-- (via `machineRunNCA_of_real_main`), and, for the parent, `ts_hkid` / `ts_runFacts` / `ts_outsCheck` / `ts_kidsMasked` / `ts_designCheck` /
-- `ts_traceXA` / `ts_soundLA` / `ts_composedA` in generic form.
-- WHAT THE TEXT STILL SUPPLIES (named, exactly; NOT derived here):
--  * `GenFacts` (one per declaration: parent, each callee) = the elaborator-generated `X.machine_ok / machine_body / machine_inits / machine_writes /
--    machine_result / machine_source / machine_ext_causal` of that declaration (statements about its generated `machineInits/Body/Result/Ext/ExtB/Source`);
--  * for each callee: `hcalls` (the old chain's `old_seqparent% hcalls`: per-call `SeqFactsRN` of the callee's calls to the leaf) and the two
--    facts that the generated `machineExt/ExtB` read the declared inputs (`hext`, `hextB`, from `seq_child_runN_ofR1`);
--  * for the parent: `QuadGroupFacts` = the part of `SeqFactsRN` for each of the parent's calls that depends on the generated definitions of
--    `machineExt/ExtB` (the `InRange` of the argument values and the callee-source output equal to the call-field input position): in the
--    instance these are the old chain's `gfR*`, `gfHb*`, `gfHv*` facts + `decoded_eq`;
--  * the extra DECIDABLE data facts (`LeafKidData`, `LeafCalleeExtra`, `QuadParentExtra`: an instance proves them by `decide` on the stored `machineData`).
-- Everything else — the callee interfaces, closings, `KidFactsA`, the `machine_linkedT_callsRNA` data conditions, the callee runs, the parent's
-- `MachineRanA`, the four design checks, the trace, `ComposedG` — is derived from these and from `QuadParentData` / `LeafCalleeData` / `LeafData`.
-- `RealChildA` / `ServedRealA` / `JQC` / `MachineRunNCA` are histories of past synthesis results, not freshness or semantic correctness in the current environment.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field; no existing statement changed.
namespace Tools.ShippingQuadComposed
open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadReturned
open Tools.ShippingTopShareRun
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildVCA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPinC
open Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses
open Tools.ShippingMachineAuto
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingSharedLeafNL
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingMachineShipping
open Tools.ShippingSeqParentAt
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.IR.Semantics
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tools.ShippingSeqChildDeepKidFactsA (KidFactsA)
open Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA Tools.ShippingServedRealA
open Tools.ShippingChildTranslateA Tools.ShippingParentRanA Tools.ShippingChildComposeC Tools.ShippingChildRunAMain
open Tools.ShippingParentSeqComposedA
open Tools.ShippingSeqParentLemmas
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## Extra decidable data facts -/

/-- Extra DECIDABLE facts of the shared LEAF `dG` (no environment reads) used for its `KidFactsA`: an instance proves them by `decide` on the stored
`machineData`.  (`LeafData` has `ok`, `body`, `insts`, `outTy`.) -/
structure LeafKidData (dG : MachineData) : Prop where
  callsOk : dG.callsOk dG.nIn = true
  domB : ∀ b ∈ dG.shape.binders.drop dG.nIn, b.2 ≠ .domain
  slotsNe : dG.shape.layout.slots ≠ []
  slots : dG.ss.length = dG.shape.layout.slots.length
  outsClean : ∀ o ∈ dG.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true
  scalar : ∀ o ∈ dG.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true

/-- Extra DECIDABLE facts of a callee `dC` (`n` declared inputs) whose calls are all the leaf `dG`, used for its `KidFactsA` / `ComposedNW` /
`SeqChildRunN`. -/
structure LeafCalleeExtra (dC dG : MachineData) (n : Nat) : Prop where
  callWidths : Tools.ShippingCallWidths.callWidthsOk dC n (fun _ => dG.shape.layout.outs) = true
  callArgs : Tools.ShippingPortsMatchRaw.callArgsOk dC n (fun _ => Tools.ShippingPortWidthsPure.declWidths dG) = true
  outsClean : ∀ o ∈ dC.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true
  scalar : ∀ o ∈ dC.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true
  outNameOk : ∀ o ∈ dC.shape.layout.outs, outNameOk o.name = true

/-- `d.bsIn.drop n` has no domain binder when `d.shape.binders.drop n` has none. -/
theorem bsIn_drop_nodomain (d : MachineData) (n : Nat) (hdom : ∀ b ∈ d.shape.binders.drop n, b.2 ≠ .domain) :
    ∀ b ∈ d.bsIn.drop n, b.2 ≠ .domain := by
  intro b hb
  apply hdom b
  unfold MachineData.bsIn at hb
  rw [List.drop_take] at hb
  exact List.mem_of_mem_take hb

/-! ## The text-supplied facts of one generated declaration -/

section GenFacts
variable (d : MachineData) {ι : Type} (dom : ι → DomainConfig) {ρ : ι → Type} [Inhabited (HList (tys d.ss))]

/-- **The elaborator-generated facts of one declaration `X` (text-supplied, named exactly):** `inits body obsR ext extB src` are `X.machineInits`,
`X.machineBody`, `X.machineResult`, `X.machineExt`, `X.machineExtB`, `X.machineSource`, and the fields are `X.machine_ok`, `X.machine_body`,
`X.machine_inits`, `X.machine_writes`, `X.machine_result`, `X.machine_source`, and the causality of `X.machine_ext_causal` (as `HCausalOf`).  These
are the premises of `Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA` and are NOT derived generically. -/
structure GenFacts (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop where
  ok : d.ok = true
  body_eq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  init : d.initOk inits = true
  writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) d.nexts
  result : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) o.2)
  source : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst
  causal : HCausalOf d dom ext extB

end GenFacts

/-- **The trace of a generated declaration at a `MachineRunJQC` run** (generic form of `ts_traceXA` / `ts0_C_traceXA` / `ts1_C_traceXA`). -/
theorem genTrace (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} (d : MachineData) {ι : Type} (dom : ι → DomainConfig) {ρ : ι → Type} [Inhabited (HList (tys d.ss))]
    {inits : HList (tys d.ss)}
    {body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i)}
    {obsR : (i : ι) → ρ i → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (GF : GenFacts d dom inits body obsR ext extB src) {D₀ : Nat}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (ran : Tools.ShippingServedRealA.MachineRunJQC O mctx cctx (D₀ + 1) declName d.shape m design) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O declName d.shape m design) declName d m design dom src
      (fun i bools bits => ext i bools bits (stateLoop inits (body i bools bits)))
      (fun i bools bits => extB i bools bits (stateLoop inits (body i bools bits)))
      (letObsB d dom inits body ext extB) :=
  Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA d dom inits body obsR ext extB src GF.ok GF.body_eq GF.init
    GF.writes GF.result GF.source GF.causal O (bodyStepC_of_tele O T) hA (n := D₀ + 1) (htr_of_tele O hA T D₀) (m := m) (design := design) ran

/-! ## The leaf's `KidFactsA` -/

/-- **`KidFactsA` of the shared leaf** (generic form of `ts0_G_kidFactsA` / `ts1_G_kidFactsA`), at any depth `n`. -/
theorem leaf_kidFactsA (O : RefLawsAOps MkRefd mref cref) {dG : MachineData} {G : Name}
    (hG : LeafData dG) (hK : LeafKidData dG)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) (n : Nat) :
    KidFactsA O G dG.shape.layout.outs (Tools.ShippingPortWidthsPure.declWidths dG) n := by
  have hon : ∀ o ∈ dG.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
    fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (hK.outsClean o ho)
  exact
  { outsIn := fun y hy =>
      (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O dG hG.ok hG.body hG.insts hG.outTy hR0 hcl hy).outsIn
    outTys := fun y hy =>
      Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA (O := O) dG hG.ok hG.body hG.insts hK.slotsNe hK.slots hG.outTy hR0
        (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => hcl mctx' cctx' (Tools.ShippingChildInv.profLogIO b) w r w' hr) hy
    kidA := fun y hy =>
      Tools.ShippingParentRunFactsA.leaf_real_kidAA O dG hG.ok hG.body hG.insts hK.slotsNe hK.slots hG.outTy hR0 hcl hy
    kidR := fun y hy =>
      Tools.ShippingParentRunFactsA.leaf_real_kidRA O dG hG.ok hG.body hG.insts hG.outTy hR0 hcl hy
    masked := fun y hy =>
      Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA (nDecl := dG.nIn) O dG hG.ok hG.body hK.callsOk hK.domB hG.insts hK.slotsNe hK.slots hG.outTy
        hR0 hcl hy
    portsIn := fun y hy =>
      Tools.ShippingParentDesignFA.leaf_real_portsInA O dG hG.ok hG.body (nDecl := dG.nIn) hK.callsOk hK.domB hG.insts hK.slots hG.outTy hR0 hcl hon
        hK.scalar hy
    inW := fun y hy j q hq =>
      Tools.ShippingParentDesignFA.leaf_real_inWidthsA O dG hG.ok hG.body (nDecl := dG.nIn) hK.callsOk hK.domB hG.insts hK.slots hG.outTy hR0 hcl hy j q hq
    clk := fun y hy =>
      Tools.ShippingParentDesignFA.leaf_real_clkA O dG hG.ok hG.body (nDecl := dG.nIn) hK.callsOk hK.domB hG.insts hK.slots hG.outTy hR0 hcl hy
    check := fun y hy ms _ _ => by
      have hK' := Tools.ShippingParentDesignFA.leaf_real_kidK_regA O dG hG.ok hG.body (nDecl := dG.nIn) hK.callsOk hK.domB hG.insts hK.slotsNe hK.slots
        hG.outTy hR0 hcl hon hK.scalar hy
      exact ⟨hK'.1 _ n, fun g hg => hK'.2 g hg _ n⟩ }

/-! ## A callee whose calls are all the leaf -/

/-- The boundary of a callee's served run: the leaf's `MachineDefines` (generic form of `ts0_C_Bnd` / `ts1_C_Bnd`). -/
def leafBnd (G : Name) (dG : MachineData) (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) :
    Meta.Context → Core.Context → Void IO.RealWorld → Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop :=
  fun mctx cctx _ _ _ => MachineDefines mctx mref cctx cref G dG.shape

/-- the child tables of a callee whose calls are all the leaf `G` (the shape of the old chain's `hcalls`) -/
def leafBsC (G : Name) (dG : MachineData) : Name → List (Name × MixedGateBinder) :=
  fun n => if n = G then dG.bsIn else []
def leafOutsC (G : Name) (dG : MachineData) : Name → List OutField :=
  fun n => if n = G then dG.shape.layout.outs else []
def leafSrcC (G : Name) (dG : MachineData)
    (srcG : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)) :
    DomainConfig → Name → (Nat → List Nat) → List (Nat → Nat) :=
  fun i n => if n = G then fun vals => srcG i (Tools.ShippingMachineChild.boolsOf dG.bsIn vals) (Tools.ShippingMachineChild.bitsOf dG.bsIn vals)
    else fun _ => []
def leafPC (G : Name) (dG : MachineData) : Name → Sparkle.IR.AST.Module → Prop :=
  fun n => if n = G then (fun mc => Tools.ShippingGateChild.MachineRun G dG.shape mc)
    else (fun mc => Tools.ShippingGateChild.MachineRun G dG.shape mc)

/-- **`KidFactsA` of a callee whose calls are one leaf** (generic form of `ts0_C_kidFactsA` / `ts1_C_kidFactsA`; `m + 1` the depth). -/
theorem leafCallee_kidFactsA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {dC dG : MachineData} {C G : Name} {n : Nat}
    (hG : LeafData dG) (hK : LeafKidData dG) (hC : LeafCalleeData dC dG C G n) (hX : LeafCalleeExtra dC dG n)
    (entry : MachineDefines mctx mref cctx cref C dC.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) (m : Nat) :
    KidFactsA O C dC.shape.layout.outs (Tools.ShippingCallsChildPorts.argWidths dC n) (m + 1) :=
  Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidFactsA O T dC hC.ok hC.body (nDecl := n) hC.callsOk hC.slots hC.domB hC.insts_ne hC.slotsNe
    hC.fne hC.outTy hC.nomem n hC.hkD hC.hIlen hC.hSL hC.hSlen hC.hLlen hC.hNIn
    (fun _ => dG.shape.layout.outs) (fun _ => Tools.ShippingPortWidthsPure.declWidths dG) m
    (fun k hk => by rw [(hC.kids k hk).1]; exact leaf_kidFactsA O hG hK hR0 hcl m)
    (fun k hk => by rw [(hC.kids k hk).1]; exact leaf_kidFactsA O hG hK hR0 hcl (m + 1))
    hX.callWidths hX.callArgs (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (hX.outsClean o ho)) hX.scalar
    (leafCallee_hsep O hG hC hR0 hcl) entry
    (fun _ _ hA' => leafCallee_closesA O T hA' hG hC (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl)

section Callee
variable {dC dG : MachineData} {C G : Name} {n : Nat} [Inhabited (HList (tys dC.ss))] {ρ : DomainConfig → Type}
  {initsC : HList (tys dC.ss)}
  {bodyC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys dC.ss)) (Circuit.SigList i (tys dC.ss)) (tys dC.ss) →
      Circuit i (Circuit.SigList i (tys dC.ss)) (ρ i)}
  {obsRC : (i : DomainConfig) → ρ i → List (Nat → Nat)}
  {extC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys dC.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n)}
  {extBC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys dC.ss)) → Nat → Signal i Bool}
  {srcC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}
  {srcG : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}

/-- **The trace of a callee at its served run** (generic form of `ts0_C_traceXA` / `ts1_C_traceXA`). -/
theorem leafCallee_traceXA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hG : LeafData dG) (hC : LeafCalleeData dC dG C G n)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    (GF : GenFacts dC (fun i : DomainConfig => i) initsC bodyC obsRC extC extBC srcC)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore C [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref C dC.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O C dC.shape m design) C dC m design (fun i : DomainConfig => i) srcC
      (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC) :=
  genTrace O T hA dC (fun i : DomainConfig => i) GF
    (machineRunJQC_of_closesA O hA hcore entry (leafCallee_closesA O T hA hG hC (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl) hw hc)

set_option maxHeartbeats 4000000 in
/-- **`ComposedNW` at depth 1 of a callee whose calls are one leaf** (generic form of `ts0_C_composedA` / `ts1_C_composedA`).  TEXT-SUPPLIED premise
`hcalls`: the per-call `SeqFactsRN` of the callee's calls to the leaf (the old chain's `old_seqparent% hcalls`). -/
theorem leafCallee_composedA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hG : LeafData dG) (hC : LeafCalleeData dC dG C G n)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    (GF : GenFacts dC (fun i : DomainConfig => i) initsC bodyC obsRC extC extBC srcC)
    (hcalls : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 dC design m (dom := fun i : DomainConfig => i)
        (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC)
        (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
        (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
        n (leafBsC G dG) (leafOutsC G dG) (leafSrcC G dG srcG) (leafPC G dG))
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore C [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref C dC.shape) :
    Tools.ShippingMachineDepthRun.ComposedNW 1 C dC n m design (fun i : DomainConfig => i) srcC
      (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits))) := by
  have h := leafCallee_traceXA O T hA hG hC hR0 hcl GF hw hc hcore entry
  exact machine_linkedT_callsRNA 1 O h hC.fne n hC.hkD (bsIn_drop_nodomain dC n hC.domB) hC.hIlen hC.hSL hC.hSlen hC.hLlen hC.hNIn
    (leafBsC G dG) (leafOutsC G dG) (leafSrcC G dG srcG) (leafPC G dG) (hcalls m design)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < dC.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = G := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact (hC.kids k hk).1
      have hmr : Tools.ShippingGateChild.MachineRun G dG.shape mc :=
        ⟨mctx', mref, cctx', cref, w1, w2, Dc, hck ▸ hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR0, hcl mctx' cctx'⟩
      rw [hck]
      unfold leafPC
      split <;> exact hmr)

set_option maxHeartbeats 4000000 in
/-- **`SeqChildRunN` at depth 2 of a served callee run** (generic form of `ts0_C_seqChildRunN2` / `ts1_C_seqChildRunN2`).  TEXT-SUPPLIED premises
besides `hcalls`: `hextB`, `hext` (the generated `machineExtB/Ext` read the declared inputs, from `seq_child_runN_ofR1`). -/
theorem leafCallee_seqChildRunN2 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hG : LeafData dG) (hC : LeafCalleeData dC dG C G n) (hX : LeafCalleeExtra dC dG n)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    (GF : GenFacts dC (fun i : DomainConfig => i) initsC bodyC obsRC extC extBC srcC)
    (hcalls : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 dC design m (dom := fun i : DomainConfig => i)
        (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC)
        (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
        (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
        n (leafBsC G dG) (leafOutsC G dG) (leafSrcC G dG srcG) (leafPC G dG))
    (hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < n →
      extBC i bools bits (stateLoop initsC (bodyC i bools bits)) j = bools j)
    (hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < n →
      extC i bools bits (stateLoop initsC (bodyC i bools bits)) j n' = bits j n')
    {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : MachineRunNCA O C dC.shape (leafBnd G dG mref cref) mc design) :
    Tools.ShippingMachineDepth.SeqChildRunN (childMap design.modules) design 2 mc (List.take n dC.bsIn) dC.shape.layout.outs
      (fun vals => srcC Sparkle.Core.Domain.defaultDomain
        (Tools.ShippingMachineChild.boolsOf (List.take n dC.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take n dC.bsIn) vals)) :=
  Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA O 1 (leafBnd G dG mref cref)
    (fun hcore hadm hjqc entry _ hB =>
      leafCallee_composedA O T hadm hG hC hB hcl GF hcalls hjqc.1 (Or.inr hjqc.2) hcore entry)
    hC.outTy hX.outNameOk hC.slotsNe (Nat.pos_of_ne_zero (fun h0 => hC.insts_ne (List.eq_nil_of_length_eq_zero h0)))
    hC.hkD hC.hIlen hC.hSL hC.hSlen hC.hLlen hC.hNIn hextB hext Sparkle.Core.Domain.defaultDomain h

end Callee

/-- **`MachineRunNCA` of a served callee run** (generic form of the `machineRunNCA_of_real_main` application inside `ts_composedA`). -/
theorem leafCallee_runNCA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {dC dG : MachineData} {C G : Name} {n : Nat}
    (hG : LeafData dG) (hC : LeafCalleeData dC dG C G n)
    (entry : MachineDefines mctx mref cctx cref C dC.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {mc : Sparkle.IR.AST.Module} {Dc design : Sparkle.IR.AST.Design}
    (hreal : RealChildA O C (mc, Dc))
    (hcons : ∀ g ∈ Dc.modules, moduleByName design.modules g.name = some g) :
    MachineRunNCA O C dC.shape (leafBnd G dG mref cref) mc design :=
  machineRunNCA_of_real_main O T (BndA := leafBnd G dG mref cref) hreal hcons entry
    (fun _ _ _ _ _ _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hR0)
    (fun _ _ _ _ _ hin _ => by
      obtain ⟨_, _, _, hadm', _⟩ := hin
      exact leafCallee_closesA O T hadm' hG hC (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl)
    hC.insts_ne

/-! ## The parent with the call list `[c₁, c₁, c₂, c₂]` -/

/-- the callee at call `k` (`Name.anonymous` out of range) -/
def quadCalleeAt (dP : MachineData) (k : Nat) : Name := ((dP.shape.insts[k]?).map (·.1)).getD Name.anonymous

theorem quadCalleeAt_eq (dP : MachineData) (k : Nat) (hk : k < dP.shape.insts.length) :
    quadCalleeAt dP k = (dP.shape.insts[k]).1 := by
  simp [quadCalleeAt, List.getElem?_eq_getElem hk]

/-- the callee's output fields by name -/
def quadOutsOf (c₁ c₂ : Name) (d₁ d₂ : MachineData) (n : Name) : List OutField :=
  if n = c₁ then d₁.shape.layout.outs else if n = c₂ then d₂.shape.layout.outs else []
/-- the callee's argument widths by name -/
def quadWidthsOf (c₁ c₂ : Name) (d₁ d₂ : MachineData) (n₁ n₂ : Nat) (n : Name) : List Nat :=
  if n = c₁ then Tools.ShippingCallsChildPorts.argWidths d₁ n₁ else if n = c₂ then Tools.ShippingCallsChildPorts.argWidths d₂ n₂ else []
/-- Extra DECIDABLE facts of the parent (`nP` declared inputs) used for its call-entry bundle, the four design checks and the `machine_linkedT_callsRNA`
data conditions: an instance proves them by `decide` on the stored `machineData`. -/
structure QuadParentExtra (dP d₁ d₂ : MachineData) (c₁ c₂ : Name) (nP n₁ n₂ : Nat) : Prop where
  slotsNe : dP.shape.layout.slots ≠ []
  outTy : ∀ o ∈ dP.shape.layout.outs, o.ty.bitWidth = o.width
  nomem : ∀ x ∈ dP.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true
  callWidths : Tools.ShippingCallWidths.callWidthsOk dP nP (fun k => quadOutsOf c₁ c₂ d₁ d₂ (quadCalleeAt dP k)) = true
  callArgs : Tools.ShippingPortsMatchRaw.callArgsOk dP nP (fun k => quadWidthsOf c₁ c₂ d₁ d₂ n₁ n₂ (quadCalleeAt dP k)) = true
  outsClean : ∀ o ∈ dP.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true
  scalar : ∀ o ∈ dP.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true
  hkD : nP ≤ dP.bsIn.length
  hIlen : (dP.bsIn.drop nP).length = dP.shape.insts.length
  hSL : ∀ b ∈ dP.slotBs ++ dP.letBs, b.2 ≠ .domain
  hSlen : dP.slotBs.length = dP.shape.layout.slots.length
  hLlen : dP.letBs.length = dP.shape.layout.lets
  hNIn : machNIn dP.shape = ((dP.bsIn.take nP).filter (fun b => b.2 != .domain)).length

/-- **All the decidable data facts of a QUAD instance** (parent, two callees, leaf), as one bundle (the fields are the `QuadLeafGeneric` structures and the
extras of this file). -/
structure QuadAll (dP d₁ d₂ dG : MachineData) (c c₁ c₂ G : Name) (nP n₁ n₂ : Nat) : Prop where
  hP : QuadParentData dP d₁ d₂ c c₁ c₂ G nP
  hPX : QuadParentExtra dP d₁ d₂ c₁ c₂ nP n₁ n₂
  hG : LeafData dG
  hK : LeafKidData dG
  hC₁ : LeafCalleeData d₁ dG c₁ G n₁
  hX₁ : LeafCalleeExtra d₁ dG n₁
  hC₂ : LeafCalleeData d₂ dG c₂ G n₂
  hX₂ : LeafCalleeExtra d₂ dG n₂

/-- the `S`-tables of the parent's `machine_linkedT_callsRNA`: binders, outputs, sources and child predicate, by callee name -/
def quadBsF (c₁ c₂ : Name) (d₁ d₂ : MachineData) (n₁ n₂ : Nat) : Name → List (Name × MixedGateBinder) :=
  fun n => if n = c₁ then List.take n₁ d₁.bsIn else if n = c₂ then List.take n₂ d₂.bsIn else []
def quadSrcF {ι : Type} (c₁ c₂ : Name) (d₁ d₂ : MachineData) (n₁ n₂ : Nat)
    (src₁ src₂ : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat))
    (_i : ι) (n : Name) : (Nat → List Nat) → List (Nat → Nat) :=
  if n = c₁ then fun vals => src₁ Sparkle.Core.Domain.defaultDomain
      (Tools.ShippingMachineChild.boolsOf (List.take n₁ d₁.bsIn) vals) (Tools.ShippingMachineChild.bitsOf (List.take n₁ d₁.bsIn) vals)
  else if n = c₂ then fun vals => src₂ Sparkle.Core.Domain.defaultDomain
      (Tools.ShippingMachineChild.boolsOf (List.take n₂ d₂.bsIn) vals) (Tools.ShippingMachineChild.bitsOf (List.take n₂ d₂.bsIn) vals)
  else fun _ => []
def quadPC (O : RefLawsAOps MkRefd mref cref) (design : Sparkle.IR.AST.Design) (c₁ c₂ G : Name) (d₁ d₂ dG : MachineData)
    (n : Name) (mc : Sparkle.IR.AST.Module) : Prop :=
  if n = c₁ then MachineRunNCA O c₁ d₁.shape (leafBnd G dG mref cref) mc design
  else if n = c₂ then MachineRunNCA O c₂ d₂.shape (leafBnd G dG mref cref) mc design else True

/-- Every call entry of a QUAD parent calls `c₁` or `c₂`; the first two call `c₁` (index `< 2`), the last two `c₂`. -/
theorem quad_callee_at {dP d₁ d₂ : MachineData} {c c₁ c₂ G : Name} {nP : Nat}
    (hP : QuadParentData dP d₁ d₂ c c₁ c₂ G nP) (k : Nat) (hk : k < dP.shape.insts.length) :
    ((dP.shape.insts[k]).1 = c₁ ∧ k < 2) ∨ ((dP.shape.insts[k]).1 = c₂ ∧ ¬ k < 2) := by
  have hm : dP.shape.insts.map (·.1) = [c₁, c₁, c₂, c₂] := by
    rw [← Tools.ShippingInstTagged.instTagged_map_fst]; exact hP.names
  have hk4 : k < 4 := hP.len4 ▸ hk
  have hget : (dP.shape.insts.map (·.1))[k]? = some ([c₁, c₁, c₂, c₂][k]'(by simpa using hk4)) := by
    rw [hm]; exact List.getElem?_eq_getElem _
  rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hget
  have heq : (dP.shape.insts[k]).1 = [c₁, c₁, c₂, c₂][k]'(by simpa using hk4) := Option.some.inj hget
  rcases k with _ | _ | _ | _ | k
  · exact Or.inl ⟨heq, by decide⟩
  · exact Or.inl ⟨heq, by decide⟩
  · exact Or.inr ⟨heq, by decide⟩
  · exact Or.inr ⟨heq, by decide⟩
  · omega

theorem quad_insts_mem {dP d₁ d₂ : MachineData} {c c₁ c₂ G : Name} {nP : Nat}
    (hP : QuadParentData dP d₁ d₂ c c₁ c₂ G nP) (k : Nat) (hk : k < dP.shape.insts.length) :
    (dP.shape.insts[k]).1 = c₁ ∨ (dP.shape.insts[k]).1 = c₂ :=
  (quad_callee_at hP k hk).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

/-- the callee of an entry `k` with `(insts.map (·.1))[k]? = some c'` is `c₁` or `c₂` -/
theorem quad_name_mem {dP d₁ d₂ : MachineData} {c c₁ c₂ G : Name} {nP : Nat}
    (hP : QuadParentData dP d₁ d₂ c c₁ c₂ G nP) {k : Nat} {c' : Name}
    (hc' : (dP.shape.insts.map (·.1))[k]? = some c') : c' = c₁ ∨ c' = c₂ := by
  rw [← Tools.ShippingInstTagged.instTagged_map_fst, hP.names] at hc'
  have := List.mem_of_getElem? hc'
  simp at this
  rcases this with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The arguments of every call are `let`s (from `callsOk`). -/
theorem callsOk_args (d : MachineData) (n : Nat) (h : d.callsOk n = true) (k : Nat) (hk : k < d.shape.insts.length) :
    (d.shape.insts[k]).2.1.all (· < d.ls.length) = true := by
  unfold MachineData.callsOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, h2⟩, _⟩, _⟩ := h
  have := List.all_eq_true.mp h2 _ (List.getElem_mem hk)
  simpa using this

section Parent
variable {dP d₁ d₂ dG : MachineData} {c c₁ c₂ G : Name} {nP n₁ n₂ : Nat}

/-- `MachineRanA` of the parent's raw core run at the start world `JQC O 0 w` (generic form of `ts_ranA`). -/
theorem quad_ranA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1)
    (entry : MachineDefines mctx mref cctx cref c dP.shape) (hw : JQC O 0 w) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx c dP.shape raw D :=
  Tools.ShippingTopShareRan.machineRanA_start0 O hA T hcore entry
    (quad_closes0 O T hA Q.hP Q.hG Q.hC₁ Q.hC₂ entry₁ entry₂ hR0 hcl) hw

/-- **`KidFactsA` of every call entry's callee** (generic form of `ts_hkid`). -/
theorem quad_hkid (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) (m : Nat) :
    ∀ (k : Nat) (hk : k < dP.shape.insts.length),
      KidFactsA O (dP.shape.insts[k]).1 (quadOutsOf c₁ c₂ d₁ d₂ (quadCalleeAt dP k))
        (quadWidthsOf c₁ c₂ d₁ d₂ n₁ n₂ (quadCalleeAt dP k)) (m + 1) := by
  intro k hk
  rw [quadCalleeAt_eq dP k hk]
  rcases quad_insts_mem Q.hP k hk with hn | hn
  · rw [hn]
    unfold quadOutsOf quadWidthsOf
    rw [if_pos rfl, if_pos rfl]
    exact leafCallee_kidFactsA O T Q.hG Q.hK Q.hC₁ Q.hX₁ entry₁ hR0 hcl m
  · rw [hn]
    unfold quadOutsOf quadWidthsOf
    rw [if_neg (Ne.symm Q.hP.c12), if_neg (Ne.symm Q.hP.c12), if_pos rfl, if_pos rfl]
    exact leafCallee_kidFactsA O T Q.hG Q.hK Q.hC₂ Q.hX₂ entry₂ hR0 hcl m

end Parent

section Parent2
variable {dP d₁ d₂ dG : MachineData} {c c₁ c₂ G : Name} {nP n₁ n₂ : Nat}

/-- **`RunFacts` of the parent's shipped module** (generic form of `ts_runFacts`). -/
theorem quad_runFacts (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (m : Nat)
    (hA : AdmCtx O.quiet mctx cctx) (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref c dP.shape) (hw : JQC O 0 w) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  Tools.ShippingSeqParentKidFactsA.kidsA_runFacts O dP Q.hP.ok Q.hP.body (nDecl := nP) Q.hP.callsOk Q.hP.slots Q.hP.domB Q.hP.insts_ne
    Q.hPX.slotsNe Q.hP.fne Q.hPX.outTy Q.hPX.nomem
    (fun k => quadOutsOf c₁ c₂ d₁ d₂ (quadCalleeAt dP k)) (fun k => quadWidthsOf c₁ c₂ d₁ d₂ n₁ n₂ (quadCalleeAt dP k)) (m + 1)
    (quad_hkid O T Q entry₁ entry₂ hR0 hcl m) Q.hPX.callWidths hpost
    (quad_ranA O T hA Q entry₁ entry₂ hR0 hcl hcore entry hw)

/-- **`outsCheck` of the parent's shipped module** (generic form of `ts_outsCheck`). -/
theorem quad_outsCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (m : Nat)
    (hA : AdmCtx O.quiet mctx cctx) (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref c dP.shape) (hw : JQC O 0 w) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) (m + 1) (checkedOptimize b) = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_outsCheck O dP Q.hP.ok Q.hP.body (nDecl := nP) Q.hP.callsOk Q.hP.slots Q.hP.domB Q.hP.insts_ne
    Q.hPX.outTy Q.hPX.nomem
    (fun k => quadOutsOf c₁ c₂ d₁ d₂ (quadCalleeAt dP k)) (fun k => quadWidthsOf c₁ c₂ d₁ d₂ n₁ n₂ (quadCalleeAt dP k)) (m + 1)
    (quad_hkid O T Q entry₁ entry₂ hR0 hcl m) hpost (quad_ranA O T hA Q entry₁ entry₂ hR0 hcl hcore entry hw)
    (quad_runFacts O T m hA Q entry₁ entry₂ hR0 hcl hcore hpost entry hw).gate

/-- **`kidsMaskedN` of the parent's shipped module** (generic form of `ts_kidsMasked`). -/
theorem quad_kidsMasked (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (m : Nat)
    (hA : AdmCtx O.quiet mctx cctx) (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref c dP.shape) (hw : JQC O 0 w) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_maskedN O dP Q.hP.ok Q.hP.body (nDecl := nP) Q.hP.callsOk Q.hP.slots Q.hP.domB Q.hP.insts_ne Q.hP.fne
    Q.hPX.outTy Q.hPX.nomem
    (fun k => quadOutsOf c₁ c₂ d₁ d₂ (quadCalleeAt dP k)) (fun k => quadWidthsOf c₁ c₂ d₁ d₂ n₁ n₂ (quadCalleeAt dP k)) (m + 1)
    (quad_hkid O T Q entry₁ entry₂ hR0 hcl m) hpost (quad_ranA O T hA Q entry₁ entry₂ hR0 hcl hcore entry hw)

/-- **`designCheck` of the parent's shipped module** (generic form of `ts_designCheck`). -/
theorem quad_designCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (m : Nat)
    (hA : AdmCtx O.quiet mctx cctx) (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref c dP.shape) (hw : JQC O 0 w) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) (m + 1) (checkedOptimize b) = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_designCheck O dP Q.hP.ok Q.hP.body (nDecl := nP) Q.hP.callsOk Q.hP.slots Q.hP.domB Q.hP.insts_ne
    Q.hPX.slotsNe Q.hP.fne Q.hPX.outTy Q.hPX.nomem
    (fun k => quadOutsOf c₁ c₂ d₁ d₂ (quadCalleeAt dP k)) (fun k => quadWidthsOf c₁ c₂ d₁ d₂ n₁ n₂ (quadCalleeAt dP k)) (m + 1)
    (quad_hkid O T Q entry₁ entry₂ hR0 hcl m) Q.hPX.callWidths Q.hPX.callArgs hpost
    (quad_ranA O T hA Q entry₁ entry₂ hR0 hcl hcore entry hw)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (Q.hPX.outsClean o ho)) Q.hPX.scalar

/-- **The trace of the parent** (generic form of `ts_traceXA`): the parent's `MachineRunJQC` at depth 1 is `quad_machineRun`. -/
theorem quad_traceXA {ι : Type} {dom : ι → DomainConfig} {ρ : ι → Type} [Inhabited (HList (tys dP.ss))]
    {initsP : HList (tys dP.ss)}
    {bodyP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys dP.ss)) (Circuit.SigList (dom i) (tys dP.ss)) (tys dP.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys dP.ss)) (ρ i)}
    {obsRP : (i : ι) → ρ i → List (Nat → Nat)}
    {extP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extBP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → Nat → Signal (dom i) Bool}
    {srcP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    (GP : GenFacts dP dom initsP bodyP obsRP extP extBP srcP)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O c dP.shape m design) c dP m design dom srcP
      (fun i bools bits => extP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (fun i bools bits => extBP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (letObsB dP dom initsP bodyP extP extBP) :=
  genTrace O T hA dP dom GP (D₀ := 0)
    (quad_machineRun O T hA Q.hP Q.hG Q.hC₁ Q.hC₂ entryP entry₁ entry₂ hR0 hcl hw hcore)

/-- **`MachineTraceLB` of the parent** (generic form of `ts_soundLA`; the `soundL` premise of the endpoint). -/
theorem quad_soundLA {ι : Type} {dom : ι → DomainConfig} {ρ : ι → Type} [Inhabited (HList (tys dP.ss))]
    {initsP : HList (tys dP.ss)}
    {bodyP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys dP.ss)) (Circuit.SigList (dom i) (tys dP.ss)) (tys dP.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys dP.ss)) (ρ i)}
    {obsRP : (i : ι) → ρ i → List (Nat → Nat)}
    {extP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extBP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → Nat → Signal (dom i) Bool}
    {srcP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    (GP : GenFacts dP dom initsP bodyP obsRP extP extBP srcP)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineAuto.MachineTraceLB c dP m design dom srcP
      (fun i bools bits => extP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (fun i bools bits => extBP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (letObsB dP dom initsP bodyP extP extBP) := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, -, tr⟩ :=
    quad_traceXA O T hA Q GP entryP entry₁ entry₂ hR0 hcl hw hcore
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

end Parent2

/-! ## `ComposedG` of the parent -/

/-- **TEXT-SUPPLIED group facts of the parent's calls** (named exactly): the part of `SeqFactsRN` for call `k` that depends on the generated
definitions of `machineExt` / `machineExtB` and is therefore NOT derived generically — (R) the argument values of the call, read from the `let`
observations `lsrc`, are in range of the callee's binders; (F) the callee's source at the decoded argument values has, at the output field the call
reads, exactly the value of the parent's input position `nP + k` (the call-output position) at every time.  In an instance these are the old chain's
`gfR*` / `gfHb*` / `gfHv*` facts with `decoded_eq`.  The remaining conjuncts of `SeqFactsRN` (no memory child, the argument list, the callee's
run theorem, the arguments are `let`s) are DERIVED in `quad_composed`. -/
def QuadGroupFacts (dP : MachineData) (nP : Nat) {ι : Type} {dom : ι → DomainConfig}
    (lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (bsC : Name → List (Name × MixedGateBinder)) (outsC : Name → List OutField)
    (S : ι → Name → (Nat → List Nat) → List (Nat → Nat)) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k : Nat) (hk : k < dP.shape.insts.length),
    (∀ τ, Tools.ShippingMachineChild.InRange
        (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1 τ)
        ((bsC (dP.shape.insts[k]).1).filter fun b => b.2 != .domain)) ∧
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
      (outsC (dP.shape.insts[k]).1)[k']? = some o ∧ o.name = dP.shape.instFields.getD k "" ∧
      (S i (dP.shape.insts[k]).1 (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => ((extB i bools bits) p).val τ) (fun p n => ((ext i bools bits) p n).val τ)
        (nP + k) (((dP.bsIn.drop nP)[k]?.map (·.2)).getD .domain) = f τ

section Parent3
variable {dP d₁ d₂ dG : MachineData} {c c₁ c₂ G : Name} {nP n₁ n₂ : Nat}
  {ι : Type} {dom : ι → DomainConfig} {ρ : ι → Type} [Inhabited (HList (tys dP.ss))]
  {initsP : HList (tys dP.ss)}
  {bodyP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys dP.ss)) (Circuit.SigList (dom i) (tys dP.ss)) (tys dP.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys dP.ss)) (ρ i)}
  {obsRP : (i : ι) → ρ i → List (Nat → Nat)}
  {extP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
  {extBP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → Nat → Signal (dom i) Bool}
  {srcP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
  [Inhabited (HList (tys d₁.ss))] [Inhabited (HList (tys d₂.ss))]
  {ρ₁ ρ₂ : DomainConfig → Type}
  {inits₁ : HList (tys d₁.ss)}
  {body₁ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys d₁.ss)) (Circuit.SigList i (tys d₁.ss)) (tys d₁.ss) →
      Circuit i (Circuit.SigList i (tys d₁.ss)) (ρ₁ i)}
  {obsR₁ : (i : DomainConfig) → ρ₁ i → List (Nat → Nat)}
  {ext₁ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys d₁.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n)}
  {extB₁ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys d₁.ss)) → Nat → Signal i Bool}
  {src₁ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}
  {inits₂ : HList (tys d₂.ss)}
  {body₂ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys d₂.ss)) (Circuit.SigList i (tys d₂.ss)) (tys d₂.ss) →
      Circuit i (Circuit.SigList i (tys d₂.ss)) (ρ₂ i)}
  {obsR₂ : (i : DomainConfig) → ρ₂ i → List (Nat → Nat)}
  {ext₂ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys d₂.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n)}
  {extB₂ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys d₂.ss)) → Nat → Signal i Bool}
  {src₂ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}
  {srcG : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}

set_option maxHeartbeats 8000000 in
/-- **`ComposedG` at depth 2 of a QUAD parent from the generic per-callee pieces** (generic form of `ts_composedA`; the `composed` premise of
`quad_returned` / `quad_wired` / the endpoint).  TEXT-SUPPLIED premises, named: `GP` / `G₁` / `G₂` (the generated `machine_*` facts of the parent and
the two callees), `hcalls₁` / `hcalls₂` (the old chain's per-call `SeqFactsRN` of the callees' calls to the leaf), `hextB₁` / `hext₁` / `hextB₂` / `hext₂`
(the generated `machineExtB/Ext` of a callee read its declared inputs), `hgrp` (`QuadGroupFacts` of the parent).  Derived here: the parent's trace, the
`machine_linkedT_callsRNA` data conditions, the per-call `SeqFactsRN` structure, the callees' depth-2 runs, the served callee `MachineRunNCA`. -/
theorem quad_composed
    (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    (GP : GenFacts dP dom initsP bodyP obsRP extP extBP srcP)
    (G₁ : GenFacts d₁ (fun i : DomainConfig => i) inits₁ body₁ obsR₁ ext₁ extB₁ src₁)
    (G₂ : GenFacts d₂ (fun i : DomainConfig => i) inits₂ body₂ obsR₂ ext₂ extB₂ src₂)
    (hcalls₁ : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 d₁ design m (dom := fun i : DomainConfig => i)
        (letObsB d₁ (fun i : DomainConfig => i) inits₁ body₁ ext₁ extB₁)
        (fun i bools bits => ext₁ i bools bits (stateLoop inits₁ (body₁ i bools bits)))
        (fun i bools bits => extB₁ i bools bits (stateLoop inits₁ (body₁ i bools bits)))
        n₁ (leafBsC G dG) (leafOutsC G dG) (leafSrcC G dG srcG) (leafPC G dG))
    (hcalls₂ : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 d₂ design m (dom := fun i : DomainConfig => i)
        (letObsB d₂ (fun i : DomainConfig => i) inits₂ body₂ ext₂ extB₂)
        (fun i bools bits => ext₂ i bools bits (stateLoop inits₂ (body₂ i bools bits)))
        (fun i bools bits => extB₂ i bools bits (stateLoop inits₂ (body₂ i bools bits)))
        n₂ (leafBsC G dG) (leafOutsC G dG) (leafSrcC G dG srcG) (leafPC G dG))
    (hextB₁ : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < n₁ →
      extB₁ i bools bits (stateLoop inits₁ (body₁ i bools bits)) j = bools j)
    (hext₁ : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < n₁ →
      ext₁ i bools bits (stateLoop inits₁ (body₁ i bools bits)) j n' = bits j n')
    (hextB₂ : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < n₂ →
      extB₂ i bools bits (stateLoop inits₂ (body₂ i bools bits)) j = bools j)
    (hext₂ : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < n₂ →
      ext₂ i bools bits (stateLoop inits₂ (body₂ i bools bits)) j n' = bits j n')
    (hgrp : QuadGroupFacts dP nP (letObsB dP dom initsP bodyP extP extBP)
      (fun i bools bits => extP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (fun i bools bits => extBP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (quadBsF c₁ c₂ d₁ d₂ n₁ n₂) (quadOutsOf c₁ c₂ d₁ d₂) (quadSrcF c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂))
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref c dP.shape)
    (hB : QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w m design) :
    ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) c dP nP m design dom srcP
      (fun i bools bits => extP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (fun i bools bits => extBP i bools bits (stateLoop initsP (bodyP i bools bits))) := by
  obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
  have h := quad_traceXA O T hA Q GP entry hM0 hM1 hR0 hcl hw hcore
  refine Tools.ShippingMachineShipsDepth.composedG_of_NW ?_
  exact machine_linkedT_callsRNA 2 O h Q.hP.fne nP Q.hPX.hkD (bsIn_drop_nodomain dP nP Q.hP.domB) Q.hPX.hIlen Q.hPX.hSL Q.hPX.hSlen
    Q.hPX.hLlen Q.hPX.hNIn (quadBsF c₁ c₂ d₁ d₂ n₁ n₂) (quadOutsOf c₁ c₂ d₁ d₂) (quadSrcF c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂)
    (quadPC O design c₁ c₂ G d₁ d₂ dG)
    (fun i bools bits k c' hk2 => by
      obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hk2
      have hlt : k < dP.shape.insts.length := by simpa using hlt'
      have hget' : (dP.shape.insts[k]).1 = c' := by simpa using hget
      subst hget'
      right
      unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
      obtain ⟨hR, hF⟩ := hgrp i bools bits k hlt
      refine ⟨origin_child_none _ (Q.hP.nomemKey k hlt), (dP.shape.insts[k]).2.1,
        by simp [List.getElem?_map, List.getElem?_eq_getElem hlt], ?_,
        Tools.ShippingMachineCallsLinkedT.args_facts (callsOk_args dP nP Q.hP.callsOk k hlt)
          (by simp [letObsB]), hR, hF⟩
      intro mc hmc
      rcases quad_callee_at Q.hP k hlt with ⟨hn, hk2'⟩ | ⟨hn, hk2'⟩
      · rw [hn] at hmc ⊢
        unfold quadPC at hmc
        rw [if_pos rfl] at hmc
        have hr := leafCallee_seqChildRunN2 O T Q.hG Q.hC₁ Q.hX₁ hcl G₁ hcalls₁ hextB₁ hext₁ hmc
        refine ⟨?_, ?_⟩
        · unfold quadBsF quadOutsOf quadSrcF
          simp only [if_pos rfl]
          exact hr
        · rw [hr.2.2.2.2.2.1, ← Q.hC₁.hNIn, ← Q.hP.argsN k hlt]
          simp [quadNk, hk2']
      · rw [hn] at hmc ⊢
        unfold quadPC at hmc
        rw [if_neg (Ne.symm Q.hP.c12), if_pos rfl] at hmc
        have hr := leafCallee_seqChildRunN2 O T Q.hG Q.hC₂ Q.hX₂ hcl G₂ hcalls₂ hextB₂ hext₂ hmc
        refine ⟨?_, ?_⟩
        · unfold quadBsF quadOutsOf quadSrcF
          simp only [if_neg (Ne.symm Q.hP.c12), if_pos rfl]
          exact hr
        · rw [hr.2.2.2.2.2.1, ← Q.hC₂.hNIn, ← Q.hP.argsN k hlt]
          simp [quadNk, hk2'])
    (fun k c' hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      rcases quad_name_mem Q.hP hc' with hck | hck
      · have hrun' : RunsTo (synthesizeCombinational c₁) mctx' mref cctx' cref w1 (mc, Dc) w2 := hck ▸ hrun
        rw [hck]
        unfold quadPC
        rw [if_pos rfl]
        exact leafCallee_runNCA O T Q.hG Q.hC₁ hM0 hR0 hcl (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun') hcons
      · have hrun' : RunsTo (synthesizeCombinational c₂) mctx' mref cctx' cref w1 (mc, Dc) w2 := hck ▸ hrun
        rw [hck]
        unfold quadPC
        rw [if_neg (Ne.symm Q.hP.c12), if_pos rfl]
        exact leafCallee_runNCA O T Q.hG Q.hC₂ hM1 hR0 hcl (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun') hcons)

end Parent3

end Tools.ShippingQuadComposed

#print axioms Tools.ShippingQuadComposed.genTrace
#print axioms Tools.ShippingQuadComposed.leaf_kidFactsA
#print axioms Tools.ShippingQuadComposed.leafCallee_kidFactsA
#print axioms Tools.ShippingQuadComposed.leafCallee_traceXA
#print axioms Tools.ShippingQuadComposed.leafCallee_composedA
#print axioms Tools.ShippingQuadComposed.leafCallee_seqChildRunN2
#print axioms Tools.ShippingQuadComposed.leafCallee_runNCA
#print axioms Tools.ShippingQuadComposed.quad_ranA
#print axioms Tools.ShippingQuadComposed.quad_hkid
#print axioms Tools.ShippingQuadComposed.quad_runFacts
#print axioms Tools.ShippingQuadComposed.quad_outsCheck
#print axioms Tools.ShippingQuadComposed.quad_kidsMasked
#print axioms Tools.ShippingQuadComposed.quad_designCheck
#print axioms Tools.ShippingQuadComposed.quad_traceXA
#print axioms Tools.ShippingQuadComposed.quad_soundLA
#print axioms Tools.ShippingQuadComposed.quad_composed
