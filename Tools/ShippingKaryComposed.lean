import Tools.ShippingKaryLeafGeneric
import Tools.ShippingQuadCalls
-- BUILT (unit SR21): k5 exit 0 (Tools.ShippingKaryComposed, dev run); the final-SHA rebuild is in REPORT-SR21.md.
-- SCOPE (binding, ledger L8ba): the PARENT-level blocks of the shared-leaf class generalised from two callees to a LIST `cs : List KCal` of K ≥ 1 callees that call ONE shared leaf
-- (`Tools/ShippingQuadComposed.lean` / `ShippingQuadCalls.lean` stay untouched).  The call list of the parent is `cs.flatMap (fun e => [e.c, e.c])` (`KaryParentData`).  PROVED here, generically
-- in K (no induction on K is needed: every callee is handled by the SAME per-callee lemma `leafCallee_*` of SR13–SR16, found in `cs` by name): `kary_hkid`, `kary_ranA`,
-- `kary_runFacts`, `kary_outsCheck`, `kary_kidsMasked`, `kary_designCheck`, `kary_traceXA`, `kary_soundLA`, `kary_inRange`, `kary_composed_split`.
-- The tables of the old QUAD lemmas (`quadOutsOf`, `quadBsF`, `quadSrcF`, `quadPC`, …, defined by `if n = c₁ … else if n = c₂ …`) are replaced by lookups by name in `cs` (`kFind`).
-- TEXT-SUPPLIED premises that remain (named, per declaration, NOT derived): `GenFacts` of the parent and of every callee (`KaryGen.gen`), the leaf's `LeafSeqRunN`, the per-call output equation
-- `CallFactF` of every callee (`KaryGen.hF`) and of the parent (`hFP`), `hextB` / `hext` of every callee (`KaryGen.hextB/hext`); the decidable data facts (`KaryAll`).  Every other block of
-- the endpoint — the interface / closing / `KidFactsA` / run-theorem of each callee, the parent's `MachineRanA`, the four design checks, the trace — is derived.  `RealChildA` /
-- `ServedRealA` / `JQC` / `MachineRunNCA` are histories of past synthesis results, not freshness or semantic correctness in the current environment.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingKaryComposed
open Tools.ShippingKaryRun Tools.ShippingKaryEntry Tools.ShippingKaryLeafGeneric
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
open Tools.ShippingMachineCallsLinkedT
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingPortWidthsPure (nonDom declWidths declN)
open Tools.ShippingQuadComposed Tools.ShippingQuadCalls

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## Lookup by name in the callee list -/

/-- the callee named `n` (the callee names are pairwise different) -/
def kFind (cs : List KCal) (n : Name) : Option KCal := cs.find? (fun e => decide (e.c = n))

theorem kFind_of_mem {cs : List KCal} (hnd : (cs.map (·.c)).Nodup) {e : KCal} (he : e ∈ cs) :
    kFind cs e.c = some e := by
  unfold kFind
  cases h : cs.find? (fun x => decide (x.c = e.c)) with
  | none =>
    have := (List.find?_eq_none.mp h) e he
    simp at this
  | some x =>
    have hx := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    have hxe : x.c = e.c := of_decide_eq_true hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    have hij := kary_idx_of_name hnd hi hj hxe
    subst hij
    rw [hi] at hj
    exact hj

/-- the callee's output fields by name -/
def kOutsOf (cs : List KCal) (n : Name) : List OutField :=
  match kFind cs n with
  | some e => e.d.shape.layout.outs
  | none => []
/-- the callee's argument widths by name -/
def kWidthsOf (cs : List KCal) (n : Name) : List Nat :=
  match kFind cs n with
  | some e => Tools.ShippingCallsChildPorts.argWidths e.d e.n
  | none => []
/-- the callee's binder table by name -/
def kBsF (cs : List KCal) (n : Name) : List (Name × MixedGateBinder) :=
  match kFind cs n with
  | some e => List.take e.n e.d.bsIn
  | none => []
/-- the callees' sources by name, on the decoded families (`e.src` is the source of the callee `e`) -/
def kSrcF {ι : Type} (cs : List KCal) (_i : ι) (n : Name) : (Nat → List Nat) → List (Nat → Nat) :=
  match kFind cs n with
  | some e => fun vals => e.src Sparkle.Core.Domain.defaultDomain
      (Tools.ShippingMachineChild.boolsOf (List.take e.n e.d.bsIn) vals) (Tools.ShippingMachineChild.bitsOf (List.take e.n e.d.bsIn) vals)
  | none => fun _ => []
/-- the child predicate by name: a served run of the callee -/
def kPC (O : RefLawsAOps MkRefd mref cref) (design : Sparkle.IR.AST.Design) (G : Name) (dG : MachineData) (cs : List KCal)
    (n : Name) (mc : Sparkle.IR.AST.Module) : Prop :=
  match kFind cs n with
  | some e => MachineRunNCA O e.c e.d.shape (leafBnd G dG mref cref) mc design
  | none => True

/-! ## The data bundle -/

/-- Extra DECIDABLE facts of the parent (`nP` declared inputs): `QuadParentExtra` with the K-ary tables. -/
structure KaryParentExtra (dP : MachineData) (cs : List KCal) (nP : Nat) : Prop where
  slotsNe : dP.shape.layout.slots ≠ []
  outTy : ∀ o ∈ dP.shape.layout.outs, o.ty.bitWidth = o.width
  nomem : ∀ x ∈ dP.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true
  callWidths : Tools.ShippingCallWidths.callWidthsOk dP nP (fun k => kOutsOf cs (quadCalleeAt dP k)) = true
  callArgs : Tools.ShippingPortsMatchRaw.callArgsOk dP nP (fun k => kWidthsOf cs (quadCalleeAt dP k)) = true
  outsClean : ∀ o ∈ dP.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true
  scalar : ∀ o ∈ dP.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true
  hkD : nP ≤ dP.bsIn.length
  hIlen : (dP.bsIn.drop nP).length = dP.shape.insts.length
  hSL : ∀ b ∈ dP.slotBs ++ dP.letBs, b.2 ≠ .domain
  hSlen : dP.slotBs.length = dP.shape.layout.slots.length
  hLlen : dP.letBs.length = dP.shape.layout.lets
  hNIn : machNIn dP.shape = ((dP.bsIn.take nP).filter (fun b => b.2 != .domain)).length

/-- **All the decidable data facts of a K-callee instance** (parent, callees, shared leaf), as one bundle (K-ary `QuadAll`). -/
structure KaryAll (dP dG : MachineData) (cs : List KCal) (c G : Name) (nP : Nat) : Prop where
  hP : KaryParentData dP cs c G nP
  hPX : KaryParentExtra dP cs nP
  hG : LeafData dG
  hK : LeafKidData dG
  hC : KaryCallees cs dG G
  hX : ∀ e ∈ cs, LeafCalleeExtra e.d dG e.n

/-- the conjunction of `p` over the list, written as an explicit `∧` chain (`p a ∧ p b ∧ p c` for `[a, b, c]`, no trailing `True`): the boundary of an endpoint then unfolds to the
conjunction a human would write for K callees. -/
def KAnd {α : Type} (p : α → Prop) : List α → Prop
  | [] => True
  | [a] => p a
  | a :: b :: l => p a ∧ KAnd p (b :: l)

theorem kand_forall {α : Type} {p : α → Prop} : ∀ {l : List α}, KAnd p l → ∀ a ∈ l, p a
  | [], _, a, ha => absurd ha (List.not_mem_nil)
  | [x], h, a, ha => by
    have : a = x := by simpa using ha
    subst this; exact h
  | x :: y :: l, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact h.1
    · exact kand_forall h.2 a ha'

theorem forall_kand {α : Type} {p : α → Prop} : ∀ {l : List α}, (∀ a ∈ l, p a) → KAnd p l
  | [], _ => trivial
  | [x], h => h x (List.mem_cons_self ..)
  | x :: y :: l, h => ⟨h x (List.mem_cons_self ..), forall_kand (fun a ha => h a (List.mem_cons_of_mem _ ha))⟩

/-- The class boundary of the K-callee endpoint: the callees' and the leaf's `MachineDefines` and the start world `JQC O 0 w` (K-ary `QuadBnd`; the callees as a `KAnd` chain). -/
def KaryBnd (cs : List KCal) (G : Name) (dG : MachineData) : CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧ KAnd (fun e : KCal => MachineDefines mctx mref cctx cref e.c e.d.shape) cs ∧
    MachineDefines mctx mref cctx cref G dG.shape ∧ JQC O 0 w

/-- the callee of call `k` is a member of `cs` found by name -/
theorem kary_callee_at {dP : MachineData} {cs : List KCal}
    (hP : dP.shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c]))
    {k : Nat} (hk : k < dP.shape.insts.length) :
    ∃ e ∈ cs, (dP.shape.insts[k]).1 = e.c ∧ cs[k / 2]? = some e := by
  obtain ⟨h1, h2⟩ := kary_call_callee hP hk
  exact ⟨_, List.getElem_mem _, h2, h1⟩

/-- the callee of a call entry with `(insts.map (·.1))[k]? = some c'` -/
theorem kary_name_mem {dP : MachineData} {cs : List KCal}
    (hP : dP.shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c]))
    {k : Nat} {c' : Name} (hc' : (dP.shape.insts.map (·.1))[k]? = some c') : ∃ e ∈ cs, c' = e.c := by
  rw [← Tools.ShippingInstTagged.instTagged_map_fst, hP, dup_getElem?] at hc'
  obtain ⟨e, he, hec⟩ := Option.map_eq_some_iff.mp hc'
  exact ⟨e, List.mem_of_getElem? he, hec.symm⟩

theorem kNk_of {cs : List KCal} {k : Nat} {e : KCal} (h : cs[k / 2]? = some e) : kNk cs k = machNIn e.d.shape := by
  simp [kNk, h]

section Parent
variable {dP dG : MachineData} {cs : List KCal} {c G : Name} {nP : Nat}

/-- `MachineRanA` of the parent's raw core run at the start world `JQC O 0 w` (K-ary `quad_ranA`). -/
theorem kary_ranA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (Q : KaryAll dP dG cs c G nP) (hent : KaryEntries mctx mref cctx cref cs)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1)
    (entry : MachineDefines mctx mref cctx cref c dP.shape) (hw : JQC O 0 w) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx c dP.shape raw D :=
  Tools.ShippingTopShareRan.machineRanA_start0 O hA T hcore entry
    (kary_closes0 O T hA Q.hP Q.hG Q.hC hent hR0 hcl) hw

/-- **`KidFactsA` of every call entry's callee** (K-ary `quad_hkid`). -/
theorem kary_hkid (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (Q : KaryAll dP dG cs c G nP) (hent : KaryEntries mctx mref cctx cref cs)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) (m : Nat) :
    ∀ (k : Nat) (hk : k < dP.shape.insts.length),
      KidFactsA O (dP.shape.insts[k]).1 (kOutsOf cs (quadCalleeAt dP k))
        (kWidthsOf cs (quadCalleeAt dP k)) (m + 1) := by
  intro k hk
  rw [quadCalleeAt_eq dP k hk]
  obtain ⟨e, he, hn, -⟩ := kary_callee_at Q.hP.names hk
  rw [hn]
  unfold kOutsOf kWidthsOf
  rw [kFind_of_mem Q.hP.nodup he]
  exact leafCallee_kidFactsA O T Q.hG Q.hK (Q.hC e he) (Q.hX e he) (hent e he) hR0 hcl m

/-- **`RunFacts` of the parent's shipped module** (K-ary `quad_runFacts`). -/
theorem kary_runFacts (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (m : Nat)
    (hA : AdmCtx O.quiet mctx cctx) (Q : KaryAll dP dG cs c G nP) (hent : KaryEntries mctx mref cctx cref cs)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref c dP.shape) (hw : JQC O 0 w) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  Tools.ShippingSeqParentKidFactsA.kidsA_runFacts O dP Q.hP.ok Q.hP.body (nDecl := nP) Q.hP.callsOk Q.hP.slots Q.hP.domB Q.hP.insts_ne
    Q.hPX.slotsNe Q.hP.fne Q.hPX.outTy Q.hPX.nomem
    (fun k => kOutsOf cs (quadCalleeAt dP k)) (fun k => kWidthsOf cs (quadCalleeAt dP k)) (m + 1)
    (kary_hkid O T Q hent hR0 hcl m) Q.hPX.callWidths hpost
    (kary_ranA O T hA Q hent hR0 hcl hcore entry hw)

/-- **`outsCheck` of the parent's shipped module** (K-ary `quad_outsCheck`). -/
theorem kary_outsCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (m : Nat)
    (hA : AdmCtx O.quiet mctx cctx) (Q : KaryAll dP dG cs c G nP) (hent : KaryEntries mctx mref cctx cref cs)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref c dP.shape) (hw : JQC O 0 w) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) (m + 1) (checkedOptimize b) = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_outsCheck O dP Q.hP.ok Q.hP.body (nDecl := nP) Q.hP.callsOk Q.hP.slots Q.hP.domB Q.hP.insts_ne
    Q.hPX.outTy Q.hPX.nomem
    (fun k => kOutsOf cs (quadCalleeAt dP k)) (fun k => kWidthsOf cs (quadCalleeAt dP k)) (m + 1)
    (kary_hkid O T Q hent hR0 hcl m) hpost (kary_ranA O T hA Q hent hR0 hcl hcore entry hw)
    (kary_runFacts O T m hA Q hent hR0 hcl hcore hpost entry hw).gate

/-- **`kidsMaskedN` of the parent's shipped module** (K-ary `quad_kidsMasked`). -/
theorem kary_kidsMasked (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (m : Nat)
    (hA : AdmCtx O.quiet mctx cctx) (Q : KaryAll dP dG cs c G nP) (hent : KaryEntries mctx mref cctx cref cs)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref c dP.shape) (hw : JQC O 0 w) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_maskedN O dP Q.hP.ok Q.hP.body (nDecl := nP) Q.hP.callsOk Q.hP.slots Q.hP.domB Q.hP.insts_ne Q.hP.fne
    Q.hPX.outTy Q.hPX.nomem
    (fun k => kOutsOf cs (quadCalleeAt dP k)) (fun k => kWidthsOf cs (quadCalleeAt dP k)) (m + 1)
    (kary_hkid O T Q hent hR0 hcl m) hpost (kary_ranA O T hA Q hent hR0 hcl hcore entry hw)

/-- **`designCheck` of the parent's shipped module** (K-ary `quad_designCheck`). -/
theorem kary_designCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (m : Nat)
    (hA : AdmCtx O.quiet mctx cctx) (Q : KaryAll dP dG cs c G nP) (hent : KaryEntries mctx mref cctx cref cs)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref c dP.shape) (hw : JQC O 0 w) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) (m + 1) (checkedOptimize b) = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_designCheck O dP Q.hP.ok Q.hP.body (nDecl := nP) Q.hP.callsOk Q.hP.slots Q.hP.domB Q.hP.insts_ne
    Q.hPX.slotsNe Q.hP.fne Q.hPX.outTy Q.hPX.nomem
    (fun k => kOutsOf cs (quadCalleeAt dP k)) (fun k => kWidthsOf cs (quadCalleeAt dP k)) (m + 1)
    (kary_hkid O T Q hent hR0 hcl m) Q.hPX.callWidths Q.hPX.callArgs hpost
    (kary_ranA O T hA Q hent hR0 hcl hcore entry hw)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (Q.hPX.outsClean o ho)) Q.hPX.scalar

/-- **The trace of the parent** (K-ary `quad_traceXA`): the parent's `MachineRunJQC` at depth 1 is `kary_machineRun`. -/
theorem kary_traceXA {ι : Type} {dom : ι → DomainConfig} {ρ : ι → Type} [Inhabited (HList (tys dP.ss))]
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
    (Q : KaryAll dP dG cs c G nP)
    (GP : GenFacts dP dom initsP bodyP obsRP extP extBP srcP)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (hent : KaryEntries mctx mref cctx cref cs)
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
    (kary_machineRun O T hA Q.hP Q.hG Q.hC hent entryP hR0 hcl hw hcore)

/-- **`MachineTraceLB` of the parent** (K-ary `quad_soundLA`; the `soundL` premise of the endpoint). -/
theorem kary_soundLA {ι : Type} {dom : ι → DomainConfig} {ρ : ι → Type} [Inhabited (HList (tys dP.ss))]
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
    (Q : KaryAll dP dG cs c G nP)
    (GP : GenFacts dP dom initsP bodyP obsRP extP extBP srcP)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (hent : KaryEntries mctx mref cctx cref cs)
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
    kary_traceXA O T hA Q GP entryP hent hR0 hcl hw hcore
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

/-- **The range `R` of the parent's calls, derived** (K-ary `quad_inRange`). -/
theorem kary_inRange (Q : KaryAll dP dG cs c G nP)
    {ι : Type} {dom : ι → DomainConfig} [Inhabited (HList (tys dP.ss))] {ρ : ι → Type}
    (initsP : HList (tys dP.ss))
    (bodyP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys dP.ss)) (Circuit.SigList (dom i) (tys dP.ss)) (tys dP.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys dP.ss)) (ρ i))
    (extP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extBP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → Nat → Signal (dom i) Bool)
    (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    ∀ (k : Nat) (hk : k < dP.shape.insts.length) (τ : Nat),
      Tools.ShippingMachineChild.InRange
        (Tools.ShippingMachineCallsLinkedT.valsOf (Tools.ShippingMachineCausal.letObsB dP dom initsP bodyP extP extBP i bools bits)
          (dP.shape.insts[k]).2.1 τ)
        ((kBsF cs (dP.shape.insts[k]).1).filter fun b => b.2 != .domain) := by
  have hwid : ∀ (d : MachineData) (n : Nat), Tools.ShippingCallsChildPorts.argWidths d n =
      ((d.bsIn.take n).filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth := by
    intro d n
    unfold Tools.ShippingCallsChildPorts.argWidths
    rw [List.map_map]; rfl
  refine call_inRange dP (n := nP) Q.hP.ok Q.hPX.hkD Q.hPX.hIlen Q.hP.slots Q.hP.callsOk
    (fun k => kWidthsOf cs (quadCalleeAt dP k)) Q.hPX.callArgs (kBsF cs) ?_ ?_
    (Tools.ShippingMachineCausal.letObsB dP dom initsP bodyP extP extBP i bools bits)
    (letObsB_hl dP dom initsP bodyP extP extBP i bools bits)
  · intro k hk
    show kWidthsOf cs (quadCalleeAt dP k) = _
    rw [quadCalleeAt_eq dP k hk]
    obtain ⟨e, he, hn, -⟩ := kary_callee_at Q.hP.names hk
    rw [hn]; unfold kWidthsOf kBsF
    rw [kFind_of_mem Q.hP.nodup he]
    exact hwid e.d e.n
  · intro k hk
    have hnk := Q.hP.argsN k hk
    obtain ⟨e, he, hn, hce⟩ := kary_callee_at Q.hP.names hk
    rw [hn]; unfold kBsF
    rw [kFind_of_mem Q.hP.nodup he]
    rw [kNk_of hce] at hnk
    rw [← hnk, (Q.hC e he).hNIn]

end Parent

end Tools.ShippingKaryComposed
