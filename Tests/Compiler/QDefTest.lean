import Tests.Compiler.CDefTest
import Tests.Compiler.Srm4ComposedQTest
-- C5-SPEC (issue sparkle-gen-c5-spec): the Q-shape class QSharedLeafParent (a PLAIN leaf + wrappers with ordinary AND memory calls,
-- per-wrapper arity), its member P_Q (topshareQ), the frozen C5 statement elaborated as a Prop (FrozenC5), and defeq / binder / axiom audits.
-- Spec: scripts/c5/Q_CLASS.md, scripts/c5/C5_STATEMENT.lean.txt, scripts/c5/GAP_MAP.md.  Test-only; CDefTest and the C4 files are NOT edited.
-- NOT proved here: Q-KID, Q-CLOSES, Q-HCALLS, Q-RUN, Q-COMPOSED, Q-MASK (see GAP_MAP.md).  No target Prop is a field.
set_option autoImplicit false
namespace Tests.Compiler.QDef
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts QuadGroupFacts LeafKidData)
open Tools.ShippingQuadLeafGeneric (LeafData leafNk)
open Tools.ShippingQuadCalls (LeafSeqRunN)
open Tools.ShippingSrm3Callee (MemCalleeData)
open Tools.ShippingMachineCallsLinkedT (MemFacts)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingNmEntry (NmParentData)
open Tools.ShippingNmGroup (NCal)
open Sparkle.Compiler.Elab (MixedGateBinder)
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemKid (memOuts memIns)
open Tools.ShippingMachineEntry (posEnc kindTy)
open Sparkle.Compiler.MachMemory (memModule memChildName memChild?)
open Tests.Compiler.CDef (GenPkg)

/-- AMENDMENT-5-style decoding check with a PORT MAP: at leaf port `p` of the port list `bs`, the call argument `args[portIdx bs p]` is a
let of `d` whose term is `d`'s own input term at wrapper position `pos p` (`boolInput j` with `bpos j = pos p`, or `bitsInput n j` with
`vpos j = pos p`).  (`Tests.Compiler.CDef.argInOk` is the case `pos = id`, which does NOT hold for wrapQ: its `x` is at wrapper position 3 but
at leaf port 1.)  Domain ports and positions past the list are vacuous. -/
def argInOkQ (d : MachineData) (bs : List (Name × MixedGateBinder)) (args : List Nat) (pos : Nat → Nat) (p : Nat) : Bool :=
  match bs[p]? with
  | none => true
  | some b =>
    match b.2 with
    | .domain => true
    | .bool =>
      match args[Tools.ShippingMachineChild.portIdx bs p]? with
      | none => false
      | some a =>
        match d.ls[a]? with
        | some ⟨.bool, .boolInput j⟩ => d.bpos j == pos p
        | _ => false
    | .bits n =>
      match args[Tools.ShippingMachineChild.portIdx bs p]? with
      | none => false
      | some a =>
        match d.ls[a]? with
        | some ⟨.bits m, .bitsInput _ j⟩ => m == n && d.vpos j == pos p
        | _ => false

/-- the PLAIN shared leaf (no instances, no generated ext): the three things the class reads (AMENDMENT 2 of C4) -/
structure QLeafPkg where
  decl : Lean.Name
  d : MachineData
  src : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)

/-- everything the class records about ONE wrapper `w` (a generated callee, declared arity `arity`) of the plain leaf `L`.
Each of its calls is ORDINARY (`child? = none`; a call of `L`) or a MEMORY entry (`child? = some (memModule ..)`). -/
structure QWrapData (L : QLeafPkg) (w : GenPkg DomainConfig (fun i => i)) where
  arity : Nat                                                    -- DATA: declared-input count of this wrapper (P_Q: 3 and 5)
  -- per-call tables of MemCalleeData (per wrapper; the SAME record serves ordinary and memory calls)
  nameK : Nat → String                                           -- DATA
  nk : Nat → Nat                                                 -- DATA
  outsK : Nat → List String                                      -- DATA
  namesK : Nat → List String                                     -- DATA
  names : List String                                            -- DATA: this wrapper's `names` (namesP / namesQ; csQ's per-wrapper list)
  mem : MemCalleeData w.d w.decl arity nameK nk outsK namesK names                          -- DATA (decide)
  -- the kind of each call
  ordKid : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none → (w.d.shape.insts[k]).1 = L.decl  -- DATA: ordinary ⇒ leaf
  ordArgsN : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    (w.d.shape.insts[k]).2.1.length = (L.d.bsIn.filter Tools.ShippingPortWidthsPure.nonDom).length                          -- DATA
  ordT : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    nameK k = Sparkle.IR.ModuleName.ofDecl L.decl ∧ nk k = leafNk L.d ∧ outsK k = L.d.shape.layout.outs.map (·.name) ∧ namesK k = []  -- DATA: ordinary tables = the leaf's
  widths : Nat → List Nat                                        -- DATA: call widths (leaf widths at ordinary calls, memIns at memory calls)
  wid : Tools.ShippingPortsMatchRaw.callArgsOk w.d arity widths = true                                                   -- DATA
  ordW : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    widths k = (L.d.bsIn.filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth                              -- DATA
  kidOuts : Nat → List OutField                                  -- DATA: KidFactsNC tables (leaf outs at ordinary, memOuts at memory calls)
  kidIns : Nat → List Nat                                        -- DATA
  kidMemT : ∀ (k : Nat) (hk : k < w.d.shape.insts.length) (cb : Bool) (aw dw : Nat),
    (originAt w.d.shape k).child? = some (memModule cb aw dw) → kidOuts k = memOuts dw ∧ kidIns k = memIns aw dw          -- DATA
  kidOrdT : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    kidOuts k = L.d.shape.layout.outs ∧ kidIns k = Tools.ShippingPortWidthsPure.declWidths L.d                              -- DATA
  cw : Tools.ShippingCallWidths.callWidthsOk w.d arity kidOuts = true                                                     -- DATA
  outsClean : ∀ o ∈ w.d.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true                      -- DATA
  scalar : ∀ o ∈ w.d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true                                       -- DATA
  outOk : ∀ o ∈ w.d.shape.layout.outs, outNameOk o.name = true                                                              -- DATA
  -- CalleeNM data (every call is a leaf call or a memory entry of ONE memory shape (mcb, maw, mdw))
  mcb : Bool                                                     -- DATA: the memory shape of this wrapper's memory entries (unused when it has none)
  maw : Nat
  mdw : Nat
  tags : ∀ x ∈ w.d.shape.instTagged, x.1 = L.decl ∨ x.1 = memChildName mcb maw mdw                                         -- DATA
  agree : Tools.ShippingInstTagged.TagsAgree w.d.shape                                                                    -- DATA
  cne : ∀ k (hk : k < w.d.shape.insts.length), (w.d.shape.insts[k]).1 ≠ w.decl                                            -- DATA
  -- generated-shape facts (filled by the same uniform unfolding as hext / hextB / memcalls; NOT generator certificates)
  hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat),
    j < arity → w.extBS i bools bits j = bools j                                                                          -- GEN-SHAPE
  hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat),
    j < arity → w.extS i bools bits j n' = bits j n'                                                                      -- GEN-SHAPE
  memCalls : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (k : Nat) (c : Name),
    (w.d.shape.insts.map (·.1))[k]? = some c → (originAt w.d.shape k).child? ≠ none →
    MemFacts w.d.shape (w.lsrc i bools bits) w.d.ls.length (w.d.bsIn.drop arity) arity (w.extS i bools bits) k c         -- GEN-SHAPE (memory calls only)
  -- ordinary-call decoding and output (replace TqHcallsP's / TqFQ's CallFactF / CallFactFO inputs; ORDINARY calls only)
  argPos : Nat → Nat → Nat                                       -- DATA: call k, leaf port p ↦ the wrapper input position passed at that port
  argsIn : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    ∀ p, p < L.d.bsIn.length → argInOkQ w.d L.d.bsIn (w.d.shape.insts[k]).2.1 (argPos k) p = true                         -- DATA
  callOut : ∀ (k : Nat) (_ : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
    ∃ (k' : Nat) (o : OutField), L.d.shape.layout.outs[k']? = some o ∧ o.name = w.d.shape.instFields.getD k "" ∧
      ∀ (bools' : Nat → Signal i Bool) (bits' : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
        (∀ p, L.d.bsIn[p]?.map (·.2) = some MixedGateBinder.bool → bools' p = bools (argPos k p)) →
        (∀ p n, L.d.bsIn[p]?.map (·.2) = some (MixedGateBinder.bits n) → bits' p n = bits (argPos k p) n) →
        ∃ f : Nat → Nat, (L.src i bools' bits')[k']? = some f ∧
          ∀ τ, posEnc (fun p => (w.extBS i bools bits p).val τ) (fun p n => (w.extS i bools bits p n).val τ)
            (arity + k) (((w.d.bsIn.drop arity)[k]?.map (·.2)).getD .domain) = f τ                                        -- GEN-SHAPE (ordinary calls only)

/-- a wrapper: its generated package and its Q data -/
structure QWrapper (L : QLeafPkg) where
  pkg : GenPkg DomainConfig (fun i => i)
  dat : QWrapData L pkg

abbrev QWrapper.decl {L : QLeafPkg} (w : QWrapper L) : Lean.Name := w.pkg.decl
abbrev QWrapper.d {L : QLeafPkg} (w : QWrapper L) : MachineData := w.pkg.d
abbrev QWrapper.arity {L : QLeafPkg} (w : QWrapper L) : Nat := w.dat.arity

/-- The class Q: parents of wrappers over ONE plain shared leaf; each wrapper has ordinary calls (of the leaf) and/or memory entries. -/
structure QSharedLeafParent where
  top : GenPkg Unit (fun _ => defaultDomain)
  nDecl : Nat
  cs : List NCal
  pdata : NmParentData top.d cs top.decl nDecl                                                    -- DATA (decide)
  outTy : ∀ o ∈ top.d.shape.layout.outs, o.ty.bitWidth = o.width                                  -- DATA
  noMem : ∀ x ∈ top.d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true  -- DATA
  slotsNe : top.d.shape.layout.slots ≠ []                                                         -- DATA
  outsOf : Nat → List OutField                                                                    -- DATA
  insOf : Nat → List Nat                                                                          -- DATA
  cw : Tools.ShippingCallWidths.callWidthsOk top.d nDecl outsOf = true                            -- DATA
  ca : Tools.ShippingPortsMatchRaw.callArgsOk top.d nDecl insOf = true                            -- DATA
  -- the plain leaf
  leaf : QLeafPkg
  leafData : LeafData leaf.d                                                                      -- DATA (machine_ok / machine_body + decide)
  leafKidData : LeafKidData leaf.d                                                                -- DATA (decide)
  leafLetsOk : leaf.d.letsOk = true                                                               -- DATA (decide): MachineCloses of the leaf is DERIVED from it
  leafNoMem : memChild? leaf.decl = none                                                          -- DATA (rfl / decide)
  leafRun : LeafSeqRunN leaf.decl leaf.d leaf.src                                                 -- GENERATED (leafP.seq_child_runN by generateSeqChildN)
  -- the wrappers (callees of the top)
  wrappers : List (QWrapper leaf)
  bsC : Lean.Name → List (Name × MixedGateBinder)                                                 -- DATA
  outsC : Lean.Name → List OutField                                                               -- DATA
  srcC : Unit → Lean.Name → (Nat → List Nat) → List (Nat → Nat)                                   -- DATA
  group : QuadGroupFacts top.d nDecl top.lsrc top.extS top.extBS bsC outsC srcC                   -- STRUCTURAL CLASS ASSUMPTION (= TqGrp)
  wOf : Nat → Nat                                                                                 -- DATA: call index ↦ wrapper index
  tieCallee : ∀ k, k < top.d.shape.insts.length →
    wOf k < wrappers.length ∧ (top.d.shape.insts.map (·.1))[k]? = (wrappers.map (·.pkg.decl))[wOf k]?       -- DATA
  tieOuts : ∀ k, k < top.d.shape.insts.length → outsOf k = (wrappers.map (·.pkg.d.shape.layout.outs)).getD (wOf k) []   -- DATA
  tieIns : ∀ k, k < top.d.shape.insts.length →
    insOf k = (wrappers.map (fun w => argWidths w.pkg.d w.dat.arity)).getD (wOf k) []                       -- DATA
  tieBsC : ∀ w ∈ wrappers, bsC w.pkg.decl = w.pkg.d.bsIn.take w.dat.arity                        -- DATA
  tieOutsC : ∀ w ∈ wrappers, outsC w.pkg.decl = w.pkg.d.shape.layout.outs                         -- DATA
  tieSrcC : ∀ w ∈ wrappers, srcC () w.pkg.decl = fun vals => w.pkg.src defaultDomain
    (Tools.ShippingMachineChild.boolsOf (w.pkg.d.bsIn.take w.dat.arity) vals) (Tools.ShippingMachineChild.bitsOf (w.pkg.d.bsIn.take w.dat.arity) vals)  -- STRUCTURAL (rfl-style)
  tieCs : cs = wrappers.map (fun w => (⟨w.pkg.decl, w.pkg.d, [], w.dat.names⟩ : NCal))            -- DATA (rfl): Gs = [], per-wrapper names
  csNc : ∀ e ∈ cs, ∀ e' ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) ∧ e'.c ∉ e.Gs   -- DATA
  csCd : ∀ e ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ top.decl) ∧ top.decl ∉ e.Gs       -- DATA

/-- the per-wrapper arities (`wArity`) -/
abbrev QSharedLeafParent.wArity (P : QSharedLeafParent) : List Nat := P.wrappers.map (·.dat.arity)

/-! ## the member P_Q = topshareQ -/
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tests.Compiler.SharedLeafMemKidIfaceTest
open Tests.Compiler.Srm9ComposedTest (TqBnd tqExt tqExtB)

def wpName : Nat → String := fun _ => Sparkle.IR.ModuleName.ofDecl ``leafP
noncomputable def wpNk : Nat → Nat := fun _ => leafNk leafP.machineData
noncomputable def wpOuts : Nat → List String := fun _ => leafP.machineData.shape.layout.outs.map (·.name)
def wpNames : Nat → List String := fun _ => []
noncomputable def wpW : Nat → List Nat := fun _ =>
  (leafP.machineData.bsIn.filter (fun b => b.2 != .domain)).map (fun b => (kindTy b.2).bitWidth)
noncomputable def wpKidOuts : Nat → List OutField := fun _ => leafP.machineData.shape.layout.outs
noncomputable def wpKidIns : Nat → List Nat := fun _ => Tools.ShippingPortWidthsPure.declWidths leafP.machineData

theorem wrapP_memCallee : MemCalleeData wrapP.machineData ``wrapP 3 wpName wpNk wpOuts wpNames namesP := by
  refine ⟨wrapP.machine_ok, wrapP.machine_body, ?_, ?_, ?_, ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    fun h0 => absurd (congrArg List.length h0) (by decide), ?_, fun h0 => absurd (congrArg List.length h0) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel

theorem wrapP_len : wrapP.machineData.shape.insts.length = 2 := by decide

theorem wrapP_allOrd : ∀ k (hk : k < wrapP.machineData.shape.insts.length), (originAt wrapP.machineData.shape k).child? = none := by
  first | decide | decide +kernel

noncomputable abbrev qLeafP : QLeafPkg := ⟨``leafP, leafP.machineData, leafP.machineSource⟩

noncomputable abbrev wrapPPkg : GenPkg DomainConfig (fun i => i) :=
  { decl := ``wrapP, d := wrapP.machineData, ρ := _, inh := wrapP_inhab, inits := wrapP.machineInits, body := wrapP.machineBody,
    obsR := wrapP.machineResult, ext := wrapP.machineExt, extB := wrapP.machineExtB, src := wrapP.machineSource, gen := wrapP_gen }

noncomputable abbrev wrapQPkg : GenPkg DomainConfig (fun i => i) :=
  { decl := ``wrapQ, d := wrapQ.machineData, ρ := _, inh := wrapQ_inhab, inits := wrapQ.machineInits, body := wrapQ.machineBody,
    obsR := wrapQ.machineResult, ext := wrapQ.machineExt, extB := wrapQ.machineExtB, src := wrapQ.machineSource, gen := wrapQ_gen }

noncomputable def wrapPDat : QWrapData qLeafP wrapPPkg where
  arity := 3
  nameK := wpName
  nk := wpNk
  outsK := wpOuts
  namesK := wpNames
  names := namesP
  mem := wrapP_memCallee
  ordKid := by first | decide | decide +kernel
  ordArgsN := by first | decide | decide +kernel
  ordT := fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩
  widths := wpW
  wid := by first | decide | decide +kernel
  ordW := fun _ _ _ => rfl
  kidOuts := wpKidOuts
  kidIns := wpKidIns
  kidMemT := fun k hk cb aw dw h => by
    have h0 := wrapP_allOrd k hk
    rw [h0] at h; cases h
  kidOrdT := fun _ _ _ => ⟨rfl, rfl⟩
  cw := by first | decide | decide +kernel
  outsClean := by first | decide | decide +kernel
  scalar := by first | decide | decide +kernel
  outOk := by first | decide | decide +kernel
  mcb := false
  maw := 4
  mdw := 8
  tags := by first | decide | decide +kernel
  agree := wrapP_agree
  cne := wrapP_cne
  hextB := wrapP_hextB
  hext := wrapP_hext
  memCalls := fun i bools bits k c hc hch =>
    absurd (wrapP_allOrd k (by have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this)) hch
  argPos := fun _ p => p
  argsIn := by first | decide | decide +kernel
  callOut := by
    intro k hk hn i bools bits
    have hk2 : k = 0 ∨ k = 1 := by have hk3 : k < wrapP.machineData.shape.insts.length := hk; have := wrapP_len; omega
    rcases hk2 with rfl | rfl
    · refine ⟨0, leafP.machineData.shape.layout.outs[0]'(by decide), List.getElem?_eq_getElem (by decide), by decide +kernel, ?_⟩
      intro bools' bits' hb hb'
      have hB : bits' 1 8 = bits 1 8 := hb' 1 8 (by first | decide +kernel | rfl)
      obtain ⟨f, hf⟩ : ∃ f, (leafP.machineSource i bools' bits')[0]? = some f := by
        unfold leafP.machineSource; exact ⟨_, rfl⟩
      refine ⟨f, hf, ?_⟩
      unfold leafP.machineSource at hf
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      intro τ
      unfold posEnc
      simp only [Tests.Compiler.CDef.GenPkg.extS, Tests.Compiler.CDef.GenPkg.extBS]
      unfold wrapP.machineExt wrapP.machineExtB
      simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
      have hkd : ((wrapPPkg.d.bsIn.drop 3)[0]?.map (·.2)).getD .domain = .bits 8 := by decide +kernel
      rw [hkd, hB]
      simp
    · refine ⟨1, leafP.machineData.shape.layout.outs[1]'(by decide), List.getElem?_eq_getElem (by decide), by decide +kernel, ?_⟩
      intro bools' bits' hb hb'
      have hB : bits' 1 8 = bits 1 8 := hb' 1 8 (by first | decide +kernel | rfl)
      obtain ⟨f, hf⟩ : ∃ f, (leafP.machineSource i bools' bits')[1]? = some f := by
        unfold leafP.machineSource; exact ⟨_, rfl⟩
      refine ⟨f, hf, ?_⟩
      unfold leafP.machineSource at hf
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      intro τ
      unfold posEnc
      simp only [Tests.Compiler.CDef.GenPkg.extS, Tests.Compiler.CDef.GenPkg.extBS]
      unfold wrapP.machineExt wrapP.machineExtB
      simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
      have hkd : ((wrapPPkg.d.bsIn.drop 3)[1]?.map (·.2)).getD .domain = .bool := by decide +kernel
      rw [hkd, hB]
      simp

noncomputable def wrapQDat : QWrapData qLeafP wrapQPkg where
  arity := 5
  nameK := wqName
  nk := wqNk
  outsK := wqOuts
  namesK := wqNames
  names := namesQ
  mem := wrapQ_memCallee
  ordKid := wrapQ_ordKid
  ordArgsN := wrapQ_argsN
  ordT := fun k hk hn => by
    have h2 := (wrapQ_ord k hk hn).1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [wqName, wqNk, wqOuts, wqNames, h2]
  widths := wqW
  wid := wrapQ_wid
  ordW := wrapQ_hw
  kidOuts := wqKidOuts
  kidIns := wqKidIns
  kidMemT := fun k hk cb aw dw h => by
    have hk2 : k = 2 := by
      rcases Nat.lt_or_ge k 2 with hk' | hk'
      · have h0 : (originAt wrapQ.machineData.shape k).child? = none := (wrapQ_ord_lt k hk hk')
        rw [h0] at h; cases h
      · have hk3 : k < wrapQ.machineData.shape.insts.length := hk
        have := wrapQ_len; omega
    subst hk2
    obtain ⟨e1, e2, e3⟩ := Tools.ShippingSrm4Kid.memModule_inj ((Option.some.inj (wrapQ_origin2.symm.trans h)))
    subst e1; subst e2; subst e3
    simp only [wqKidOuts, wqKidIns]
    exact ⟨by simp, by simp⟩
  kidOrdT := fun k hk hn => by
    have h2 := (wrapQ_ord k hk hn).1
    refine ⟨?_, ?_⟩ <;> simp [wqKidOuts, wqKidIns, h2]
  cw := by first | decide | decide +kernel
  outsClean := wrapQ_outsClean
  scalar := by first | decide | decide +kernel
  outOk := wrapQ_outOk
  mcb := false
  maw := 4
  mdw := 8
  tags := by first | decide | decide +kernel
  agree := wrapQ_agree
  cne := wrapQ_cne
  hextB := wrapQ_hextB
  hext := wrapQ_hext
  memCalls := fun i bools bits k c hc hch => wrapQ_memcalls i bools bits k c hc hch
  argPos := fun _ p => if p = 1 then 3 else p
  argsIn := by first | decide | decide +kernel
  callOut := by
    intro k hk hn i bools bits
    have hk2 : k = 0 ∨ k = 1 := by have h2 := (wrapQ_ord k (by exact hk) hn).1; omega
    rcases hk2 with rfl | rfl
    · refine ⟨0, leafP.machineData.shape.layout.outs[0]'(by decide), List.getElem?_eq_getElem (by decide), by decide +kernel, ?_⟩
      intro bools' bits' hb hb'
      have hB : bits' 1 8 = bits 3 8 := hb' 1 8 (by first | decide +kernel | rfl)
      obtain ⟨f, hf⟩ : ∃ f, (leafP.machineSource i bools' bits')[0]? = some f := by
        unfold leafP.machineSource; exact ⟨_, rfl⟩
      refine ⟨f, hf, ?_⟩
      unfold leafP.machineSource at hf
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      intro τ
      unfold posEnc
      simp only [Tests.Compiler.CDef.GenPkg.extS, Tests.Compiler.CDef.GenPkg.extBS]
      unfold wrapQ.machineExt wrapQ.machineExtB
      simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
      have hkd : ((wrapQPkg.d.bsIn.drop 5)[0]?.map (·.2)).getD .domain = .bits 8 := by decide +kernel
      rw [hkd, hB]
      simp
    · refine ⟨1, leafP.machineData.shape.layout.outs[1]'(by decide), List.getElem?_eq_getElem (by decide), by decide +kernel, ?_⟩
      intro bools' bits' hb hb'
      have hB : bits' 1 8 = bits 3 8 := hb' 1 8 (by first | decide +kernel | rfl)
      obtain ⟨f, hf⟩ : ∃ f, (leafP.machineSource i bools' bits')[1]? = some f := by
        unfold leafP.machineSource; exact ⟨_, rfl⟩
      refine ⟨f, hf, ?_⟩
      unfold leafP.machineSource at hf
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      intro τ
      unfold posEnc
      simp only [Tests.Compiler.CDef.GenPkg.extS, Tests.Compiler.CDef.GenPkg.extBS]
      unfold wrapQ.machineExt wrapQ.machineExtB
      simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
      have hkd : ((wrapQPkg.d.bsIn.drop 5)[1]?.map (·.2)).getD .domain = .bool := by decide +kernel
      rw [hkd, hB]
      simp

noncomputable def P_Q (hgrp : TqGrp) : QSharedLeafParent where
  top := { decl := ``topshareQ, d := topshareQ.machineData, ρ := _, inh := topshareQ_inhab, inits := topshareQ.machineInits,
           body := topshareQ.machineBody, obsR := topshareQ.machineResult, ext := topshareQ.machineExt, extB := topshareQ.machineExtB,
           src := topshareQ.machineSource, gen := topshareQ_gen }
  nDecl := 4
  cs := csQ
  pdata := topshareQ_parentData
  outTy := topshareQ_outTy
  noMem := topshareQ_nomem
  slotsNe := topshareQ_slotsNe
  outsOf := tqOuts
  insOf := tqIns
  cw := topshareQ_cw
  ca := topshareQ_ca
  leaf := qLeafP
  leafData := leafP_data
  leafKidData := leafP_kidData
  leafLetsOk := by first | decide | decide +kernel
  leafNoMem := leafP_nomem
  leafRun := leafP_run
  wrappers := [⟨wrapPPkg, wrapPDat⟩, ⟨wrapQPkg, wrapQDat⟩]
  bsC := tqBsC
  outsC := tqOutsC
  srcC := tqSrcC
  group := hgrp
  wOf := fun k => if k < 2 then 0 else 1
  tieCallee := by first | decide | decide +kernel
  tieOuts := by first | decide | decide +kernel
  tieIns := by first | decide | decide +kernel
  tieBsC := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | rfl | decide | decide +kernel
  tieOutsC := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | rfl | decide | decide +kernel
  tieSrcC := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | rfl | (simp [tqSrcC])
  tieCs := rfl
  csNc := csQ_nc
  csCd := csQ_cd

/-! ## defeq audits (Q): the class projections ARE the terms of TqGrp / topshareQ_soundLA / tqOuts / tqIns / tqBsC / csQ -/
variable {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}

theorem P_Q_group_defeq (hgrp : TqGrp) :
    QuadGroupFacts (P_Q hgrp).top.d (P_Q hgrp).nDecl (P_Q hgrp).top.lsrc (P_Q hgrp).top.extS (P_Q hgrp).top.extBS (P_Q hgrp).bsC (P_Q hgrp).outsC (P_Q hgrp).srcC = TqGrp := rfl
theorem P_Q_ext_defeq (hgrp : TqGrp) : (P_Q hgrp).top.extS = tqExt := rfl
theorem P_Q_extB_defeq (hgrp : TqGrp) : (P_Q hgrp).top.extBS = tqExtB := rfl
theorem P_Q_lsrc_defeq (hgrp : TqGrp) :
    (P_Q hgrp).top.lsrc = Tools.ShippingMachineCausal.letObsB topshareQ.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineInits
        topshareQ.machineBody topshareQ.machineExt topshareQ.machineExtB := rfl
theorem P_Q_tables_defeq (hgrp : TqGrp) : (P_Q hgrp).outsOf = tqOuts ∧ (P_Q hgrp).insOf = tqIns ∧ (P_Q hgrp).bsC = tqBsC ∧ (P_Q hgrp).outsC = tqOutsC ∧ (P_Q hgrp).srcC = tqSrcC :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem P_Q_cs_defeq (hgrp : TqGrp) : (P_Q hgrp).cs = csQ ∧ (P_Q hgrp).wArity = [3, 5] ∧
    (P_Q hgrp).wrappers.map (·.pkg.decl) = [``wrapP, ``wrapQ] ∧ (P_Q hgrp).wrappers.map (·.dat.names) = [namesP, namesQ] :=
  ⟨rfl, rfl, rfl, rfl⟩
/-- the statement of `topshareQ_soundLA` re-spelled through the class projections is the same type -/
theorem P_Q_soundL_defeq (hgrp : TqGrp) :
    Tools.ShippingMachineAuto.MachineTraceLB (P_Q hgrp).top.decl (P_Q hgrp).top.d m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) (P_Q hgrp).top.src
      (P_Q hgrp).top.extS (P_Q hgrp).top.extBS (P_Q hgrp).top.lsrc =
    Tools.ShippingMachineAuto.MachineTraceLB ``topshareQ topshareQ.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineSource
      (fun i bools bits => topshareQ.machineExt i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (fun i bools bits => topshareQ.machineExtB i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshareQ.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineInits
        topshareQ.machineBody topshareQ.machineExt topshareQ.machineExtB) := rfl
/-- the leaf run field IS the generated `leafP.seq_child_runN` (as `leafP_run`) -/
theorem P_Q_leafRun_defeq (hgrp : TqGrp) :
    LeafSeqRunN (P_Q hgrp).leaf.decl (P_Q hgrp).leaf.d (P_Q hgrp).leaf.src = LeafSeqRunN ``leafP leafP.machineData leafP.machineSource := rfl
/-- `MachineCloses` of the plain leaf (TqBnd's `hcl` component) is DERIVED from the class: `leafLetsOk` + `leafData` through `closes_of_data` -/
theorem P_Q_hcl (hgrp : TqGrp) {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State} :
    ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``leafP leafP.machineData.shape :=
  fun mc cc => Tools.ShippingMachineClosesData.closes_of_data (declName := (P_Q hgrp).leaf.decl) (P_Q hgrp).leaf.d
    (P_Q hgrp).leafData.ok (P_Q hgrp).leafData.body (P_Q hgrp).leafLetsOk mc mref cc cref

/-! ## the frozen C5 statement (scripts/c5/C5_STATEMENT.lean.txt), elaborated as a Prop -/
section Frozen
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingMachineLinked (childMap)
open Sparkle.IR.RegDedup (declWidth)
open Sparkle.IR.OptCheck Sparkle.IR.HierCheck Sparkle.IR.Semantics
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun
open Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMixedSourceBridge
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Tools.ShippingMachineAuto

def FrozenC5 : Prop := ∀ (P : QSharedLeafParent)

    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (T : Tools.ShippingChildInvA.RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    (hw : JQC O 0 w)

    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)),
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = P.top.d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = P.top.d.ss.length ∧
      ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
        (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
        (T' : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
        (kids : String → KT 2),

        (∀ t st, t < T' → SourceInputs P.top.decl (P.top.d.bsIn.take P.nDecl) ids cache
          (fun j => (P.top.extBS i bools bits j).val (T' - 1 - t))
          (fun j n => (P.top.extS i bools bits j n).val (T' - 1 - t)) (seedIn b ins t st)) →
        (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
        (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          P.top.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        ResetNk 2 raw D kids →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
        (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
          st0 x < 2 ^ declWidth b x) →
        ∃ envsO, runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b))
            (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T'
            ⟨st0, mems, kids⟩ = some envsO ∧
          envsO.length = T' ∧
          ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            P.top.d.shape.layout.outs[k]? = some o → (P.top.src i bools bits)[k]? = some f →
            (envsO[j]'hj) o.name = f j

end Frozen

/-! ## audits -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- (1) the member takes exactly ONE explicit binder, the group class assumption TqGrp
  let t := (← getConstInfo ``P_Q).type
  forallTelescope t fun xs body => do
    unless xs.size == 1 do throwError "QDEF AUDIT FAILED: P_Q has {xs.size} binders, expected 1 (the group assumption)"
    unless ← isDefEq (← inferType xs[0]!) (mkConst ``Tests.Compiler.SharedLeafMemKidIfaceTest.TqGrp) do throwError "QDEF AUDIT FAILED: P_Q's binder is not TqGrp"
    unless ← isDefEq body (mkConst ``QSharedLeafParent) do throwError "QDEF AUDIT FAILED: P_Q is not a QSharedLeafParent"
  -- (2) the frozen statement has exactly the C4 binder list (19 binders incl. P), no hcl binder
  let fz ← getConstInfo ``FrozenC5
  let some fv := fz.value? | throwError "QDEF AUDIT FAILED: no frozen value"
  let frozenNames : List String := ["P", "mctx", "mref", "cctx", "cref", "w", "w1", "O", "T", "hA", "entryL", "entryW", "entry", "hw",
    "b", "raw", "D", "hcore", "hpost"]
  let frozenImplicit : List String := ["mctx", "mref", "cctx", "cref", "w", "w1", "b", "raw", "D"]
  forallTelescope fv fun xs _ => do
    unless xs.size == frozenNames.length do throwError "QDEF AUDIT FAILED: FrozenC5 has {xs.size} binders, expected {frozenNames.length}"
    for (x, nm) in xs.toList.zip frozenNames do
      let u := (← x.fvarId!.getUserName).toString
      unless u == nm do throwError "QDEF AUDIT FAILED: FrozenC5 binder {u}, expected {nm}"
      let bi ← x.fvarId!.getBinderInfo
      unless (bi == .implicit) == frozenImplicit.contains nm do throwError "QDEF AUDIT FAILED: FrozenC5 binder {nm} info {repr bi}"
  -- (3) NO field of the class (or of its parts) is a target Prop
  let banned : List Name := [``Tools.ShippingSeqParentLemmas.HCallsOf, ``Tools.ShippingQuadCalls.CallFactF, ``Tools.ShippingSrm4Mixed.CallFactFO,
    ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingMachineDepthRun.ComposedNW, ``Tools.ShippingSrm4Core6.KidFactsNC]
  let nFields ← IO.mkRef (0 : Nat)
  for sn in [``QSharedLeafParent, ``QWrapData, ``QWrapper, ``QLeafPkg] do
    let info ← getConstInfo sn
    forallTelescope info.type fun _ _ => pure ()
    let ctor ← match (← getEnv).find? (sn ++ `mk) with
      | some (.ctorInfo c) => pure c
      | _ => throwError "QDEF AUDIT FAILED: {sn}.mk missing"
    forallTelescope ctor.type fun xs _ => do
      for x in xs do
        nFields.modify (· + 1)
        let ty ← inferType x
        for c in ty.getUsedConstants do
          if banned.contains c then
            throwError "QDEF AUDIT FAILED: field {← x.fvarId!.getUserName} of {sn} mentions the target {c}"
  -- (4) the member, the audits and the derived-hcl lemma: standard axioms only
  let audits := [``P_Q, ``P_Q_group_defeq, ``P_Q_ext_defeq, ``P_Q_extB_defeq, ``P_Q_lsrc_defeq, ``P_Q_tables_defeq, ``P_Q_cs_defeq,
    ``P_Q_soundL_defeq, ``P_Q_leafRun_defeq, ``P_Q_hcl, ``wrapPDat, ``wrapQDat]
  unless audits.length == 12 do throwError "QDEF AUDIT FAILED: audit list has {audits.length} entries, not 12"
  unless audits.Nodup do throwError "QDEF AUDIT FAILED: duplicate entries in the audit list"
  for a in audits do
    discard <| getConstInfo a
    let axs ← Lean.collectAxioms a
    for x in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "QDEF AUDIT FAILED: non-standard axiom {x} in {a}"
  logInfo m!"QDEF|ok|P_Q: one binder (TqGrp), QSharedLeafParent; FrozenC5 has {frozenNames.length} binders = the C4 list (no hcl); {← nFields.get} constructor binders checked free of target Props; {audits.length} constants with standard axioms only"

end Tests.Compiler.QDef
