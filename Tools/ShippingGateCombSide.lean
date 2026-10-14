import Tools.ShippingGateOptComb
import Tools.ShippingGateDesignPost
import Tools.ShippingOneOutFacts
import Tools.ShippingInstWidthsParts
import Tools.ShippingChecksDepthGate
import Tools.ShippingGuardsSound

/-! # Gate-route parents: narrowing the checker bundles `combOptSide` and `DesignSide` (worker N, round 12)

WRITTEN, NOT BUILT. PURE: no run.

`Tools.ShippingGateOptComb.combOptSide ms b` (nine conjuncts, five of them
about `b`, four about the shipped `checkedOptimize b`) and
`Tools.ShippingGateDesignLift.DesignSide ms b ins st0 kids` (two decidable
checks of the shipped module, five width / start-state premises) are the
antecedents left on the seven `…_gate_designSV''`. Here they are narrowed the
way the machine route's `machine_design_svH_free` narrowed `shipsHierHCheck`
/ `kidsComb` / `designCheck` (`Tools.ShippingOneOutHead`,
`Tools.ShippingOneOutFacts.shipped_factsH` / `designCheckH_rest`):

DERIVED
* `hierGate b` — from the walk: (B) `PostKeeps b M` (assignments and
  instances) and `ModOk.has` (an instance in the core body)
  (`hierGate_of_post`, `hierGate_of_modOk`);
* the FOUR conjuncts about `checkedOptimize b` (`linkedWF`, distinct instance
  names, `noSelfRead`, `kidsLocal`) — from the same facts of `b`, whatever
  branch the compiler took (`Tools.ShippingGuardsSound.checkedOptimize_facts`:
  the guards of `deinline` on an accepted candidate; the instance statements
  of the shipped module are `b`'s, `checkedOptimize_inst_iff_gate`, so the
  per-instance checks move; `kidsLocal_of_comb`) — `shipped_factsG`
  (`shipped_factsH` without its unused `rst` field);
* `kidsComb ms (checkedOptimize b).body` of `DesignSide` — moved from
  `kidsComb ms b.body` along the instance statements;
* `designCheck (childMap ms) 0 (checkedOptimize b)` of `DesignSide` — six of
  the eight `textCheckI` conjuncts derived (statement kinds, linked
  well-formedness, distinct names, no self read, every instance resolved, and
  the two emitted-text conjuncts MOVED from `b` by
  `Tools.ShippingTextShipped.text_shipped_of`); the children's check moved
  from `b`'s instance statements;
* the children's start-state premise of `DesignSide` stated over `b`'s
  instance statements (moved to the shipped module).

LEFT (`combSideB`, `designSideB`, `DesignSideR`; all OUTSIDE ALLOWED; see
the round-12 record for why each is not derived by the walk):
* `combSideB ms b` — six facts of the FULL ENTRY's module `b` (not of the
  optimizer's output): `linkedWF (childMap ms) b.body`, distinct instance
  names of `b.body`, `noSelfRead`, `outsExtracted`, `kidsComb ms b.body`,
  `hierTyped (childMap ms) b`;
* `designSideB ms b` — the two emitted-text conjuncts OF `b`
  (`seqCheck (wofOf b) (weS b) b.body`, the `seqNames` width agreement), the
  connection widths `portsMatchB (childMap ms) (checkedOptimize b)` (the one
  conjunct of the shipped module still asked; the machine route left the
  same one), the children's leaf check over `b`'s instances;
* `DesignSideR` — the run-level width premises (inputs fit in `declWidth b`
  and in the emitted widths `weS (checkedOptimize b)`, the start state bounded
  off the outputs and within the emitted widths, every child's start state
  `InvN … 0`): premises about the inputs and the start state, the machine
  route's `Bnd`, not checks. -/
namespace Tools.ShippingGateCombSide
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (hierGate)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingDesignSV (designCheck weS)
open Tools.ShippingDesignSVBounds (InvN)
open Tools.ShippingHierState (KidState)
open Tools.ShippingGateDesignLift (PostKeeps DesignSide)
open Tools.ShippingGateOptComb (combOptSide)

/-! ## `hierGate b` from the walk -/

/-- **The statement-kind gate of the returned module**, from (B) and an
instance in the core body. -/
theorem hierGate_of_post {b M : Sparkle.IR.AST.Module} (hB : PostKeeps b M)
    (hi : Tools.ShippingGateParentRun.HasInst M.body) : hierGate b = true := by
  obtain ⟨hcomb, hbody, -⟩ := hB
  apply Tools.ShippingInstWidthsParts.hierGate_of
  · obtain ⟨mn, i, cs, hm⟩ := hi
    refine ⟨mn, i, cs, ?_⟩
    rw [hbody]
    exact hm
  · intro st hst
    rw [hbody] at hst
    have h1 := List.all_eq_true.mp hcomb st hst
    cases st with
    | assign l r => exact Or.inr rfl
    | inst mn i cs => exact Or.inl rfl
    | _ => simp [Tools.ShippingHierSVSoundness.combStmtI] at h1

/-- **`hierGate b` from the walk's `ModOk`** and the post-pass shape. -/
theorem hierGate_of_modOk {N : String} {M b : Sparkle.IR.AST.Module}
    (h : Tools.ShippingGateParentRun.ModOk N M)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) :
    hierGate b = true :=
  hierGate_of_post (Tools.ShippingGateDesignPost.postKeeps_of_modOk h hpost) h.has

/-! ## The shipped module's facts from `b`'s -/

/-- **`Tools.ShippingOneOutFacts.shipped_factsH` without `RunFactsH.rst`**
(a copy of its proof, which never read that field): the shipped module, in
every branch of the compiler, is linked-well-formed, has distinct instance
names, passes the self-read test and has combinational children, when `b`
does. -/
theorem shipped_factsG {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (hg : hierGate b = true)
    (hwfB : Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true)
    (hndB : (Tools.ShippingHierState.instNames b.body).Nodup)
    (hself : Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) b.body = true)
    (hout : Tools.ShippingHierPremisesBase.outsExtracted (childMap ms) b = true)
    (hcomb : Tools.ShippingMachineDepthH.kidsComb ms b.body = true) :
    Tools.ShippingHierOpen.linkedWF (childMap ms) (checkedOptimize b).body = true ∧
      (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup ∧
      Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) (checkedOptimize b).body = true ∧
      Tools.ShippingMachineDepthH.kidsComb ms (checkedOptimize b).body = true := by
  obtain ⟨hwfS, hndS, -⟩ :=
    Tools.ShippingGuardsSound.checkedOptimize_facts hg hwfB hndB hout
  refine ⟨hwfS, hndS, ?_, ?_⟩
  · exact Tools.ShippingChecksDerived2.all_inst_transfer _
      (fun mn iname conns =>
        (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hg mn iname conns).mp)
      (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) hself
  · exact Tools.ShippingChecksDerived2.all_inst_transfer _
      (fun mn iname conns =>
        (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hg mn iname conns).mp)
      (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) hcomb

/-! ## The residue of `combOptSide`: six facts of `b` -/

/-- The facts of the full entry's module `b` that `combOptSide` still needs
(decidable, OUTSIDE ALLOWED). -/
def combSideB (ms : List Sparkle.IR.AST.Module) (b : Sparkle.IR.AST.Module) : Bool :=
  Tools.ShippingHierOpen.linkedWF (childMap ms) b.body &&
    decide (Tools.ShippingHierState.instNames b.body).Nodup &&
    Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) b.body &&
    Tools.ShippingHierPremisesBase.outsExtracted (childMap ms) b &&
    Tools.ShippingMachineDepthH.kidsComb ms b.body &&
    Tools.ShippingHierTyped.hierTyped (childMap ms) b

theorem combSideB_sound {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (h : combSideB ms b = true) :
    Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true ∧
      (Tools.ShippingHierState.instNames b.body).Nodup ∧
      Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) b.body = true ∧
      Tools.ShippingHierPremisesBase.outsExtracted (childMap ms) b = true ∧
      Tools.ShippingMachineDepthH.kidsComb ms b.body = true ∧
      Tools.ShippingHierTyped.hierTyped (childMap ms) b = true := by
  simp only [combSideB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **`combOptSide` from the gate and `b`'s six facts**: `hierGate b` and
the four conjuncts about the shipped module are derived. -/
theorem combOptSide_of_B {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (hg : hierGate b = true) (h : combSideB ms b = true) : combOptSide ms b = true := by
  obtain ⟨hwf, hnd, hself, hout, hcomb, hty⟩ := combSideB_sound h
  obtain ⟨hwfS, hndS, hselfS, hcombS⟩ := shipped_factsG hg hwf hnd hself hout hcomb
  have hloc := Tools.ShippingOneOutClose.kidsLocal_of_comb hcombS
  simp only [combOptSide, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hg, hwf⟩, hwfS⟩, hnd⟩, hndS⟩, hselfS⟩, hout⟩, hloc⟩, hty⟩

/-! ## The residue of `designCheck … 0 (checkedOptimize b)` -/

/-- What `designCheck (childMap ms) 0 (checkedOptimize b)` still needs
beyond `combSideB` (decidable, OUTSIDE ALLOWED): the two emitted-text
conjuncts of `b`, the connection widths of the shipped module, the
children's leaf check over `b`'s instances. -/
def designSideB (ms : List Sparkle.IR.AST.Module) (b : Sparkle.IR.AST.Module) : Bool :=
  Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b) (weS b) b.body &&
    (Tools.ShippingSeqSVSoundness.seqNames b.body).all (fun x => declWidth b x == weS b x) &&
    Tools.ShippingDesignSV.portsMatchB (childMap ms) (checkedOptimize b) &&
    Tools.ShippingDesignSV.kidsPass (childMap ms)
      (Tools.ShippingChecksDesign.kidCheck (childMap ms) 0) b.body

/-- **`designCheck` of the shipped module at depth 0** from the gate,
`b`'s facts and `designSideB` (the route of
`Tools.ShippingOneOutFacts.designCheckH_rest`, without `rst`). -/
theorem designCheck0_of {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (hg : hierGate b = true)
    (hwfB : Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true)
    (hndB : (Tools.ShippingHierState.instNames b.body).Nodup)
    (hself : Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) b.body = true)
    (hout : Tools.ShippingHierPremisesBase.outsExtracted (childMap ms) b = true)
    (hcomb : Tools.ShippingMachineDepthH.kidsComb ms b.body = true)
    (h : designSideB ms b = true) :
    designCheck (childMap ms) 0 (checkedOptimize b) = true := by
  simp only [designSideB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hsc, hsn⟩, hports⟩, hkids⟩ := h
  obtain ⟨h2, h3⟩ := Tools.ShippingTextShipped.text_shipped_of hg ⟨hsc, hsn⟩
  obtain ⟨hwfS, hndS, hselfS, -⟩ := shipped_factsG hg hwfB hndB hself hout hcomb
  have hkidsS : Tools.ShippingDesignSV.kidsPass (childMap ms)
      (Tools.ShippingChecksDesign.kidCheck (childMap ms) 0) (checkedOptimize b).body = true :=
    Tools.ShippingChecksDerived2.all_inst_transfer _
      (fun mn iname conns =>
        (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hg mn iname conns).mp)
      (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) hkids
  rw [Tools.ShippingChecksDesign.designCheck_eq]
  exact Tools.ShippingChecksDepth.and_true_intro
    (Tools.ShippingChecksDesign.textCheckI_of
      (Tools.ShippingChecksDesign.seqStmtOkI_of_linkedWF _ hwfS) h2 h3 hwfS hndS hselfS hports
      (fun mn iname conns hm => by
        obtain ⟨child, cwe, hc, -⟩ :=
          Tools.ShippingGuardsSound.linkedWF_inst _ hwfS mn iname conns hm
        simp [hc]))
    hkidsS

/-! ## The residue of `DesignSide`: the width premises of the run -/

/-- `DesignSide` without its two checks, the children's start states stated
over `b`'s instance statements: premises about the inputs and the start
state (the machine route's `Bnd`), not checks. -/
def DesignSideR (ms : List Sparkle.IR.AST.Module) (b : Sparkle.IR.AST.Module)
    (ins : Nat → String → Nat) (st0 : String → Nat) (kids : String → KidState) : Prop :=
  (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) ∧
  Tools.ShippingHierTyped.BoundOff (declWidth b) (b.outputs.map (·.name)) st0 ∧
  (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) ∧
  Bounded (weS (checkedOptimize b)) st0 ∧
  (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ b.body →
    childMap ms mn = some (gc, gcwe) → InvN (childMap ms) 0 gc (kids iname))

/-- **`DesignSide` from the gate, `combSideB`, `designSideB` and the width
premises.** -/
theorem designSide_of_R {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    {ins : Nat → String → Nat} {st0 : String → Nat} {kids : String → KidState}
    (hg : hierGate b = true) (hB : combSideB ms b = true) (hD : designSideB ms b = true)
    (hR : DesignSideR ms b ins st0 kids) : DesignSide ms b ins st0 kids := by
  obtain ⟨hwf, hnd, hself, hout, hcomb, -⟩ := combSideB_sound hB
  obtain ⟨-, -, -, hcombS⟩ := shipped_factsG hg hwf hnd hself hout hcomb
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  exact ⟨h1, h2, hcombS, designCheck0_of hg hwf hnd hself hout hcomb hD, h3, h4,
    fun mn iname conns gc gcwe hm hc =>
      h5 mn iname conns gc gcwe
        ((Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hg mn iname conns).mp hm) hc⟩

end Tools.ShippingGateCombSide

#print axioms Tools.ShippingGateCombSide.hierGate_of_modOk
#print axioms Tools.ShippingGateCombSide.shipped_factsG
#print axioms Tools.ShippingGateCombSide.combOptSide_of_B
#print axioms Tools.ShippingGateCombSide.designCheck0_of
#print axioms Tools.ShippingGateCombSide.designSide_of_R
