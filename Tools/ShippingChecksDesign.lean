import Tools.ShippingChecksRunFacts
import Tools.ShippingChecksDepthGate

/-! # `designCheck`: its structural conjuncts from the run's facts (isolated branch `fix/opt-fallback`)

`designCheck C n o = textCheckI C o && kidsPass C (leafCheck | designCheck C (n-1)) o.body`
with `o = checkedOptimize b` is the last check antecedent of the depth SV
endpoints. `textCheckI` has eight conjuncts (inventory and classification:
`docs/parallel/G1-designCheck.md`). FIVE are about the shipped module's
structure and follow from `Tools.ShippingGuardsSound.RunFacts C b` — what
`Tools.ShippingChecksRunFacts.core_runFacts` derives from the core run —
with NO check premise:

* `core_design_linked` (conjunct 4) and `core_design_names` (5):
  `core_shipped_facts`;
* `core_design_kinds` (1): `linkedWF` accepts only assignments, instances
  and registers (`seqStmtOkI_of_linkedWF`);
* `core_design_self` (6): the shipped module has the full entry's instance
  statements under the gate (`checkedOptimize_inst_iff_gate`);
* `core_design_resolve` (8): `linkedWF` resolves every instance.

`textCheckI_of`: `textCheckI` from its eight conjuncts, named.
`core_designCheck_rest`: `designCheck C n (checkedOptimize b)` at every
depth from `RunFacts C b` and the FOUR remaining facts as hypotheses — the
three emitted-text conjuncts of the shipped module (`seqCheck`, the width
tables' agreement on `seqNames`, `portsMatchB`) and the children's check
(`kidCheck C n`: `leafCheck` at depth 0, `designCheck C k` at depth `k+1`).

What is NOT proved here: those four (see the doc: which printer / width
statements they need).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksDesign
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RegDedup (declWidth)

/-- `linkedWF` accepts only assignments, instances and registers. -/
theorem seqStmtOkI_of_linkedWF {C : String → Option (Sparkle.IR.AST.Module × WEnv)} :
    ∀ (body : List Stmt), Tools.ShippingHierOpen.linkedWF C body = true →
      body.all Tools.ShippingHierSVSoundness.seqStmtOkI = true
  | [], _ => rfl
  | st :: rest, h => by
    cases st with
    | assign l r =>
      simp only [Tools.ShippingHierOpen.linkedWF, Bool.and_eq_true] at h
      have ih := seqStmtOkI_of_linkedWF (C := C) rest h.2
      have hk : Tools.ShippingHierSVSoundness.seqStmtOkI (Stmt.assign l r) = true := rfl
      exact Tools.ShippingChecksDepth.and_true_intro hk ih
    | inst mn i conns =>
      simp only [Tools.ShippingHierOpen.linkedWF, Bool.and_eq_true] at h
      have ih := seqStmtOkI_of_linkedWF (C := C) rest h.2
      have hk : Tools.ShippingHierSVSoundness.seqStmtOkI (Stmt.inst mn i conns) = true := rfl
      exact Tools.ShippingChecksDepth.and_true_intro hk ih
    | register o c rk inp iv =>
      simp only [Tools.ShippingHierOpen.linkedWF] at h
      have ih := seqStmtOkI_of_linkedWF (C := C) rest h
      have hk : Tools.ShippingHierSVSoundness.seqStmtOkI (Stmt.register o c rk inp iv) = true :=
        rfl
      exact Tools.ShippingChecksDepth.and_true_intro hk ih
    | _ => simp [Tools.ShippingHierOpen.linkedWF] at h

variable {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {b : Sparkle.IR.AST.Module}

/-- Conjunct 4: the shipped body is linked-well-formed. -/
theorem core_design_linked (h : Tools.ShippingGuardsSound.RunFacts C b) :
    Tools.ShippingHierOpen.linkedWF C (checkedOptimize b).body = true :=
  (Tools.ShippingChecksRunFacts.core_shipped_facts h).1

/-- Conjunct 5: the shipped body's instance names are distinct. -/
theorem core_design_names (h : Tools.ShippingGuardsSound.RunFacts C b) :
    (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup :=
  (Tools.ShippingChecksRunFacts.core_shipped_facts h).2.1

/-- Conjunct 1: the shipped body is assignments, registers and instances. -/
theorem core_design_kinds (h : Tools.ShippingGuardsSound.RunFacts C b) :
    (checkedOptimize b).body.all Tools.ShippingHierSVSoundness.seqStmtOkI = true :=
  seqStmtOkI_of_linkedWF _ (core_design_linked h)

/-- Conjunct 6: no instance of the shipped body reads its own output. -/
theorem core_design_self (h : Tools.ShippingGuardsSound.RunFacts C b) :
    Tools.ShippingHierPremisesBase.noSelfRead C (checkedOptimize b).body = true :=
  Tools.ShippingChecksDerived2.all_inst_transfer _
    (fun mn iname conns =>
      (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate h.gate mn iname conns).mp)
    (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h.self

/-- Conjunct 8: every instance of the shipped body resolves. -/
theorem core_design_resolve (h : Tools.ShippingGuardsSound.RunFacts C b) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      (C mn).isSome = true := by
  intro mn iname conns hm
  obtain ⟨child, cwe, hc, -⟩ :=
    Tools.ShippingGuardsSound.linkedWF_inst _ (core_design_linked h) mn iname conns hm
  simp [hc]

/-- **`textCheckI` is the conjunction of eight named facts.** -/
theorem textCheckI_of {o : Sparkle.IR.AST.Module}
    (hkinds : o.body.all Tools.ShippingHierSVSoundness.seqStmtOkI = true)
    (htext : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf o)
      (Tools.ShippingDesignSV.weS o) o.body = true)
    (hwidths : (Tools.ShippingSeqSVSoundness.seqNames o.body).all
      (fun x => declWidth o x == Tools.ShippingDesignSV.weS o x) = true)
    (hlinked : Tools.ShippingHierOpen.linkedWF C o.body = true)
    (hnames : (Tools.ShippingHierState.instNames o.body).Nodup)
    (hself : Tools.ShippingHierPremisesBase.noSelfRead C o.body = true)
    (hports : Tools.ShippingDesignSV.portsMatchB C o = true)
    (hresolve : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → (C mn).isSome = true) :
    Tools.ShippingDesignSV.textCheckI C o = true := by
  simp only [Tools.ShippingDesignSV.textCheckI, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨hkinds, htext⟩, hwidths⟩, hlinked⟩, hnames⟩, hself⟩, hports⟩,
    List.all_eq_true.mpr fun st hst => by
      cases st with
      | inst mn iname conns => exact hresolve mn iname conns hst
      | _ => rfl⟩

/-- What `designCheck C n` asks of each child: the leaf check at depth 0, the
design check one level down otherwise. -/
def kidCheck (C : String → Option (Sparkle.IR.AST.Module × WEnv)) :
    Nat → Sparkle.IR.AST.Module → Bool
  | 0 => Tools.ShippingDesignSV.leafCheck
  | k + 1 => Tools.ShippingDesignSV.designCheck C k

/-- `designCheck` in one equation over the depth. -/
theorem designCheck_eq (n : Nat) (o : Sparkle.IR.AST.Module) :
    Tools.ShippingDesignSV.designCheck C n o =
      (Tools.ShippingDesignSV.textCheckI C o &&
        Tools.ShippingDesignSV.kidsPass C (kidCheck C n) o.body) := by
  cases n <;> rfl

/-- **`designCheck` of the shipped module, at every depth, with the
structural conjuncts derived.** Hypotheses left: the three emitted-text
conjuncts of the shipped module and the children's check. -/
theorem core_designCheck_rest (h : Tools.ShippingGuardsSound.RunFacts C b) (n : Nat)
    -- TEXT: every assignment / register input is in the emitted fragment at
    -- its declared width, under clean declared names
    (htext : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf (checkedOptimize b))
      (Tools.ShippingDesignSV.weS (checkedOptimize b)) (checkedOptimize b).body = true)
    -- TEXT (width tables): the IR's and the emitter's widths agree on the names used
    (hwidths : (Tools.ShippingSeqSVSoundness.seqNames (checkedOptimize b).body).all
      (fun x => declWidth (checkedOptimize b) x ==
        Tools.ShippingDesignSV.weS (checkedOptimize b) x) = true)
    -- TEXT (connections): a connected wire and its child port have one emitted width
    (hports : Tools.ShippingDesignSV.portsMatchB C (checkedOptimize b) = true)
    -- CHILDREN: each instance's child passes the check one level down
    (hkids : Tools.ShippingDesignSV.kidsPass C (kidCheck C n) (checkedOptimize b).body = true) :
    Tools.ShippingDesignSV.designCheck C n (checkedOptimize b) = true := by
  rw [designCheck_eq]
  exact Tools.ShippingChecksDepth.and_true_intro
    (textCheckI_of (core_design_kinds h) htext hwidths (core_design_linked h)
      (core_design_names h) (core_design_self h) hports (core_design_resolve h))
    hkids

end Tools.ShippingChecksDesign
