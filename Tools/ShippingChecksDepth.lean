import Tools.ShippingChecksDerived3
import Tools.ShippingDesignWithG

/-! # `outsCheck` at every depth, from a design closed under resolution (G1)

`outsCheck C (n+1) o` asks, of each instance's child, `outsAssigned` and
`outsCheck C n`. With ONE child map for the whole design this is not a
per-depth fact: if every module of the design assigns its outputs (`hA`) and
every instance statement of every module of the design resolves in the
design (`hR`), then `outsCheck` holds of every module of the design at every
depth, and of the printed top module too. Pure.

* `outsCheck_design`: every module of such a design, every depth;
* `outsCheck_opt_all`: the printed module `checkedOptimize b` of a module
  `b` whose instances resolve in the design, every depth, under the gate
  `hierBinds b`;
* `visited_name`: the joined design has a module of every visited module's
  NAME (the join keeps the first module of a name);
* `resolves_by_name`: a name some module of the list has resolves;
* `designCheck0_of`: `designCheck C 0 o` from its nine conjuncts, named —
  the factoring of the one Bool (which of the nine are structural and which
  are emitted-text checks: docs/parallel/G1-checks.md §9).

Nothing about runs here (`Tools.ShippingChecksCore`). -/
namespace Tools.ShippingChecksDepth
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Semantics
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (hierBinds)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingChecksDerived Tools.ShippingChecksDerived2
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingDesignWith Tools.ShippingDesignWithG

theorem and_true_intro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  subst ha
  subst hb
  rfl

/-- **`outsCheck` of every module of a design closed under resolution whose
modules assign their outputs, at every depth.** -/
theorem outsCheck_design {ms : List Sparkle.IR.AST.Module}
    (hA : ∀ g ∈ ms, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hR : ∀ g ∈ ms, ∀ mn iname conns, Stmt.inst mn iname conns ∈ g.body →
      ∃ mc, moduleByName ms mn = some mc) :
    ∀ (n : Nat) (g : Sparkle.IR.AST.Module), g ∈ ms →
      Tools.ShippingDesignSVBack.outsCheck (childMap ms) n g = true
  | 0, g, hg => kidsPass_of_insts fun mn iname conns hm => by
    obtain ⟨mc, hmc⟩ := hR g hg mn iname conns hm
    have hmem := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
    exact ⟨mc, _, congrArg (Option.map fun c => (c, declWidth c)) hmc,
      outsLeaf_of_assigned (Tools.ShippingDesignSVBack.outsAssigned_sound (hA mc hmem))⟩
  | n + 1, g, hg => kidsPass_of_insts fun mn iname conns hm => by
    obtain ⟨mc, hmc⟩ := hR g hg mn iname conns hm
    have hmem := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
    exact ⟨mc, _, congrArg (Option.map fun c => (c, declWidth c)) hmc,
      and_true_intro (hA mc hmem) (outsCheck_design hA hR n mc hmem)⟩

/-- **`outsCheck` of the printed module at every depth.** -/
theorem outsCheck_opt_all {b : Sparkle.IR.AST.Module} {ms : List Sparkle.IR.AST.Module}
    (hb : hierBinds b = true)
    (hres : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName ms mn = some mc)
    (hA : ∀ g ∈ ms, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hR : ∀ g ∈ ms, ∀ mn iname conns, Stmt.inst mn iname conns ∈ g.body →
      ∃ mc, moduleByName ms mn = some mc) :
    ∀ n : Nat, Tools.ShippingDesignSVBack.outsCheck (childMap ms) n (checkedOptimize b) = true
  | 0 => outsCheck0_opt hb hres
      (fun _ mc hmc _ => hA mc (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1)
  | n + 1 => kidsPass_of_insts fun mn iname conns hm => by
    obtain ⟨mc, hmc⟩ := hres mn iname conns ((checkedOptimize_inst_iff hb mn iname conns).mp hm)
    have hmem := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
    exact ⟨mc, _, congrArg (Option.map fun c => (c, declWidth c)) hmc,
      and_true_intro (hA mc hmem) (outsCheck_design hA hR n mc hmem)⟩

/-- The joined design has a module of every visited module's name. -/
theorem visited_name {children : List (Sparkle.IR.AST.Module × Design)} {d : Design}
    (hd : d.modules = []) :
    ∀ g ∈ visited children, ∃ y ∈ (designWith children d).modules, y.name = g.name := by
  rw [designWith_flatG children d, hd]
  obtain ⟨-, -, hcv⟩ := fold_facts (visited children) [] (by simp)
  exact fun g hg => hcv g (Or.inr hg)

/-- A name some module of the list has resolves. -/
theorem resolves_by_name {ms : List Sparkle.IR.AST.Module} {mn : String}
    (h : ∃ g ∈ ms, g.name = mn) : ∃ mc, moduleByName ms mn = some mc := by
  obtain ⟨g, hg, hn⟩ := h
  have hs : (ms.find? fun c => c.name == mn).isSome = true :=
    List.find?_isSome.mpr ⟨g, hg, by simp [hn]⟩
  exact Option.isSome_iff_exists.mp hs

/-- **`designCheck` at depth 0 is the conjunction of nine named facts.**
Structural: `hkinds`, `hlinked`, `hnames`, `hself`, `hresolve` and the
statement-kind part of `hkids`; emitted-text: `htext`, `hwidths`, `hports`
and the rest of `hkids` (`leafCheck`'s width agreement and `seqCheck`). -/
theorem designCheck0_of {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {o : Sparkle.IR.AST.Module}
    (hkinds : o.body.all Tools.ShippingHierSVSoundness.seqStmtOkI = true)
    (htext : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf o)
      (Tools.ShippingDesignSV.weS o) o.body = true)
    (hwidths : (Tools.ShippingSeqSVSoundness.seqNames o.body).all
      (fun x => declWidth o x == Tools.ShippingDesignSV.weS o x) = true)
    (hlinked : Tools.ShippingHierOpen.linkedWF C o.body = true)
    (hnames : (Tools.ShippingHierState.instNames o.body).Nodup)
    (hself : Tools.ShippingHierPremisesBase.noSelfRead C o.body = true)
    (hports : Tools.ShippingDesignSV.portsMatchB C o = true)
    (hresolve : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → (C mn).isSome = true)
    (hkids : Tools.ShippingDesignSV.kidsPass C Tools.ShippingDesignSV.leafCheck o.body = true) :
    Tools.ShippingDesignSV.designCheck C 0 o = true := by
  simp only [Tools.ShippingDesignSV.designCheck, Tools.ShippingDesignSV.textCheckI,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hkinds, htext⟩, hwidths⟩, hlinked⟩, hnames⟩, hself⟩, hports⟩,
    List.all_eq_true.mpr fun st hst => by
      cases st with
      | inst mn iname conns => exact hresolve mn iname conns hst
      | _ => rfl⟩, hkids⟩

end Tools.ShippingChecksDepth
