import Tools.ShippingChecksDepth
import Tools.ShippingGuardsSound

/-! # `outsCheck` of the printed module under the statement-kind GATE (isolated branch `fix/opt-fallback`)

`Tools.ShippingChecksDepth.outsCheck_opt_all` asks `hierBinds b = true`. It
uses it for ONE thing: the printed module has the full entry's instance
statements (`checkedOptimize_inst_iff`). On this branch `checkedOptimize`
returns the input module when the gate holds and the check does not bind
(`Tools.ShippingGuardsSound.checkedOptimize_not_binding`), so that fact
holds under the gate alone:

* `checkedOptimize_inst_iff_gate`: under `hierGate b`, the printed module's
  instance statements are `b`'s (binding: `checkedOptimize_inst_iff`; not
  binding: the printed module IS `b`);
* `outsCheck_opt_all_gate`: `outsCheck_opt_all` with `hierGate b` in place
  of `hierBinds b` (its proof, copied, on the gate version of the fact).

Pure; nothing about runs.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksDepthGate
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Semantics
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (hierBinds)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingChecksDerived Tools.ShippingChecksDerived2
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingDesignWith Tools.ShippingDesignWithG

/-- **The printed module has the full entry's instance statements**, under
the statement-kind gate alone. -/
theorem checkedOptimize_inst_iff_gate {b : Sparkle.IR.AST.Module}
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) :
    Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (checkedOptimize b).body ↔
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ b.body := by
  by_cases hb : hierBinds b = true
  · exact Tools.ShippingChecksDerived2.checkedOptimize_inst_iff hb mn iname conns
  · have hb0 : hierBinds b = false := by simpa using hb
    have e : checkedOptimize b = b :=
      Tools.ShippingGuardsSound.checkedOptimize_not_binding hg hb0
    exact (congrArg (fun m : Sparkle.IR.AST.Module =>
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ m.body) e).to_iff

/-- **`outsCheck` of the printed module at every depth**, under the gate. -/
theorem outsCheck_opt_all_gate {b : Sparkle.IR.AST.Module} {ms : List Sparkle.IR.AST.Module}
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hres : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName ms mn = some mc)
    (hA : ∀ g ∈ ms, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hR : ∀ g ∈ ms, ∀ mn iname conns, Stmt.inst mn iname conns ∈ g.body →
      ∃ mc, moduleByName ms mn = some mc) :
    ∀ n : Nat, Tools.ShippingDesignSVBack.outsCheck (childMap ms) n (checkedOptimize b) = true
  | 0 => outsCheck0_of_insts fun mn iname conns hm => by
    obtain ⟨mc, hmc⟩ := hres mn iname conns ((checkedOptimize_inst_iff_gate hg mn iname conns).mp hm)
    have hmem := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
    exact ⟨mc, _, congrArg (Option.map fun c => (c, declWidth c)) hmc,
      outsLeaf_of_assigned (Tools.ShippingDesignSVBack.outsAssigned_sound (hA mc hmem))⟩
  | n + 1 => kidsPass_of_insts fun mn iname conns hm => by
    obtain ⟨mc, hmc⟩ := hres mn iname conns ((checkedOptimize_inst_iff_gate hg mn iname conns).mp hm)
    have hmem := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
    exact ⟨mc, _, congrArg (Option.map fun c => (c, declWidth c)) hmc,
      Tools.ShippingChecksDepth.and_true_intro (hA mc hmem)
        (Tools.ShippingChecksDepth.outsCheck_design hA hR n mc hmem)⟩

end Tools.ShippingChecksDepthGate
