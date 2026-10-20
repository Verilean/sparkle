import Tools.ShippingChecksDerived2

/-! # `shipsHierCheck`, conjunct by conjunct (G1)

`shipsHierCheck C b = hierCheck C b && instOutWidthsOk C (declWidth b) b.body`
(`Tools/ShippingHierPremisesBase.lean`), eight conjuncts on the full entry's
module `b` and the printed module `checkedOptimize b`. Read from the
definitions; class 1 = a fact of the run (core run, closing, real children),
class 2 = a fact about a post-pass, class 3 = a check on emitted text.

| # | Conjunct | Class | Status |
|---|---|---|---|
| 1 | `hierBinds b` — `hierGate b`, and `refineCheck flat flat` for the extracted interface `flat = openFlat b (openIns b) (openOuts b)` | 1, but of a different kind: the right-hand sides of `b` are in the normal forms `refineCheck` knows | NOT derived. `hierGate` (an instance, only assignments / registers / instances) follows from the run's statement kinds; `refineCheck flat flat` is the gate the register machines discharge by `machine_ships_wired`'s route — no instance-parent version exists |
| 2 | `linkedWF C (checkedOptimize b).body` | 2 | NOT derivable on this line: `hierRefineCheck` (membership of instance statements, connection agreement) does not give the ORDER of the optimized body's assignments relative to its instances (P2, docs/parallel/G1-checks.md §6) |
| 3 | `(instNames b.body).Nodup` | 1 | NOT derived: no lemma states it of a run's module (the wiring's instance statements are `inst{k}_…` with distinct `k`; the proof needs the instance-name format's injectivity in `k` and the N1 separation of the children's printed names) |
| 4 | `(instNames (checkedOptimize b).body).Nodup` | 2 | on this line NOT derivable (P1); on `fix/merge-guards` it is `checkedOptimize_instNames_nodup` from 3 |
| 5 | `noSelfRead C (checkedOptimize b).body` | 1 after transfer | the transfer to `b.body` is PROVED (`noSelfRead_opt`, instance statements only); `noSelfRead C b.body` of a run is NOT derived (an instance's input connections against its own output wires: the call's arguments are positions of earlier values, its outputs fresh `inst{k}_…` wires) |
| 6 | `outsExtracted C b` — every instance-driven wire is a declared wire of `b`, is not assigned, is not an input | 1 | NOT derived (needs: the instance output wires are declared, and `drivesOf b.body` does not contain them) |
| 7 | `"rst" ∈ b.inputs.map (·.name)` | 1 | NOT derived here; `closeMachine` adds `clk`, `rst` when the layout has a slot, and the cleanup keeps the inputs — two existing facts, not yet put together for a machine with calls |
| 8 | `instOutWidthsOk C (declWidth b) b.body` — each instance output wire's declared width is the child port's | 1 | NOT derived (needs the child's output port TYPES; `ChildIfaceG` / `ChildIfaceD` carry the port names only) |

No conjunct is of class 3. Two (2, 4) are post-pass facts, so on this line
`shipsHierCheck` cannot leave the endpoint; six are run facts, of which this
file proves none from the run.

What IS proved here: the assembly `shipsHierCheck_of` — the check from the
eight facts, with conjunct 5 asked of `b.body` (its transfer inside). It is
the statement a `core_shipsHier_rest` would have with ALL eight still as
hypotheses; it removes no premise. Nothing here makes an endpoint.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksShipsHier
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (hierBinds)
open Tools.ShippingHierOpen Tools.ShippingHierState
open Tools.ShippingHierPremisesBase

/-- **`shipsHierCheck` from its eight conjuncts**, the self-read test asked
of the full entry's module (moved to the printed module by
`noSelfRead_opt`). -/
theorem shipsHierCheck_of {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {b : Sparkle.IR.AST.Module}
    (hb : hierBinds b = true)
    (hwfO : linkedWF C (checkedOptimize b).body = true)
    (hndB : (instNames b.body).Nodup)
    (hndO : (instNames (checkedOptimize b).body).Nodup)
    (hself : noSelfRead C b.body = true)
    (houts : outsExtracted C b = true)
    (hrst : "rst" ∈ b.inputs.map (·.name))
    (hwid : instOutWidthsOk C (declWidth b) b.body = true) :
    shipsHierCheck C b = true := by
  have hselfO : noSelfRead C (checkedOptimize b).body = true :=
    Tools.ShippingChecksDerived2.noSelfRead_opt hb hself
  simp only [shipsHierCheck, hierCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_eq_mem]
  exact ⟨⟨⟨⟨⟨⟨⟨hb, hwfO⟩, hndB⟩, hndO⟩, hselfO⟩, houts⟩, by simpa using hrst⟩, hwid⟩

end Tools.ShippingChecksShipsHier
