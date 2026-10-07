import Tools.ShippingHierState
import Tools.ShippingMemComboSoundness
import Sparkle.Compiler.MachMemory

/-! # A memory child inside the stateful linked run

The machine route reads `Signal.memoryComboRead wa wd we ra` as an instance
of the memory-only child `memModule true aw dw` (Sparkle.Compiler.MachMemory).
Inside the stateful linked run (`runModuleT_of_childRuns`) an instance's
premise is the child's own run, fed with the parent's values on its input
wires. For a memory child that run is `memComboRun`: if the parent's values
on the four operand wires are those of four Signals, and on the output wire
the source read, the child's run shows the parent's values on its output. -/
namespace Tools.ShippingHierMem
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierState
open Tools.ShippingMemComboSoundness

theorem connEnvS_at {conns : List (String × Expr)} {env : Env} {cst : String → Nat}
    {k w : String} (h : conns.lookup k = some (.ref w)) : connEnvS conns env cst k = env w := by
  simp [connEnvS, h]

/-- The combinational-read memory child's body is the canonical one. -/
theorem memModule_body (aw dw : Nat) :
    (Sparkle.Compiler.MachMemory.memModule true aw dw).1.body =
      memBodyC "mem" "clk" "wa" "wd" "we" "ra" "out_rdata" aw dw := rfl

/-- **A memory child's own run inside the parent.** Fed at every cycle (seed
index `t`, time `T - 1 - t`) with the parent's values `P t` on its four
operand wires — the values of the Signals `A`, `Dd`, `E`, `R` — the memory
child's run shows on `out` the parent's value on the output wire, when that
is the source read `Signal.memoryComboRead A Dd E R`. -/
theorem memChild_run {D : DomainConfig} {aw dw : Nat} (we : WEnv) (P : Nat → Env) (T : Nat)
    (conns : List (String × Expr)) (waW wdW weW raW outW : String)
    (hwa : (inConns (Sparkle.Compiler.MachMemory.memModule true aw dw).1.outputs conns).lookup "wa" =
      some (.ref waW))
    (hwd : (inConns (Sparkle.Compiler.MachMemory.memModule true aw dw).1.outputs conns).lookup "wd" =
      some (.ref wdW))
    (hwe : (inConns (Sparkle.Compiler.MachMemory.memModule true aw dw).1.outputs conns).lookup "we" =
      some (.ref weW))
    (hra : (inConns (Sparkle.Compiler.MachMemory.memModule true aw dw).1.outputs conns).lookup "ra" =
      some (.ref raW))
    (A : Signal D (BitVec aw)) (Dd : Signal D (BitVec dw)) (E : Signal D Bool)
    (R : Signal D (BitVec aw))
    (hA : ∀ t, t < T → P t waW = (A.val (T - 1 - t)).toNat)
    (hD : ∀ t, t < T → P t wdW = (Dd.val (T - 1 - t)).toNat)
    (hE : ∀ t, t < T → P t weW = (if E.val (T - 1 - t) then 1 else 0))
    (hR : ∀ t, t < T → P t raW = (R.val (T - 1 - t)).toNat)
    (hO : ∀ t, t < T → P t outW = ((Signal.memoryComboRead A Dd E R).val (T - 1 - t)).toNat)
    (cst0 : String → Nat) (mems0 : MEnv) (hm0 : ∀ n i, mems0 n i = 0) :
    ∃ cenvs, runModule we (Sparkle.Compiler.MachMemory.memModule true aw dw).1.body
        (fun t cst => connEnvS (inConns (Sparkle.Compiler.MachMemory.memModule true aw dw).1.outputs
          conns) (P t) cst) T cst0 mems0 = some cenvs ∧
      ∀ j, j < T → (cenvs[j]?).map (· "out") = some (P (T - 1 - j) outW) := by
  have hzero : mems0 = srcArr "mem" mems0 A Dd E 0 := by
    funext n i
    unfold srcArr
    split
    · rename_i h; rw [Signal.memState_zero]; simp [hm0]
    · rfl
  rw [memModule_body]
  obtain ⟨envs, hrun, hlen, hobs⟩ := memComboRun (we := we) (nm := "mem") (clk := "clk")
    (wa := "wa") (wd := "wd") (wen := "we") (ra := "ra") (rd := "out_rdata") (aw := aw) (dw := dw)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) A Dd E R T
    (fun t cst => connEnvS (inConns (Sparkle.Compiler.MachMemory.memModule true aw dw).1.outputs
      conns) (P t) cst) mems0
    (fun t stv ht => ⟨by rw [connEnvS_at hwa]; exact hA t ht, by rw [connEnvS_at hwd]; exact hD t ht,
      by rw [connEnvS_at hwe]; exact hE t ht, by rw [connEnvS_at hra]; exact hR t ht⟩)
    T (Nat.le_refl T) cst0
  rw [Nat.sub_self, ← hzero] at hrun
  refine ⟨envs, hrun, fun j hj => ?_⟩
  have hj' : j < envs.length := by rw [hlen]; exact hj
  rw [List.getElem?_eq_getElem hj', Option.map_some, hobs j hj', Nat.sub_self, Nat.zero_add,
    hO (T - 1 - j) (by omega), show T - 1 - (T - 1 - j) = j by omega]

end Tools.ShippingHierMem
