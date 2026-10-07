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

/-- A run reads its seeding only below its length. -/
theorem runModule_seed_congrT (we : WEnv) (body : List Stmt) :
    ∀ (k : Nat) (s1 s2 : Nat → (String → Nat) → Env),
    (∀ td, td < k → s1 td = s2 td) →
    ∀ (st : String → Nat) (mems : MEnv),
    runModule we body s1 k st mems = runModule we body s2 k st mems
  | 0, _, _, _, _, _ => rfl
  | k + 1, s1, s2, h, st, mems => by
    simp only [runModule, Option.bind_eq_bind]
    rw [h k (by omega)]
    congr 1
    funext r
    rw [runModule_seed_congrT we body k s1 s2 (fun td htd => h td (by omega))]

/-- The synchronous-read memory child's body is the canonical one. -/
theorem memModule_body_sync (aw dw : Nat) :
    (Sparkle.Compiler.MachMemory.memModule false aw dw).1.body =
      Tools.ShippingMemorySoundness.memBody "mem" "clk" "wa" "wd" "we" "ra" "out_rdata" aw dw := rfl

/-- **A synchronous-read memory child's own run inside the parent** (the
twin of `memChild_run`): from a zero latch and array, the child's run shows
on `out` the parent's value on the output wire, when that is the source
read `Signal.memory A Dd E R`. -/
theorem memSyncChild_run {D : DomainConfig} {aw dw : Nat} (we : WEnv) (P : Nat → Env) (T : Nat)
    (conns : List (String × Expr)) (waW wdW weW raW outW : String)
    (hwa : (inConns (Sparkle.Compiler.MachMemory.memModule false aw dw).1.outputs conns).lookup "wa" =
      some (.ref waW))
    (hwd : (inConns (Sparkle.Compiler.MachMemory.memModule false aw dw).1.outputs conns).lookup "wd" =
      some (.ref wdW))
    (hwe : (inConns (Sparkle.Compiler.MachMemory.memModule false aw dw).1.outputs conns).lookup "we" =
      some (.ref weW))
    (hra : (inConns (Sparkle.Compiler.MachMemory.memModule false aw dw).1.outputs conns).lookup "ra" =
      some (.ref raW))
    (hrd : (inConns (Sparkle.Compiler.MachMemory.memModule false aw dw).1.outputs conns).lookup
      "out_rdata" = none)
    (A : Signal D (BitVec aw)) (Dd : Signal D (BitVec dw)) (E : Signal D Bool)
    (R : Signal D (BitVec aw))
    (hA : ∀ t, t < T → P t waW = (A.val (T - 1 - t)).toNat)
    (hD : ∀ t, t < T → P t wdW = (Dd.val (T - 1 - t)).toNat)
    (hE : ∀ t, t < T → P t weW = (if E.val (T - 1 - t) then 1 else 0))
    (hR : ∀ t, t < T → P t raW = (R.val (T - 1 - t)).toNat)
    (hO : ∀ t, t < T → P t outW = ((Signal.memory A Dd E R).val (T - 1 - t)).toNat)
    (cst0 : String → Nat) (hst0 : cst0 "out_rdata" = 0) (mems0 : MEnv) (hm0 : ∀ n i, mems0 n i = 0) :
    ∃ cenvs, runModule we (Sparkle.Compiler.MachMemory.memModule false aw dw).1.body
        (fun t cst => connEnvS (inConns (Sparkle.Compiler.MachMemory.memModule false aw dw).1.outputs
          conns) (P t) cst) T cst0 mems0 = some cenvs ∧
      ∀ j, j < T → (cenvs[j]?).map (· "out") = some (P (T - 1 - j) outW) := by
  let C := inConns (Sparkle.Compiler.MachMemory.memModule false aw dw).1.outputs conns
  let seed : Nat → (String → Nat) → Env := fun t cst => connEnvS C (P t) cst
  let seed' : Nat → (String → Nat) → Env := fun t cst n =>
    if t < T then seed t cst n
    else if n = "wa" then (A.val (T - 1 - t)).toNat
    else if n = "wd" then (Dd.val (T - 1 - t)).toNat
    else if n = "we" then (if E.val (T - 1 - t) then 1 else 0)
    else if n = "ra" then (R.val (T - 1 - t)).toNat
    else cst n
  have hcongr : runModule we (Sparkle.Compiler.MachMemory.memModule false aw dw).1.body seed T cst0
      mems0 = runModule we (Sparkle.Compiler.MachMemory.memModule false aw dw).1.body seed' T cst0
      mems0 :=
    runModule_seed_congrT we _ T seed seed' (fun t ht => by
      funext cst n; simp only [seed', if_pos ht]) cst0 mems0
  rw [memModule_body_sync] at hcongr ⊢
  obtain ⟨envs, hrun, hlen, hobs⟩ := Tools.ShippingMemorySoundness.memory_run_val (we := we)
    (nm := "mem") (clk := "clk") (wa := "wa") (wd := "wd") (wen := "we") (ra := "ra")
    (rd := "out_rdata") (by decide) (by decide) (by decide) (by decide) (by decide) A Dd E R
    T seed' cst0 mems0
    (fun t stv => by
      by_cases ht : t < T
      · simp only [seed', if_pos ht, seed]
        exact ⟨by simp [connEnvS, C, hrd], by rw [connEnvS_at hwa]; exact hA t ht,
          by rw [connEnvS_at hwd]; exact hD t ht, by rw [connEnvS_at hwe]; exact hE t ht,
          by rw [connEnvS_at hra]; exact hR t ht⟩
      · simp [seed', ht])
    hst0 hm0
  refine ⟨envs, hcongr ▸ hrun, fun j hj => ?_⟩
  have hj' : j < envs.length := by rw [hlen]; exact hj
  rw [List.getElem?_eq_getElem hj', Option.map_some, hobs j hj',
    hO (T - 1 - j) (by omega), show T - 1 - (T - 1 - j) = j by omega]

end Tools.ShippingHierMem
