import Tools.ShippingGen2Defs
import Tools.ShippingGen2TopContract

set_option autoImplicit false

/-! # S5 D1: where `TopShips` is vacuous (scripts/gen2/S5_SLOTLESS_FREEZE.md §2.4, D1)

Built: g2s5-f7e42988 (clean snapshot, exit 0, standard axioms).

This file documents the PRE-R-G `TopShips` contract. After U-TOP-DEF (Defs switched to R-G) its statements are about the frozen
copy `TopShipsOld` (Tools/ShippingGen2TopContract.lean; theorems renamed `topShipsOld_iff_inner`, `topShipsOld_iff_outer_of_noClk`).
`TopShips` below in the prose means the OLD text; Defs `TopShips` is now the R-G contract and is NOT vacuous for a clock-free
module (its clk premise is guarded on membership).

`TopShips` (Tools/ShippingGen2Defs.lean:273-295) has two parts:
- the OUTER existence: `∃ ids, ids.Nodup ∧ ids.length = … ∧ ∃ cache regs, regs.Nodup ∧ regs.length = …`;
- the INNER execution guarantee (`TopShipsInner` below, a verbatim copy of Defs:278-295): for every
  `i bools bits T ins st0 mems kids`, the premises (source inputs, register seeding, `ins t "rst" = 0`,
  `∀ t st, seedIn b ins t st "clk" = 0`, slot inits, `ResetNk`, input/state ranges) imply a run `envsO`.

When `"clk" ∉ b.inputs.map (·.name)`, the clock premise (Defs:283) is refutable (`seedIn` reads the state at
`"clk"`, and `st := fun _ => 1` gives 1), so the INNER guarantee holds for EVERY `ids`/`cache`/`regs`
(`topShipsInner_of_noClk`). Hence for such `b`, `TopShips` is EQUIVALENT to the OUTER existence alone
(`topShipsOld_iff_outer_of_noClk`): it says nothing about any run. The outer existence (`ids.Nodup`, the lengths) is
NOT vacuous and is not claimed or discharged here.

This file is a kernel statement of the vacuity; it is not non-vacuity evidence for anything. -/
namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain

variable {ι : Type} {dom : ι → DomainConfig}

/-- **The clock binder is refutable without a clock input.** `seedIn` reads the state at `"clk"`. -/
theorem not_seedIn_clk_zero {b : Sparkle.IR.AST.Module} (ins : Nat → String → Nat)
    (h : "clk" ∉ b.inputs.map (·.name)) : ¬ (∀ t st, seedIn b ins t st "clk" = 0) := by
  intro hz
  have h1 := hz 0 (fun _ => 1)
  simp [seedIn, List.contains_eq_mem, h] at h1

/-- The INNER execution guarantee of `TopShips` for given `ids`/`cache`/`regs`: Defs:278-295 verbatim. -/
def TopShipsInner (p : Pkg ι dom) (n : Nat) (declName : Name) (b raw : Sparkle.IR.AST.Module) (D : Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String) : Prop :=
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- `TopShipsOld` = OUTER existence ∧ INNER guarantee (definitional; checks that `TopShipsInner` is the verbatim body). -/
theorem topShipsOld_iff_inner (p : Pkg ι dom) (n : Nat) (declName : Name) (b raw : Sparkle.IR.AST.Module)
    (D : Design) :
    TopShipsOld p n declName b raw D ↔
      ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
      ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        regs.Nodup ∧ regs.length = p.d.ss.length ∧ TopShipsInner p n declName b raw D ids cache regs :=
  Iff.rfl

/-- **The INNER guarantee is vacuous without a clock input**: it holds for every `ids`, `cache`, `regs`. -/
theorem topShipsInner_of_noClk (p : Pkg ι dom) (n : Nat) (declName : Name) (b raw : Sparkle.IR.AST.Module)
    (D : Design) (h : "clk" ∉ b.inputs.map (·.name))
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String) :
    TopShipsInner p n declName b raw D ids cache regs := by
  unfold TopShipsInner
  intro i bools bits T ins st0 mems kids _ _ _ hclk
  exact absurd hclk (not_seedIn_clk_zero ins h)

/-- **Corollary (D1).** Without a clock input, `TopShipsOld` is exactly its OUTER existence (`ids.Nodup`, the
lengths): the run part carries no information. The OUTER part is not vacuous and is not claimed here. -/
theorem topShipsOld_iff_outer_of_noClk (p : Pkg ι dom) (n : Nat) (declName : Name) (b raw : Sparkle.IR.AST.Module)
    (D : Design) (h : "clk" ∉ b.inputs.map (·.name)) :
    TopShipsOld p n declName b raw D ↔
      ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
      ∃ (_cache : IO.Ref (ExprStructMap String)) (regs : List String),
        regs.Nodup ∧ regs.length = p.d.ss.length := by
  rw [topShipsOld_iff_inner]
  constructor
  · rintro ⟨ids, hnd, hlen, cache, regs, hrnd, hrlen, _⟩
    exact ⟨ids, hnd, hlen, cache, regs, hrnd, hrlen⟩
  · rintro ⟨ids, hnd, hlen, cache, regs, hrnd, hrlen⟩
    exact ⟨ids, hnd, hlen, cache, regs, hrnd, hrlen, topShipsInner_of_noClk p n declName b raw D h ids cache regs⟩

end Tools.ShippingGen2
