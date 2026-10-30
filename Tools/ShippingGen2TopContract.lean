import Tools.ShippingGen2Defs
import Tools.ShippingGen2TopClkIn
set_option autoImplicit false
-- NOT BUILT (no build run yet at this commit). No `sorry`, no `axiom`, no `native_decide`.

/-! # U-TOP-DEF: the old `TopShips` text (history pin) and L1, L2 against the R-G `TopShips` of Defs

scripts/gen2/TOP_CONTRACT_REVISION.md §2 (R-G), §3 (L1-L4), rev1.1, rev2. `Tools.ShippingGen2.TopShips` (Defs) now carries
the guarded premises
`("rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0) → ("clk" ∈ b.inputs.map (·.name) → ∀ t, ins t "clk" = 0)`.

* `TopShipsOld`: the PRE-R-G text (Defs line :290 of 43977202: `(∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0)`),
  every other line verbatim. It is the premise-for-premise statement of `machine_ships_hierC_noHstR` / `machine_ships_hierC_run`
  (consumer 1, unchanged) and the frozen copy for history (TopVacuity, S5Check).
* L1 `topShips_toOld`: `TopShips ⇒ TopShipsOld`, no hypothesis.
* L2 `topShips_ofOld`: `TopShipsOld ⇒ TopShips`, given BOTH `"rst"` and `"clk"` inputs. NOT claimed without the clk membership.
* `topShips_ofOld_wired`: L2 with both memberships read off the run's `MachineWired` (U-TOP-CLKIN, `clk_rst_in_b_of_wired`) for a
  machine with slots; this is what the consumer-1 producers use (memory parent, one-output parents). -/
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
open Tools.ShippingMachineShipsDepth (ResetNk)

/-- **`TopShipsOld`**: `TopShips` before R-G (the unguarded `rst` and `seedIn … "clk"` premises); every other line verbatim. -/
def TopShipsOld {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
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

/-- `seedIn` at an input reads the stream. -/
theorem tc_seedIn_in {m : Sparkle.IR.AST.Module} {ins : Nat → String → Nat} {t : Nat} {st : String → Nat}
    {x : String} (hx : x ∈ m.inputs.map (·.name)) : seedIn m ins t st x = ins t x := by
  have hc : (m.inputs.map (·.name)).contains x = true := List.contains_iff_mem.mpr hx
  show (if (m.inputs.map (·.name)).contains x then ins t x else st x) = ins t x
  rw [if_pos hc]

/-- **L1 (new ⇒ old)**, no hypothesis: the old antecedents give the guarded ones (rst trivially; clk through `seedIn` at an
input). Same witnesses. -/
theorem topShips_toOld {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) :
    TopShips p n declName b raw D → TopShipsOld p n declName b raw D := by
  intro h
  unfold TopShips at h
  unfold TopShipsOld
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hreset hfit hst
  refine H i bools bits T ins st0 mems kids hsrc hpass (fun _ => hrst) ?_ hinit hreset hfit hst
  intro hc t
  have h0 := hclk t (fun _ => 0)
  rw [tc_seedIn_in hc] at h0
  exact h0

/-- **L2 (old ⇒ new)**, given BOTH `"rst"` and `"clk"` inputs. Same witnesses. -/
theorem topShips_ofOld {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design)
    (hr : "rst" ∈ b.inputs.map (·.name)) (hc : "clk" ∈ b.inputs.map (·.name)) :
    TopShipsOld p n declName b raw D → TopShips p n declName b raw D := by
  intro h
  unfold TopShipsOld at h
  unfold TopShips
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrstG hclkG hinit hreset hfit hst
  refine H i bools bits T ins st0 mems kids hsrc hpass (hrstG hr) ?_ hinit hreset hfit hst
  intro t st
  rw [tc_seedIn_in hc]
  exact hclkG hc t

/-- **L2 for a machine with slots** (U-TOP-CLKIN): both memberships from the run's `MachineWired`. -/
theorem topShips_ofOld_wired {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {raw b : Sparkle.IR.AST.Module} {D : Design} {regs lets : List String}
    (wired : MachineWired p.decl p.d.shape ids cache raw D regs lets) (hsl : p.d.shape.layout.slots ≠ [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    TopShipsOld p n p.decl b raw D → TopShips p n p.decl b raw D := by
  obtain ⟨hc, hr⟩ := clk_rst_in_b_of_wired wired hsl hpost
  exact topShips_ofOld p n p.decl b raw D hr hc

end Tools.ShippingGen2
