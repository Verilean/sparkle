import Tools.ShippingFGCircuitS1kPkg
import Tools.ShippingGen5SemExtPkg
import Tools.ShippingGen5SemSrcCausal
import Tools.ShippingFGCircuitRoots4
import Tools.ShippingMachineFuse
set_option autoImplicit false
-- FG circuit pilot S1u: `hsrc` for the non-leaf root `synth_hftPcieOutByte`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §25.

/-! # S1u (part A): the generic `ExtStage` induction for a finite list of callees

`ExtStage Q g i bools bits S k` runs the first `k` calls of `g.d` over the callee table `Q`. `calleeOut` reads a callee package only through `q.d`, `q.kD` and `q.src`. So two tables that agree on those three
fields at every callee name give the same `ExtStage` at every stage (`ExtStage_agree_tables`, an induction on the stage). The package that `genGP` returns for the callee can therefore be replaced by the
callee's declaration-level observation, once the callee's own `src` is known. -/
namespace Tools.ShippingFGCircuitS1uSrc
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingGen5Sem Tools.ShippingGen2

section Generic
variable {ι : Type} {dom : ι → DomainConfig}

/-- two callee packages agree on everything `calleeOut` reads -/
def CalleeAgree (q q' : SemPkg ι dom) : Prop := q.d = q'.d ∧ q.kD = q'.kD ∧ q.src = q'.src

/-- two callee tables agree, name by name, up to `CalleeAgree` -/
def TablesAgree (Q Q' : Name → Option (SemPkg ι dom)) : Prop :=
  ∀ c, (Q c = none ∧ Q' c = none) ∨ ∃ q q', Q c = some q ∧ Q' c = some q' ∧ CalleeAgree q q'

theorem calleeOut_agree_tables (Q Q' : Name → Option (SemPkg ι dom)) (hQ : TablesAgree Q Q') (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat) :
    calleeOut Q g i S bs vs k = calleeOut Q' g i S bs vs k := by
  unfold calleeOut
  cases hk : g.d.shape.insts[k]? with
  | none => rfl
  | some e =>
    obtain ⟨c, a, κ⟩ := e
    dsimp only
    rcases hQ c with ⟨h1, h2⟩ | ⟨q, q', h1, h2, hd, hkd, hs⟩
    · rw [h1, h2]
    · rw [h1, h2]
      dsimp only
      have hsel : selIdx g.d q k = selIdx g.d q' k := by
        unfold selIdx; rw [hd]
      rw [hsel, hd, hkd, hs]

theorem callOut_agree_tables (Q Q' : Name → Option (SemPkg ι dom)) (hQ : TablesAgree Q Q') (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))) :
    callOut Q g i S k st = callOut Q' g i S k st := by
  unfold callOut
  simp only [calleeOut_agree_tables Q Q' hQ g i S]

/-- **the `ExtStage` induction** (generic in the callee list): the stages over two agreeing tables are equal -/
theorem ExtStage_agree_tables (Q Q' : Name → Option (SemPkg ι dom)) (hQ : TablesAgree Q Q') (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) :
    ExtStage Q g i bools bits S n = ExtStage Q' g i bools bits S n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ExtStage_succ, ExtStage_succ, ih, callOut_agree_tables Q Q' hQ]

theorem genSemGen_agree_tables (Q Q' : Name → Option (SemPkg ι dom)) (hQ : TablesAgree Q Q') (X : Name) (g : GenIn) :
    genSemGen Q X g = genSemGen Q' X g := by
  have hb : extBOf Q g = extBOf Q' g := by
    funext i bools bits S; unfold extBOf; rw [ExtStage_agree_tables Q Q' hQ]
  have hv : extOf Q g = extOf Q' g := by
    funext i bools bits S; unfold extOf; rw [ExtStage_agree_tables Q Q' hQ]
  unfold genSemGen; rw [hb, hv]

end Generic

end Tools.ShippingFGCircuitS1uSrc
