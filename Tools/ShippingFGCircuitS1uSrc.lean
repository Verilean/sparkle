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
open Tools.ShippingUnifiedSource (eval)

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

/-! # S1u (part B): the generated source of a package with calls, from a link to the declaration

`src_eq_of_states` (the leaf case) has `ExtStage … 0 = id`, so the loop body does not read the state through the call streams. With calls the body's writes at `t` read the callee streams at `t`, which read the state at the cycles `≤ t`: the loop
recurrence is `loop_state_causal`, and the causality of the call streams is `extCausal_of_genSem` (from `CalleesCausal`). The link `hlink` is what the declaration side must supply: every state signal that starts at `inits` and follows the generated
recurrence over the generated call streams has the declaration's observation at the outputs. -/
section Rec
variable {ι : Type} {dom : ι → DomainConfig}
open Tools.ShippingFGCircuitSrc (list_ext_of_map_eval)

theorem genSemGen_src_eq_of_link (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : CalleesCausal Q g.d) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (obs : List (Nat → Nat))
    (hlink : ∀ S : Signal (dom i) (HList (tys g.d.ss)), S.val 0 = g.inits →
      (∀ t, S.val (t + 1) = evalTerms
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)).v (g.d.vpos j) w) g.d.nexts) →
      ∀ t, obs.map (fun f => f t) = g.d.outs.map fun o => enc o.1 (eval
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)).v (g.d.vpos j) w) o.2)) :
    (genSemGen Q X g).src i bools bits = obs := by
  letI : Inhabited (HList (tys g.d.ss)) := ⟨g.inits⟩
  let eb := extBOf Q g
  let ev := extOf Q g
  let Sl : Signal (dom i) (HList (tys g.d.ss)) :=
    @stateLoop (dom i) _ _ ⟨g.inits⟩ g.inits (refBodyE g eb ev i bools bits)
  have hW : ∀ (l l' : Signal (dom i) (HList (tys g.d.ss))) (t : Nat), (∀ c, c ≤ t → l.val c = l'.val c) →
      valsAt (tys g.d.ss)
        (refBodyE g eb ev i bools bits (mkRegList l (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) l)).snd t =
      valsAt (tys g.d.ss)
        (refBodyE g eb ev i bools bits (mkRegList l' (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) l')).snd t := by
    intro l l' t h
    rw [genSemGenE_writes X g eb ev i bools bits l t, genSemGenE_writes X g eb ev i bools bits l' t]
    obtain ⟨hv, hb⟩ := extCausal_of_genSem Q g hQ i bools bits l l' t h
    have key := Tools.ShippingMachineCausal.typedVal_congrB g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits l) (eb i bools bits l')
      (ev i bools bits l) (ev i bools bits l') t (l.val t) hb hv
    rw [key, h t (Nat.le_refl t)]
  obtain ⟨hS0, hSs⟩ := Tools.ShippingMachineFuse.loop_state_causal (dom := dom i) (tys g.d.ss) g.inits
    (fun live => (refBodyE g eb ev i bools bits (mkRegList live (tys g.d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys g.d.ss) live)).snd) hW
  have hrec : ∀ t, Sl.val (t + 1) = evalTerms
      (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits Sl) (ev i bools bits Sl) t (Sl.val t)).b (g.d.bpos j))
      (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits Sl) (ev i bools bits Sl) t (Sl.val t)).v (g.d.vpos j) w) g.d.nexts := by
    intro t
    exact (hSs t).trans (genSemGenE_writes X g eb ev i bools bits Sl t)
  apply list_ext_of_map_eval
  intro t
  show (refBodyE g eb ev i bools bits (mkRegList Sl (tys g.d.ss) (fun s => s) (fun f => f))
      (mkHolds (tys g.d.ss) Sl)).fst.map (fun f => f t) = _
  rw [genSemGenE_result X g eb ev i bools bits Sl t]
  exact (hlink Sl hS0 hrec t).symm

end Rec

end Tools.ShippingFGCircuitS1uSrc
