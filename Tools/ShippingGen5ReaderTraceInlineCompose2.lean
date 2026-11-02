import Tools.ShippingGen5ReaderTraceInlineP1
import Tools.ShippingGen5ReaderTraceAbbrevS1
import Tools.ShippingGen5ReaderTraceDirect2
import Tools.PassPh.Pass
-- NOT BUILT. Integration candidate (conditional): the inline composition with the `PassPh` hypothesis replaced by `pass_ph` (Tools/PassPh/Pass.lean) and its assumptions. Port of Tools/ShippingGen5ReaderTraceInlineCompose.lean to the Except-valued `userInliner` / `userInlinerEWith` (S2); that file does not build on this tree (its `PassPh` and `userInliner.rounds` predate S2) and is left unchanged. No sorry / axiom / native_decide. Hypotheses only: DeclValuePh, RecRulePhU, ReplaceAgrees, Inst1Agrees, HeadBetaAgreesL, BetaNonTargetAgrees, ExprEqvLaws.

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel Tools.Assume.AbbrevExtern Tools.ShippingGen5ReaderTraceAbbrevS1
open Sparkle.Compiler.MachTupleIn Tools.ShippingGen5ReaderTracePack Tools.ShippingReaderFuelShapeR5
open Tools.PassPh

theorem inl_step_ph_pp (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (e : Lean.Expr) (hn : NoPh e = true) (hb : BvarLt 0 e = true) :
    NoPh (userInlStep env e) = true ∧ BvarLt 0 (userInlStep env e) = true :=
  inlineDefs_user_ph env hv 0 e hn hb

theorem rounds_ph_pp (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePhU env) (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL)
    (hbt : BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws) (fuel : Nat) :
    ∀ (k : Nat) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      userInlinerEWith.rounds fuel env k e = .ok r → NoPh r = true ∧ BvarLt 0 r = true := by
  intro k
  induction k with
  | zero =>
    intro e r hn hb h
    simp only [userInlinerEWith.rounds] at h
    cases h; exact ⟨hn, hb⟩
  | succ k ih =>
    intro e r hn hb h
    simp only [userInlinerEWith.rounds, bind, Except.bind] at h
    cases hp : Sparkle.Compiler.MachRecUnfold.passWith fuel env canonicalNatLitValue? (userRecHelper env) e with
    | error m => rw [hp] at h; cases h
    | ok e' =>
      rw [hp] at h
      have hpe := passWith_ph canonicalNatLitValue? env hv hrr hrep hi1 hh hbt hEq fuel (userRecHelper env) e e' hn hb hp
      simp only [] at h
      split at h
      · cases h; exact ⟨hn, hb⟩
      · have h2 := inl_step_ph_pp env hv e' hpe.1 hpe.2
        exact ih _ r h2.1 h2.2 h

theorem abbrev_fold_ph_pp (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hr : ReplaceAgrees) (hb : HeadBetaAgrees0) (x : Lean.Expr) (hn : NoPh x = true) (hbl : BvarLt 0 x = true) :
    NoPh (inlFoldNat (inlAbbrevs env 4 x)) = true ∧ BvarLt 0 (inlFoldNat (inlAbbrevs env 4 x)) = true := by
  have h3 := inlAbbrevs_ph env hv hr hb 4 x hn hbl
  exact inlFoldNat_ph (L := 0) _ h3.1 h3.2

end Tools.ShippingGen5ReaderTrace
