import Tools.ShippingGen5ReaderTraceArms
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceChain, exit 0, 724 jobs) on the tree of a2005315 (source content identical; this header is comment-only). Written against freeze rev4 `scripts/gen5/DG_READERTRACE_FREEZE_REV4.md` (approved at bc6b1e12). Clean issue-linked build: pending (coder). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R3b: the two non-`letE` arms of `chainStep` (`pure'`, `bind`/`next`)

Statements are those of `DG_READERTRACE_FREEZE_REV4.md` §1. Conditional (intermediate) result: `chain_basic_trace` holds under
`hT : TraceGood senv nDecl (readF senv n)` (the fuel-`n` table) and `hv` (a successful run).
Not supplied: `chainStep` `letE` arm, `convStep` `app` / `letE` arms, the other bodies, `TraceGood senv nDecl (readF senv n)` as a whole,
U-R2, `PhFacts`, `ShapeInputs`, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

def ChainBasic : Lean.Expr → Prop
  | .letE _ _ _ _ _ => False
  | _ => True

theorem envPh_cons_unit {nDecl : Nat} {st : MachRead} {env : List MachVal}
    (h : EnvPh nDecl st env) : EnvPh nDecl st (MachVal.unit :: env) := by
  refine ⟨fun v hv => ?_, fun b n hbn => ?_⟩
  · rcases List.mem_cons.mp hv with hv | hv
    · cases hv
    · exact h.1 v hv
  · rcases List.mem_cons.mp hbn with hv | hv
    · cases hv
    · exact h.2 b n hv

theorem chain_basic_trace (senv : StructEnv) (nDecl : Nat) (n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hb : ChainBasic e)
    (hpre : TracePre senv nDecl (Call.chain env e st))
    (v : (Call.chain env e st).Res)
    (hv : (chainStep senv env e st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.chain env e st) v) ∧
    PhPost senv nDecl (Call.chain env e st) v := by
  obtain ⟨⟨hst, hE, hl⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  have key : SatP (readF senv n)
      (fun p : List (Nat × Lean.Expr) × Lean.Expr × MachRead => FReachC nDecl st p.2.2 ∧ ChainPh senv nDecl p)
      (chainStep senv env e st) := by
    revert hb hnp hbl hl
    unfold chainStep
    split
    · rename_i v0
      intro _ _ hnp hbl
      have hnv : NoPh v0 = true := by simp [NoPh] at hnp; exact hnp.2
      have hbv : BvarLt (0 + env.length + nDecl) v0 = true := by
        simp only [Nat.zero_add]
        simp [BvarLt] at hbl; exact hbl.2
      refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 v0 st) p)
        (fun p hp => hT (Call.conv env 0 v0 st)
          ⟨⟨hst, hE, noPh_letOk 0 v0 hnv⟩, ⟨hTr, hEp, hnv, hbv⟩⟩ p hp) ?_
      rintro ⟨v', s1⟩ hQ
      obtain ⟨_, hR, hX⟩ := hQ
      refine satp_okO ⟨hR, hX.1, ?_, hX.2.1, hX.2.2⟩
      intro w hw
      exact absurd hw (by simp)
    · rename_i _ _ _ _ _ _ _ _ _ _ _ _ _ hh rhs _ _ rest _
      intro _ _ hnp hbl
      have hnp' : NoPh rhs = true ∧ NoPh rest = true := by
        simp [NoPh] at hnp; exact ⟨hnp.1.2.2, hnp.2.2⟩
      have hbl' : BvarLt (env.length + nDecl) rhs = true ∧ BvarLt (env.length + nDecl + 1) rest = true := by
        simp [BvarLt] at hbl; exact ⟨hbl.1.2.2, hbl.2.2⟩
      have hbr : BvarLt (0 + env.length + nDecl) rhs = true := by
        simp only [Nat.zero_add]; exact hbl'.1
      refine satp_bind ?_
      intro r hr
      have hr' : ∀ a b, r = some (a, b) →
          TracePost senv nDecl (Call.conv env 0 rhs st) (a, b) := by
        intro a b he
        subst he
        exact hT (Call.conv env 0 rhs st)
          ⟨⟨hst, hE, noPh_letOk 0 rhs hnp'.1⟩, ⟨hTr, hEp, hnp'.1, hbr⟩⟩ (a, b) hr
      revert hr'
      split
      · rename_i i rhs' s1 hmatch
        intro hr'
        obtain ⟨hP1, hR1, hX1⟩ := hr' _ _ rfl
        have hAdv : Adv st s1 := hP1.1
        by_cases hg : i < s1.kinds.size
        · rw [if_pos hg]
          have hbl2 : BvarLt ((MachVal.unit :: env).length + nDecl) rest = true := by
            have : (MachVal.unit :: env).length + nDecl = env.length + nDecl + 1 := by
              simp [List.length_cons]; omega
            rw [this]; exact hbl'.2
          refine satp_bindO (Q := fun p : List (Nat × Lean.Expr) × Lean.Expr × MachRead =>
              TracePost senv nDecl (Call.chain (MachVal.unit :: env) rest s1) p)
            (fun p hp => hT (Call.chain (MachVal.unit :: env) rest s1)
              ⟨⟨hAdv.1, envOk_cons (envOk_mono hAdv.2 hE) (fun w hw => by cases hw),
                noPh_letOk 0 rest hnp'.2⟩,
               ⟨hX1.1, envPh_cons_unit (envPh_mono hEp hR1), hnp'.2, hbl2⟩⟩ p hp) ?_
          rintro ⟨ws, v2, s2⟩ hQ2
          obtain ⟨_, hR2, hY⟩ := hQ2
          obtain ⟨hl2, hI2, hK2⟩ := reachC_sizes_mono hR2
          refine satp_okO ⟨reachC_trans hR1 hR2, hY.1, ?_, hY.2.2.1, hY.2.2.2⟩
          intro w hw
          rcases List.mem_cons.mp hw with hw | hw
          · subst hw
            exact ⟨Nat.lt_of_lt_of_le hg hK2, inRange_mono hX1.2.1 hI2 hK2 hl2⟩
          · exact hY.2.1 w hw
        · rw [if_neg hg]
          exact satp_failO
      · intro _
        exact satp_failO
    · intro hb
      exact hb.elim
    · intro _ _ _ _
      exact satp_failO
  exact key v hv

end Tools.ShippingGen5ReaderTrace
