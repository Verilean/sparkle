import Tools.ShippingGen5ReaderTraceCtl
set_option autoImplicit false
-- NOT BUILT yet (U-R3a, written against freeze rev3 `scripts/gen5/DG_READERTRACE_FREEZE_REV3.md`, approved at 730c8fa8). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R3a: atoms / `lam` / `forallE` / `bvar` arms of `convStep`, and the fuel reduction

Statements are those of `DG_READERTRACE_FREEZE_REV3.md` §1. Conditional (intermediate) results:
`readF_traceGood_of_step` has the hypothesis `hstep` (it proves nothing about any arm), and `conv_basic_trace` covers only the
`ConvBasic` constructors, under `hT : TraceGood senv nDecl (readF senv n)` (the fuel-`n` table) and `hv` (a successful run).
Not supplied: `app` / `letE` arms, the other six bodies, `TraceGood senv nDecl (readF senv n)` as a whole, U-R2, `PhFacts`,
`ShapeInputs`, the real run and FG. `F : PureFacts senv` (existing record) is a premise of `readF_traceGood_of_step` only. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

def IsAtom : Lean.Expr → Prop
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lit _ => True
  | _ => False

def ConvBasic : Lean.Expr → Prop
  | .bvar _ => True
  | .lam _ _ _ _ => True
  | .forallE _ _ _ _ => True
  | .mdata _ _ => True
  | .proj _ _ _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lit _ => True
  | .app _ _ => False
  | .letE _ _ _ _ _ => False

theorem inRange_atom {nDecl k : Nat} {st : MachRead} {e : Lean.Expr}
    (ha : IsAtom e) (hn : NoPh e = true) : InRange nDecl st k e := by
  cases e with
  | fvar id =>
    obtain ⟨nm⟩ := id
    have key : ∀ tag, phTag tag = true → ∀ i, ¬ MentionsPh tag i (.fvar ⟨nm⟩) := by
      intro tag htag i hi
      rcases nm with _ | ⟨p, t⟩ | ⟨p, j⟩
      · simp [MentionsPh] at hi
      · simp [MentionsPh] at hi
      · rcases p with _ | ⟨p', t⟩ | ⟨p', t⟩
        · simp [MentionsPh] at hi
        · rcases p' with _ | ⟨_, _⟩ | ⟨_, _⟩
          · simp only [MentionsPh] at hi
            obtain ⟨h1, _⟩ := hi
            subst h1
            simp [NoPh, htag] at hn
          · simp [MentionsPh] at hi
          · simp [MentionsPh] at hi
        · simp [MentionsPh] at hi
    exact ⟨fun i hi => absurd hi (key "_machIn" rfl i), fun i hi => absurd hi (key "_machInst" rfl i),
      fun i hi => absurd hi (key "_machSlot" rfl i), fun i hi => absurd hi (key "_machLet" rfl i)⟩
  | mvar _ => exact inRange_closed (fun _ _ h => (h : False))
  | sort _ => exact inRange_closed (fun _ _ h => (h : False))
  | const _ _ => exact inRange_closed (fun _ _ h => (h : False))
  | lit _ => exact inRange_closed (fun _ _ h => (h : False))
  | bvar _ => exact ha.elim
  | app _ _ => exact ha.elim
  | lam _ _ _ _ => exact ha.elim
  | forallE _ _ _ _ => exact ha.elim
  | letE _ _ _ _ _ => exact ha.elim
  | mdata _ _ => exact ha.elim
  | proj _ _ _ => exact ha.elim

theorem noLoose_atom {d : Nat} {e : Lean.Expr} (ha : IsAtom e) : NoLoose d e := by
  cases e with
  | fvar _ => exact fun _ h => (h : False)
  | mvar _ => exact fun _ h => (h : False)
  | sort _ => exact fun _ h => (h : False)
  | const _ _ => exact fun _ h => (h : False)
  | lit _ => exact fun _ h => (h : False)
  | bvar _ => exact ha.elim
  | app _ _ => exact ha.elim
  | lam _ _ _ _ => exact ha.elim
  | forallE _ _ _ _ => exact ha.elim
  | letE _ _ _ _ _ => exact ha.elim
  | mdata _ _ => exact ha.elim
  | proj _ _ _ => exact ha.elim

theorem inRange_lam {nDecl k : Nat} {st : MachRead} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : InRange nDecl st k t) (hb : InRange nDecl st k b) : InRange nDecl st k (.lam nm t b bi) :=
  ⟨fun i hi => hi.elim (ht.1 i) (hb.1 i), fun i hi => hi.elim (ht.2.1 i) (hb.2.1 i),
   fun i hi => hi.elim (ht.2.2.1 i) (hb.2.2.1 i), fun i hi => hi.elim (ht.2.2.2 i) (hb.2.2.2 i)⟩

theorem inRange_forallE {nDecl k : Nat} {st : MachRead} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : InRange nDecl st k t) (hb : InRange nDecl st k b) : InRange nDecl st k (.forallE nm t b bi) :=
  ⟨fun i hi => hi.elim (ht.1 i) (hb.1 i), fun i hi => hi.elim (ht.2.1 i) (hb.2.1 i),
   fun i hi => hi.elim (ht.2.2.1 i) (hb.2.2.1 i), fun i hi => hi.elim (ht.2.2.2 i) (hb.2.2.2 i)⟩

theorem noLoose_lam {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : NoLoose d t) (hb : NoLoose (d + 1) b) : NoLoose d (.lam nm t b bi) :=
  fun x hx => hx.elim (ht x) (hb x)

theorem noLoose_forallE {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : NoLoose d t) (hb : NoLoose (d + 1) b) : NoLoose d (.forallE nm t b bi) :=
  fun x hx => hx.elim (ht x) (hb x)

theorem conv_basic_trace (senv : StructEnv) (nDecl : Nat) (n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead)
    (hb : ConvBasic e)
    (hpre : TracePre senv nDecl (Call.conv env d e st))
    (v : (Call.conv env d e st).Res)
    (hv : (convStep senv env d e st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d e st) v) ∧
    PhPost senv nDecl (Call.conv env d e st) v := by
  obtain ⟨⟨hst, hE, hl⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  cases e with
  | bvar j =>
    have hv' : convBvar env d j st = some v := by
      simp only [convStep, run_pure, Option.some.injEq] at hv
      exact hv
    obtain ⟨h1, h2, h3⟩ := convBvar_trace hEp hTr.2.2.2.2.1 hbl hv'
    show FReachC nDecl st (v : Lean.Expr × MachRead).2 ∧ ExprPh senv nDecl d (v : Lean.Expr × MachRead)
    show FReachC nDecl st v.2 ∧ TrInv senv nDecl v.2 ∧ InRange nDecl v.2 v.2.lets.size v.1 ∧ NoLoose d v.1
    rw [h1]
    exact ⟨FReachC.refl st, hTr, h2, h3⟩
  | lam nm t b bi =>
    have hnp' : NoPh t = true ∧ NoPh b = true := by simpa [NoPh] using hnp
    have hbl' : BvarLt (d + env.length + nDecl) t = true ∧ BvarLt (d + env.length + nDecl + 1) b = true := by
      simpa [BvarLt] using hbl
    have key : SatP (readF senv n)
        (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl d p)
        (bindO (cConv env d t st) fun (t', st) =>
          bindO (cConv env (d + 1) b st) fun (b', st) => okO (Lean.Expr.lam nm t' b' bi, st)) := by
      refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env d t st) p)
        (fun p hp => hT (Call.conv env d t st)
          ⟨⟨hst, hE, noPh_letOk 0 t hnp'.1⟩, ⟨hTr, hEp, hnp'.1, hbl'.1⟩⟩ p hp) ?_
      rintro ⟨t', s1⟩ hQ1
      obtain ⟨hP1, hR1, hX1⟩ := hQ1
      have hAdv : Adv st s1 := hP1.1
      refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env (d + 1) b s1) p)
        (fun p hp => hT (Call.conv env (d + 1) b s1)
          ⟨⟨hAdv.1, envOk_mono hAdv.2 hE, noPh_letOk 0 b hnp'.2⟩,
           ⟨hX1.1, envPh_mono hEp hR1, hnp'.2, ?_⟩⟩ p hp) ?_
      · have hh : d + 1 + env.length + nDecl = d + env.length + nDecl + 1 := by omega
        rw [hh]
        exact hbl'.2
      rintro ⟨b', s2⟩ hQ2
      obtain ⟨_, hR2, hX2⟩ := hQ2
      obtain ⟨hl2, hI2, hK2⟩ := reachC_sizes_mono hR2
      refine satp_okO ⟨reachC_trans hR1 hR2, hX2.1, ?_, ?_⟩
      · exact inRange_lam (inRange_mono hX1.2.1 hI2 hK2 hl2) hX2.2.1
      · exact noLoose_lam hX1.2.2 hX2.2.2
    exact key v hv
  | forallE nm t b bi =>
    have hnp' : NoPh t = true ∧ NoPh b = true := by simpa [NoPh] using hnp
    have hbl' : BvarLt (d + env.length + nDecl) t = true ∧ BvarLt (d + env.length + nDecl + 1) b = true := by
      simpa [BvarLt] using hbl
    have key : SatP (readF senv n)
        (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl d p)
        (bindO (cConv env d t st) fun (t', st) =>
          bindO (cConv env (d + 1) b st) fun (b', st) => okO (Lean.Expr.forallE nm t' b' bi, st)) := by
      refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env d t st) p)
        (fun p hp => hT (Call.conv env d t st)
          ⟨⟨hst, hE, noPh_letOk 0 t hnp'.1⟩, ⟨hTr, hEp, hnp'.1, hbl'.1⟩⟩ p hp) ?_
      rintro ⟨t', s1⟩ hQ1
      obtain ⟨hP1, hR1, hX1⟩ := hQ1
      have hAdv : Adv st s1 := hP1.1
      refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env (d + 1) b s1) p)
        (fun p hp => hT (Call.conv env (d + 1) b s1)
          ⟨⟨hAdv.1, envOk_mono hAdv.2 hE, noPh_letOk 0 b hnp'.2⟩,
           ⟨hX1.1, envPh_mono hEp hR1, hnp'.2, ?_⟩⟩ p hp) ?_
      · have hh : d + 1 + env.length + nDecl = d + env.length + nDecl + 1 := by omega
        rw [hh]
        exact hbl'.2
      rintro ⟨b', s2⟩ hQ2
      obtain ⟨_, hR2, hX2⟩ := hQ2
      obtain ⟨hl2, hI2, hK2⟩ := reachC_sizes_mono hR2
      refine satp_okO ⟨reachC_trans hR1 hR2, hX2.1, ?_, ?_⟩
      · exact inRange_forallE (inRange_mono hX1.2.1 hI2 hK2 hl2) hX2.2.1
      · exact noLoose_forallE hX1.2.2 hX2.2.2
    exact key v hv
  | mdata m e' =>
    exfalso
    simp [convStep, failO, run_pure] at hv
  | proj s i e' =>
    exfalso
    simp [convStep, failO, run_pure] at hv
  | app f a => exact hb.elim
  | letE nm ty val body nd => exact hb.elim
  | fvar _ | mvar _ | sort _ | const _ _ | lit _ =>
    simp only [convStep, okO, run_pure, Option.some.injEq] at hv
    subst hv
    exact ⟨FReachC.refl st, hTr, inRange_atom (by simp [IsAtom]) hnp, noLoose_atom (by simp [IsAtom])⟩

theorem readF_traceGood_of_step (senv : StructEnv) (F : PureFacts senv) (nDecl : Nat)
    (hstep : ∀ n : Nat, TraceGood senv nDecl (readF senv n) →
      ∀ c : Call, TracePre senv nDecl c → ∀ v : c.Res,
        (step senv c).run (readF senv n) = some (some v) →
        FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v) :
    ∀ n : Nat, TraceGood senv nDecl (readF senv n)
  | 0 => fun c _ v hv => by
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | n + 1 => fun c hpre v hv => by
    have ih := readF_traceGood_of_step senv F nDecl hstep n
    have hv' : (step senv c).run (readF senv n) = some (some v) := hv
    obtain ⟨hr, hp⟩ := hstep n ih c hpre v hv'
    exact ⟨readF_good senv F (n + 1) c hpre.1 v hv, hr, hp⟩

end Tools.ShippingGen5ReaderTrace
