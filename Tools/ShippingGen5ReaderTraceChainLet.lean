import Tools.ShippingGen5ReaderTraceLet
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceChainLet, exit 0) on the tree of 745e7fda39e8aa60e718ae54ce43c87ee4cfdae0 (Lean content identical; this header is comment-only). Written against freeze rev10 addendum §2 `scripts/gen5/DG_READERTRACE_FREEZE_REV10.md` (U-R5b: `chainStep` `letE` arm; premises: existing named hypotheses `LiftAgrees` T1L-50 and `RootFloatAgrees` T1L-52 only). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R5b: the `letE` arm of `chainStep`

Same shape as U-R5a (`conv_letE_trace`), with the recursion through `cChain` (no binder depth `d`). Conditional (intermediate) result under `hla`, `hrf` (existing named hypotheses), `hT` and a successful run `hv`.
Not supplied: the other arms of the seven bodies, `TraceGood senv nDecl (readF senv n)` as a whole, the dispatch, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv

theorem chain_letE_trace (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.chain env (.letE nm ty v b nd) st))
    (r : (Call.chain env (.letE nm ty v b nd) st).Res)
    (hv : (chainStep senv env (.letE nm ty v b nd) st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.chain env (.letE nm ty v b nd) st) r) ∧
    PhPost senv nDecl (Call.chain env (.letE nm ty v b nd) st) r := by
  obtain ⟨⟨hst, hE, hl⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  have key : SatP (readF senv n)
      (fun p : List (Nat × Lean.Expr) × Lean.Expr × MachRead => FReachC nDecl st p.2.2 ∧ ChainPh senv nDecl p)
      (chainStep senv env (.letE nm ty v b nd) st) := by
    simp only [chainStep]
    have hn3 : (NoPh ty = true ∧ NoPh v = true) ∧ NoPh b = true := by simpa [NoPh] using hnp
    have hb3 : (BvarLt (env.length + nDecl) ty = true ∧ BvarLt (env.length + nDecl) v = true) ∧
        BvarLt (env.length + nDecl + 1) b = true := by simpa [BvarLt] using hbl
    have hbb : ∀ mv : MachVal, BvarLt ((mv :: env).length + nDecl) b = true := by
      intro mv
      have hh : (mv :: env).length + nDecl = env.length + nDecl + 1 := by simp [List.length_cons]; omega
      rw [hh]; exact hb3.2
    have hrfv := rootFloat_ph hrf hn3.1.2 hb3.1.2
    generalize Sparkle.Compiler.MachRawSurface.rootFloat v = vf at hrfv ⊢
    split
    · rename_i _ n2 t2 v2 w nd2
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hrfv
      obtain ⟨⟨⟨hnt2, hnv2⟩, hnw⟩, ⟨⟨hbt2, hbv2⟩, hbw⟩⟩ := hrfv
      obtain ⟨hnty, hbty⟩ := lift01_ph hla hn3.1.1 hb3.1.1
      obtain ⟨hnb1, hbb1⟩ := lift11_ph hla hn3.2 hb3.2
      have hn' : NoPh (Lean.Expr.letE n2 t2 v2 (Lean.Expr.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) = true := by
        simp [NoPh, hnt2, hnv2, hnw, hnty, hnb1]
      have hb' : BvarLt (env.length + nDecl) (Lean.Expr.letE n2 t2 v2 (Lean.Expr.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) = true := by
        simp [BvarLt, hbt2, hbv2, hbw, hbty, hbb1]
      intro r' hr'
      have hh := hT (Call.chain env _ st) ⟨⟨hst, hE, noPh_letOk 0 _ hn'⟩, ⟨hTr, hEp, hn', hb'⟩⟩ r' hr'
      exact ⟨hh.2.1, hh.2.2⟩
    · obtain ⟨hnvf, hbvf⟩ := hrfv
      split
      · refine satp_bindO (Q := fun p : MachVal × MachRead => TracePost senv nDecl (Call.loopRoot env vf st) p)
          (fun p hp => hT (Call.loopRoot env vf st)
            ⟨⟨hst, hE, noPh_letOk 0 vf hnvf⟩, ⟨hTr, hEp, hnvf, hbvf⟩⟩ p hp) ?_
        rintro ⟨mv, s1⟩ ⟨hP1, hR1, hX1⟩
        have hAdv : Adv st s1 := hP1.1
        have hEv : EnvOk s1.lets.size (mv :: env) :=
          envOk_cons (envOk_mono hAdv.2 hE) (fun w hw => by subst hw; exact hP1.2)
        intro r' hr'
        have hh := hT (Call.chain (mv :: env) b s1)
          ⟨⟨hAdv.1, hEv, noPh_letOk 0 b hn3.2⟩,
           ⟨hX1.1, envPh_cons_root (envPh_mono hEp hR1) hX1.2.1 hX1.2.2, hn3.2, hbb mv⟩⟩ r' hr'
        exact ⟨reachC_trans hR1 hh.2.1, hh.2.2⟩
      · split
        · rename_i p _
          intro r' hr'
          have hh := hT (Call.chain (MachVal.regs p :: env) b st)
            ⟨⟨hst, envOk_cons hE (fun w hw => by cases hw), noPh_letOk 0 b hn3.2⟩,
             ⟨hTr, envPh_cons_regs hEp p, hn3.2, hbb _⟩⟩ r' hr'
          exact ⟨hh.2.1, hh.2.2⟩
        · split
          · rename_i i _
            intro r' hr'
            have hh := hT (Call.chain (MachVal.handle i :: env) b st)
              ⟨⟨hst, envOk_cons hE (fun w hw => by cases hw), noPh_letOk 0 b hn3.2⟩,
               ⟨hTr, envPh_cons_handle hEp i, hn3.2, hbb _⟩⟩ r' hr'
            exact ⟨hh.2.1, hh.2.2⟩
          · have hbv0 : BvarLt (0 + env.length + nDecl) vf = true := by
              rw [Nat.zero_add]; exact hbvf
            refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 vf st) p)
              (fun p hp => hT (Call.conv env 0 vf st)
                ⟨⟨hst, hE, noPh_letOk 0 vf hnvf⟩, ⟨hTr, hEp, hnvf, hbv0⟩⟩ p hp) ?_
            rintro ⟨v', s1⟩ ⟨hP1, hR1, hX1⟩
            have hA1 : Adv st s1 := hP1.1
            have hv'' : LetOk s1.lets.size v' = true := hP1.2
            have hbr := bindLet_reach (nm := nm) (ty := ty) hX1.2.1 hX1.2.2
            have hTr2 := trInv_bindLet (nm := nm) (ty := ty) hX1.1 hX1.2.1 hX1.2.2
            have hN := machBindLet_noAlias (nm := nm) (ty := ty) (v' := v') hA1.1.1
            have hRg := machBindLet_range (nm := nm) (ty := ty) (v' := v') hv''
            have hA : Adv st { s1 with lets := (machBindLet nm ty v' s1.lets).2 } :=
              adv_lets hA1 hN hRg.1 (by rfl) (by rfl)
            have hEv : EnvOk (({ s1 with lets := (machBindLet nm ty v' s1.lets).2 } : MachRead).lets.size)
                (MachVal.val (machBindLet nm ty v' s1.lets).1 :: env) :=
              envOk_cons (envOk_mono (Nat.le_trans hA1.2 hRg.1) hE)
                (fun w hw => by injection hw with hw; subst hw; exact hRg.2)
            have hEp2 := envPh_cons_val (envPh_mono hEp (reachC_trans hR1 hbr.1)) hbr.2.1 hbr.2.2
            show SatP _ _ (cChain (MachVal.val (machBindLet nm ty v' s1.lets).1 :: env) b
              { s1 with lets := (machBindLet nm ty v' s1.lets).2 })
            intro r' hr'
            have hh := hT (Call.chain (MachVal.val (machBindLet nm ty v' s1.lets).1 :: env) b
                { s1 with lets := (machBindLet nm ty v' s1.lets).2 })
              ⟨⟨hA.1, hEv, noPh_letOk 0 b hn3.2⟩, ⟨hTr2, hEp2, hn3.2, hbb _⟩⟩ r' hr'
            exact ⟨reachC_trans hR1 (reachC_trans hbr.1 hh.2.1), hh.2.2⟩
  exact key r hv

end Tools.ShippingGen5ReaderTrace
