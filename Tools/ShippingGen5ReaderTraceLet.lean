import Tools.ShippingGen5ReaderTraceReg
import Tools.ShippingGen5ReaderTraceLift
import Tools.ShippingLetsExternSpec
import Tools.ShippingLetsAliasInv
set_option autoImplicit false
-- NOT BUILT: written against freeze rev10 `scripts/gen5/DG_READERTRACE_FREEZE_REV10.md` (U-R5a: `convStep` `letE` arm; premises: existing named hypotheses `LiftAgrees` T1L-50 and `RootFloatAgrees` T1L-52 only). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R5a: the `letE` arm of `convStep`

Conditional (intermediate) result: `conv_letE_trace` takes `hla : LiftAgrees`, `hrf : RootFloatAgrees` (existing named hypotheses, not proved here),
the fuel-`n` table `hT : TraceGood senv nDecl (readF senv n)` and a successful run `hv`. No `hstep`, no `PureFacts`, no new premise.
Not supplied: the other arms, `TraceGood senv nDecl (readF senv n)` as a whole, the dispatch, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv

theorem lift01_ph (hla : LiftAgrees) {e : Lean.Expr} {L : Nat} (hn : NoPh e = true) (hb : BvarLt L e = true) :
    NoPh (e.liftLooseBVars 0 1) = true ∧ BvarLt (L + 1) (e.liftLooseBVars 0 1) = true := by
  rw [(hla e (noPh_letOk 0 e hn)).1]
  exact ⟨liftSpec_noPh e 0 1 hn, liftSpec_bvarLt e 0 1 L hb⟩

theorem lift11_ph (hla : LiftAgrees) {e : Lean.Expr} {L : Nat} (hn : NoPh e = true) (hb : BvarLt L e = true) :
    NoPh (e.liftLooseBVars 1 1) = true ∧ BvarLt (L + 1) (e.liftLooseBVars 1 1) = true := by
  rw [(hla e (noPh_letOk 0 e hn)).2]
  exact ⟨liftSpec_noPh e 1 1 hn, liftSpec_bvarLt e 1 1 L hb⟩

theorem rootFloat_ph (hrf : RootFloatAgrees) {v : Lean.Expr} {L : Nat} (hn : NoPh v = true) (hb : BvarLt L v = true) :
    NoPh (Sparkle.Compiler.MachRawSurface.rootFloat v) = true ∧
    BvarLt L (Sparkle.Compiler.MachRawSurface.rootFloat v) = true := by
  rw [hrf v (noPh_letOk 0 v hn)]
  exact ⟨rootFloatS_noPh v hn, rootFloatS_bvarLt v L hb⟩

theorem envPh_cons_regs {nDecl : Nat} {st : MachRead} {env : List MachVal} (h : EnvPh nDecl st env) (p : Nat) :
    EnvPh nDecl st (MachVal.regs p :: env) := by
  refine ⟨fun v hv => ?_, fun b n hbn => ?_⟩
  · rcases List.mem_cons.mp hv with hv | hv
    · cases hv
    · exact h.1 v hv
  · rcases List.mem_cons.mp hbn with hv | hv
    · cases hv
    · exact h.2 b n hv

theorem envPh_cons_handle {nDecl : Nat} {st : MachRead} {env : List MachVal} (h : EnvPh nDecl st env) (i : Nat) :
    EnvPh nDecl st (MachVal.handle i :: env) := by
  refine ⟨fun v hv => ?_, fun b n hbn => ?_⟩
  · rcases List.mem_cons.mp hv with hv | hv
    · cases hv
    · exact h.1 v hv
  · rcases List.mem_cons.mp hbn with hv | hv
    · cases hv
    · exact h.2 b n hv

theorem envPh_cons_root {nDecl : Nat} {st : MachRead} {env : List MachVal} {mv : MachVal} (h : EnvPh nDecl st env)
    (hs : ∀ b n, mv = MachVal.state b n → b + n ≤ st.kinds.size)
    (hv : ∀ v, mv = MachVal.val v → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) :
    EnvPh nDecl st (mv :: env) := by
  refine ⟨fun v hm => ?_, fun b n hbn => ?_⟩
  · rcases List.mem_cons.mp hm with hm | hm
    · exact hv v hm.symm
    · exact h.1 v hm
  · rcases List.mem_cons.mp hbn with hm | hm
    · exact hs b n hm.symm
    · exact h.2 b n hm

/-- helper: pushing one `let` whose value is in range and loose-free keeps `TrInv`. -/
theorem trInv_pushLet {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st)
    (nm : Name) (kd : MixedGateBinder) {v' : Lean.Expr} (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    TrInv senv nDecl { st with lets := st.lets.push (nm, kd, v') } := by
  have hreach := reachC_letv (nDecl := nDecl) st nm kd v' h
  refine ⟨fullInv_reachC hTr.1 hreach, ?_⟩
  obtain ⟨hlw, hbr, hne, hdm, hln, hgr⟩ := hTr.2
  obtain ⟨hl, hi, hk⟩ := reachC_sizes_mono hreach
  refine ⟨hlw, hbr, ?_, ?_, ?_, hgr⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hne x hx
    exact ⟨inRange_mono h1 hi hk hl, h2⟩
  · intro d hd
    obtain ⟨h1, h2⟩ := hdm d hd
    exact ⟨inRange_mono h1 hi hk hl, h2⟩
  · intro j nm' kd' v'' hj
    have hj' : (st.lets.push (nm, kd, v'))[j]? = some (nm', kd', v'') := hj
    rw [Array.getElem?_push] at hj'
    by_cases hjs : j = st.lets.size
    · rw [if_pos hjs] at hj'
      have := Option.some.inj hj'
      simp only [Prod.mk.injEq] at this
      obtain ⟨_, _, rfl⟩ := this
      exact hn
    · rw [if_neg hjs] at hj'
      exact hln j nm' kd' v'' hj'

theorem trInv_bindLet {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {ty v' : Lean.Expr} (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    TrInv senv nDecl { st with lets := (machBindLet nm ty v' st.lets).2 } := by
  unfold machBindLet
  split
  · exact hTr
  · exact hTr
  · split
    · exact hTr
    · split
      · exact hTr
      · exact trInv_pushLet hTr _ _ h hn

theorem conv_letE_trace (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.letE nm ty v b nd) st))
    (r : (Call.conv env d (.letE nm ty v b nd) st).Res)
    (hv : (convStep senv env d (.letE nm ty v b nd) st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.conv env d (.letE nm ty v b nd) st) r) ∧
    PhPost senv nDecl (Call.conv env d (.letE nm ty v b nd) st) r := by
  obtain ⟨⟨hst, hE, hl⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  have key : SatP (readF senv n)
      (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl d p)
      (convStep senv env d (.letE nm ty v b nd) st) := by
    by_cases hd0 : d = 0
    · subst hd0
      simp only [convStep, bne_self_eq_false, Bool.false_eq_true, if_false]
      have hn3 : (NoPh ty = true ∧ NoPh v = true) ∧ NoPh b = true := by simpa [NoPh] using hnp
      have hb3 : (BvarLt (env.length + nDecl) ty = true ∧ BvarLt (env.length + nDecl) v = true) ∧
          BvarLt (env.length + nDecl + 1) b = true := by simpa [BvarLt] using hbl
      have hbb : ∀ mv : MachVal, BvarLt (0 + (mv :: env).length + nDecl) b = true := by
        intro mv
        have hh : 0 + (mv :: env).length + nDecl = env.length + nDecl + 1 := by simp [List.length_cons]; omega
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
        have hb' : BvarLt (0 + env.length + nDecl) (Lean.Expr.letE n2 t2 v2 (Lean.Expr.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) = true := by
          simp [BvarLt, hbt2, hbv2, hbw, hbty, hbb1]
        intro r' hr'
        have hh := hT (Call.conv env 0 _ st) ⟨⟨hst, hE, noPh_letOk 0 _ hn'⟩, ⟨hTr, hEp, hn', hb'⟩⟩ r' hr'
        exact ⟨hh.2.1, hh.2.2⟩
      · rename_i hnl
        obtain ⟨hnvf, hbvf⟩ := hrfv
        split
        · refine satp_bindO (Q := fun p : MachVal × MachRead => TracePost senv nDecl (Call.loopRoot env vf st) p)
            (fun p hp => hT (Call.loopRoot env vf st)
              ⟨⟨hst, hE, noPh_letOk 0 vf hnvf⟩, ⟨hTr, hEp, hnvf, hbvf⟩⟩ p hp) ?_
          rintro ⟨mv, s1⟩ ⟨hP1, hR1, hX1⟩
          have hAdv : Adv st s1 := hP1.1
          have hEv : EnvOk s1.lets.size (mv :: env) :=
            envOk_cons (envOk_mono hAdv.2 hE) (fun w hw => by subst hw; exact hP1.2)
          intro r' hr'
          have hh := hT (Call.conv (mv :: env) 0 b s1)
            ⟨⟨hAdv.1, hEv, noPh_letOk 0 b hn3.2⟩,
             ⟨hX1.1, envPh_cons_root (envPh_mono hEp hR1) hX1.2.1 hX1.2.2, hn3.2, hbb mv⟩⟩ r' hr'
          exact ⟨reachC_trans hR1 hh.2.1, hh.2.2⟩
        · split
          · rename_i p _
            intro r' hr'
            have hh := hT (Call.conv (MachVal.regs p :: env) 0 b st)
              ⟨⟨hst, envOk_cons hE (fun w hw => by cases hw), noPh_letOk 0 b hn3.2⟩,
               ⟨hTr, envPh_cons_regs hEp p, hn3.2, hbb _⟩⟩ r' hr'
            exact ⟨hh.2.1, hh.2.2⟩
          · split
            · rename_i i _
              intro r' hr'
              have hh := hT (Call.conv (MachVal.handle i :: env) 0 b st)
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
              show SatP _ _ (cConv (MachVal.val (machBindLet nm ty v' s1.lets).1 :: env) 0 b
                { s1 with lets := (machBindLet nm ty v' s1.lets).2 })
              intro r' hr'
              have hh := hT (Call.conv (MachVal.val (machBindLet nm ty v' s1.lets).1 :: env) 0 b
                  { s1 with lets := (machBindLet nm ty v' s1.lets).2 })
                ⟨⟨hA.1, hEv, noPh_letOk 0 b hn3.2⟩, ⟨hTr2, hEp2, hn3.2, hbb _⟩⟩ r' hr'
              exact ⟨reachC_trans hR1 (reachC_trans hbr.1 hh.2.1), hh.2.2⟩
    · have hne : (d != 0) = true := by simp [hd0]
      simp only [convStep, hne, if_true]
      exact satp_failO
  exact key r hv

end Tools.ShippingGen5ReaderTrace
