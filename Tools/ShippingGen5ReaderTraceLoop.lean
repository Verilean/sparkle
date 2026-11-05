import Tools.ShippingGen5ReaderTraceLet
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceLoop, exit 0, 755 jobs) on the tree of 97de8a8e8a8ada2267a12a6d50738201a64e9ec5 (Lean content identical; this header is comment-only). Written against freeze rev13 `scripts/gen5/DG_READERTRACE_FREEZE_REV13.md` §1 (U-R9: `loopBodyStep`; no premise). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R9: `loopBodyStep`

Conditional (intermediate) result: `loopBody_trace` holds under the fuel-`n` table `hT : TraceGood senv nDecl (readF senv n)` and a successful run `hv`. No `hstep`, no `PureFacts`, no extern fact, no named hypothesis.
Not supplied: `instSStep`, `loopRootStep`, the dispatch, `TraceGood senv nDecl (readF senv n)` as a whole, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv

theorem loopReg_ph {L : Nat} {a : Lean.Expr} {r : Lean.Expr × Lean.Expr × Lean.Expr}
    (hn : NoPh a = true) (hb : BvarLt L a = true) (h : machLoopReg? a = some r) :
    NoPh r.2.2 = true ∧ BvarLt L r.2.2 = true := by
  unfold machLoopReg? at h
  split at h
  · injection h with h
    subst h
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    exact ⟨hn.2, hb.2⟩
  · cases h

theorem loopRegs_ph {L : Nat} : ∀ (e : Lean.Expr) (regs : List (Lean.Expr × Lean.Expr × Lean.Expr)),
    NoPh e = true → BvarLt L e = true → machLoopRegs e = some regs →
    ∀ r ∈ regs, NoPh r.2.2 = true ∧ BvarLt L r.2.2 = true := by
  intro e
  induction e with
  | app f b ihf ihb =>
    intro regs hn hb h
    unfold machLoopRegs at h
    split at h
    · rename_i heq
      injection heq with hf hb'
      subst hf
      subst hb'
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      try simp only [Option.bind_eq_bind] at h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rs, hrs, h⟩ := Option.bind_eq_some_iff.mp h
      injection h with h
      subst h
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact loopReg_ph hn.1.2 hb.1.2 hr
      · exact ihb rs hn.2 hb.2 hrs q hq
    · obtain ⟨r, hr, h⟩ := Option.map_eq_some_iff.mp h
      subst h
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact loopReg_ph hn hb hr
  | _ =>
    intro regs hn hb h
    simp only [machLoopRegs] at h
    obtain ⟨r, hr, h⟩ := Option.map_eq_some_iff.mp h
    subst h
    intro q hq
    rw [List.mem_singleton.mp hq]
    exact loopReg_ph hn hb hr

/-- The value `resolve` returns is the input or a stored value (range at the current table size, loose-free). -/
theorem resolve_ph {nDecl : Nat} {st : MachRead} (hF : FullInv nDecl st) (hln : LetsNoLoose st) :
    ∀ (fuel : Nat) (e : Lean.Expr), InRange nDecl st st.lets.size e → NoLoose 0 e →
      InRange nDecl st st.lets.size (machBindLetAlias.resolve st.lets fuel e) ∧
      NoLoose 0 (machBindLetAlias.resolve st.lets fuel e) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro e he hn
    unfold machBindLetAlias.resolve
    split
    · exact ⟨he, hn⟩
    · split
      · rename_i a b v hget
        have hj := (getElem?_eq_some_iff.mp hget).1
        have hv1 : InRange nDecl st st.lets.size v :=
          inRange_mono (hF.2.1.1 _ a b v hget) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_of_lt hj)
        exact ih _ (by omega) v hv1 (hln _ a b v hget)
      · exact ⟨he, hn⟩
    · exact ⟨he, hn⟩

theorem trInv_bindLetNamed {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {ty v' : Lean.Expr} (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    TrInv senv nDecl { st with lets := (machBindLetNamed nm ty v' st.lets).2 } := by
  unfold machBindLetNamed
  split
  · exact hTr
  · exact hTr
  · split
    · exact hTr
    · exact trInv_pushLet hTr _ _ h hn

theorem bindLetAlias_trace {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {ty v' : Lean.Expr} (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    FReachC nDecl st { st with lets := (machBindLetAlias nm ty v' st.lets).2 } ∧
    TrInv senv nDecl { st with lets := (machBindLetAlias nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (machBindLetAlias nm ty v' st.lets).2 } (machBindLetAlias nm ty v' st.lets).2.size
      (machBindLetAlias nm ty v' st.lets).1 ∧
    NoLoose 0 (machBindLetAlias nm ty v' st.lets).1 := by
  unfold machBindLetAlias
  by_cases hc : machIsLetVar (machBindLetAlias.resolve st.lets st.lets.size v') = true
  · rw [if_pos hc]
    have hr := bindLetNamed_reach (nm := nm) (ty := ty) h hn
    exact ⟨hr.1, trInv_bindLetNamed hTr h hn, hr.2.1, hr.2.2⟩
  · rw [if_neg hc]
    obtain ⟨hr, hrn⟩ := resolve_ph hTr.1 hTr.2.2.2.2.2.1 st.lets.size v' h hn
    split
    · exact ⟨FReachC.refl st, hTr, h, hn⟩
    · exact ⟨FReachC.refl st, hTr, h, hn⟩
    · dsimp only
      split
      · next j hj =>
        exact ⟨FReachC.refl st, hTr, inRange_machLet (Array.findIdx?_eq_some_iff_getElem.mp hj).1,
          fun _ hh => (hh : False)⟩
      · refine ⟨reachC_letv st _ _ _ hr, trInv_pushLet hTr _ _ hr hrn, ?_, fun _ hh => (hh : False)⟩
        simp only [Array.size_push]
        exact inRange_machLet (Nat.lt_succ_self _)

/-- The three-way choice of `loopBodyStep`'s `letE` arm. -/
theorem loopLet_ph {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {ty v' : Lean.Expr} (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    FReachC nDecl st { st with lets := (if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
      else machBindLet nm ty v' st.lets).2 } ∧
    TrInv senv nDecl { st with lets := (if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
      else machBindLet nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
      else machBindLet nm ty v' st.lets).2 } (if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
      else machBindLet nm ty v' st.lets).2.size (if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
      else machBindLet nm ty v' st.lets).1 ∧
    NoLoose 0 (if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
      else machBindLet nm ty v' st.lets).1 := by
  by_cases h1 : machIsSlot v' = true
  · simp only [if_pos h1]
    have hr := bindLetNamed_reach (nm := nm) (ty := ty) h hn
    exact ⟨hr.1, trInv_bindLetNamed hTr h hn, hr.2.1, hr.2.2⟩
  · simp only [if_neg h1]
    by_cases h2 : machIsLetVar v' = true
    · simp only [if_pos h2]
      exact bindLetAlias_trace hTr h hn
    · simp only [if_neg h2]
      have hr := bindLet_reach (nm := nm) (ty := ty) h hn
      exact ⟨hr.1, trInv_bindLet hTr h hn, hr.2.1, hr.2.2⟩

def LoopFold (senv : StructEnv) (nDecl : Nat) (st0 : MachRead) (p : List (Nat × Lean.Expr) × MachRead) : Prop :=
  Adv st0 p.2 ∧ FReachC nDecl st0 p.2 ∧ TrInv senv nDecl p.2 ∧
  (∀ w ∈ p.1, w.1 < p.2.kinds.size ∧ InRange nDecl p.2 p.2.lets.size w.2)

theorem loopNext_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (base : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (n0 : Nat) (hbase : base + n0 ≤ st0.kinds.size)
    (a : Lean.Expr × Lean.Expr × Lean.Expr) (ha : NoPh a.2.2 = true ∧ BvarLt (env.length + nDecl) a.2.2 = true)
    (ws : List (Nat × Lean.Expr)) (st : MachRead) (hlen : ws.length < n0) (hI : LoopFold senv nDecl st0 (ws, st)) :
    SatP (readF senv n) (fun p : List (Nat × Lean.Expr) × MachRead => LoopFold senv nDecl st0 p ∧ p.1.length = ws.length + 1)
      (loopNext env base (ws, st) a) := by
  obtain ⟨hA, hR, hTr, hws⟩ := hI
  obtain ⟨t, i, nx⟩ := a
  unfold loopNext
  have hbd0 : BvarLt (0 + env.length + nDecl) nx = true := by rw [Nat.zero_add]; exact ha.2
  refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 nx st) p)
    (fun p hp => hT (Call.conv env 0 nx st)
      ⟨⟨hA.1, envOk_mono hA.2 hE0, noPh_letOk 0 nx ha.1⟩,
       ⟨hTr, envPh_mono hEp0 hR, ha.1, hbd0⟩⟩ p hp) ?_
  rintro ⟨nx', s1⟩ ⟨hP1, hR1, hX1⟩
  have hA1 : Adv st s1 := hP1.1
  obtain ⟨hl1, hi1, hk1⟩ := reachC_sizes_mono hR1
  refine satp_okO ⟨⟨adv_trans hA hA1, reachC_trans hR hR1, hX1.1, ?_⟩, by simp⟩
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨h1, h2⟩ := hws w hw
    exact ⟨Nat.lt_of_lt_of_le h1 hk1, inRange_mono h2 hi1 hk1 hl1⟩
  · rw [List.mem_singleton.mp hw]
    obtain ⟨_, _, hk0⟩ := reachC_sizes_mono (reachC_trans hR hR1)
    refine ⟨?_, hX1.2.1⟩
    have hk0' : st0.kinds.size ≤ s1.kinds.size := hk0
    show base + ws.length < s1.kinds.size
    omega

theorem loopFold_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (base : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (n0 : Nat) (hbase : base + n0 ≤ st0.kinds.size) :
    ∀ (l : List (Lean.Expr × Lean.Expr × Lean.Expr)),
      (∀ a ∈ l, NoPh a.2.2 = true ∧ BvarLt (env.length + nDecl) a.2.2 = true) →
    ∀ (ws : List (Nat × Lean.Expr)) (st : MachRead), ws.length + l.length ≤ n0 →
      LoopFold senv nDecl st0 (ws, st) →
      SatP (readF senv n) (fun p : List (Nat × Lean.Expr) × MachRead => LoopFold senv nDecl st0 p ∧
          p.1.length = ws.length + l.length)
        (foldO (loopNext env base) (ws, st) l)
  | [], _, ws, st, _, hI => by
    unfold foldO
    exact satp_okO ⟨hI, by simp⟩
  | a :: l, hl, ws, st, hlen, hI => by
    unfold foldO
    refine satp_bindO (Q := fun p : List (Nat × Lean.Expr) × MachRead =>
        LoopFold senv nDecl st0 p ∧ p.1.length = ws.length + 1)
      (loopNext_trace senv nDecl n hT env base hE0 hEp0 n0 hbase a (hl a List.mem_cons_self) ws st
        (by simp at hlen; omega) hI) ?_
    rintro ⟨ws', s'⟩ ⟨hI', hl'⟩
    simp only at hl'
    refine satp_mono ?_ (loopFold_trace senv nDecl n hT env base hE0 hEp0 n0 hbase l
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) ws' s' (by simp at hlen; omega) hI')
    intro p hp
    refine ⟨hp.1, ?_⟩
    have := hp.2
    simp only [List.length_cons]
    omega

theorem loopBody_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.loopBody base env e st))
    (r : (Call.loopBody base env e st).Res)
    (hv : (loopBodyStep base env e st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.loopBody base env e st) r) ∧
    PhPost senv nDecl (Call.loopBody base env e st) r := by
  obtain ⟨⟨hst, hE, hl⟩, ⟨hTr, hEp, hnp, hbl, hregs⟩⟩ := hpre
  have key : SatP (readF senv n) (fun s : MachRead => FReachC nDecl st s ∧ TrInv senv nDecl s)
      (loopBodyStep base env e st) := by
    cases e
    case letE nm ty v b nd =>
      have hn3 : (NoPh ty = true ∧ NoPh v = true) ∧ NoPh b = true := by simpa [NoPh] using hnp
      have hb3 : (BvarLt (env.length + nDecl) ty = true ∧ BvarLt (env.length + nDecl) v = true) ∧
          BvarLt (env.length + nDecl + 1) b = true := by simpa [BvarLt] using hbl
      have hl' : (LetOk 0 ty = true ∧ LetOk 0 v = true) ∧ LetOk 0 b = true := by simpa [LetOk] using hl
      have hbv0 : BvarLt (0 + env.length + nDecl) v = true := by rw [Nat.zero_add]; exact hb3.1.2
      unfold loopBodyStep
      refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 v st) p)
        (fun p hp => hT (Call.conv env 0 v st)
          ⟨⟨hst, hE, hl'.1.2⟩, ⟨hTr, hEp, hn3.1.2, hbv0⟩⟩ p hp) ?_
      rintro ⟨v', s1⟩ ⟨hP1, hR1, hX1⟩
      have hA1 : Adv st s1 := hP1.1
      have hv'' : LetOk s1.lets.size v' = true := hP1.2
      have hF := loopLet_facts (nm := nm) (ty := ty) (v' := v') hA1.1.1 hv''
      have hP := loopLet_ph (nm := nm) (ty := ty) (v' := v') hX1.1 hX1.2.1 hX1.2.2
      dsimp only
      generalize (if machIsSlot v' then machBindLetNamed nm ty v' s1.lets
        else if machIsLetVar v' then machBindLetAlias nm ty v' s1.lets
        else machBindLet nm ty v' s1.lets) = bl at hF hP ⊢
      obtain ⟨x, lets'⟩ := bl
      have hA : Adv st { s1 with lets := lets' } := adv_lets hA1 hF.1 hF.2.1 (by rfl) (by rfl)
      have hEv : EnvOk (({ s1 with lets := lets' } : MachRead).lets.size) (MachVal.val x :: env) :=
        envOk_cons (envOk_mono (Nat.le_trans hA1.2 hF.2.1) hE)
          (fun w hw => by injection hw with hw; subst hw; exact hF.2.2)
      have hEp2 := envPh_cons_val (envPh_mono hEp (reachC_trans hR1 hP.1)) hP.2.2.1 hP.2.2.2
      have hbb : BvarLt ((MachVal.val x :: env).length + nDecl) b = true := by
        have hh : (MachVal.val x :: env).length + nDecl = env.length + nDecl + 1 := by
          simp [List.length_cons]; omega
        rw [hh]; exact hb3.2
      obtain ⟨_, _, hk0⟩ := reachC_sizes_mono (reachC_trans hR1 hP.1)
      have hrg : ∀ regs, machLoopRegs (machLetTail b) = some regs →
          base + regs.length ≤ ({ s1 with lets := lets' } : MachRead).kinds.size := by
        intro regs hreg
        have h1 : machLoopRegs (machLetTail (Lean.Expr.letE nm ty v b nd)) = some regs := by
          simpa [machLetTail] using hreg
        have hk' : st.kinds.size ≤ ({ s1 with lets := lets' } : MachRead).kinds.size := hk0
        exact Nat.le_trans (hregs regs h1) hk'
      show SatP _ _ (cLoopBody base (MachVal.val x :: env) b { s1 with lets := lets' })
      intro r' hr'
      have hh := hT (Call.loopBody base (MachVal.val x :: env) b { s1 with lets := lets' })
        ⟨⟨hA.1, hEv, hl'.2⟩, ⟨hP.2.1, hEp2, hn3.2, hbb, hrg⟩⟩ r' hr'
      exact ⟨reachC_trans hR1 (reachC_trans hP.1 hh.2.1), hh.2.2⟩
    all_goals
      unfold loopBodyStep
      try dsimp only
      refine satp_optK ?_
      intro regs hreg
      have hrgs := loopRegs_ph _ regs hnp hbl hreg
      have hb0 : base + regs.length ≤ st.kinds.size := hregs regs (by simpa [machLetTail] using hreg)
      refine satp_bindO (Q := fun p : List (Nat × Lean.Expr) × MachRead =>
          LoopFold senv nDecl st p ∧ p.1.length = ([] : List (Nat × Lean.Expr)).length + regs.length)
        (loopFold_trace senv nDecl n hT env base hE hEp regs.length hb0 regs hrgs [] st (by simp)
          ⟨adv_refl hst, FReachC.refl st, hTr, by simp⟩) ?_
      rintro ⟨ws, st2⟩ ⟨⟨hA2, hR2, hTr2, hws⟩, _⟩
      have hws2 : ∀ w ∈ st2.ws ++ ws.toArray, w.1 < st2.kinds.size ∧ InRange nDecl st2 st2.lets.size w.2 := by
        intro w hw
        rcases Array.mem_append.mp hw with hw | hw
        · exact hTr2.1.2.1.2 w hw
        · exact hws w (List.mem_toArray.mp hw)
      have hreach := reachC_ws st2 _ hws2
      exact satp_okO ⟨reachC_trans hR2 hreach, fullInv_reachC hTr2.1 hreach, hTr2.2⟩
  exact ⟨(key r hv).1, (key r hv).2⟩

end Tools.ShippingGen5ReaderTrace
