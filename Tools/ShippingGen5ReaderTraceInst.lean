import Tools.ShippingGen5ReaderTraceNested
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceInst, exit 0) on the tree of 8b0e4991e87038616105e152f98a2a2635390cb0 (Lean content identical; this header is comment-only). Written against freeze rev10 addendum §4 `scripts/gen5/DG_READERTRACE_FREEZE_REV10.md` (U-R7: `instStep`; no premise). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R7: `instStep` (ordinary / memory instance call)

Conditional (intermediate) result: `inst_trace` holds under the fuel-`n` table `hT : TraceGood senv nDecl (readF senv n)` and a successful run `hv`. No `hstep`, no `PureFacts`, no extern fact, no named hypothesis.
Not supplied: `instSStep`, the other bodies, `TraceGood senv nDecl (readF senv n)` as a whole, the dispatch, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Sparkle.Compiler.MachInstOrigin

def InstFold (senv : StructEnv) (nDecl : Nat) (st0 : MachRead) (p : List Nat × MachRead) : Prop :=
  Adv st0 p.2 ∧ FReachC nDecl st0 p.2 ∧ TrInv senv nDecl p.2 ∧ ∀ a ∈ p.1, a < p.2.lets.size

def nonDom : MixedGateBinder → Nat
  | .domain => 0
  | _ => 1

theorem inRange_machInstOut {nDecl k' kk : Nat} {st : MachRead} (h : k' < st.insts.size) :
    InRange nDecl st kk (machInstOut k') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi; simp [machInstOut, MentionsPh] at hi
  · intro j hj; simp only [machInstOut, MentionsPh] at hj; omega
  · intro i hi; simp [machInstOut, MentionsPh] at hi
  · intro i hi; simp [machInstOut, MentionsPh] at hi

theorem trInv_letIndex {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {kd : MixedGateBinder} {v' : Lean.Expr} (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    TrInv senv nDecl { st with lets := (machLetIndex nm kd v' st.lets).2 } := by
  unfold machLetIndex
  split
  · exact hTr
  · split
    · exact hTr
    · exact trInv_pushLet hTr _ _ h hn

theorem trInv_dom {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    FReachC nDecl st { st with dom := some v' } ∧ TrInv senv nDecl { st with dom := some v' } := by
  have hreach : FReachC nDecl st { st with dom := some v' } := .ctrl (.refl st) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hreach, fullInv_reachC hTr.1 hreach, ?_⟩
  obtain ⟨hlw, hbr, hne, hdm, hln, hgr⟩ := hTr.2
  refine ⟨hlw, hbr, hne, ?_, hln, fun k c js r h1 h2 => hgr k c js r h1 h2⟩
  intro d hd
  have hd' : some v' = some d := hd
  cases hd'
  exact ⟨h, hn⟩

theorem trInv_pushInst {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st)
    (c : Name) (js : List Nat) (r : MixedGateBinder) (o : Sparkle.Compiler.MachInstOrigin.InstOrigin) (f : String)
    (hj : ∀ a ∈ js, a < st.lets.size) (hr : r ≠ .domain)
    (ho : ∀ cb aw dw, o = .mem cb aw dw → js.length = 4 ∧ r = .bits dw) (hf : ∀ i, o ≠ .field i) :
    FReachC nDecl st { st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f,
                               instOrigins := st.instOrigins.push o } ∧
    TrInv senv nDecl { st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f,
                               instOrigins := st.instOrigins.push o } := by
  have hreach : FReachC nDecl st ({ st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f, instOrigins := st.instOrigins.push o } : MachRead) :=
    .ctrl (.tail (.refl st) (FStep.inst st c js r o hj hr ho)) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hreach, fullInv_reachC hTr.1 hreach, ?_⟩
  obtain ⟨hlw, hbr, hne, hdm, hln, hgr⟩ := hTr.2
  obtain ⟨hl, hi, hk⟩ := reachC_sizes_mono hreach
  have hO : st.instOrigins.size = st.insts.size := hTr.1.2.2.1
  refine ⟨hlw, hbr, ?_, ?_, hln, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hne x hx
    exact ⟨inRange_mono h1 hi hk hl, h2⟩
  · intro d hd
    obtain ⟨h1, h2⟩ := hdm d hd
    exact ⟨inRange_mono h1 hi hk hl, h2⟩
  · intro k c' js' r' h1 h2
    have h1' : (st.insts.push (c, js, r))[k]? = some (c', js', r') := h1
    have h2' : (st.instOrigins.push o)[k]? = some (.field 0) := h2
    rw [Array.getElem?_push] at h1' h2'
    by_cases hks : k = st.insts.size
    · rw [if_pos (hO ▸ hks)] at h2'
      exact absurd (Option.some.inj h2') (hf 0)
    · rw [if_neg hks] at h1'
      rw [if_neg (hO ▸ hks)] at h2'
      obtain ⟨kinds, ty, resTy, args, ctor, fields, e1, e2, e3, e4⟩ := hgr k c' js' r' h1' h2'
      refine ⟨kinds, ty, resTy, args, ctor, fields, e1, e2, e3, ?_⟩
      show k + fields.length ≤ (st.insts.push (c, js, r)).size
      rw [Array.size_push]; omega

theorem instArg_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (k : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (kind : MixedGateBinder) (arg : Lean.Expr) (harg : NoPh arg = true ∧ BvarLt (env.length + nDecl) arg = true)
    (js : List Nat) (st : MachRead) (hI : InstFold senv nDecl st0 (js, st)) :
    SatP (readF senv n) (fun p : List Nat × MachRead => InstFold senv nDecl st0 p ∧ p.1.length = js.length + nonDom kind)
      (instArg env k (js, st) (kind, arg)) := by
  obtain ⟨hA, hR, hTr, hjs⟩ := hI
  unfold instArg
  have hbd0 : BvarLt (0 + env.length + nDecl) arg = true := by rw [Nat.zero_add]; exact harg.2
  refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 arg st) p)
    (fun p hp => hT (Call.conv env 0 arg st)
      ⟨⟨hA.1, envOk_mono hA.2 hE0, noPh_letOk 0 arg harg.1⟩,
       ⟨hTr, envPh_mono hEp0 hR, harg.1, hbd0⟩⟩ p hp) ?_
  rintro ⟨v', s1⟩ ⟨hP1, hR1, hX1⟩
  have hA1 : Adv st s1 := hP1.1
  have hv'' : LetOk s1.lets.size v' = true := hP1.2
  have hAs : Adv st0 s1 := adv_trans hA hA1
  have hRs : FReachC nDecl st0 s1 := reachC_trans hR hR1
  have hjs1 : ∀ a ∈ js, a < s1.lets.size := fun a ha => Nat.lt_of_lt_of_le (hjs a ha) hA1.2
  refine satp_pure ?_
  intro r hr
  cases kind with
  | domain =>
    try dsimp only at hr
    split at hr
    · next d _ =>
      split at hr
      · cases hr
      · injection hr with hr
        subst hr
        exact ⟨⟨hAs, hRs, hX1.1, hjs1⟩, by simp [nonDom]⟩
    · injection hr with hr
      subst hr
      obtain ⟨hr2, hT2⟩ := trInv_dom hX1.1 hX1.2.1 hX1.2.2
      exact ⟨⟨adv_dom hAs (by rfl) (by rfl) (by rfl) hv'', reachC_trans hRs hr2, hT2, hjs1⟩, by simp [nonDom]⟩
  | bits w =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    obtain ⟨hr2, hj2⟩ := letIndex_reach (nm := Name.mkSimple s!"inst{k}_arg{js.length}") (kd := .bits w) hX1.2.1
    refine ⟨⟨adv_lets hAs (machLetIndex_noAlias hAs.1.1) machLetIndex_size (by rfl) (by rfl),
      reachC_trans hRs hr2, trInv_letIndex hX1.1 hX1.2.1 hX1.2.2, ?_⟩, by simp [nonDom]⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact Nat.lt_of_lt_of_le (hjs1 a ha) machLetIndex_size
    · rw [List.mem_singleton.mp ha]; exact hj2
  | bool =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    obtain ⟨hr2, hj2⟩ := letIndex_reach (nm := Name.mkSimple s!"inst{k}_arg{js.length}") (kd := .bool) hX1.2.1
    refine ⟨⟨adv_lets hAs (machLetIndex_noAlias hAs.1.1) machLetIndex_size (by rfl) (by rfl),
      reachC_trans hRs hr2, trInv_letIndex hX1.1 hX1.2.1 hX1.2.2, ?_⟩, by simp [nonDom]⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact Nat.lt_of_lt_of_le (hjs1 a ha) machLetIndex_size
    · rw [List.mem_singleton.mp ha]; exact hj2

theorem instFold_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (k : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env) :
    ∀ (l : List (MixedGateBinder × Lean.Expr)), (∀ a ∈ l, NoPh a.2 = true ∧ BvarLt (env.length + nDecl) a.2 = true) →
    ∀ (js : List Nat) (st : MachRead), InstFold senv nDecl st0 (js, st) →
      SatP (readF senv n) (fun p : List Nat × MachRead => InstFold senv nDecl st0 p ∧
          p.1.length = js.length + (l.map fun a => nonDom a.1).sum)
        (foldO (instArg env k) (js, st) l)
  | [], _, js, st, hI => by
    unfold foldO
    exact satp_okO ⟨hI, by simp⟩
  | (kind, arg) :: l, hl, js, st, hI => by
    unfold foldO
    refine satp_bindO (Q := fun p : List Nat × MachRead => InstFold senv nDecl st0 p ∧ p.1.length = js.length + nonDom kind)
      (instArg_trace senv nDecl n hT env k hE0 hEp0 kind arg (hl (kind, arg) List.mem_cons_self) js st hI) ?_
    rintro ⟨js', s'⟩ ⟨hI', hlen⟩
    refine satp_mono ?_ (instFold_trace senv nDecl n hT env k hE0 hEp0 l
      (fun a ha => hl a (List.mem_cons_of_mem _ ha)) js' s' hI')
    intro p hp
    refine ⟨hp.1, ?_⟩
    have := hp.2
    simp only [List.map_cons, List.sum_cons]
    simp only at hlen
    omega

/-- helper: `instEntry` keeps `TrInv`, is reachable, and its result kind is not a domain. -/
theorem instEntry_trace {senv : StructEnv} {nDecl : Nat} {st st1 : MachRead} {res : MixedGateBinder}
    (hTr : TrInv senv nDecl st) (h : instEntry res st = some st1) :
    res ≠ MixedGateBinder.domain ∧ FReachC nDecl st st1 ∧ TrInv senv nDecl st1 := by
  cases res with
  | bits w =>
    have h' : some st = some st1 := h
    injection h' with h1
    subst h1
    exact ⟨(fun hh => by cases hh), FReachC.refl _, hTr⟩
  | bool =>
    have h' : some { st with instStruct := true } = some st1 := h
    injection h' with h1
    subst h1
    have hreach : FReachC nDecl st { st with instStruct := true } := .ctrl (.refl st) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨(fun hh => by cases hh), hreach, fullInv_reachC hTr.1 hreach, hTr.2⟩
  | domain =>
    have h' : (none : Option MachRead) = some st1 := h
    cases h'

theorem inst_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (c : Name) (org : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.inst env c org kinds res args st))
    (r : (Call.inst env c org kinds res args st).Res)
    (hv : (instStep env c org kinds res args st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.inst env c org kinds res args st) r) ∧
    PhPost senv nDecl (Call.inst env c org kinds res args st) r := by
  obtain ⟨⟨hst, hE, hla⟩, ⟨hTr, hEp, hargs, horg⟩⟩ := hpre
  have key : SatP (readF senv n)
      (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl 0 p)
      (instStep env c org kinds res args st) := by
    unfold instStep
    refine satp_optK ?_
    intro st1 hst1
    have h1 : Adv st st1 := instEntry_adv (adv_refl hst) hst1
    obtain ⟨hresd, hreach1, hTr1⟩ := instEntry_trace hTr hst1
    have hargs' : ∀ a ∈ kinds.zip args, NoPh a.2 = true ∧ BvarLt (env.length + nDecl) a.2 = true :=
      fun a ha => hargs a.2 (List.of_mem_zip ha).2
    refine satp_bindO (Q := fun p : List Nat × MachRead => InstFold senv nDecl st1 p ∧
        p.1.length = ([] : List Nat).length + ((kinds.zip args).map fun a => nonDom a.1).sum)
      (instFold_trace senv nDecl n hT env st1.insts.size (envOk_mono h1.2 hE) (envPh_mono hEp hreach1)
        (kinds.zip args) hargs' [] st1 ⟨adv_refl h1.1, .refl st1, hTr1, by simp⟩) ?_
    rintro ⟨js, st2⟩ ⟨⟨hA2, hR2, hTr2, hjs⟩, hlen⟩
    have hR2' : FReachC nDecl st st2 := reachC_trans hreach1 hR2
    obtain ⟨hl2, hi2, hk2⟩ := reachC_sizes_mono hR2
    have hi2' : st1.insts.size ≤ st2.insts.size := hi2
    refine satp_pure ?_
    intro r' hr'
    split at hr'
    · next k' hfind =>
      injection hr' with hr'
      subst hr'
      have hk' : k' < st2.insts.size := by
        have := (Array.findIdx?_eq_some_iff_getElem.mp hfind).1
        simpa [Array.size_zipIdx] using this
      exact ⟨hR2', hTr2, inRange_machInstOut hk', noLoose_fvar⟩
    · injection hr' with hr'
      subst hr'
      have hmem : ∀ cb aw dw, org = Sparkle.Compiler.MachInstOrigin.InstOrigin.mem cb aw dw →
          js.length = 4 ∧ res = MixedGateBinder.bits dw := by
        intro cb aw dw ho
        rcases horg with h | ⟨cb', aw', dw', h1', h2', h3', h4'⟩
        · rw [h] at ho; cases ho
        · rw [h1'] at ho
          injection ho with e1 e2 e3
          subst e1 e2 e3
          refine ⟨?_, h3'⟩
          subst h2'
          obtain ⟨a1, a2, a3, a4, a5, rfl⟩ : ∃ a1 a2 a3 a4 a5, args = [a1, a2, a3, a4, a5] := by
            match args, h4' with
            | [a1, a2, a3, a4, a5], _ => exact ⟨_, _, _, _, _, rfl⟩
          simpa [nonDom] using hlen
      have hnf : ∀ i, org ≠ Sparkle.Compiler.MachInstOrigin.InstOrigin.field i := by
        intro i hh
        rcases horg with h | ⟨cb', aw', dw', h1', _⟩
        · rw [h] at hh; cases hh
        · rw [h1'] at hh; cases hh
      obtain ⟨hr3, hT3⟩ := trInv_pushInst hTr2 c js res org "out" hjs hresd hmem hnf
      refine ⟨reachC_trans hR2' hr3, hT3, inRange_machInstOut ?_, noLoose_fvar⟩
      show st1.insts.size < (st2.insts.push (c, js, res)).size
      rw [Array.size_push]; omega
  exact key r hv

end Tools.ShippingGen5ReaderTrace
