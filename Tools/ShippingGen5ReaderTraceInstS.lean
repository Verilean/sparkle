import Tools.ShippingGen5ReaderTraceInst
import Tools.ShippingGen5ReaderTraceInst1
import Tools.ShippingGen5ReaderTraceReg
import Tools.Assume.EnvInstS
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceInstS, exit 0, 759 jobs) on the tree of this file's commit. Written against freeze rev12 (U-R8; option A, `InstSFieldsDet` as a named hypothesis). No sorry / axiom / native_decide in source.
-- NOT BUILT yet.

/-! # DG-READERTRACE U-R8: `instSStep` (structure-returning instance call)

Written against freeze rev12 §4 `scripts/gen5/DG_READERTRACE_FREEZE_REV12.md` (reviewer-approved, option A).
Conditional (intermediate) result: `instS_trace` holds under the named condition `InstSFieldsDet senv` (`Tools/Assume/EnvInstS.lean`, FG +1, used by the
dedup arm only), `Inst1Ph`, the fuel-`n` table `hT : TraceGood senv nDecl (readF senv n)` and a successful run `hv`. It does not claim that `InstSFieldsDet` is true.
Not supplied: the other bodies, `TraceGood senv nDecl (readF senv n)` as a whole, the dispatch, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Sparkle.Compiler.MachInstOrigin
  Tools.Assume.EnvInstS

theorem instRes_ph (hI : Inst1Ph) {L : Nat} : ∀ (args : List Lean.Expr) (ty r : Lean.Expr),
    NoPh ty = true → BvarLt L ty = true → (∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) →
    instRes ty args = some r → NoPh r = true ∧ BvarLt L r = true
  | [], ty, r, hn, hb, _, h => by
    simp only [instRes, Option.some.injEq] at h
    subst h
    exact ⟨hn, hb⟩
  | a :: as, ty, r, hn, hb, ha, h => by
    cases ty with
    | forallE nm t b bi =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [instRes] at h
      have ha0 := ha a List.mem_cons_self
      have hi := hI b a L L hn.2 ha0.1 hb.2 ha0.2 (Nat.le_refl _)
      exact instRes_ph hI as _ r hi.1 hi.2 (fun x hx => ha x (List.mem_cons_of_mem _ hx)) h
    | _ => simp [instRes] at h

theorem inRange_foldApp {nDecl : Nat} {s : MachRead} : ∀ (l : List Lean.Expr) (f : Lean.Expr),
    InRange nDecl s s.lets.size f → NoLoose 0 f → (∀ x ∈ l, InRange nDecl s s.lets.size x ∧ NoLoose 0 x) →
    InRange nDecl s s.lets.size (l.foldl Lean.mkApp f) ∧ NoLoose 0 (l.foldl Lean.mkApp f)
  | [], f, hf, hn, _ => ⟨hf, hn⟩
  | x :: l, f, hf, hn, hl => by
    simp only [List.foldl_cons]
    exact inRange_foldApp l _ (inRange_app hf (hl x List.mem_cons_self).1) (noLoose_app hn (hl x List.mem_cons_self).2)
      (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem instS_expr {nDecl : Nat} {s : MachRead} (ctor : Name) (lvls : List Level) (params : List Lean.Expr) (base m : Nat)
    (hp : ∀ q ∈ params, InRange nDecl s s.lets.size q ∧ NoLoose 0 q) (hb : base + m ≤ s.insts.size) :
    InRange nDecl s s.lets.size
      (mkAppN (.const ctor lvls) (params.toArray ++ ((List.range m).map fun i => machInstOut (base + i)).toArray)) ∧
    NoLoose 0
      (mkAppN (.const ctor lvls) (params.toArray ++ ((List.range m).map fun i => machInstOut (base + i)).toArray)) := by
  have h0 : InRange nDecl s s.lets.size (.const ctor lvls) :=
    inRange_closed (fun tag i h => by simp [MentionsPh] at h)
  have := inRange_foldApp (nDecl := nDecl) (s := s) (params ++ (List.range m).map fun i => machInstOut (base + i))
    (.const ctor lvls) h0 noLoose_const (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hp x hx
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have hi' := List.mem_range.mp hi
        exact ⟨inRange_machInstOut (by omega), noLoose_fvar⟩)
  simpa [Lean.mkAppN, ← Array.foldl_toList] using this

theorem trInv_pushGroup {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    (c : Name) (js : List Nat) (fields : List (String × MixedGateBinder))
    (kinds : List MixedGateBinder) (ty resTy : Lean.Expr) (args : List Lean.Expr) (ctor : Name)
    (hj : ∀ a ∈ js, a < s.lets.size) (hd : ∀ f ∈ fields, f.2 ≠ MixedGateBinder.domain)
    (hsig : senv.instS c = some (kinds, ty)) (hres : instRes ty args = some resTy)
    (hmo : machOuts? senv resTy = some (some ctor, fields)) :
    FReachC nDecl s { s with
          insts := s.insts ++ (fields.map fun f => (c, js, f.2)).toArray
          instFields := s.instFields ++ (fields.map (·.1)).toArray
          instStruct := true
          instOrigins := s.instOrigins ++
            ((List.range fields.length).map Sparkle.Compiler.MachInstOrigin.InstOrigin.field).toArray } ∧
    TrInv senv nDecl { s with
          insts := s.insts ++ (fields.map fun f => (c, js, f.2)).toArray
          instFields := s.instFields ++ (fields.map (·.1)).toArray
          instStruct := true
          instOrigins := s.instOrigins ++
            ((List.range fields.length).map Sparkle.Compiler.MachInstOrigin.InstOrigin.field).toArray } := by
  have hmap : (fields.map fun f => (c, js, f.2)) = (fields.map (·.2)).map (fun r => (c, js, r)) := by
    simp [List.map_map, Function.comp_def]
  have hg : FReachC nDecl s { s with
      insts := s.insts ++ ((fields.map (·.2)).map fun r => (c, js, r)).toArray,
      instOrigins := s.instOrigins ++
        ((List.range fields.length).map Sparkle.Compiler.MachInstOrigin.InstOrigin.field).toArray } :=
    .tail (.refl s) (FStep.group s c js (fields.map (·.2))
      ((List.range fields.length).map Sparkle.Compiler.MachInstOrigin.InstOrigin.field)
      (by simp) hj (by intro r hr; obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hr; exact hd f hf)
      (by intro o ho cb aw dw; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ho; intro h; cases h))
  have hreach : FReachC nDecl s { s with
          insts := s.insts ++ (fields.map fun f => (c, js, f.2)).toArray
          instFields := s.instFields ++ (fields.map (·.1)).toArray
          instStruct := true
          instOrigins := s.instOrigins ++
            ((List.range fields.length).map Sparkle.Compiler.MachInstOrigin.InstOrigin.field).toArray } :=
    .ctrl hg ⟨rfl, by simp [hmap], rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hreach, fullInv_reachC hTr.1 hreach, ?_⟩
  obtain ⟨hlw, hbr, hne, hdm, hln, hgr⟩ := hTr.2
  obtain ⟨hl, hi, hk⟩ := reachC_sizes_mono hreach
  have hO : s.instOrigins.size = s.insts.size := hTr.1.2.2.1
  refine ⟨hlw, hbr, ?_, ?_, hln, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hne x hx
    exact ⟨inRange_mono h1 hi hk hl, h2⟩
  · intro d hd'
    obtain ⟨h1, h2⟩ := hdm d hd'
    exact ⟨inRange_mono h1 hi hk hl, h2⟩
  · intro k c' js' r' h1 h2
    have h1' : (s.insts ++ ((fields.map (·.2)).map fun r => (c, js, r)).toArray)[k]? = some (c', js', r') := by
      have := h1
      simp only [hmap] at this
      exact this
    have h2' : (s.instOrigins ++
        ((List.range fields.length).map Sparkle.Compiler.MachInstOrigin.InstOrigin.field).toArray)[k]? =
        some (InstOrigin.field 0) := h2
    rcases origin_group_get h2' with h2o | ⟨hk2, h2o⟩
    · have hklt : k < s.instOrigins.size := (Array.getElem?_eq_some_iff.mp h2o).1
      rcases group_get h1' with h1o | ⟨r, _, hge, _⟩
      · obtain ⟨kinds', ty', resTy', args', ctor', fields', e1, e2, e3, e4⟩ := hgr k c' js' r' h1o h2o
        exact ⟨kinds', ty', resTy', args', ctor', fields', e1, e2, e3, Nat.le_trans e4 hi⟩
      · omega
    · rcases group_get h1' with h1o | ⟨r, _, hge, hx⟩
      · have : k < s.insts.size := (Array.getElem?_eq_some_iff.mp h1o).1
        omega
      · simp only [List.getElem?_map] at h2o
        have hk0 : k - s.instOrigins.size = 0 := by
          obtain ⟨i, hi1, hi2⟩ := Option.map_eq_some_iff.mp h2o
          have hi3 := (List.getElem?_eq_some_iff.mp hi1)
          obtain ⟨hlt, hval⟩ := hi3
          rw [List.getElem_range] at hval
          have : InstOrigin.field i = InstOrigin.field 0 := hi2
          injection this with this
          omega
        have hkk : k = s.insts.size := by omega
        simp only [Prod.mk.injEq] at hx
        obtain ⟨hc, hjs, _⟩ := hx
        rw [hc]
        refine ⟨kinds, ty, resTy, args, ctor, fields, hsig, hres, hmo, ?_⟩
        show k + fields.length ≤ (s.insts ++ (fields.map fun f => (c, js, f.2)).toArray).size
        simp only [Array.size_append, List.size_toArray, List.length_map]
        omega

theorem instSArg_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (kind : MixedGateBinder) (arg : Lean.Expr) (harg : NoPh arg = true ∧ BvarLt (env.length + nDecl) arg = true)
    (js : List Nat) (st : MachRead) (hI : InstFold senv nDecl st0 (js, st)) :
    SatP (readF senv n) (fun p : List Nat × MachRead => InstFold senv nDecl st0 p)
      (instSArg env (js, st) (kind, arg)) := by
  obtain ⟨hA, hR, hTr, hjs⟩ := hI
  unfold instSArg
  have hbd0 : BvarLt (0 + env.length + nDecl) arg = true := by rw [Nat.zero_add]; exact harg.2
  refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 arg st) p)
    (fun p hp => hT (Call.conv env 0 arg st)
      ⟨⟨hA.1, envOk_mono hA.2 hE0, noPh_letOk 0 arg harg.1⟩,
       ⟨hTr, envPh_mono hEp0 hR, harg.1, hbd0⟩⟩ p hp) ?_
  rintro ⟨v', s1⟩ ⟨hP1, hR1, hX1⟩
  have hA1 : Adv st s1 := hP1.1
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
        exact ⟨hAs, hRs, hX1.1, hjs1⟩
    · injection hr with hr
      subst hr
      obtain ⟨hr2, hT2⟩ := trInv_dom hX1.1 hX1.2.1 hX1.2.2
      exact ⟨adv_dom hAs (by rfl) (by rfl) (by rfl) hP1.2, reachC_trans hRs hr2, hT2, hjs1⟩
  | bits w =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    obtain ⟨hr2, hj2⟩ := letIndex_reach (nm := Name.mkSimple s!"inst{s1.insts.size}_arg{js.length}") (kd := .bits w) hX1.2.1
    refine ⟨adv_lets hAs (machLetIndex_noAlias hAs.1.1) machLetIndex_size (by rfl) (by rfl),
      reachC_trans hRs hr2, trInv_letIndex hX1.1 hX1.2.1 hX1.2.2, ?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact Nat.lt_of_lt_of_le (hjs1 a ha) machLetIndex_size
    · rw [List.mem_singleton.mp ha]; exact hj2
  | bool =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    obtain ⟨hr2, hj2⟩ := letIndex_reach (nm := Name.mkSimple s!"inst{s1.insts.size}_arg{js.length}") (kd := .bool) hX1.2.1
    refine ⟨adv_lets hAs (machLetIndex_noAlias hAs.1.1) machLetIndex_size (by rfl) (by rfl),
      reachC_trans hRs hr2, trInv_letIndex hX1.1 hX1.2.1 hX1.2.2, ?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact Nat.lt_of_lt_of_le (hjs1 a ha) machLetIndex_size
    · rw [List.mem_singleton.mp ha]; exact hj2

def ParFold (senv : StructEnv) (nDecl : Nat) (st0 : MachRead) (p : List Lean.Expr × MachRead) : Prop :=
  Adv st0 p.2 ∧ FReachC nDecl st0 p.2 ∧ TrInv senv nDecl p.2 ∧
  ∀ q ∈ p.1, InRange nDecl p.2 p.2.lets.size q ∧ NoLoose 0 q

theorem instSParam_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (p : Lean.Expr) (hp : NoPh p = true ∧ BvarLt (env.length + nDecl) p = true)
    (ps : List Lean.Expr) (st : MachRead) (hI : ParFold senv nDecl st0 (ps, st)) :
    SatP (readF senv n) (fun q : List Lean.Expr × MachRead => ParFold senv nDecl st0 q)
      (instSParam env (ps, st) p) := by
  obtain ⟨hA, hR, hTr, hps⟩ := hI
  unfold instSParam
  have hbd0 : BvarLt (0 + env.length + nDecl) p = true := by rw [Nat.zero_add]; exact hp.2
  refine satp_bindO (Q := fun q : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 p st) q)
    (fun q hq => hT (Call.conv env 0 p st)
      ⟨⟨hA.1, envOk_mono hA.2 hE0, noPh_letOk 0 p hp.1⟩,
       ⟨hTr, envPh_mono hEp0 hR, hp.1, hbd0⟩⟩ q hq) ?_
  rintro ⟨p', s1⟩ ⟨hP1, hR1, hX1⟩
  obtain ⟨hl1, hi1, hk1⟩ := reachC_sizes_mono hR1
  refine satp_okO ⟨adv_trans hA hP1.1, reachC_trans hR hR1, hX1.1, ?_⟩
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact ⟨inRange_mono (hps q hq).1 hi1 hk1 hl1, (hps q hq).2⟩
  · rw [List.mem_singleton.mp hq]; exact ⟨hX1.2.1, hX1.2.2⟩

theorem instS_trace (senv : StructEnv) (nDecl n : Nat) (hI : Inst1Ph) (hD : InstSFieldsDet senv)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.instS env c kinds ty args st))
    (r : (Call.instS env c kinds ty args st).Res)
    (hv : (instSStep senv env c kinds ty args st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.instS env c kinds ty args st) r) ∧
    PhPost senv nDecl (Call.instS env c kinds ty args st) r := by
  obtain ⟨⟨hst, hE, hla⟩, ⟨hTr, hEp, hsig, hlen, hargs, hnp, hbl⟩⟩ := hpre
  have key : SatP (readF senv n)
      (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl 0 p)
      (instSStep senv env c kinds ty args st) := by
    unfold instSStep
    refine satp_ite satp_failO ?_
    refine satp_optK ?_
    intro resTy hres
    have hresPh := instRes_ph hI args ty resTy hnp hbl hargs hres
    refine satp_optK ?_
    rintro ⟨oc, fields⟩ hmo
    cases oc with
    | none => exact satp_failO
    | some ctor =>
      dsimp only
      by_cases hg : (fields.isEmpty || fields.any (fun f => f.2 == MixedGateBinder.domain)) = true
      · rw [if_pos hg]; exact satp_failO
      rw [if_neg hg]
      have hnd : ∀ f ∈ fields, f.2 ≠ MixedGateBinder.domain := by
        intro f hf hfd
        apply hg
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨f, hf, by simp [hfd]⟩
      have hargs' : ∀ a ∈ kinds.zip args, NoPh a.2 = true ∧ BvarLt (env.length + nDecl) a.2 = true :=
        fun a ha => hargs a.2 (List.of_mem_zip ha).2
      refine satp_bindO (Q := fun p : List Nat × MachRead => InstFold senv nDecl st p)
        (satp_foldO (P := fun p : List Nat × MachRead => InstFold senv nDecl st p) (kinds.zip args) ([], st)
          (fun s a ha hs => by
            obtain ⟨js, s0⟩ := s
            obtain ⟨kd, ar⟩ := a
            exact instSArg_trace senv nDecl n hT env hE hEp kd ar (hargs' (kd, ar) ha) js s0 hs)
          ⟨adv_refl hst, .refl st, hTr, by simp⟩) ?_
      rintro ⟨js, st2⟩ ⟨hA2, hR2, hTr2, hjs⟩
      have hpars : ∀ a ∈ resTy.getAppArgs.toList, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true :=
        fun a ha => phArgs_getAppArgs hresPh.1 hresPh.2 a (Array.mem_toList_iff.mp ha)
      have hE2 : EnvOk st2.lets.size env := envOk_mono hA2.2 hE
      have hEp2 : EnvPh nDecl st2 env := envPh_mono hEp hR2
      refine satp_bindO (Q := fun p : List Lean.Expr × MachRead => ParFold senv nDecl st2 p)
        (satp_foldO (P := fun p : List Lean.Expr × MachRead => ParFold senv nDecl st2 p) resTy.getAppArgs.toList
          ([], st2)
          (fun s a ha hs => by
            obtain ⟨ps, s0⟩ := s
            exact instSParam_trace senv nDecl n hT env hE2 hEp2 a (hpars a ha) ps s0 hs)
          ⟨adv_refl hA2.1, .refl st2, hTr2, by simp⟩) ?_
      rintro ⟨params, st3⟩ ⟨hA3, hR3, hTr3, hpr⟩
      have hR3' : FReachC nDecl st st3 := reachC_trans hR2 hR3
      obtain ⟨hl3, hi3, hk3⟩ := reachC_sizes_mono hR3
      have hjs3 : ∀ a ∈ js, a < st3.lets.size := fun a ha => Nat.lt_of_lt_of_le (hjs a ha) hl3
      dsimp only
      split
      · next k0 hfind =>
        obtain ⟨hk0, hpred, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfind
        have hk0' : k0 < st3.insts.size := by simpa [Array.size_zipIdx] using hk0
        simp only [Array.getElem_zipIdx, Bool.and_eq_true, beq_iff_eq] at hpred
        obtain ⟨⟨hc0, hjs0⟩, ho0⟩ := hpred
        have hrow : st3.insts[k0]? = some (c, js, (st3.insts[k0]'hk0').2.2) := by
          rw [Array.getElem?_eq_getElem hk0']
          congr 1
          exact Prod.ext hc0 (Prod.ext hjs0 rfl)
        obtain ⟨kinds0, ty0, resTy0, args0, ctor0, fields0, e1, e2, e3, e4⟩ := hTr3.2.2.2.2.2.2 k0 c js _ hrow (by simpa using ho0)
        rw [hsig] at e1
        have ht : ty = ty0 := (Prod.mk.inj (Option.some.inj e1)).2
        subst ht
        have hlen0 := hD c kinds ty args args0 resTy resTy0 (some ctor) (some ctor0) fields fields0 hsig hres e2 hmo e3
        have e4' : k0 + fields0.length ≤ st3.insts.size := e4
        have hb : k0 + fields.length ≤ st3.insts.size := by omega
        have := instS_expr (nDecl := nDecl) (s := st3) ctor resTy.getAppFn.constLevels! params k0 fields.length hpr hb
        exact satp_okO ⟨hR3', hTr3, this.1, this.2⟩
      · obtain ⟨hrg, hT4⟩ := trInv_pushGroup hTr3 c js fields kinds ty resTy args ctor hjs3 hnd hsig hres hmo
        obtain ⟨hl4, hi4, hk4⟩ := reachC_sizes_mono hrg
        have hb : st3.insts.size + fields.length ≤
            (st3.insts ++ (fields.map fun f => (c, js, f.2)).toArray).size := by
          simp only [Array.size_append, List.size_toArray, List.length_map]; omega
        have := instS_expr (nDecl := nDecl) (s := { st3 with
          insts := st3.insts ++ (fields.map fun f => (c, js, f.2)).toArray
          instFields := st3.instFields ++ (fields.map (·.1)).toArray
          instStruct := true
          instOrigins := st3.instOrigins ++
            ((List.range fields.length).map Sparkle.Compiler.MachInstOrigin.InstOrigin.field).toArray })
          ctor resTy.getAppFn.constLevels! params st3.insts.size fields.length
          (fun q hq => ⟨inRange_mono (hpr q hq).1 hi4 hk4 hl4, (hpr q hq).2⟩) hb
        exact satp_okO ⟨reachC_trans hR3' hrg, hT4, this.1, this.2⟩
  exact key r hv

end Tools.ShippingGen5ReaderTrace
