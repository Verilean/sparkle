import Tools.ShippingGen5Cover6
import Tools.ShippingLetsReaderInvBase
import Tools.ShippingReaderFuelDefs
set_option autoImplicit false
-- Built in Pod build rt3v-1f8d15d6 (exit 0, 722 jobs; approved at 1f8d15d6; Lean content unchanged since 521b3e8a). Totality of NoPh / BvarLt vs the independent specs is the two kernel theorems noPh_eq_exp / bvarLt_eq_exp (checked in ReaderTraceCheck); the 247 samples there only detect mutants. No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R1 (independent part): `NoPh`, `BvarLt`, `NoLoose`, `EnvPh`, `DomPh`, the `FReachC` glue, `convBvar_trace`

Statements follow `scripts/gen5/DG_READERTRACE_FREEZE.md` §2 with the rev1 corrections of `scripts/gen5/DG_READERTRACE_FREEZE_REV1.md`.
`CtlPh` / `TrInv` / `PhPre` / `TraceGood` are NOT defined here (they are the part of the freeze still under review).
`NoLoose d v` is exactly `∀ b, ¬ LooseOcc d v b` (`LooseOcc` does not descend `letE / mdata / proj`).
Not supplied: R-trace for any `readF` call, R-in/R-nl/R-dom for the reader, `TraceGood`, any extern fact (`liftLooseBVars`, `instantiate1`, `rootFloat`). -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

/-- the four placeholder tags -/
def phTag (t : String) : Bool := t == "_machIn" || t == "_machInst" || t == "_machSlot" || t == "_machLet"

/-- recursive placeholder-freeness (descends letE/mdata/proj like `LetOk`; `MentionsPh` does not) -/
def NoPh : Lean.Expr → Bool
  | .fvar ⟨.num (.str .anonymous t) _⟩ => !phTag t
  | .app f a => NoPh f && NoPh a
  | .lam _ t b _ => NoPh t && NoPh b
  | .forallE _ t b _ => NoPh t && NoPh b
  | .letE _ t v b _ => NoPh t && NoPh v && NoPh b
  | .mdata _ e => NoPh e
  | .proj _ _ e => NoPh e
  | _ => true

/-- every loose bvar index of `e` (relative to its root; bound ones are admitted by the `+1` per binder) is `< L`. -/
def BvarLt : Nat → Lean.Expr → Bool
  | L, .bvar j => decide (j < L)
  | L, .app f a => BvarLt L f && BvarLt L a
  | L, .lam _ t b _ => BvarLt L t && BvarLt (L + 1) b
  | L, .forallE _ t b _ => BvarLt L t && BvarLt (L + 1) b
  | L, .letE _ t v b _ => BvarLt L t && BvarLt L v && BvarLt (L + 1) b
  | L, .mdata _ e => BvarLt L e
  | L, .proj _ _ e => BvarLt L e
  | _, _ => true

/-- R-nl atom: no loose bvar of `v` (read at binder depth `d`), exactly the `LooseOcc` meaning. -/
def NoLoose (d : Nat) (v : Lean.Expr) : Prop := ∀ b, ¬ LooseOcc d v b

/-- converted values of the environment are in range of the CURRENT state and loose-free; loop states name existing slots. -/
def EnvPh (nDecl : Nat) (st : MachRead) (env : List MachVal) : Prop :=
  (∀ v, MachVal.val v ∈ env → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) ∧
  (∀ b n, MachVal.state b n ∈ env → b + n ≤ st.kinds.size)

/-- the `dom` conjunct of `CtlPh` (R-dom, loose-free part). -/
def DomPh (nDecl : Nat) (st : MachRead) : Prop :=
  ∀ d, st.dom = some d → InRange nDecl st st.lets.size d ∧ NoLoose 0 d

/-! ## NoLoose / BvarLt / NoPh lemmas -/

theorem noLoose_zero_le {d : Nat} {v : Lean.Expr} (h : NoLoose 0 v) : NoLoose d v := by
  have key : ∀ (e : Lean.Expr) (d0 d : Nat) (b : Nat), LooseOcc (d0 + d) e b → LooseOcc d0 e (b + d) := by
    intro e
    induction e with
    | bvar i => intro d0 d b h; simp only [LooseOcc] at h ⊢; omega
    | app f a ihf iha => intro d0 d b h; rcases h with h | h; exact Or.inl (ihf _ _ _ h); exact Or.inr (iha _ _ _ h)
    | lam _ t e bi iht ihe =>
      intro d0 d b h; rcases h with h | h
      · exact Or.inl (iht _ _ _ h)
      · refine Or.inr ?_
        have := ihe (d0 + 1) d b (by simpa [Nat.add_right_comm] using h)
        exact this
    | forallE _ t e bi iht ihe =>
      intro d0 d b h; rcases h with h | h
      · exact Or.inl (iht _ _ _ h)
      · refine Or.inr ?_
        have := ihe (d0 + 1) d b (by simpa [Nat.add_right_comm] using h)
        exact this
    | _ => intro d0 d b h; simp only [LooseOcc] at h
  intro b hb
  have := key v 0 d b (by simpa using hb)
  exact h _ (by simpa using this)

theorem bvarLt_mono {L L' : Nat} {e : Lean.Expr} (hL : L ≤ L') (h : BvarLt L e = true) : BvarLt L' e = true := by
  induction e generalizing L L' with
  | bvar j => simp only [BvarLt, decide_eq_true_eq] at h ⊢; omega
  | app f a ihf iha =>
    simp only [BvarLt, Bool.and_eq_true] at h ⊢; exact ⟨ihf hL h.1, iha hL h.2⟩
  | lam _ t b _ iht ihb =>
    simp only [BvarLt, Bool.and_eq_true] at h ⊢; exact ⟨iht hL h.1, ihb (by omega) h.2⟩
  | forallE _ t b _ iht ihb =>
    simp only [BvarLt, Bool.and_eq_true] at h ⊢; exact ⟨iht hL h.1, ihb (by omega) h.2⟩
  | letE _ t v b _ iht ihv ihb =>
    simp only [BvarLt, Bool.and_eq_true] at h ⊢; exact ⟨⟨iht hL h.1.1, ihv hL h.1.2⟩, ihb (by omega) h.2⟩
  | mdata _ e ih => simp only [BvarLt] at h ⊢; exact ih hL h
  | proj _ _ e ih => simp only [BvarLt] at h ⊢; exact ih hL h
  | _ => simp [BvarLt]

theorem noPh_letOk (n : Nat) (e : Lean.Expr) (h : NoPh e = true) : LetOk n e = true := by
  induction e with
  | fvar id =>
    simp only [LetOk]
    cases hf : letFv id with
    | none => rfl
    | some j =>
      exfalso
      obtain ⟨n⟩ := id
      have hn : n = .num (.str .anonymous "_machLet") j := by
        unfold letFv at hf; split at hf <;> simp_all
      subst hn
      simp [NoPh, phTag] at h
  | app f a ihf iha => simp only [NoPh, Bool.and_eq_true] at h; simp only [LetOk, Bool.and_eq_true]; exact ⟨ihf h.1, iha h.2⟩
  | lam _ t b _ iht ihb => simp only [NoPh, Bool.and_eq_true] at h; simp only [LetOk, Bool.and_eq_true]; exact ⟨iht h.1, ihb h.2⟩
  | forallE _ t b _ iht ihb => simp only [NoPh, Bool.and_eq_true] at h; simp only [LetOk, Bool.and_eq_true]; exact ⟨iht h.1, ihb h.2⟩
  | letE _ t v b _ iht ihv ihb =>
    simp only [NoPh, Bool.and_eq_true] at h; simp only [LetOk, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | mdata _ e ih => simp only [NoPh] at h; simp only [LetOk]; exact ih h
  | proj _ _ e ih => simp only [NoPh] at h; simp only [LetOk]; exact ih h
  | _ => simp [LetOk]

/-! ## InRange helpers -/

theorem inRange_closed {nDecl k : Nat} {st : MachRead} {e : Lean.Expr}
    (h : ∀ tag i, ¬ MentionsPh tag i e) : InRange nDecl st k e :=
  ⟨fun i hi => absurd hi (h _ _), fun j hj => absurd hj (h _ _), fun i hi => absurd hi (h _ _), fun j hj => absurd hj (h _ _)⟩

theorem inRange_app {nDecl k : Nat} {st : MachRead} {f a : Lean.Expr}
    (hf : InRange nDecl st k f) (ha : InRange nDecl st k a) : InRange nDecl st k (.app f a) :=
  ⟨fun i hi => hi.elim (hf.1 i) (ha.1 i), fun i hi => hi.elim (hf.2.1 i) (ha.2.1 i),
   fun i hi => hi.elim (hf.2.2.1 i) (ha.2.2.1 i), fun i hi => hi.elim (hf.2.2.2 i) (ha.2.2.2 i)⟩

theorem noLoose_app {d : Nat} {f a : Lean.Expr} (hf : NoLoose d f) (ha : NoLoose d a) : NoLoose d (.app f a) :=
  fun b hb => hb.elim (hf b) (ha b)

theorem inRange_machSlot {nDecl k : Nat} {st : MachRead} {i : Nat} (hi : i < st.kinds.size) :
    InRange nDecl st k (machSlot i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj; simp [machSlot, MentionsPh] at hj
  · intro j hj; simp [machSlot, MentionsPh] at hj
  · intro j hj; simp only [machSlot, MentionsPh] at hj; omega
  · intro j hj; simp [machSlot, MentionsPh] at hj

theorem noLoose_fvar {d : Nat} {id : FVarId} : NoLoose d (.fvar id) := fun _ h => h.elim

theorem noLoose_const {d : Nat} {c : Name} {ls : List Level} : NoLoose d (.const c ls) := fun _ h => h.elim

/-! ## State glue (all in-tree) -/

theorem reachC_ws {nDecl : Nat} (st : MachRead) (ws' : Array (Nat × Lean.Expr))
    (h : ∀ w ∈ ws', w.1 < st.kinds.size ∧ InRange nDecl st st.lets.size w.2) : FReachC nDecl st { st with ws := ws' } :=
  .tail (.refl st) (FStep.ws st ws' h)

theorem reachC_letv {nDecl : Nat} (st : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr)
    (h : InRange nDecl st st.lets.size v) : FReachC nDecl st { st with lets := st.lets.push (nm, kd, v) } :=
  .tail (.refl st) (FStep.letv st nm kd v h)

theorem reachC_slots {nDecl : Nat} (st : MachRead) (ks : List MixedGateBinder) (is : List Nat) (ns : List Name) :
    FReachC nDecl st { st with kinds := st.kinds ++ ks.toArray, inits := st.inits ++ is.toArray, names := st.names ++ ns.toArray } :=
  .tail (.refl st) (FStep.slots st ks is ns)

theorem envPh_mono {nDecl : Nat} {st st' : MachRead} {env : List MachVal} (h : EnvPh nDecl st env)
    (hr : FReachC nDecl st st') : EnvPh nDecl st' env := by
  obtain ⟨hl, hi, hk⟩ := reachC_sizes_mono hr
  exact ⟨fun v hv => ⟨inRange_mono (h.1 v hv).1 hi hk hl, (h.1 v hv).2⟩,
    fun b n hbn => Nat.le_trans (h.2 b n hbn) hk⟩

theorem envPh_cons_val {nDecl : Nat} {st : MachRead} {env : List MachVal} {x : Lean.Expr} (h : EnvPh nDecl st env)
    (hx : InRange nDecl st st.lets.size x) (hn : NoLoose 0 x) : EnvPh nDecl st (MachVal.val x :: env) := by
  refine ⟨fun v hv => ?_, fun b n hbn => ?_⟩
  · rcases List.mem_cons.mp hv with hv | hv
    · cases hv; exact ⟨hx, hn⟩
    · exact h.1 v hv
  · rcases List.mem_cons.mp hbn with hv | hv
    · cases hv
    · exact h.2 b n hv

/-! ## `convBvar`: the only creation site of `_machIn` -/

theorem mapM_some_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ x ∈ l, ∃ y, f x = some y ∧ y ∈ ys
  | [], ys, _, x, hx => absurd hx (by simp)
  | a :: l, ys, h, x, hx => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        have h' : ys = b :: bs := by
          simp [hfa, hl] at h
          first | exact h | exact h.symm
        subst h'
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, hfa, List.mem_cons.mpr (Or.inl rfl)⟩
        · obtain ⟨y, hy, hm⟩ := mapM_some_mem f l bs hl x hx
          exact ⟨y, hy, List.mem_cons.mpr (Or.inr hm)⟩

/-- the type of a bundled slot is closed -/
def TyClosed (y : Lean.Expr) : Prop := (∀ tag i, ¬ MentionsPh tag i y) ∧ NoLoose 0 y

theorem tyClosed_bits (w : Nat) : TyClosed (mkApp (.const ``BitVec []) (inlNatLit w)) := by
  refine ⟨fun tag i h => ?_, fun b h => ?_⟩
  · simp [inlNatLit, mkApp3, mkApp, MentionsPh] at h
  · simp [inlNatLit, mkApp3, mkApp, LooseOcc] at h

theorem tyClosed_bool : TyClosed (.const ``Bool []) :=
  ⟨fun _ _ h => h.elim, fun _ h => h.elim⟩

/-- `bundleSlots` on in-range slots and closed types gives an in-range, loose-free pair. -/
theorem bundleSlots_ph {nDecl : Nat} {st : MachRead} {dom : Lean.Expr}
    (hdom : InRange nDecl st st.lets.size dom) (hdn : NoLoose 0 dom) :
    ∀ (is : List Nat) (ts : List Lean.Expr) (e t : Lean.Expr),
      (∀ i ∈ is, i < st.kinds.size) → (∀ y ∈ ts, TyClosed y) →
      bundleSlots dom is ts = some (e, t) →
      InRange nDecl st st.lets.size e ∧ NoLoose 0 e ∧ TyClosed t
  | [], _, _, _, _, _, h => by simp [bundleSlots] at h
  | [i], [t0], e, t, hi, ht, h => by
    simp only [bundleSlots, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨inRange_machSlot (hi i (by simp)), fun _ hb => hb.elim, ht _ (by simp)⟩
  | [_], [], _, _, _, _, h => by simp [bundleSlots] at h
  | [_], _ :: _ :: _, _, _, _, _, h => by simp [bundleSlots] at h
  | i :: i2 :: is, [], _, _, _, _, h => by simp [bundleSlots] at h
  | i :: i2 :: is, t0 :: ts, e, t, hi, ht, h => by
    simp only [bundleSlots] at h
    cases hr : bundleSlots dom (i2 :: is) ts with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨rest, restT⟩ := p
      simp only [hr, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hr1, hr2, hr3⟩ := bundleSlots_ph hdom hdn (i2 :: is) ts rest restT
        (fun k hk => hi k (List.mem_cons.mpr (Or.inr hk))) (fun y hy => ht y (List.mem_cons.mpr (Or.inr hy))) hr
      have ht0 : TyClosed t0 := ht t0 (List.mem_cons.mpr (Or.inl rfl))
      have hslot : InRange nDecl st st.lets.size (machSlot i) := inRange_machSlot (hi i (by simp))
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine inRange_app (inRange_app (inRange_app (inRange_app (inRange_app (inRange_closed (fun _ _ h => h.elim)) hdom)
          (inRange_closed ht0.1)) (inRange_closed hr3.1)) hslot) hr1
      · exact noLoose_app (noLoose_app (noLoose_app (noLoose_app (noLoose_app (fun _ h => h.elim) hdn) ht0.2) hr3.2)
          (fun _ h => h.elim)) hr2
      · exact fun tag j h => by
          simp only [mkApp2, mkApp, MentionsPh] at h
          rcases h with (h | h) | h
          · exact h.elim
          · exact ht0.1 _ _ h
          · exact hr3.1 _ _ h
      · exact fun b hb => by
          simp only [mkApp2, mkApp, LooseOcc] at hb
          rcases hb with (hb | hb) | hb
          · exact hb.elim
          · exact ht0.2 b hb
          · exact hr3.2 b hb

/-- the slot-type map of `convBvar`'s bundle arm (its local `tyOf`) -/
def tyOfK (kd : MixedGateBinder) : Option Lean.Expr :=
  match kd with
  | .bits w => some (mkApp (.const ``BitVec []) (inlNatLit w))
  | .bool => some (.const ``Bool [])
  | .domain => none

theorem mapM_kinds_ok (st : MachRead) : ∀ (l : List Nat) (tys : List Lean.Expr),
    l.mapM (fun i => st.kinds[i]? >>= tyOfK) = some tys →
    (∀ i ∈ l, i < st.kinds.size) ∧ ∀ y ∈ tys, TyClosed y
  | [], tys, h => by
    rw [List.mapM_nil] at h
    have h' : [] = tys := Option.some.inj h
    subst h'
    exact ⟨fun i hi => absurd hi (by simp), fun y hy => absurd hy (by simp)⟩
  | a :: l, tys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y0, hy0, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys, hys, h⟩ := Option.bind_eq_some_iff.mp h
    have h' : y0 :: ys = tys := Option.some.inj h
    subst h'
    obtain ⟨ih1, ih2⟩ := mapM_kinds_ok st l ys hys
    obtain ⟨kd, hk, hty⟩ := Option.bind_eq_some_iff.mp hy0
    obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hk
    have hy0c : TyClosed y0 := by
      cases kd with
      | bits w => simp only [tyOfK, Option.some.injEq] at hty; subst hty; exact tyClosed_bits w
      | bool => simp only [tyOfK, Option.some.injEq] at hty; subst hty; exact tyClosed_bool
      | domain => simp [tyOfK] at hty
    refine ⟨fun i hi => ?_, fun y hy => ?_⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact hlt
      · exact ih1 i hi
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hy0c
      · exact ih2 y hy

/-- the `.state b n` (`n ≠ 1`) arm of `convBvar`, as its own statement -/
theorem convBvar_bundle {nDecl : Nat} {st : MachRead} {b n : Nat} {r : Lean.Expr × MachRead}
    (hD : DomPh nDecl st)
    (h : (do
      let dom ← st.dom
      let tyOf (k : MixedGateBinder) : Option Lean.Expr := match k with
        | .bits w => some (mkApp (.const ``BitVec []) (inlNatLit w))
        | .bool => some (.const ``Bool [])
        | .domain => none
      let tys ← ((List.range n).map (b + ·)).mapM fun i => st.kinds[i]? >>= tyOf
      let (e, _) ← bundleSlots dom ((List.range n).map (b + ·)) tys
      some (e, st) : Option (Lean.Expr × MachRead)) = some r) :
    r.2 = st ∧ InRange nDecl st st.lets.size r.1 ∧ NoLoose 0 r.1 := by
  obtain ⟨dm, hdom, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tys, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨p, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hidx, hty⟩ := mapM_kinds_ok st _ tys hm
  obtain ⟨hdr, hdn⟩ := hD dm hdom
  obtain ⟨e, t⟩ := p
  obtain ⟨h1, h2, _⟩ := bundleSlots_ph hdr hdn _ tys e t hidx hty hb
  have hr : r = (e, st) := (Option.some.inj h).symm
  subst hr
  exact ⟨rfl, h1, h2⟩

theorem inRange_machIn {nDecl k : Nat} {st : MachRead} {i : Nat} (hi : i < nDecl) :
    InRange nDecl st k (machIn i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj; simp only [machIn, MentionsPh] at hj; omega
  · intro j hj; simp [machIn, MentionsPh] at hj
  · intro j hj; simp [machIn, MentionsPh] at hj
  · intro j hj; simp [machIn, MentionsPh] at hj

theorem inRange_machLet {nDecl k : Nat} {st : MachRead} {j : Nat} (hj : j < k) :
    InRange nDecl st k (machLet j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi; simp [machLet, MentionsPh] at hi
  · intro i hi; simp [machLet, MentionsPh] at hi
  · intro i hi; simp [machLet, MentionsPh] at hi
  · intro i hi; simp only [machLet, MentionsPh] at hi; omega

theorem convBvar_trace {nDecl : Nat} {env : List MachVal} {d j : Nat} {st : MachRead}
    {r : Lean.Expr × MachRead} (hE : EnvPh nDecl st env) (hD : DomPh nDecl st)
    (hb : BvarLt (d + env.length + nDecl) (Lean.Expr.bvar j) = true) (h : convBvar env d j st = some r) :
    r.2 = st ∧ InRange nDecl st st.lets.size r.1 ∧ NoLoose d r.1 := by
  unfold convBvar at h
  by_cases hj : j < d
  · rw [if_pos hj] at h
    cases h
    refine ⟨rfl, inRange_closed (fun tag i hh => by simp [MentionsPh] at hh), fun b hb => ?_⟩
    simp only [LooseOcc] at hb; omega
  · rw [if_neg hj] at h
    rcases hget : env[j - d]? with _ | m
    · simp only [hget] at h
      cases h
      have hlen : env.length ≤ j - d := List.getElem?_eq_none_iff.mp hget
      simp only [BvarLt, decide_eq_true_eq] at hb
      exact ⟨rfl, inRange_machIn (by omega), fun _ hh => (hh : False)⟩
    · cases m with
      | val v =>
        simp only [hget] at h
        cases h
        have hv := hE.1 v (List.mem_of_getElem? hget)
        exact ⟨rfl, hv.1, noLoose_zero_le hv.2⟩
      | state b n =>
        rcases n with _ | _ | n
        · simp only [hget] at h
          obtain ⟨a1, a2, a3⟩ := convBvar_bundle hD h
          exact ⟨a1, a2, noLoose_zero_le a3⟩
        · simp only [hget] at h
          cases h
          have := hE.2 b (0 + 1) (List.mem_of_getElem? hget)
          exact ⟨rfl, inRange_machSlot (by omega), fun _ hh => (hh : False)⟩
        · simp only [hget] at h
          obtain ⟨a1, a2, a3⟩ := convBvar_bundle hD h
          exact ⟨a1, a2, noLoose_zero_le a3⟩
      | regs p => simp [hget] at h
      | handle i => simp [hget] at h
      | unit => simp [hget] at h

/-! ## `machBindLet`: the returned placeholder and the extended table -/

theorem bindLet_reach {nDecl : Nat} {st : MachRead} {nm : Name} {ty v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    FReachC nDecl st { st with lets := (machBindLet nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (machBindLet nm ty v' st.lets).2 } (machBindLet nm ty v' st.lets).2.size
      (machBindLet nm ty v' st.lets).1 ∧
    NoLoose 0 (machBindLet nm ty v' st.lets).1 := by
  unfold machBindLet
  split
  · exact ⟨FReachC.refl st, h, hn⟩
  · exact ⟨FReachC.refl st, h, hn⟩
  · split
    · exact ⟨FReachC.refl st, h, hn⟩
    · split
      · next j hj =>
        exact ⟨FReachC.refl st, inRange_machLet (Array.findIdx?_eq_some_iff_getElem.mp hj).1, fun _ hh => (hh : False)⟩
      · refine ⟨reachC_letv st _ _ v' h, ?_, fun _ hh => (hh : False)⟩
        simp only [Array.size_push]
        exact inRange_machLet (Nat.lt_succ_self _)

end Tools.ShippingGen5ReaderTrace
