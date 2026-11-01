import Tools.ShippingGen5Cover3
set_option autoImplicit false
-- Built in gdw3e at cd4df277 (Pod `kjob lake build Tools.ShippingGen5Cover3Canon`, exit 0, no warning from this file). Clean build is the coder's. No sorry / axiom / native_decide in source. Units: `scripts/gen5/CV1_CANON_FREEZE.md` §1/§3/§4 ((a1)-(a3), (b), rowC_of_reader_canon); not here: letQuoteEqC_witness, production fuel, loop paths 2/3.

namespace Tools.ShippingGen5Cover3Canon
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
  Tools.ShippingGen5Cover2 Tools.ShippingGen5Sem Tools.ShippingGen5Cover Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto

theorem inlCanonLam_looseOcc (k d : Nat) (e : Lean.Expr) (b : Nat) :
    LooseOcc d (inlCanonLam k e) b ↔ LooseOcc d e b := by
  induction e generalizing k d with
  | lam n t body bi iht ihb => simp only [inlCanonLam, LooseOcc, ihb]
  | _ => simp [inlCanonLam]

theorem inlCanonPi_looseOcc (d : Nat) (e : Lean.Expr) (b : Nat) :
    LooseOcc d (inlCanonPi e) b ↔ LooseOcc d e b := by
  induction e generalizing d with
  | forallE n t body bi iht ihb => simp only [inlCanonPi, LooseOcc, ihb]
  | _ => simp [inlCanonPi]

theorem looseOcc_machCanonApNode (d : Nat) (e : Lean.Expr) (b : Nat) :
    LooseOcc d (machCanonApNode e) b ↔ LooseOcc d e b := by
  unfold machCanonApNode
  split
  · simp only [LooseOcc, inlCanonPi_looseOcc, inlCanonLam_looseOcc]
  · exact Iff.rfl

theorem looseOcc_machCanonAp (d : Nat) (e : Lean.Expr) (b : Nat) :
    LooseOcc d (machCanonAp e) b ↔ LooseOcc d e b := by
  induction e generalizing d with
  | app f a ihf iha =>
    simp only [machCanonAp, looseOcc_machCanonApNode, LooseOcc, ihf, iha]
  | _ => simp [machCanonAp]


/-! ## (b) `readsOfQuoteStmtC` -/

def ReadsOfQuoteStmtC : Prop :=
  ∀ (dom : Lean.Expr) (nDecl kI n k : Nat) (bpos vpos : Nat → Nat) (okP : Nat → Bool)
    {s : SType} (t : Term s) (v : Lean.Expr),
    PhInRange nDecl kI n k v →
    (∀ j, bpos j < nDecl + kI + n + k) → (∀ j, vpos j < nDecl + kI + n + k) →
    (∀ b, ¬ LooseOcc 0 v b) →
    quote dom (fun j => inputExpr (nDecl + kI + n + k) (bpos j))
      (fun j => inputExpr (nDecl + kI + n + k) (vpos j)) t = machCanonAp (machClose kI n k 0 v) →
    (∀ p, MentionPos nDecl kI n k v p → okP p = true) →
    Tools.ShippingMachineRef.reads (fun j => okP (bpos j)) (fun j => okP (vpos j)) t = true

theorem readsOfQuoteStmtC : ReadsOfQuoteStmtC := by
  intro dom nDecl kI n k bpos vpos okP s t v hr hb hv hn hq hm
  have key := reads_of_quote_loose dom (fun j => nDecl + kI + n + k - 1 - bpos j)
    (fun j => nDecl + kI + n + k - 1 - vpos j) (fun b => okP (nDecl + kI + n + k - 1 - b)) t ?_
  · have e1 : (fun j => okP (nDecl + kI + n + k - 1 - (nDecl + kI + n + k - 1 - bpos j))) = fun j => okP (bpos j) := by
      funext j; have := hb j; congr 1; omega
    have e2 : (fun j => okP (nDecl + kI + n + k - 1 - (nDecl + kI + n + k - 1 - vpos j))) = fun j => okP (vpos j) := by
      funext j; have := hv j; congr 1; omega
    simp only [e1, e2] at key
    exact key
  · intro b hl
    have hl' : LooseOcc 0 (machClose kI n k 0 v) b := by
      have h1 : LooseOcc 0 (machCanonAp (machClose kI n k 0 v)) b := by
        rw [← hq]; exact hl
      exact (looseOcc_machCanonAp 0 _ b).1 h1
    obtain ⟨p, hp, hbp⟩ := looseOcc_machClose nDecl kI n k 0 v b hn hr hl'
    have hlt := mentionPos_lt hp
    have : nDecl + kI + n + k - 1 - b = p := by omega
    simp only [this]
    exact hm p hp

/-! ## (a) commutation -/

theorem machClose_eq_app {kI n k d : Nat} {x a b : Lean.Expr} (h : machClose kI n k d x = .app a b) :
    ∃ x1 x2, x = .app x1 x2 ∧ machClose kI n k d x1 = a ∧ machClose kI n k d x2 = b := by
  cases x with
  | app f a' => exact ⟨f, a', rfl, by simpa [machClose] using h⟩
  | fvar i =>
    exfalso
    unfold machClose at h
    split at h <;> simp_all
  | _ => simp [machClose] at h

theorem machClose_eq_const {kI n k d : Nat} {x : Lean.Expr} {c : Name} {ls : List Level}
    (h : machClose kI n k d x = .const c ls) : x = .const c ls := by
  cases x with
  | fvar i =>
    exfalso
    unfold machClose at h
    split at h <;> simp_all
  | _ => simp [machClose] at h <;> simp_all

theorem machClose_inlCanonLam (kI n k : Nat) (e : Lean.Expr) :
    ∀ d j, machClose kI n k d (inlCanonLam j e) = inlCanonLam j (machClose kI n k d e) := by
  induction e with
  | lam nm t b bi iht ihb => intro d j; simp [inlCanonLam, machClose, ihb]
  | fvar i => intro d j; simp only [inlCanonLam]; unfold machClose; split <;> simp_all [inlCanonLam]
  | _ => intro d j; simp [inlCanonLam, machClose]

theorem machClose_inlCanonPi (kI n k : Nat) (e : Lean.Expr) :
    ∀ d, machClose kI n k d (inlCanonPi e) = inlCanonPi (machClose kI n k d e) := by
  induction e with
  | forallE nm t b bi iht ihb => intro d; simp [inlCanonPi, machClose, ihb]
  | fvar i => intro d; simp only [inlCanonPi]; unfold machClose; split <;> simp_all [inlCanonPi]
  | _ => intro d; simp [inlCanonPi, machClose]

theorem machCanonApNode_machClose (kI n k d : Nat) (x y : Lean.Expr) :
    machCanonApNode (.app (machClose kI n k d x) (machClose kI n k d y))
      = machClose kI n k d (machCanonApNode (.app x y)) := by
  unfold machCanonApNode
  split
  · rename_i ls dom α β ls' dom' α' γ fn x' b heq
    obtain ⟨hx, rfl⟩ := Expr.app.inj heq
    obtain ⟨x1, xm, rfl, hx1, hxm⟩ := machClose_eq_app hx
    obtain ⟨x11, xb, rfl, hx11, rfl⟩ := machClose_eq_app hx1
    obtain ⟨x111, xa, rfl, hx111, rfl⟩ := machClose_eq_app hx11
    obtain ⟨xc, xd, rfl, hxc, rfl⟩ := machClose_eq_app hx111
    obtain rfl := machClose_eq_const hxc
    obtain ⟨m1, xx, rfl, hm1, rfl⟩ := machClose_eq_app hxm
    obtain ⟨m2, xfn, rfl, hm2, rfl⟩ := machClose_eq_app hm1
    obtain ⟨m3, xg, rfl, hm3, rfl⟩ := machClose_eq_app hm2
    obtain ⟨m4, xa', rfl, hm4, rfl⟩ := machClose_eq_app hm3
    obtain ⟨m5, xd', rfl, hm5, rfl⟩ := machClose_eq_app hm4
    obtain rfl := machClose_eq_const hm5
    simp [mkApp5, mkApp4, mkApp, mkAppB, machClose, machClose_inlCanonPi, machClose_inlCanonLam]
  · rename_i hne
    split
    · rename_i ls dom α β ls' dom' α' γ fn x' b heq
      obtain ⟨rfl, rfl⟩ := Expr.app.inj heq
      exact (hne ls (machClose kI n k d dom) (machClose kI n k d α) (machClose kI n k d β) ls'
        (machClose kI n k d dom') (machClose kI n k d α') (machClose kI n k d γ) (machClose kI n k d fn)
        (machClose kI n k d x') (machClose kI n k d y) (by simp [machClose])).elim
    · simp [machClose]


theorem machCanonAp_machClose (kI n k d : Nat) (e : Lean.Expr) :
    machCanonAp (machClose kI n k d e) = machClose kI n k d (machCanonAp e) := by
  induction e generalizing d with
  | app f a ihf iha =>
    simp only [machClose, machCanonAp, ihf, iha]
    exact machCanonApNode_machClose kI n k d _ _
  | fvar i => unfold machClose; split <;> simp_all [machCanonAp]
  | lam nm t b bi iht ihb => simp [machClose, machCanonAp]
  | forallE nm t b bi iht ihb => simp [machClose, machCanonAp]
  | _ => simp [machClose, machCanonAp]


theorem machCanonAp_natLit (n : Nat) : machCanonAp (inlNatLit n) = inlNatLit n := by
  simp [inlNatLit, mkApp3, mkApp, mkAppB, machCanonAp, machCanonApNode]

theorem machCanonAp_machLitE (dom : Lean.Expr) (hdom : machCanonAp dom = dom) (k v : Nat) :
    machCanonAp (machLitE dom k v) = machLitE dom k v := by
  simp [machLitE, mkApp3, mkApp2, mkApp, mkAppB, machCanonAp, machCanonApNode, hdom, machCanonAp_natLit]

theorem machCanonAp_machBoolBits (dom : Lean.Expr) (hdom : machCanonAp dom = dom) (e : Lean.Expr) :
    machCanonAp (machBoolBits dom e) = machBoolBits dom (machCanonAp e) := by
  simp [machBoolBits, machLitE, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB, machCanonAp, machCanonApNode, hdom, machCanonAp_natLit]

theorem machCanonAp_machConcatE (dom : Lean.Expr) (hdom : machCanonAp dom = dom) (m n : Nat) (a b : Lean.Expr) :
    machCanonAp (machConcatE dom m n a b) = machConcatE dom m n (machCanonAp a) (machCanonAp b) := by
  simp [machConcatE, machSigT, mkApp6, mkApp4, mkApp3, mkApp2, mkApp, mkAppB, machCanonAp, machCanonApNode, hdom, machCanonAp_natLit]


theorem machCanonAp_machField (dom : Lean.Expr) (hdom : machCanonAp dom = dom)
    (kd : MixedGateBinder) (e : Lean.Expr) :
    (machField dom kd e).map (fun p => (p.1, machCanonAp p.2)) = machField dom kd (machCanonAp e) := by
  cases kd <;> simp [machField, machCanonAp_machBoolBits dom hdom]

theorem machCanonAp_machPack (dom : Lean.Expr) (hdom : machCanonAp dom = dom)
    (fs : List (Nat × Lean.Expr)) :
    (machPack dom fs).map (fun p => (p.1, machCanonAp p.2)) = machPack dom (fs.map fun p => (p.1, machCanonAp p.2)) := by
  induction fs with
  | nil => simp [machPack]
  | cons f rest ih =>
    obtain ⟨m, a⟩ := f
    cases rest with
    | nil => simp [machPack]
    | cons r rs =>
      simp only [List.map_cons] at ih ⊢
      simp only [machPack]
      rw [← ih]
      cases hp : machPack dom (r :: rs) with
      | none => simp
      | some p =>
        obtain ⟨n, b⟩ := p
        simp [machCanonAp_machConcatE dom hdom]

def LetQuoteEqC (d : MachineData) (st : MachRead) : Prop :=
  ∀ (j : Nat) (hj : j < d.ls.length) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i))
                (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.vpos i)) (d.ls[j]'hj).2
      = machCanonAp (machClose st.insts.size st.kinds.size st.lets.size 0 v)


theorem rowC_of_reader_canon {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hqC : LetQuoteEqC d st) (hnl : LetsNoLoose st)
    (hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length) :
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true := by
  intro k hk l0 hl0
  obtain ⟨c, js, r, hd, hs⟩ := entry_of_agree hag hk
  rw [callArgs_of hd] at hl0
  obtain ⟨hC, hR, hO, hK⟩ := hi
  have hnin := kDOf_add_len d hag.nIn
  have hlenI : d.shape.insts.length = st.insts.size := by rw [hag.insts]; simp
  have hss : d.ss.length = st.kinds.size := hag.slots
  have hll : d.ls.length = st.lets.size := hag.lets
  have hsum : kDOf d + st.insts.size + st.kinds.size + st.lets.size = d.nIn + d.ss.length + d.ls.length := by omega
  have key : ∀ l, LetReach st.lets l0 l → (cleanLets d k)[l]? = some true := by
    intro l
    induction l using Nat.strongRecOn with
    | _ l ih =>
      intro hr
      have hlt : l < st.lets.size := letReach_lt st.lets hC.1 hr (hC.2.2.1 k c js r hs l0 hl0)
      have hldl : l < d.ls.length := by omega
      obtain ⟨nm, kd, v, hv_l⟩ : ∃ nm kd v, st.lets[l]? = some (nm, kd, v) := by
        cases hg : st.lets[l]? with
        | none => rw [Array.getElem?_eq_getElem hlt] at hg; simp at hg
        | some x => exact ⟨x.1, x.2.1, x.2.2, rfl⟩
      rw [cleanLets_getElem d k l hldl]
      simp only [Option.some.injEq]
      refine readsOfQuoteStmtC d.dom (kDOf d) st.insts.size st.kinds.size st.lets.size d.bpos d.vpos
        (posOk d k ((cleanLets d k).take l)) (d.ls[l]'hldl).2 v
        (phInRange_mono (hR.1 l nm kd v hv_l) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_of_lt hlt))
        (fun j => by have := hb j; omega) (fun j => by have := hv j; omega) (hnl l nm kd v hv_l)
        (hqC l hldl nm kd v hv_l) ?_
      intro p hp
      simp only [posOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      rcases hp with ⟨i, hi', hm, hp⟩ | ⟨m, hm', hm, hp⟩ | ⟨i, hi', hm, hp⟩ | ⟨j, hj', hm, hp⟩
      · exact Or.inl (Or.inl (by omega))
      · have := hC.2.2.2 k c js r hs l0 hl0 l hr nm kd v hv_l m hm
        exact Or.inl (Or.inl (by omega))
      · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
      · have hedge : LetEdge st.lets l j := ⟨nm, kd, v, hv_l, hm⟩
        have hjl : j < l := hC.1 l nm kd v hv_l j hm
        have ihj := ih j hjl (letReach_edge hr hedge)
        refine Or.inr ⟨by omega, ?_⟩
        have e : p - (d.nIn + d.ss.length) = j := by omega
        rw [e, getD_take_of_lt _ hjl, getD_true_iff]
        exact ihj
  exact key l0 (LetReach.refl l0)


end Tools.ShippingGen5Cover3Canon
