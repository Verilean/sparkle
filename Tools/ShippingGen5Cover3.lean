import Tools.ShippingGen5Cover2
import Tools.ShippingGen5Cover
set_option autoImplicit false
-- NOT BUILT (g5cv-r6 work in progress).

/-! # DG-COVER rev4 units U-D1 / U-D2 / U-D3, `scripts/gen5/DG_COVER_FREEZE_REV4.md` §1–§3

U-D1: `ReadsOfQuoteStmt` proved (transport only; its premise `quote … = machClose …` is Q-wit and is not supplied here).
U-D2: `FullInv`/`FStep`/`FReach` preservation and range suppliers (abstract step closure, NOT a trace of the real reader).
U-D3: RowA/B/C from the invariants with the interface premises (`ShapeAgree`, `LetQuoteEq`, `LetsNoLoose`, `hb/hv`, …) named and unsupplied.

Not supplied: R-trace, R-in, R-nl, R-dom, B3, Q rows, any run, `dataOf`, `GenWF` on real data, M5, FG. -/

namespace Tools.ShippingGen5Cover3
open Lean Sparkle.Compiler.Elab Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Tools.ShippingGen5Cover2
  Tools.ShippingGen5Sem Tools.ShippingGen5Cover Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto

/-! ## U-D1 definitions (freeze rev4 §1, verbatim from `CoverNegCheck`) -/

def MentionPos (nDecl kI n k : Nat) (v : Lean.Expr) (p : Nat) : Prop :=
  (∃ i, i < nDecl ∧ MentionsPh "_machIn" i v ∧ p = nDecl - 1 - i) ∨
  (∃ j, j < kI ∧ MentionsPh "_machInst" j v ∧ p = nDecl + j) ∨
  (∃ i, i < n ∧ MentionsPh "_machSlot" i v ∧ p = nDecl + kI + i) ∨
  (∃ j, j < k ∧ MentionsPh "_machLet" j v ∧ p = nDecl + kI + n + j)

def LooseOcc : Nat → Lean.Expr → Nat → Prop
  | d, .bvar i, b => i = b + d
  | d, .app f a, b => LooseOcc d f b ∨ LooseOcc d a b
  | d, .lam _ t e _, b => LooseOcc d t b ∨ LooseOcc (d + 1) e b
  | d, .forallE _ t e _, b => LooseOcc d t b ∨ LooseOcc (d + 1) e b
  | _, _, _ => False

def ReadsOfQuoteStmt : Prop :=
  ∀ (dom : Lean.Expr) (nDecl kI n k : Nat) (bpos vpos : Nat → Nat) (okP : Nat → Bool)
    {s : SType} (t : Term s) (v : Lean.Expr),
    PhInRange nDecl kI n k v →
    (∀ j, bpos j < nDecl + kI + n + k) → (∀ j, vpos j < nDecl + kI + n + k) →
    (∀ b, ¬ LooseOcc 0 v b) →
    quote dom (fun j => inputExpr (nDecl + kI + n + k) (bpos j))
      (fun j => inputExpr (nDecl + kI + n + k) (vpos j)) t = machClose kI n k 0 v →
    (∀ p, MentionPos nDecl kI n k v p → okP p = true) →
    Tools.ShippingMachineRef.reads (fun j => okP (bpos j)) (fun j => okP (vpos j)) t = true

/-! ## Sub-expression monotonicity -/

theorem phInRange_of_sub {nDecl kI n k : Nat} {v w : Lean.Expr}
    (h : ∀ tag i, MentionsPh tag i w → MentionsPh tag i v) (hv : PhInRange nDecl kI n k v) :
    PhInRange nDecl kI n k w :=
  ⟨fun i hi => hv.1 i (h _ _ hi), fun i hi => hv.2.1 i (h _ _ hi),
   fun i hi => hv.2.2.1 i (h _ _ hi), fun i hi => hv.2.2.2 i (h _ _ hi)⟩

theorem mentionPos_of_sub {nDecl kI n k : Nat} {v w : Lean.Expr}
    (h : ∀ tag i, MentionsPh tag i w → MentionsPh tag i v) {p : Nat}
    (hp : MentionPos nDecl kI n k w p) : MentionPos nDecl kI n k v p := by
  rcases hp with ⟨i, hi, hm, hp⟩ | ⟨i, hi, hm, hp⟩ | ⟨i, hi, hm, hp⟩ | ⟨i, hi, hm, hp⟩
  · exact Or.inl ⟨i, hi, h _ _ hm, hp⟩
  · exact Or.inr (Or.inl ⟨i, hi, h _ _ hm, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, h _ _ hm, hp⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, h _ _ hm, hp⟩))

theorem sub_app_l (f a : Lean.Expr) : ∀ tag i, MentionsPh tag i f → MentionsPh tag i (.app f a) := fun _ _ h => Or.inl h
theorem sub_app_r (f a : Lean.Expr) : ∀ tag i, MentionsPh tag i a → MentionsPh tag i (.app f a) := fun _ _ h => Or.inr h
theorem sub_lam_t (nm : Name) (t e : Lean.Expr) (bi : BinderInfo) : ∀ tag i, MentionsPh tag i t → MentionsPh tag i (.lam nm t e bi) := fun _ _ h => Or.inl h
theorem sub_lam_e (nm : Name) (t e : Lean.Expr) (bi : BinderInfo) : ∀ tag i, MentionsPh tag i e → MentionsPh tag i (.lam nm t e bi) := fun _ _ h => Or.inr h
theorem sub_all_t (nm : Name) (t e : Lean.Expr) (bi : BinderInfo) : ∀ tag i, MentionsPh tag i t → MentionsPh tag i (.forallE nm t e bi) := fun _ _ h => Or.inl h
theorem sub_all_e (nm : Name) (t e : Lean.Expr) (bi : BinderInfo) : ∀ tag i, MentionsPh tag i e → MentionsPh tag i (.forallE nm t e bi) := fun _ _ h => Or.inr h

/-! ## `looseOcc_machClose` -/

theorem looseOcc_machClose (nDecl kI n k : Nat) :
    ∀ (v : Lean.Expr) (d : Nat) (b : Nat), (∀ b', ¬ LooseOcc d v b') → PhInRange nDecl kI n k v →
      LooseOcc d (machClose kI n k d v) b →
      ∃ p, MentionPos nDecl kI n k v p ∧ b = nDecl + kI + n + k - 1 - p := by
  intro v
  induction v with
  | app f a ihf iha =>
    intro d b hn hr hl
    simp only [machClose, LooseOcc] at hl
    rcases hl with hl | hl
    · obtain ⟨p, hp, hb⟩ := ihf d b (fun b' h => hn b' (Or.inl h))
        (phInRange_of_sub (sub_app_l f a) hr) hl
      exact ⟨p, mentionPos_of_sub (sub_app_l f a) hp, hb⟩
    · obtain ⟨p, hp, hb⟩ := iha d b (fun b' h => hn b' (Or.inr h))
        (phInRange_of_sub (sub_app_r f a) hr) hl
      exact ⟨p, mentionPos_of_sub (sub_app_r f a) hp, hb⟩
  | lam nm t e bi iht ihe =>
    intro d b hn hr hl
    simp only [machClose, LooseOcc] at hl
    rcases hl with hl | hl
    · obtain ⟨p, hp, hb⟩ := iht d b (fun b' h => hn b' (Or.inl h))
        (phInRange_of_sub (sub_lam_t nm t e bi) hr) hl
      exact ⟨p, mentionPos_of_sub (sub_lam_t nm t e bi) hp, hb⟩
    · obtain ⟨p, hp, hb⟩ := ihe (d + 1) b (fun b' h => hn b' (Or.inr h))
        (phInRange_of_sub (sub_lam_e nm t e bi) hr) hl
      exact ⟨p, mentionPos_of_sub (sub_lam_e nm t e bi) hp, hb⟩
  | forallE nm t e bi iht ihe =>
    intro d b hn hr hl
    simp only [machClose, LooseOcc] at hl
    rcases hl with hl | hl
    · obtain ⟨p, hp, hb⟩ := iht d b (fun b' h => hn b' (Or.inl h))
        (phInRange_of_sub (sub_all_t nm t e bi) hr) hl
      exact ⟨p, mentionPos_of_sub (sub_all_t nm t e bi) hp, hb⟩
    · obtain ⟨p, hp, hb⟩ := ihe (d + 1) b (fun b' h => hn b' (Or.inr h))
        (phInRange_of_sub (sub_all_e nm t e bi) hr) hl
      exact ⟨p, mentionPos_of_sub (sub_all_e nm t e bi) hp, hb⟩
  | bvar i =>
    intro d b hn hr hl
    have := hn b
    simp only [machClose, LooseOcc] at hl this
    exact absurd hl this
  | fvar id =>
    intro d b hn hr hl
    rcases id with ⟨nm⟩
    unfold machClose at hl
    split at hl
    · rename_i d0 _ _ i heq
      simp only [Expr.fvar.injEq, FVarId.mk.injEq] at heq
      subst heq
      simp only [LooseOcc] at hl
      have hi : i < nDecl := hr.1 i ⟨rfl, rfl⟩
      exact ⟨nDecl - 1 - i, Or.inl ⟨i, hi, ⟨rfl, rfl⟩, rfl⟩, by omega⟩
    · rename_i d0 _ _ j heq
      simp only [Expr.fvar.injEq, FVarId.mk.injEq] at heq
      subst heq
      simp only [LooseOcc] at hl
      have hj : j < kI := hr.2.1 j ⟨rfl, rfl⟩
      exact ⟨nDecl + j, Or.inr (Or.inl ⟨j, hj, ⟨rfl, rfl⟩, rfl⟩), by omega⟩
    · rename_i d0 _ _ i heq
      simp only [Expr.fvar.injEq, FVarId.mk.injEq] at heq
      subst heq
      simp only [LooseOcc] at hl
      have hi : i < n := hr.2.2.1 i ⟨rfl, rfl⟩
      exact ⟨nDecl + kI + i, Or.inr (Or.inr (Or.inl ⟨i, hi, ⟨rfl, rfl⟩, rfl⟩)), by omega⟩
    · rename_i d0 _ _ j heq
      simp only [Expr.fvar.injEq, FVarId.mk.injEq] at heq
      subst heq
      simp only [LooseOcc] at hl
      have hj : j < k := hr.2.2.2 j ⟨rfl, rfl⟩
      exact ⟨nDecl + kI + n + j, Or.inr (Or.inr (Or.inr ⟨j, hj, ⟨rfl, rfl⟩, rfl⟩)), by omega⟩
    · rename_i _ _ _ _ _ heq; cases heq
    · rename_i _ _ _ _ _ _ _ heq; cases heq
    · rename_i _ _ _ _ _ _ _ heq; cases heq
    · simp [LooseOcc] at hl
  | _ =>
    intro d b hn hr hl
    simp [machClose, LooseOcc] at hl

/-! ## Operand occurrence lemmas: every operand of a quote helper is an application argument at binder depth 0 -/

theorem lo_app_l {f a : Lean.Expr} {x : Nat} (h : LooseOcc 0 f x) : LooseOcc 0 (.app f a) x := Or.inl h
theorem lo_app_r {f a : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) : LooseOcc 0 (.app f a) x := Or.inr h

theorem lo_binE_a {dom : Lean.Expr} {n : Nat} {op} {a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (Tools.ShippingEntrySoundness.binE dom n op a b) x := lo_app_l (lo_app_r h)
theorem lo_binE_b {dom : Lean.Expr} {n : Nat} {op} {a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 b x) :
    LooseOcc 0 (Tools.ShippingEntrySoundness.binE dom n op a b) x := lo_app_r h

theorem lo_compareE_a {kind} {dom : Lean.Expr} {n : Nat} {a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (Tools.ShippingBoolSourceSoundness.compareE kind dom n a b) x := lo_app_l (lo_app_r h)
theorem lo_compareE_b {kind} {dom : Lean.Expr} {n : Nat} {a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 b x) :
    LooseOcc 0 (Tools.ShippingBoolSourceSoundness.compareE kind dom n a b) x := lo_app_r h

theorem lo_boolBinE_a {kind} {dom a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (Tools.ShippingBoolSourceSoundness.boolBinE kind dom a b) x := lo_app_l (lo_app_r h)
theorem lo_boolBinE_b {kind} {dom a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 b x) :
    LooseOcc 0 (Tools.ShippingBoolSourceSoundness.boolBinE kind dom a b) x := lo_app_r h

theorem lo_boolNotE_a {dom a : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (Tools.ShippingBoolSourceSoundness.boolNotE dom a) x := lo_app_r h

theorem lo_boolEqE_a {dom a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (Tools.ShippingBoolSourceSoundness.boolEqE dom a b) x := lo_app_l (lo_app_r h)
theorem lo_boolEqE_b {dom a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 b x) :
    LooseOcc 0 (Tools.ShippingBoolSourceSoundness.boolEqE dom a b) x := lo_app_r h

theorem lo_muxE_c {dom ty c a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 c x) :
    LooseOcc 0 (Tools.ShippingMuxTypeSoundness.muxE dom ty c a b) x := lo_app_l (lo_app_l (lo_app_r h))
theorem lo_muxE_a {dom ty c a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (Tools.ShippingMuxTypeSoundness.muxE dom ty c a b) x := lo_app_l (lo_app_r h)
theorem lo_muxE_b {dom ty c a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 b x) :
    LooseOcc 0 (Tools.ShippingMuxTypeSoundness.muxE dom ty c a b) x := lo_app_r h

theorem lo_setwE_a {dom : Lean.Expr} {w w' : Nat} {a : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (setwE dom w w' a) x := lo_app_r h

theorem lo_appE_a {dom ty body a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (appE dom ty body a b) x := lo_app_l (lo_app_r (lo_app_r h))
theorem lo_appE_b {dom ty body a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 b x) :
    LooseOcc 0 (appE dom ty body a b) x := lo_app_r h

theorem lo_sliceE_a {dom : Lean.Expr} {nm : Name} {w start len : Nat} {a : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (sliceE dom nm w start len a) x := lo_app_r h

theorem lo_concatE_a {dom : Lean.Expr} {m n : Nat} {a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (concatE dom m n a b) x := lo_app_l (lo_app_r h)
theorem lo_concatE_b {dom : Lean.Expr} {m n : Nat} {a b : Lean.Expr} {x : Nat} (h : LooseOcc 0 b x) :
    LooseOcc 0 (concatE dom m n a b) x := lo_app_r h

theorem lo_concatLitHiE_b {dom : Lean.Expr} {k v n : Nat} {b : Lean.Expr} {x : Nat} (h : LooseOcc 0 b x) :
    LooseOcc 0 (concatLitHiE dom k v n b) x := lo_app_r h
theorem lo_concatLitLoE_a {dom : Lean.Expr} {m k v : Nat} {a : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (concatLitLoE dom m k v a) x := lo_app_l (lo_app_r h)

theorem lo_zextMapE_a {dom : Lean.Expr} {nm : Name} {k n : Nat} {a : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (zextMapE dom nm k n a) x := lo_app_r h
theorem lo_sliceFE_a {dom : Lean.Expr} {nm : Name} {w start len : Nat} {a : Lean.Expr} {x : Nat} (h : LooseOcc 0 a x) :
    LooseOcc 0 (sliceFE dom nm w start len a) x := lo_app_r h

/-! ## `reads_of_quote_loose` -/

theorem reads_of_quote_loose (dom : Lean.Expr) (bb vv : Nat → Nat) (P : Nat → Bool) {s : SType} (t : Term s)
    (h : ∀ b, LooseOcc 0 (quote dom (fun j => Lean.Expr.bvar (bb j)) (fun j => Lean.Expr.bvar (vv j)) t) b → P b = true) :
    Tools.ShippingMachineRef.reads (fun j => P (bb j)) (fun j => P (vv j)) t = true := by
  revert h
  induction t with
  | boolInput j => intro h; exact h (bb j) rfl
  | bitsInput w j => intro h; exact h (vv j) rfl
  | boolLit _ => intro _; rfl
  | bitsLit _ _ => intro _; rfl
  | bitsNum _ _ => intro _; rfl
  | binary op a b iha ihb =>
    intro h; simp only [Tools.ShippingMachineRef.reads, Bool.and_eq_true]
    exact ⟨iha fun x hx => h x (lo_binE_a hx), ihb fun x hx => h x (lo_binE_b hx)⟩
  | compare op a b iha ihb =>
    intro h; simp only [Tools.ShippingMachineRef.reads, Bool.and_eq_true]
    exact ⟨iha fun x hx => h x (lo_compareE_a hx), ihb fun x hx => h x (lo_compareE_b hx)⟩
  | boolBinary op a b iha ihb =>
    intro h; simp only [Tools.ShippingMachineRef.reads, Bool.and_eq_true]
    exact ⟨iha fun x hx => h x (lo_boolBinE_a hx), ihb fun x hx => h x (lo_boolBinE_b hx)⟩
  | boolNot a iha =>
    intro h; simp only [Tools.ShippingMachineRef.reads]
    exact iha fun x hx => h x (lo_boolNotE_a hx)
  | boolEq a b iha ihb =>
    intro h; simp only [Tools.ShippingMachineRef.reads, Bool.and_eq_true]
    exact ⟨iha fun x hx => h x (lo_boolEqE_a hx), ihb fun x hx => h x (lo_boolEqE_b hx)⟩
  | mux c a b ihc iha ihb =>
    intro h; simp only [Tools.ShippingMachineRef.reads, Bool.and_eq_true]
    exact ⟨⟨ihc fun x hx => h x (lo_muxE_c hx), iha fun x hx => h x (lo_muxE_a hx)⟩, ihb fun x hx => h x (lo_muxE_b hx)⟩
  | setw w' a iha =>
    intro h; simp only [Tools.ShippingMachineRef.reads]
    exact iha fun x hx => h x (lo_setwE_a hx)
  | appCompare op a b iha ihb =>
    intro h; simp only [Tools.ShippingMachineRef.reads, Bool.and_eq_true]
    exact ⟨iha fun x hx => h x (lo_appE_a hx), ihb fun x hx => h x (lo_appE_b hx)⟩
  | appBool op a b iha ihb =>
    intro h; simp only [Tools.ShippingMachineRef.reads, Bool.and_eq_true]
    exact ⟨iha fun x hx => h x (lo_appE_a hx), ihb fun x hx => h x (lo_appE_b hx)⟩
  | appBool2 f a b iha ihb =>
    intro h; simp only [Tools.ShippingMachineRef.reads, Bool.and_eq_true]
    exact ⟨iha fun x hx => h x (lo_appE_a hx), ihb fun x hx => h x (lo_appE_b hx)⟩
  | slice nm start len a iha =>
    intro h; simp only [Tools.ShippingMachineRef.reads]
    exact iha fun x hx => h x (lo_sliceE_a hx)
  | concat a b iha ihb =>
    intro h; simp only [Tools.ShippingMachineRef.reads, Bool.and_eq_true]
    exact ⟨iha fun x hx => h x (lo_concatE_a hx), ihb fun x hx => h x (lo_concatE_b hx)⟩
  | concatLitHi k v b ihb =>
    intro h; simp only [Tools.ShippingMachineRef.reads]
    exact ihb fun x hx => h x (lo_concatLitHiE_b hx)
  | concatLitLo a k v iha =>
    intro h; simp only [Tools.ShippingMachineRef.reads]
    exact iha fun x hx => h x (lo_concatLitLoE_a hx)
  | zextMap nm k a iha =>
    intro h; simp only [Tools.ShippingMachineRef.reads]
    exact iha fun x hx => h x (lo_zextMapE_a hx)
  | sliceF nm start len a iha =>
    intro h; simp only [Tools.ShippingMachineRef.reads]
    exact iha fun x hx => h x (lo_sliceFE_a hx)

theorem mentionPos_lt {nDecl kI n k : Nat} {v : Lean.Expr} {p : Nat} (h : MentionPos nDecl kI n k v p) :
    p < nDecl + kI + n + k := by
  rcases h with ⟨i, hi, _, hp⟩ | ⟨i, hi, _, hp⟩ | ⟨i, hi, _, hp⟩ | ⟨i, hi, _, hp⟩ <;> omega

theorem readsOfQuoteStmt : ReadsOfQuoteStmt := by
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
      rw [← hq]; exact hl
    obtain ⟨p, hp, hbp⟩ := looseOcc_machClose nDecl kI n k v 0 b hn hr hl'
    have hlt := mentionPos_lt hp
    have : nDecl + kI + n + k - 1 - b = p := by omega
    simp only [this]
    exact hm p hp

/-! # U-D2 — range invariant, steps, suppliers (freeze rev4 §2) -/

def InRange (nDecl : Nat) (st : MachRead) (k : Nat) (v : Lean.Expr) : Prop :=
  PhInRange nDecl st.insts.size st.kinds.size k v

def RangeInv (nDecl : Nat) (st : MachRead) : Prop :=
  (∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → InRange nDecl st j v) ∧
  (∀ w ∈ st.ws, w.1 < st.kinds.size ∧ InRange nDecl st st.lets.size w.2)

def OrigAligned (st : MachRead) : Prop := st.instOrigins.size = st.insts.size

def EntryKinds (st : MachRead) : Prop :=
  (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → r ≠ .domain) ∧
  (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) →
     ∀ cb aw dw, st.instOrigins[k]? = some (.mem cb aw dw) → js.length = 4 ∧ r = .bits dw)

def FullInv (nDecl : Nat) (st : MachRead) : Prop :=
  CallOrderInv st ∧ RangeInv nDecl st ∧ OrigAligned st ∧ EntryKinds st

inductive FStep (nDecl : Nat) : MachRead → MachRead → Prop
  | letv (st : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr) :
      InRange nDecl st st.lets.size v → FStep nDecl st { st with lets := st.lets.push (nm, kd, v) }
  | inst (st : MachRead) (c : Name) (js : List Nat) (r : MixedGateBinder) (o : InstOrigin) :
      (∀ a ∈ js, a < st.lets.size) → r ≠ .domain →
      (∀ cb aw dw, o = .mem cb aw dw → js.length = 4 ∧ r = .bits dw) →
      FStep nDecl st { st with insts := st.insts.push (c, js, r), instOrigins := st.instOrigins.push o }
  | group (st : MachRead) (c : Name) (js : List Nat) (rs : List MixedGateBinder) (os : List InstOrigin) :
      rs.length = os.length → (∀ a ∈ js, a < st.lets.size) → (∀ r ∈ rs, r ≠ .domain) →
      (∀ o ∈ os, ∀ cb aw dw, o ≠ .mem cb aw dw) →
      FStep nDecl st { st with insts := st.insts ++ (rs.map fun r => (c, js, r)).toArray, instOrigins := st.instOrigins ++ os.toArray }
  | slot (st : MachRead) (kd : MixedGateBinder) (i : Nat) (nm : Name) :
      FStep nDecl st { st with kinds := st.kinds.push kd, inits := st.inits.push i, names := st.names.push nm }
  | slots (st : MachRead) (ks : List MixedGateBinder) (is : List Nat) (ns : List Name) :
      FStep nDecl st { st with kinds := st.kinds ++ ks.toArray, inits := st.inits ++ is.toArray, names := st.names ++ ns.toArray }
  | ws (st : MachRead) (ws' : Array (Nat × Lean.Expr)) :
      (∀ w ∈ ws', w.1 < st.kinds.size ∧ InRange nDecl st st.lets.size w.2) → FStep nDecl st { st with ws := ws' }

inductive FReach (nDecl : Nat) : MachRead → MachRead → Prop
  | refl (st : MachRead) : FReach nDecl st st
  | tail {a b c : MachRead} : FReach nDecl a b → FStep nDecl b c → FReach nDecl a c

/-! ### Helper lemmas -/

theorem inRange_mono {nDecl : Nat} {st st' : MachRead} {k k' : Nat} {v : Lean.Expr} (h : InRange nDecl st k v)
    (hI : st.insts.size ≤ st'.insts.size) (hK : st.kinds.size ≤ st'.kinds.size) (hk : k ≤ k') :
    InRange nDecl st' k' v :=
  phInRange_mono h (Nat.le_refl _) hI hK hk

theorem callOrderInv_congr {st st' : MachRead} (hl : st'.lets = st.lets) (hi : st'.insts = st.insts)
    (h : CallOrderInv st) : CallOrderInv st' := by
  simp only [CallOrderInv, LetValuesEarlier, LetsInstRange, ArgsExist, ArgsInstBounded, hl, hi]
  exact h

theorem rangeInv_mono_aux {nDecl : Nat} {st st' : MachRead} (h : RangeInv nDecl st)
    (hI : st.insts.size ≤ st'.insts.size) (hK : st.kinds.size ≤ st'.kinds.size)
    (hl : st'.lets = st.lets) (hw : st'.ws = st.ws) : RangeInv nDecl st' := by
  refine ⟨?_, ?_⟩
  · intro j nm kd v hj
    rw [hl] at hj
    exact inRange_mono (h.1 j nm kd v hj) hI hK (Nat.le_refl _)
  · intro w hw'
    rw [hw] at hw'
    obtain ⟨h1, h2⟩ := h.2 w hw'
    rw [hl]
    exact ⟨Nat.lt_of_lt_of_le h1 hK, inRange_mono h2 hI hK (Nat.le_refl _)⟩

theorem fullInv_of_empty (nDecl : Nat) (st : MachRead) (hl : st.lets = #[]) (hi : st.insts = #[])
    (ho : st.instOrigins = #[]) (hw : st.ws = #[]) : FullInv nDecl st := by
  refine ⟨callOrderInv_of_empty st hl hi, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · intro j nm kd v h; simp [hl] at h
  · intro w h; simp [hw] at h
  · simp [OrigAligned, ho, hi]
  · intro k c js r h; simp [hi] at h
  · intro k c js r h; simp [hi] at h

/-! ### Group lookup -/

theorem group_get {insts : Array (Name × List Nat × MixedGateBinder)} {c : Name} {js : List Nat}
    {rs : List MixedGateBinder} {k : Nat} {x : Name × List Nat × MixedGateBinder}
    (h : (insts ++ (rs.map fun r => (c, js, r)).toArray)[k]? = some x) :
    insts[k]? = some x ∨ (∃ r, rs[k - insts.size]? = some r ∧ insts.size ≤ k ∧ x = (c, js, r)) := by
  rw [Array.getElem?_append] at h
  split at h
  · exact Or.inl h
  · rename_i hk
    right
    simp only [List.getElem?_toArray, List.getElem?_map] at h
    cases hr : rs[k - insts.size]? with
    | none => simp [hr] at h
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      exact ⟨r, rfl, by omega, h.symm⟩

theorem origin_group_get {origs : Array InstOrigin} {os : List InstOrigin} {k : Nat} {o : InstOrigin}
    (h : (origs ++ os.toArray)[k]? = some o) :
    origs[k]? = some o ∨ (origs.size ≤ k ∧ os[k - origs.size]? = some o) := by
  rw [Array.getElem?_append] at h
  split at h
  · exact Or.inl h
  · rename_i hk
    right
    simp only [List.getElem?_toArray] at h
    exact ⟨by omega, h⟩

theorem callOrderInv_group (st : MachRead) (c : Name) (js : List Nat) (rs : List MixedGateBinder) (os : List InstOrigin)
    (h : CallOrderInv st) (hj : ∀ a ∈ js, a < st.lets.size) :
    CallOrderInv { st with insts := st.insts ++ (rs.map fun r => (c, js, r)).toArray,
                           instOrigins := st.instOrigins ++ os.toArray } := by
  obtain ⟨hE, hR, hX, hB⟩ := h
  refine ⟨hE, ?_, ?_, ?_⟩
  · intro j nm kd v hl m hm
    have := hR j nm kd v hl m hm
    show m < (st.insts ++ (rs.map fun r => (c, js, r)).toArray).size
    rw [Array.size_append]
    omega
  · intro k c' js' r' hk a ha
    rcases group_get hk with hk | ⟨r, _, _, hx⟩
    · exact hX k c' js' r' hk a ha
    · simp only [Prod.mk.injEq] at hx
      obtain ⟨-, rfl, -⟩ := hx
      exact hj a ha
  · intro k c' js' r' hk a ha i hr nm kd v hv m hm
    rcases group_get hk with hk | ⟨r, _, hsz, hx⟩
    · exact hB k c' js' r' hk a ha i hr nm kd v hv m hm
    · simp only [Prod.mk.injEq] at hx
      obtain ⟨-, rfl, -⟩ := hx
      have := hR i nm kd v hv m hm
      omega

/-! ### Step preservation -/

theorem fullInv_step {nDecl : Nat} {st st' : MachRead} (h : FullInv nDecl st) (hs : FStep nDecl st st') :
    FullInv nDecl st' := by
  obtain ⟨hC, hR, hO, hK⟩ := h
  cases hs with
  | letv nm kd v hv =>
    refine ⟨pushLet_preserves st _ nm kd v hC (fun i hi => hv.2.2.2 i hi) (fun m hm => hv.2.1 m hm) rfl, ?_, hO, hK⟩
    refine ⟨?_, ?_⟩
    · intro j nm' kd' v' hj
      simp only [Array.getElem?_push] at hj
      split at hj
      · rename_i hjs
        simp only [Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨-, -, rfl⟩ := hj
        subst hjs
        exact hv
      · exact hR.1 j nm' kd' v' hj
    · intro w hw
      obtain ⟨h1, h2⟩ := hR.2 w hw
      refine ⟨h1, inRange_mono h2 (Nat.le_refl _) (Nat.le_refl _) ?_⟩
      simp only [Array.size_push]; omega
  | inst c js r o hj hr ho =>
    refine ⟨callOrderInv_congr (st := { st with insts := st.insts.push (c, js, r) }) rfl rfl
        (pushInst_preserves st _ c js r hC hj rfl), ?_, ?_, ?_⟩
    · exact rangeInv_mono_aux hR (by simp [Array.size_push]) (Nat.le_refl _) rfl rfl
    · show (st.instOrigins.push o).size = (st.insts.push (c, js, r)).size
      simp only [Array.size_push]; rw [hO]
    · refine ⟨?_, ?_⟩
      · intro k c' js' r' hk
        simp only [Array.getElem?_push] at hk
        split at hk
        · simp only [Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨-, -, rfl⟩ := hk
          exact hr
        · exact hK.1 k c' js' r' hk
      · intro k c' js' r' hk cb aw dw hko
        simp only [Array.getElem?_push] at hk hko
        split at hk
        · rename_i hkn
          simp only [Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨-, rfl, rfl⟩ := hk
          split at hko
          · simp only [Option.some.injEq] at hko
            exact ho cb aw dw hko
          · rename_i hne
            exfalso; apply hne; rw [hO]; exact hkn
        · rename_i hkn
          split at hko
          · rename_i heq
            exfalso; apply hkn; rw [← hO]; exact heq
          · exact hK.2 k c' js' r' hk cb aw dw hko
  | group c js rs os hlen hj hr ho =>
    have hO' : st.instOrigins.size = st.insts.size := hO
    refine ⟨callOrderInv_group st c js rs os hC hj, ?_, ?_, ?_⟩
    · exact rangeInv_mono_aux hR (by simp [Array.size_append]) (Nat.le_refl _) rfl rfl
    · show (st.instOrigins ++ os.toArray).size = (st.insts ++ (rs.map fun r => (c, js, r)).toArray).size
      simp only [Array.size_append, List.size_toArray, List.length_map, hlen]
      rw [hO]
    · refine ⟨?_, ?_⟩
      · intro k c' js' r' hk
        rcases group_get hk with hk | ⟨r, hrk, _, hx⟩
        · exact hK.1 k c' js' r' hk
        · simp only [Prod.mk.injEq] at hx
          obtain ⟨-, -, rfl⟩ := hx
          exact hr _ (List.mem_of_getElem? hrk)
      · intro k c' js' r' hk cb aw dw hko
        rcases group_get hk with hk | ⟨r, hrk, hsz, hx⟩
        · rcases origin_group_get hko with hko | ⟨hsz', _⟩
          · exact hK.2 k c' js' r' hk cb aw dw hko
          · exfalso
            have := (Array.getElem?_eq_some_iff.1 hk).1
            omega
        · rcases origin_group_get hko with hko | ⟨hsz', hok⟩
          · exfalso
            have := (Array.getElem?_eq_some_iff.1 hko).1
            omega
          · exact absurd rfl (ho _ (List.mem_of_getElem? hok) cb aw dw)
  | slot kd i nm =>
    refine ⟨callOrderInv_congr (st := st) rfl rfl hC, ?_, hO, hK⟩
    exact rangeInv_mono_aux hR (Nat.le_refl _) (by simp [Array.size_push]) rfl rfl
  | slots ks is ns =>
    refine ⟨callOrderInv_congr (st := st) rfl rfl hC, ?_, hO, hK⟩
    exact rangeInv_mono_aux hR (Nat.le_refl _) (by simp [Array.size_append]) rfl rfl
  | ws ws' hw =>
    refine ⟨callOrderInv_congr (st := st) rfl rfl hC, ⟨hR.1, hw⟩, hO, hK⟩

theorem fullInv_reach {nDecl : Nat} {st0 st : MachRead} (h : FullInv nDecl st0) (hr : FReach nDecl st0 st) :
    FullInv nDecl st := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact fullInv_step ih hs

theorem fStep_sizes_mono {nDecl : Nat} {a b : MachRead} (hs : FStep nDecl a b) :
    a.lets.size ≤ b.lets.size ∧ a.insts.size ≤ b.insts.size ∧ a.kinds.size ≤ b.kinds.size := by
  cases hs <;> simp [Array.size_push, Array.size_append]

theorem reach_sizes_mono {nDecl : Nat} {a b : MachRead} (hr : FReach nDecl a b) :
    a.lets.size ≤ b.lets.size ∧ a.insts.size ≤ b.insts.size ∧ a.kinds.size ≤ b.kinds.size := by
  induction hr with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | tail _ hs ih =>
    have := fStep_sizes_mono hs
    exact ⟨Nat.le_trans ih.1 this.1, Nat.le_trans ih.2.1 this.2.1, Nat.le_trans ih.2.2 this.2.2⟩

/-! ### Suppliers -/

theorem letRange_final {nDecl : Nat} {st0 st : MachRead} (h0 : FullInv nDecl st0) (hr : FReach nDecl st0 st)
    {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr} (hj : st.lets[j]? = some (nm, kd, v)) :
    PhInRange nDecl st.insts.size st.kinds.size st.lets.size v := by
  have hI := fullInv_reach h0 hr
  have hlt := (Array.getElem?_eq_some_iff.1 hj).1
  exact phInRange_mono (hI.2.1.1 j nm kd v hj) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_of_lt hlt)

theorem writeRange_final {nDecl : Nat} {st0 st : MachRead} (h0 : FullInv nDecl st0) (hr : FReach nDecl st0 st)
    {w : Nat × Lean.Expr} (hw : w ∈ st.ws) :
    w.1 < st.kinds.size ∧ PhInRange nDecl st.insts.size st.kinds.size st.lets.size w.2 :=
  (fullInv_reach h0 hr).2.1.2 w hw

theorem resultRange_final {nDecl : Nat} {st1 st : MachRead} (hr : FReach nDecl st1 st) {v : Lean.Expr}
    (hv : InRange nDecl st1 st1.lets.size v) : PhInRange nDecl st.insts.size st.kinds.size st.lets.size v := by
  have hm := reach_sizes_mono hr
  exact inRange_mono hv hm.2.1 hm.2.2 hm.1

theorem phInRange_machSlot {nDecl kI n k i : Nat} (hi : i < n) : PhInRange nDecl kI n k (machSlot i) :=
  ⟨fun j hj => by simp [machSlot, MentionsPh] at hj, fun j hj => by simp [machSlot, MentionsPh] at hj,
   fun j hj => by simp [machSlot, MentionsPh] at hj; omega, fun j hj => by simp [machSlot, MentionsPh] at hj⟩

theorem machNext_range {nDecl : Nat} {st : MachRead} (h : RangeInv nDecl st) {i : Nat} (hi : i < st.kinds.size) :
    PhInRange nDecl st.insts.size st.kinds.size st.lets.size (machNext i st.ws.toList) := by
  unfold machNext
  split
  · rename_i a e hf
    have hm := List.mem_of_find?_eq_some hf
    rw [List.mem_reverse, Array.mem_toList_iff] at hm
    exact (h.2 _ hm).2
  · exact phInRange_machSlot hi

/-! ### Bundle / result parts -/

theorem inlSpine_mentions (tag : String) (i : Nat) :
    ∀ (e : Lean.Expr) (acc : List Lean.Expr) (x : Lean.Expr), x ∈ (inlSpine e acc).2 → MentionsPh tag i x →
      MentionsPh tag i e ∨ ∃ y ∈ acc, MentionsPh tag i y := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro acc x hx hm
    simp only [inlSpine] at hx
    rcases ihf (a :: acc) x hx hm with h | ⟨y, hy, hmy⟩
    · exact Or.inl (Or.inl h)
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact Or.inl (Or.inr hmy)
      · exact Or.inr ⟨y, hy, hmy⟩
  | _ => intro acc x hx hm; exact Or.inr ⟨x, by simpa [inlSpine] using hx, hm⟩

theorem inlSpine_range {nDecl kI n k : Nat} {e : Lean.Expr} (h : PhInRange nDecl kI n k e) :
    ∀ x ∈ (inlSpine e []).2, PhInRange nDecl kI n k x := by
  intro x hx
  exact ⟨fun i hi => h.1 i (by
      rcases inlSpine_mentions "_machIn" i e [] x hx hi with h | ⟨y, hy, _⟩
      · exact h
      · simp at hy),
    fun i hi => h.2.1 i (by
      rcases inlSpine_mentions "_machInst" i e [] x hx hi with h | ⟨y, hy, _⟩
      · exact h
      · simp at hy),
    fun i hi => h.2.2.1 i (by
      rcases inlSpine_mentions "_machSlot" i e [] x hx hi with h | ⟨y, hy, _⟩
      · exact h
      · simp at hy),
    fun i hi => h.2.2.2 i (by
      rcases inlSpine_mentions "_machLet" i e [] x hx hi with h | ⟨y, hy, _⟩
      · exact h
      · simp at hy)⟩

theorem machBundleParts_range {nDecl kI n k : Nat} :
    ∀ (m : Nat) (e : Lean.Expr) (ps : List Lean.Expr), machBundleParts? m e = some ps → PhInRange nDecl kI n k e →
      ∀ p ∈ ps, PhInRange nDecl kI n k p := by
  intro m
  induction m with
  | zero => intro e ps h; simp [machBundleParts?] at h
  | succ m ih =>
    intro e ps h hr p hp
    cases m with
    | zero =>
      have h1 : machBundleParts? 1 e = some [e] := rfl
      rw [h1, Option.some.injEq] at h
      subst h
      simp only [List.mem_singleton] at hp
      subst hp
      exact hr
    | succ m =>
      unfold machBundleParts? at h
      split at h
      · simp at h
      · exfalso; omega
      · rename_i _ _ n' us A B C a b _ heq
        have hn' : n' = m + 1 := by omega
        subst hn'
        cases hq : machBundleParts? (m + 1) b with
        | none => simp [hq] at h
        | some qs =>
          rw [hq] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          rcases List.mem_cons.1 hp with rfl | hp
          · refine phInRange_of_sub ?_ hr
            exact fun t i h => Or.inl (Or.inr h)
          · refine ih b qs hq ?_ p hp
            refine phInRange_of_sub ?_ hr
            exact fun t i h => Or.inr h
      · simp at h

theorem machResults_range {nDecl kI n k : Nat} (sel : Option (Name × Nat × Nat)) (ctor? : Option Name) (m : Nat) (v : Lean.Expr)
    (es : List Lean.Expr) (h : machResults? sel ctor? m v = some es) (hv : PhInRange nDecl kI n k v) :
    ∀ e ∈ es, PhInRange nDecl kI n k e := by
  intro e he
  unfold machResults? at h
  cases ctor? with
  | none =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    simp only [List.mem_singleton] at he
    subst he
    unfold machResult? at hr
    cases sel with
    | none => simp at hr; subst hr; exact hv
    | some t =>
      obtain ⟨ctor, np, idx⟩ := t
      simp only at hr
      split at hr
      · rename_i c us args hspine
        split at hr
        · have hmem := List.mem_of_getElem? hr
          have := inlSpine_range hv
          rw [hspine] at this
          exact this e hmem
        · simp at hr
      · simp at hr
  | some ctor =>
    simp only at h
    split at h
    · simp at h
    · split at h
      · rename_i c us args hspine
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          have hmem := List.mem_of_mem_drop he
          have := inlSpine_range hv
          rw [hspine] at this
          exact this e hmem
        · simp at h
      · simp at h

/-! # U-D3 — RowA/B/C from the invariants (freeze rev4 §3) -/

structure ShapeAgree (d : MachineData) (st : MachRead) : Prop where
  insts   : d.shape.insts = st.insts.toList
  origins : d.shape.instOrigins = st.instOrigins.toList
  slots   : d.ss.length = st.kinds.size
  lets    : d.ls.length = st.lets.size
  nIn     : d.shape.insts.length ≤ d.nIn

def LetQuoteEq (d : MachineData) (st : MachRead) : Prop :=
  ∀ (j : Nat) (hj : j < d.ls.length) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i))
                (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.vpos i)) (d.ls[j]'hj).2
      = machClose st.insts.size st.kinds.size st.lets.size 0 v

def LetsNoLoose (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ b, ¬ LooseOcc 0 v b

theorem foldl_snoc_spec {α : Type} (g : List Bool → α → Bool) :
    ∀ (ls : List α) (acc : List Bool),
      (ls.foldl (fun c l => c ++ [g c l]) acc).take acc.length = acc ∧
      (ls.foldl (fun c l => c ++ [g c l]) acc).length = acc.length + ls.length ∧
      ∀ (i : Nat) (hi : i < ls.length),
        (ls.foldl (fun c l => c ++ [g c l]) acc)[acc.length + i]? =
          some (g ((ls.foldl (fun c l => c ++ [g c l]) acc).take (acc.length + i)) (ls[i]'hi)) := by
  intro ls
  induction ls with
  | nil => intro acc; simp
  | cons x ls ih =>
    intro acc
    obtain ⟨h1, h2, h3⟩ := ih (acc ++ [g acc x])
    simp only [List.foldl_cons]
    have hl : (acc ++ [g acc x]).length = acc.length + 1 := by simp
    generalize List.foldl (fun c l => c ++ [g c l]) (acc ++ [g acc x]) ls = r at h1 h2 h3 ⊢
    rw [hl] at h1 h2
    have hacc : r.take acc.length = acc := by
      have h' : (r.take (acc.length + 1)).take acc.length = acc := by rw [h1]; simp
      rw [List.take_take] at h'
      simpa [Nat.min_eq_left (Nat.le_succ _)] using h'
    refine ⟨hacc, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro i hi
      cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        have e1 : r[acc.length]? = some (g acc x) := by
          rw [← List.getElem?_take_of_lt (Nat.lt_succ_self acc.length), h1]
          simp
        rw [e1, hacc]
      | succ i' =>
        simp only [List.getElem_cons_succ]
        have e : acc.length + (i' + 1) = (acc ++ [g acc x]).length + i' := by omega
        rw [e]
        exact h3 i' (by simpa using hi)

theorem cleanLets_getElem (d : MachineData) (k l : Nat) (hl : l < d.ls.length) :
    (cleanLets d k)[l]? = some (Tools.ShippingMachineRef.reads
      (fun j => posOk d k ((cleanLets d k).take l) (d.bpos j)) (fun j => posOk d k ((cleanLets d k).take l) (d.vpos j)) (d.ls[l]'hl).2) := by
  have := (foldl_snoc_spec (fun clean (l : Σ s : SType, Term s) =>
      Tools.ShippingMachineRef.reads (fun j => posOk d k clean (d.bpos j)) (fun j => posOk d k clean (d.vpos j)) l.2) d.ls []).2.2 l hl
  simpa [cleanLets] using this

theorem letReach_edge {lets : MachLets} {a l j : Nat} (h : LetReach lets a l) (e : LetEdge lets l j) : LetReach lets a j := by
  induction h with
  | refl => exact LetReach.step e (LetReach.refl j)
  | step he _ ih => exact LetReach.step he (ih e)

theorem entry_of_agree {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) {k : Nat} (hk : k < d.shape.insts.length) :
    ∃ (c : Name) (js : List Nat) (r : MixedGateBinder), d.shape.insts[k]? = some (c, js, r) ∧ st.insts[k]? = some (c, js, r) := by
  obtain ⟨⟨c, js, r⟩, hx⟩ : ∃ x, d.shape.insts[k]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
  refine ⟨c, js, r, hx, ?_⟩
  rw [hag.insts] at hx
  simpa using hx

theorem callArgs_of {d : MachineData} {k : Nat} {c : Name} {js : List Nat} {r : MixedGateBinder}
    (h : d.shape.insts[k]? = some (c, js, r)) : callArgs d k = js := by
  simp [callArgs, List.getElem?_map, h]

theorem rowA2_of_inv {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : OrigAligned st) :
    d.shape.instOrigins.length = d.shape.insts.length := by
  rw [hag.origins, hag.insts]
  simp only [Array.length_toList]
  exact hi

theorem rowA3_of_inv {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st) :
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, l < d.ls.length := by
  intro k hk l hl
  obtain ⟨c, js, r, hd, hs⟩ := entry_of_agree hag hk
  rw [callArgs_of hd] at hl
  rw [hag.lets]
  exact hi.1.2.2.1 k c js r hs l hl

theorem rowA4B23_mem_of_inv {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st) :
    ∀ k, k < d.shape.insts.length → ∀ cb aw dw, originOf d k = .mem cb aw dw →
      (callArgs d k).length = 4 ∧ (d.shape.insts[k]?).map (·.2.2) = some (.bits dw) := by
  intro k hk cb aw dw ho
  obtain ⟨c, js, r, hd, hs⟩ := entry_of_agree hag hk
  have hos : st.instOrigins[k]? = some (.mem cb aw dw) := by
    unfold originOf at ho
    rw [List.getD_eq_getElem?_getD] at ho
    cases hg : d.shape.instOrigins[k]? with
    | none => rw [hg] at ho; simp at ho
    | some o =>
      rw [hg] at ho
      simp only [Option.getD_some] at ho
      rw [hag.origins] at hg
      rw [← ho]
      simpa using hg
  obtain ⟨h4, hr⟩ := hi.2.2.2.2 k c js r hs cb aw dw hos
  rw [callArgs_of hd]
  refine ⟨h4, ?_⟩
  rw [hd]
  simp [hr]

theorem rowB1_of_inv {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st)
    (hcb : ∀ k (hk : k < d.shape.insts.length), (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2) :
    ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain := by
  intro k hk
  obtain ⟨c, js, r, hd, hs⟩ := entry_of_agree hag hk
  rw [callKind_eq_inst d hk hag.nIn (hcb k hk)]
  have : (d.shape.insts[k]'hk) = (c, js, r) := by
    have := List.getElem?_eq_getElem hk (l := d.shape.insts)
    rw [hd] at this
    exact (Option.some.inj this).symm
  rw [this]
  exact hi.2.2.2.1 k c js r hs

theorem getD_take_of_lt (c : List Bool) {l j : Nat} (h : j < l) : (c.take l).getD j false = c.getD j false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem rowC_of_reader {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hq : LetQuoteEq d st) (hnl : LetsNoLoose st)
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
      refine readsOfQuoteStmt d.dom (kDOf d) st.insts.size st.kinds.size st.lets.size d.bpos d.vpos
        (posOk d k ((cleanLets d k).take l)) (d.ls[l]'hldl).2 v
        (phInRange_mono (hR.1 l nm kd v hv_l) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_of_lt hlt))
        (fun j => by have := hb j; omega) (fun j => by have := hv j; omega) (hnl l nm kd v hv_l)
        (hq l hldl nm kd v hv_l) ?_
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

end Tools.ShippingGen5Cover3
