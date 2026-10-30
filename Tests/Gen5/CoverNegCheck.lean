import Tools.ShippingGen5Cover
set_option autoImplicit false
-- NOT BUILT (written in g5cv-r3; the SHA of the first successful Pod build is recorded here by a comment-only commit). Clean build is the coder's. No sorry / axiom / native_decide.

/-! # DG-COVER freeze rev2: kernel negative examples for R1 and R2 (`scripts/gen5/DG_COVER_FREEZE_REV2.md`)

The two examples below were found by the reviewer reading the definitions of `scripts/gen5/DG_COVER_FREEZE_REV1.md` §2.4 (no kernel run). Here each is checked in the kernel:
the rev1 statement is refuted by an explicit instance (`¬ …Rev1`), the instance is shown to satisfy the rev1 premises, and the rev2 statement is shown to exclude it
(the instance fails an added premise / the added invariant clause). Failure to elaborate is not counted as a negative; every `theorem` here is a closed proof.

These are statements about Prop-valued definitions of this file. Nothing here is about a successful source, a run, `dataOf`, M5 or FG. The rev2 statements are
statements only (`PushInstPreserves`, `PushLetPreserves`, `ReadsOfQuoteStmt` are not proved). -/

namespace Tests.Gen5.CoverNegCheck
open Lean Sparkle.Compiler.Elab Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge

/-! ## Shared definitions (rev1 §2.4, unchanged) -/

def MentionsPh (tag : String) (i : Nat) : Lean.Expr → Prop
  | .fvar ⟨.num (.str .anonymous t) j⟩ => t = tag ∧ j = i
  | .app f a => MentionsPh tag i f ∨ MentionsPh tag i a
  | .lam _ t b _ => MentionsPh tag i t ∨ MentionsPh tag i b
  | .forallE _ t b _ => MentionsPh tag i t ∨ MentionsPh tag i b
  | _ => False

abbrev MentionsLet (i : Nat) (e : Lean.Expr) : Prop := MentionsPh "_machLet" i e
abbrev MentionsInst (i : Nat) (e : Lean.Expr) : Prop := MentionsPh "_machInst" i e

def LetEdge (lets : MachLets) (a i : Nat) : Prop :=
  ∃ (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), lets[a]? = some (nm, kd, v) ∧ MentionsLet i v

inductive LetReach (lets : MachLets) : Nat → Nat → Prop
  | refl (a : Nat) : LetReach lets a a
  | step {a i j : Nat} : LetEdge lets a i → LetReach lets i j → LetReach lets a j

def LetValuesEarlier (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ i, MentionsLet i v → i < j

def LetsInstRange (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ m, MentionsInst m v → m < st.insts.size

def ArgsInstBounded (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, ∀ i, LetReach st.lets a i →
    ∀ (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[i]? = some (nm, kd, v) → ∀ m, MentionsInst m v → m < k

/-! ## R1 -/

/-- rev1's invariant (three clauses). -/
def CallOrderInvRev1 (st : MachRead) : Prop :=
  LetValuesEarlier st ∧ LetsInstRange st ∧ ArgsInstBounded st

/-- rev2 added clause: every argument of every pushed instance entry names an existing let. -/
def ArgsExist (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, a < st.lets.size

/-- rev2 invariant (four clauses). -/
def CallOrderInv (st : MachRead) : Prop :=
  LetValuesEarlier st ∧ LetsInstRange st ∧ ArgsExist st ∧ ArgsInstBounded st

def PushLetPreservesRev1 : Prop :=
  ∀ (st st' : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr),
    CallOrderInvRev1 st → (∀ i, MentionsLet i v → i < st.lets.size) → (∀ m, MentionsInst m v → m < st.insts.size) →
    st' = { st with lets := st.lets.push (nm, kd, v) } → CallOrderInvRev1 st'

def PushInstPreserves : Prop :=
  ∀ (st st' : MachRead) (c : Name) (js : List Nat) (r : MixedGateBinder),
    CallOrderInv st → (∀ a ∈ js, a < st.lets.size) →
    st' = { st with insts := st.insts.push (c, js, r) } → CallOrderInv st'

/-- rev2: the premise `CallOrderInv st` now includes `ArgsExist st`; the statement is otherwise the rev1 text. -/
def PushLetPreserves : Prop :=
  ∀ (st st' : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr),
    CallOrderInv st → (∀ i, MentionsLet i v → i < st.lets.size) → (∀ m, MentionsInst m v → m < st.insts.size) →
    st' = { st with lets := st.lets.push (nm, kd, v) } → CallOrderInv st'

/-- R1 example: no lets, one instance entry `(c, [0], bool)` whose argument names let 0, which does not exist. -/
def r1Pre : MachRead := { lets := #[], insts := #[(`c, [0], .bool)] }
def r1Val : Lean.Expr := machInstOut 0
def r1Post : MachRead := { r1Pre with lets := r1Pre.lets.push (`l, .bool, r1Val) }

theorem r1_pre_rev1_inv : CallOrderInvRev1 r1Pre := by
  refine ⟨?_, ?_, ?_⟩
  · intro j nm kd v h; simp [r1Pre] at h
  · intro j nm kd v h; simp [r1Pre] at h
  · intro k c js r hk a ha i hr nm kd v hv m hm
    simp [r1Pre] at hv

theorem r1_val_prem_let : ∀ i, MentionsLet i r1Val → i < r1Pre.lets.size := by
  intro i h; simp [r1Val, MentionsLet, MentionsPh, machInstOut] at h

theorem r1_val_prem_inst : ∀ m, MentionsInst m r1Val → m < r1Pre.insts.size := by
  intro m h
  simp [r1Val, MentionsInst, MentionsPh, machInstOut] at h
  simp [r1Pre, h]

theorem r1_post_not_args_bounded : ¬ ArgsInstBounded r1Post := by
  intro h
  have := h 0 `c [0] .bool (by simp [r1Post, r1Pre]) 0 (by simp) 0 (.refl 0)
    `l .bool r1Val (by simp [r1Post, r1Pre]) 0 (by simp [r1Val, MentionsInst, MentionsPh, machInstOut])
  omega

/-- The rev1 push statement is false: instance `r1Pre`/`r1Post`. -/
theorem r1_rev1_push_false : ¬ PushLetPreservesRev1 := by
  intro h
  exact r1_post_not_args_bounded
    (h r1Pre r1Post `l .bool r1Val r1_pre_rev1_inv r1_val_prem_let r1_val_prem_inst rfl).2.2

/-- rev2: the example pre-state is not in the rev2 invariant (the added clause fails), so it is not a counterexample to `PushLetPreserves`. -/
theorem r1_pre_not_rev2_inv : ¬ CallOrderInv r1Pre := by
  intro h
  have := h.2.2.1 0 `c [0] .bool (by simp [r1Pre]) 0 (by simp)
  simp [r1Pre] at this

/-! ## R2 -/

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

/-- rev2 added premise: every placeholder `v` mentions is inside the telescope `machClose nDecl kI n k` closes against (so none is closed by `Nat` subtraction saturating). -/
def PhInRange (nDecl kI n k : Nat) (v : Lean.Expr) : Prop :=
  (∀ i, MentionsPh "_machIn" i v → i < nDecl) ∧ (∀ j, MentionsPh "_machInst" j v → j < kI) ∧
  (∀ i, MentionsPh "_machSlot" i v → i < n) ∧ (∀ j, MentionsPh "_machLet" j v → j < k)

def ReadsOfQuoteStmtRev1 : Prop :=
  ∀ (dom : Lean.Expr) (nDecl kI n k : Nat) (bpos vpos : Nat → Nat) (okP : Nat → Bool)
    {s : SType} (t : Term s) (v : Lean.Expr),
    (∀ j, bpos j < nDecl + kI + n + k) → (∀ j, vpos j < nDecl + kI + n + k) →
    (∀ b, ¬ LooseOcc 0 v b) →
    quote dom (fun j => inputExpr (nDecl + kI + n + k) (bpos j))
      (fun j => inputExpr (nDecl + kI + n + k) (vpos j)) t = machClose kI n k 0 v →
    (∀ p, MentionPos nDecl kI n k v p → okP p = true) →
    Tools.ShippingMachineRef.reads (fun j => okP (bpos j)) (fun j => okP (vpos j)) t = true

/-- rev2: rev1 plus the premise `PhInRange nDecl kI n k v`. -/
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

/-- R2 example: nDecl = kI = n = 0, k = 1, bpos = vpos = const 0, t = boolInput 0, v = machLet 1, okP = const false. -/
theorem r2_rev1_false : ¬ ReadsOfQuoteStmtRev1 := by
  intro h
  have := h (.const `D []) 0 0 0 1 (fun _ => 0) (fun _ => 0) (fun _ => false) (.boolInput 0) (machLet 1)
    (by intro j; decide) (by intro j; decide)
    (by intro b hb; simp [machLet, LooseOcc] at hb)
    rfl
    (by
      intro p hp
      simp [MentionPos, machLet, MentionsPh] at hp)
  simp [Tools.ShippingMachineRef.reads] at this

/-- The premises of the rev1 statement hold for the example (shown separately: the quotation equation is by `decide`, `MentionPos` is empty). -/
theorem r2_quote_eq :
    quote (.const `D []) (fun j => inputExpr (0 + 0 + 0 + 1) ((fun _ => 0) j))
      (fun j => inputExpr (0 + 0 + 0 + 1) ((fun _ => 0) j)) (Term.boolInput 0 : Term .bool)
      = machClose 0 0 1 0 (machLet 1) := rfl

theorem r2_mentionPos_empty (p : Nat) : ¬ MentionPos 0 0 0 1 (machLet 1) p := by
  simp [MentionPos, machLet, MentionsPh]

/-- rev2: the example fails the added premise (let 1 is not below k = 1). -/
theorem r2_example_not_in_range : ¬ PhInRange 0 0 0 1 (machLet 1) := by
  intro h
  have := h.2.2.2 1 (by simp [machLet, MentionsPh])
  omega

#print axioms r1_pre_rev1_inv
#print axioms r1_val_prem_let
#print axioms r1_val_prem_inst
#print axioms r1_post_not_args_bounded
#print axioms r1_rev1_push_false
#print axioms r1_pre_not_rev2_inv
#print axioms r2_rev1_false
#print axioms r2_quote_eq
#print axioms r2_mentionPos_empty
#print axioms r2_example_not_in_range

end Tests.Gen5.CoverNegCheck
