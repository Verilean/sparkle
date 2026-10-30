import Tools.ShippingMachineAuto
set_option autoImplicit false
-- Built in doc-bc9a300d (clean issue-linked, exit 0, 743 jobs; source=end=bc9a300d on par/gen3-combined 43977202) (DG-DATAOF pure units; scripts/gen5/DG_DATAOF_FREEZE.md rev1). No sorry / axiom / native_decide.

/-! # DG-DATAOF pure units (no READKINDS, no `Laws`, no `T1Hyp*`)

* `termsOfAny` and its `fields` fact (U-A).
* `anyBeq` / `bitsBeq`, the structural comparison of typed terms that compares the INDEX (the sort / the width) as well
  as the term (U-B): `anyBeq a b = true → a = b` on `Σ s : SType, Term s`, `bitsBeq` likewise on `Σ w : Nat, Term (.bits w)`.
  `deriving DecidableEq` fails on `Term` (dependent elimination on the `m + n` index of `concat`), so `termBeq` is a
  hand-written comparison across sorts (`Term s` against `Term s'`) and `termBeq_sound` yields `s = s' ∧ HEq a b`;
  no `Lean.Expr.equal`.
* `decInit`, `initsFrom`, `initsOf`: the register reset values as typed values.
* `initOk_of_ok` (U-C): `d.ok = true → d.initOk (initsOf d) = true`. -/
namespace Tools.ShippingGen5DataOfPure
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMuxLoweringSoundness
open Sparkle.Core Sparkle.IR.Machine Sparkle.Compiler.Elab

/-! ## U-A -/

/-- A list of typed terms as a `Terms` over the list of their sorts. -/
def termsOfAny : (l : List (Σ s : SType, Term s)) → Terms (l.map (·.1))
  | []            => .nil
  | ⟨_, t⟩ :: rs => .cons t (termsOfAny rs)

theorem termsOfAny_fields : ∀ (l : List (Σ s : SType, Term s)),
    (termsOfAny l).fields = l.map (fun t => toField t.1 t.2)
  | []            => rfl
  | ⟨s, t⟩ :: rs => by
    simp only [termsOfAny, Terms.fields, List.map_cons]
    rw [termsOfAny_fields rs]

/-! ## U-B -/

def termBeq : {s s' : SType} → Term s → Term s' → Bool
  | _, _, .boolInput j, .boolInput j' => j == j'
  | _, _, .bitsInput w j, .bitsInput w' j' => w == w' && j == j'
  | _, _, .boolLit b, .boolLit b' => b == b'
  | _, _, .bitsLit w v, .bitsLit w' v' => w == w' && v == v'
  | _, _, .bitsNum w v, .bitsNum w' v' => w == w' && v == v'
  | _, _, .binary op (w := w) a b, .binary op' (w := w') a' b' =>
    decide (op = op') && w == w' && termBeq a a' && termBeq b b'
  | _, _, .compare op (w := w) a b, .compare op' (w := w') a' b' =>
    decide (op = op') && w == w' && termBeq a a' && termBeq b b'
  | _, _, .boolBinary op a b, .boolBinary op' a' b' => decide (op = op') && termBeq a a' && termBeq b b'
  | _, _, .boolNot a, .boolNot a' => termBeq a a'
  | _, _, .boolEq a b, .boolEq a' b' => termBeq a a' && termBeq b b'
  | _, _, .mux (s := s) c a b, .mux (s := s') c' a' b' =>
    decide (s = s') && termBeq c c' && termBeq a a' && termBeq b b'
  | _, _, .setw (w := w) w₂ a, .setw (w := w') w₂' a' => w == w' && w₂ == w₂' && termBeq a a'
  | _, _, .slice nm start len (w := w) a, .slice nm' start' len' (w := w') a' =>
    nm == nm' && start == start' && len == len' && w == w' && termBeq a a'
  | _, _, .concat (m := m) (n := n) a b, .concat (m := m') (n := n') a' b' =>
    m == m' && n == n' && termBeq a a' && termBeq b b'
  | _, _, .concatLitHi k v (n := n) b, .concatLitHi k' v' (n := n') b' =>
    k == k' && v == v' && n == n' && termBeq b b'
  | _, _, .concatLitLo (m := m) a k v, .concatLitLo (m := m') a' k' v' =>
    m == m' && k == k' && v == v' && termBeq a a'
  | _, _, .zextMap nm k (n := n) a, .zextMap nm' k' (n := n') a' =>
    nm == nm' && k == k' && n == n' && termBeq a a'
  | _, _, .sliceF nm start len (w := w) a, .sliceF nm' start' len' (w := w') a' =>
    nm == nm' && start == start' && len == len' && w == w' && termBeq a a'
  | _, _, .appCompare op (w := w) a b, .appCompare op' (w := w') a' b' =>
    decide (op = op') && w == w' && termBeq a a' && termBeq b b'
  | _, _, .appBool op a b, .appBool op' a' b' => decide (op = op') && termBeq a a' && termBeq b b'
  | _, _, .appBool2 f a b, .appBool2 f' a' b' => decide (f = f') && termBeq a a' && termBeq b b'
  | _, _, _, _ => false


theorem termBeq_sound : ∀ {s : SType} (a : Term s) {s' : SType} (b : Term s'), termBeq a b = true → s = s' ∧ HEq a b := by
  intro s a
  induction a <;> intro s' b h <;> cases b <;> first | (exfalso; exact Bool.noConfusion h) | skip
  case boolInput.boolInput =>
    rename_i j j'
    have h' : (j == j') = true := h
    simp only [beq_iff_eq] at h'
    subst h'; exact ⟨rfl, HEq.rfl⟩
  case bitsInput.bitsInput =>
    rename_i w j w' j'
    have h' : (w == w' && j == j') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨rfl, rfl⟩ := h'; exact ⟨rfl, HEq.rfl⟩
  case boolLit.boolLit =>
    rename_i b b'
    have h' : (b == b') = true := h
    simp only [beq_iff_eq] at h'
    subst h'; exact ⟨rfl, HEq.rfl⟩
  case bitsLit.bitsLit =>
    rename_i w v w' v'
    have h' : (w == w' && v == v') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨rfl, rfl⟩ := h'; exact ⟨rfl, HEq.rfl⟩
  case bitsNum.bitsNum =>
    rename_i w v w' v'
    have h' : (w == w' && v == v') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨rfl, rfl⟩ := h'; exact ⟨rfl, HEq.rfl⟩
  case binary.binary =>
    rename_i op w a b iha ihb op' w' a' b'
    have h' : (decide (op = op') && w == w' && termBeq a a' && termBeq b b') = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
    obtain ⟨⟨⟨rfl, rfl⟩, ha⟩, hb⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    obtain rfl := eq_of_heq (ihb _ hb).2
    exact ⟨rfl, HEq.rfl⟩
  case compare.compare =>
    rename_i op w a b iha ihb op' w' a' b'
    have h' : (decide (op = op') && w == w' && termBeq a a' && termBeq b b') = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
    obtain ⟨⟨⟨rfl, rfl⟩, ha⟩, hb⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    obtain rfl := eq_of_heq (ihb _ hb).2
    exact ⟨rfl, HEq.rfl⟩
  case boolBinary.boolBinary =>
    rename_i op a b iha ihb op' a' b'
    have h' : (decide (op = op') && termBeq a a' && termBeq b b') = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
    obtain ⟨⟨rfl, ha⟩, hb⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    obtain rfl := eq_of_heq (ihb _ hb).2
    exact ⟨rfl, HEq.rfl⟩
  case boolNot.boolNot =>
    rename_i a iha a'
    obtain rfl := eq_of_heq (iha _ (show termBeq a a' = true from h)).2
    exact ⟨rfl, HEq.rfl⟩
  case boolEq.boolEq =>
    rename_i a b iha ihb a' b'
    have h' : (termBeq a a' && termBeq b b') = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨ha, hb⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    obtain rfl := eq_of_heq (ihb _ hb).2
    exact ⟨rfl, HEq.rfl⟩
  case mux.mux =>
    rename_i s1 c a b ihc iha ihb c' a' b'
    have h' : (decide (s1 = s') && termBeq c c' && termBeq a a' && termBeq b b') = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨⟨rfl, hc⟩, ha⟩, hb⟩ := h'
    obtain rfl := eq_of_heq (ihc _ hc).2
    obtain rfl := eq_of_heq (iha _ ha).2
    obtain rfl := eq_of_heq (ihb _ hb).2
    exact ⟨rfl, HEq.rfl⟩
  case setw.setw =>
    rename_i w w2 a iha w' w2' a'
    have h' : (w == w' && w2 == w2' && termBeq a a') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨rfl, rfl⟩, ha⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    exact ⟨rfl, HEq.rfl⟩
  case slice.slice =>
    rename_i nm start len w a iha nm' start' len' w' a'
    have h' : (nm == nm' && start == start' && len == len' && w == w' && termBeq a a') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, ha⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    exact ⟨rfl, HEq.rfl⟩
  case concat.concat =>
    rename_i m n a b iha ihb m' n' a' b'
    have h' : (m == m' && n == n' && termBeq a a' && termBeq b b') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨rfl, rfl⟩, ha⟩, hb⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    obtain rfl := eq_of_heq (ihb _ hb).2
    exact ⟨rfl, HEq.rfl⟩
  case concatLitHi.concatLitHi =>
    rename_i k v n b ihb k' v' n' b'
    have h' : (k == k' && v == v' && n == n' && termBeq b b') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hb⟩ := h'
    obtain rfl := eq_of_heq (ihb _ hb).2
    exact ⟨rfl, HEq.rfl⟩
  case concatLitLo.concatLitLo =>
    rename_i m a k v iha m' a' k' v'
    have h' : (m == m' && k == k' && v == v' && termBeq a a') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, ha⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    exact ⟨rfl, HEq.rfl⟩
  case zextMap.zextMap =>
    rename_i nm k n a iha nm' k' n' a'
    have h' : (nm == nm' && k == k' && n == n' && termBeq a a') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, ha⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    exact ⟨rfl, HEq.rfl⟩
  case sliceF.sliceF =>
    rename_i nm start len w a iha nm' start' len' w' a'
    have h' : (nm == nm' && start == start' && len == len' && w == w' && termBeq a a') = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, ha⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    exact ⟨rfl, HEq.rfl⟩
  case appCompare.appCompare =>
    rename_i op w a b iha ihb op' w' a' b'
    have h' : (decide (op = op') && w == w' && termBeq a a' && termBeq b b') = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
    obtain ⟨⟨⟨rfl, rfl⟩, ha⟩, hb⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    obtain rfl := eq_of_heq (ihb _ hb).2
    exact ⟨rfl, HEq.rfl⟩
  case appBool.appBool =>
    rename_i op a b iha ihb op' a' b'
    have h' : (decide (op = op') && termBeq a a' && termBeq b b') = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨rfl, ha⟩, hb⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    obtain rfl := eq_of_heq (ihb _ hb).2
    exact ⟨rfl, HEq.rfl⟩
  case appBool2.appBool2 =>
    rename_i f a b iha ihb f' a' b'
    have h' : (decide (f = f') && termBeq a a' && termBeq b b') = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨rfl, ha⟩, hb⟩ := h'
    obtain rfl := eq_of_heq (iha _ ha).2
    obtain rfl := eq_of_heq (ihb _ hb).2
    exact ⟨rfl, HEq.rfl⟩


theorem termBeq_refl : ∀ {s : SType} (a : Term s), termBeq a a = true := by
  intro s a
  induction a
  case boolInput =>
    rename_i j
    show (j == j) = true
    simp [*]
  case bitsInput =>
    rename_i w j
    show (w == w && j == j) = true
    simp [*]
  case boolLit =>
    rename_i b
    show (b == b) = true
    simp [*]
  case bitsLit =>
    rename_i w v
    show (w == w && v == v) = true
    simp [*]
  case bitsNum =>
    rename_i w v
    show (w == w && v == v) = true
    simp [*]
  case binary =>
    rename_i op w a b iha ihb
    show (decide (op = op) && w == w && termBeq a a && termBeq b b) = true
    simp [*]
  case compare =>
    rename_i op w a b iha ihb
    show (decide (op = op) && w == w && termBeq a a && termBeq b b) = true
    simp [*]
  case boolBinary =>
    rename_i op a b iha ihb
    show (decide (op = op) && termBeq a a && termBeq b b) = true
    simp [*]
  case boolNot =>
    rename_i a iha
    show (termBeq a a) = true
    simp [*]
  case boolEq =>
    rename_i a b iha ihb
    show (termBeq a a && termBeq b b) = true
    simp [*]
  case mux =>
    rename_i s c a b ihc iha ihb
    show (decide (s = s) && termBeq c c && termBeq a a && termBeq b b) = true
    simp [*]
  case setw =>
    rename_i w w2 a iha
    show (w == w && w2 == w2 && termBeq a a) = true
    simp [*]
  case slice =>
    rename_i nm start len w a iha
    show (nm == nm && start == start && len == len && w == w && termBeq a a) = true
    simp [*]
  case concat =>
    rename_i m n a b iha ihb
    show (m == m && n == n && termBeq a a && termBeq b b) = true
    simp [*]
  case concatLitHi =>
    rename_i k v n b ihb
    show (k == k && v == v && n == n && termBeq b b) = true
    simp [*]
  case concatLitLo =>
    rename_i m a k v iha
    show (m == m && k == k && v == v && termBeq a a) = true
    simp [*]
  case zextMap =>
    rename_i nm k n a iha
    show (nm == nm && k == k && n == n && termBeq a a) = true
    simp [*]
  case sliceF =>
    rename_i nm start len w a iha
    show (nm == nm && start == start && len == len && w == w && termBeq a a) = true
    simp [*]
  case appCompare =>
    rename_i op w a b iha ihb
    show (decide (op = op) && w == w && termBeq a a && termBeq b b) = true
    simp [*]
  case appBool =>
    rename_i op a b iha ihb
    show (decide (op = op) && termBeq a a && termBeq b b) = true
    simp [*]
  case appBool2 =>
    rename_i f a b iha ihb
    show (decide (f = f) && termBeq a a && termBeq b b) = true
    simp [*]


/-- Sorts compared, then the terms. -/
def anyBeq (a b : Σ s : SType, Term s) : Bool := decide (a.1 = b.1) && termBeq a.2 b.2

/-- The width is compared as well as the term (the Sigma index is part of the value). -/
def bitsBeq (a b : Σ w : Nat, Term (.bits w)) : Bool := a.1 == b.1 && termBeq a.2 b.2

theorem anyBeq_eq {a b : Σ s : SType, Term s} (h : anyBeq a b = true) : a = b := by
  obtain ⟨s, a⟩ := a
  obtain ⟨s', b⟩ := b
  simp only [anyBeq, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  obtain ⟨rfl, hb⟩ := termBeq_sound a b h
  rw [eq_of_heq hb]

theorem anyBeq_refl (a : Σ s : SType, Term s) : anyBeq a a = true := by
  simp [anyBeq, termBeq_refl]

theorem bitsBeq_eq {a b : Σ w : Nat, Term (.bits w)} (h : bitsBeq a b = true) : a = b := by
  obtain ⟨w, a⟩ := a
  obtain ⟨w', b⟩ := b
  simp only [bitsBeq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hw, h⟩ := h
  subst hw
  obtain ⟨-, hb⟩ := termBeq_sound a b h
  rw [eq_of_heq hb]

theorem bitsBeq_refl (a : Σ w : Nat, Term (.bits w)) : bitsBeq a a = true := by
  simp [bitsBeq, termBeq_refl]

/-- The comparison looks at the width: terms with `bitsBeq = true` have equal widths. -/
theorem bitsBeq_width {a b : Σ w : Nat, Term (.bits w)} (h : bitsBeq a b = true) : a.1 = b.1 := by
  rw [bitsBeq_eq h]

/-! ## Reset values -/

/-- A reset value as a typed value: Bool ↦ `n != 0`, BitVec w ↦ `BitVec.ofNat w n`. -/
def decInit : (s : SType) → Nat → s.Type
  | .bool, n => decide (n ≠ 0)
  | .bits w, n => BitVec.ofNat w n

/-- The reset values slot by slot; a missing slot reads `0`. -/
def initsFrom (slots : List SlotField) : (ss : List SType) → HList (tys ss)
  | []      => ()
  | s :: ss => (decInit s ((slots.head?.map (·.init)).getD 0), initsFrom slots.tail ss)

def initsOf (d : MachineData) : HList (tys d.ss) := initsFrom d.shape.layout.slots d.ss

theorem enc_decInit : ∀ (s : SType) (n : Nat), n < 2 ^ s.width → enc s (decInit s n) = n
  | .bool, n, h => by
    have h2 : n < 2 := by simpa [SType.width] using h
    show encodeBool (decide (n ≠ 0)) = n
    unfold encodeBool
    by_cases h0 : n = 0
    · subst h0; rfl
    · have : n = 1 := by omega
      subst this; rfl
  | .bits w, n, h => by
    show (BitVec.ofNat w n).toNat = n
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h

theorem encState_initsFrom : ∀ (ss : List SType) (slots : List SlotField) (i : Nat) (s : SType),
    ss[i]? = some s → (slots[i]?.map (·.init)).getD 0 < 2 ^ s.width →
    encState ss (initsFrom slots ss) i = (slots[i]?.map (·.init)).getD 0
  | [], _, _, _, h, _ => by simp at h
  | t :: ss, slots, 0, s, h, hlt => by
    have hs : t = s := by simpa using h
    subst hs
    cases slots with
    | nil => simpa [initsFrom, encState] using enc_decInit t 0 (by simpa using hlt)
    | cons f fs =>
      simp only [initsFrom, encState, List.head?_cons, Option.map_some, Option.getD_some,
        List.getElem?_cons_zero] at hlt ⊢
      exact enc_decInit t f.init hlt
  | t :: ss, slots, i + 1, s, h, hlt => by
    have h' : ss[i]? = some s := by simpa using h
    have hget : slots.tail[i]? = slots[i + 1]? := by
      cases slots <;> simp
    have := encState_initsFrom ss slots.tail i s h' (by rw [hget]; exact hlt)
    simpa [initsFrom, encState, hget] using this

/-! ## `zipAllB` pointwise -/

theorem zipAllB_get {α β : Type} (p : α → β → Bool) :
    ∀ (as : List α) (bs : List β), zipAllB p as bs = true →
      as.length = bs.length ∧
      ∀ (i : Nat) (a : α) (b : β), as[i]? = some a → bs[i]? = some b → p a b = true
  | [], [], _ => ⟨rfl, fun i a b h _ => by simp at h⟩
  | a :: as, b :: bs, h => by
    simp only [zipAllB, Bool.and_eq_true] at h
    obtain ⟨hab, hrest⟩ := h
    obtain ⟨hl, hg⟩ := zipAllB_get p as bs hrest
    refine ⟨by simp [hl], fun i a' b' ha hb => ?_⟩
    cases i with
    | zero =>
      simp at ha hb
      subst ha; subst hb; exact hab
    | succ i => exact hg i a' b' (by simpa using ha) (by simpa using hb)
  | [], _ :: _, h => by simp [zipAllB] at h
  | _ :: _, [], h => by simp [zipAllB] at h

/-! ## U-C -/

theorem initOk_of_ok (d : MachineData) (h : d.ok = true) : d.initOk (initsOf d) = true := by
  unfold MachineData.ok at h
  simp only [Bool.and_eq_true] at h
  have h1 : d.nIn + d.ss.length ≤ d.shape.binders.length := of_decide_eq_true h.1
  have hz := h.2.2.2.2.2.1
  have hK : ∀ i, i < d.ss.length → d.K (d.nIn + i) = d.ss[i]? :=
    of_decide_eq_true h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hlen, hget⟩ := zipAllB_get _ _ _ hz
  have hsb : d.slotBs.length = d.ss.length := by
    unfold MachineData.slotBs; simp only [List.length_take, List.length_drop]; omega
  unfold MachineData.initOk
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < d.ss.length := List.mem_range.mp hi
  obtain ⟨s, hs⟩ : ∃ s, d.ss[i]? = some s := ⟨d.ss[i], List.getElem?_eq_getElem hi'⟩
  have hslot : i < d.shape.layout.slots.length := by omega
  obtain ⟨f, hf⟩ : ∃ f, d.shape.layout.slots[i]? = some f := ⟨_, List.getElem?_eq_getElem hslot⟩
  obtain ⟨b, hbi⟩ : ∃ b, d.shape.binders[d.nIn + i]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hsl : d.slotBs[i]? = some b := by
    unfold MachineData.slotBs
    rw [List.getElem?_take_of_lt hi', List.getElem?_drop, hbi]
  have hrow := hget i f b hf hsl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨hw, -, hinit⟩ := hrow
  have hKi := hK i hi'
  unfold MachineData.K at hKi
  rw [hbi, hs] at hKi
  simp only [Option.bind_some] at hKi
  have hwidth : f.width = s.width := by
    rw [hw]
    revert hKi
    cases hb2 : b.2 <;> simp [sortOf, machWidth] <;> (intro hh; subst hh; rfl)
  have hlt : (d.shape.layout.slots[i]?.map (·.init)).getD 0 < 2 ^ s.width := by
    rw [hf]; simp only [Option.map_some, Option.getD_some]; rw [← hwidth]; exact hinit
  have := encState_initsFrom d.ss d.shape.layout.slots i s hs hlt
  simp [initsOf, this]
