import Tools.ShippingGen5SemGen
set_option autoImplicit false
-- NOT BUILT (written in g5cv-r2; the SHA of the first successful Pod build is recorded here by a comment-only commit). Clean build is the coder's. No sorry / axiom / native_decide.

/-! # DG-COVER pure core (units U-C1 … U-C5), `scripts/gen5/DG_COVER_FREEZE.md` §4

Pure lemmas about `GenWF` (rows `RowA/RowB/RowC`), `cleanLets`, `reads`, `machClose` and `kDOf/callKind`. They use only definitions of
`Tools.ShippingGen5SemGen`, `Tools.ShippingMachineRef.reads`, `Sparkle.Compiler.Elab.machClose` and `inputExpr`. They supply no row of the
coverage survey by themselves (no run, no `dataOf`, no reader state); `GenWF` is not changed and `genWF_of_rows`/`genWFRows_of_genWF` are an
equivalence, so nothing is strengthened. -/
namespace Tools.ShippingGen5Cover
open Lean Sparkle.Compiler.Elab Sparkle.IR.Machine Sparkle.Compiler.MachInstOrigin
open Tools.ShippingGen5Sem Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingUnifiedSource (SType Term)
open Tools.ShippingMachineRef (reads)

/-! ## U-C1: the rows as ∀-statements -/

theorem rowA_iff (d : MachineData) : RowA d = true ↔
    (d.shape.insts.length ≤ d.nIn ∧ d.shape.instOrigins.length = d.shape.insts.length ∧
     ∀ k, k < d.shape.insts.length →
       (∀ l ∈ callArgs d k, l < d.ls.length) ∧
       ∀ cb aw dw, originOf d k = .mem cb aw dw → (callArgs d k).length = 4) := by
  unfold RowA
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun k => imp_congr Iff.rfl ?_))
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun cb aw dw ho => ?_⟩
    rw [ho] at h2
    simpa using h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases ho : originOf d k with
    | mem cb aw dw => simpa using h2 cb aw dw ho
    | _ => rfl

theorem rowB_iff (d : MachineData) : RowB d = true ↔
    ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain ∧
      ∀ cb aw dw, originOf d k = .mem cb aw dw →
        ∃ l0 l1 l2 l3, callArgs d k = [l0, l1, l2, l3] ∧ callKind d k = .bits dw ∧
          letSort d l0 = some (.bits aw) ∧ letSort d l1 = some (.bits dw) ∧
          letSort d l2 = some .bool ∧ letSort d l3 = some (.bits aw) := by
  unfold RowB
  simp only [List.all_eq_true, List.mem_range]
  refine forall_congr' fun k => imp_congr Iff.rfl ?_
  rw [Bool.and_eq_true]
  refine and_congr ?_ ?_
  · cases callKind d k <;> simp
  · constructor
    · intro h cb aw dw ho
      rw [ho] at h
      revert h
      cases hc : callArgs d k with
      | nil => simp
      | cons l0 t0 =>
        cases t0 with
        | nil => simp
        | cons l1 t1 =>
          cases t1 with
          | nil => simp
          | cons l2 t2 =>
            cases t2 with
            | nil => simp
            | cons l3 t3 =>
              cases t3 with
              | nil =>
                intro h
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                exact ⟨l0, l1, l2, l3, rfl, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
              | cons _ _ => simp
    · intro h
      cases ho : originOf d k with
      | mem cb aw dw =>
        obtain ⟨l0, l1, l2, l3, ha, hk, s0, s1, s2, s3⟩ := h cb aw dw ho
        rw [ha]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨⟨hk, s0⟩, s1⟩, s2⟩, s3⟩
      | _ => cases callArgs d k <;> simp

theorem rowC_iff (d : MachineData) : RowC d = true ↔
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true := by
  unfold RowC
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]

theorem genWF_iff (d : MachineData) : GenWF d = true ↔ RowA d = true ∧ RowB d = true ∧ RowC d = true := by
  unfold GenWF
  simp only [Bool.and_eq_true, and_assoc]

/-! ## U-C5: `GenWFRows` -/

structure GenWFRows (d : MachineData) : Prop where
  a1  : d.shape.insts.length ≤ d.nIn
  a2  : d.shape.instOrigins.length = d.shape.insts.length
  a3  : ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, l < d.ls.length
  a4  : ∀ k, k < d.shape.insts.length → ∀ cb aw dw, originOf d k = .mem cb aw dw → (callArgs d k).length = 4
  b1  : ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain
  b23 : ∀ k, k < d.shape.insts.length → ∀ cb aw dw, originOf d k = .mem cb aw dw →
          ∃ l0 l1 l2 l3, callArgs d k = [l0, l1, l2, l3] ∧ callKind d k = .bits dw ∧
            letSort d l0 = some (.bits aw) ∧ letSort d l1 = some (.bits dw) ∧
            letSort d l2 = some .bool ∧ letSort d l3 = some (.bits aw)
  c   : ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

theorem genWF_of_rows {d : MachineData} (h : GenWFRows d) : GenWF d = true :=
  (genWF_iff d).2
    ⟨(rowA_iff d).2 ⟨h.a1, h.a2, fun k hk => ⟨h.a3 k hk, h.a4 k hk⟩⟩,
     (rowB_iff d).2 fun k hk => ⟨h.b1 k hk, h.b23 k hk⟩,
     (rowC_iff d).2 h.c⟩

theorem genWFRows_iff (d : MachineData) : GenWFRows d ↔
    (d.shape.insts.length ≤ d.nIn ∧ d.shape.instOrigins.length = d.shape.insts.length ∧
     (∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, l < d.ls.length) ∧
     (∀ k, k < d.shape.insts.length → ∀ cb aw dw, originOf d k = .mem cb aw dw → (callArgs d k).length = 4) ∧
     (∀ k, k < d.shape.insts.length → callKind d k ≠ .domain) ∧
     (∀ k, k < d.shape.insts.length → ∀ cb aw dw, originOf d k = .mem cb aw dw →
        ∃ l0 l1 l2 l3, callArgs d k = [l0, l1, l2, l3] ∧ callKind d k = .bits dw ∧
          letSort d l0 = some (.bits aw) ∧ letSort d l1 = some (.bits dw) ∧
          letSort d l2 = some .bool ∧ letSort d l3 = some (.bits aw)) ∧
     (∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true)) :=
  ⟨fun h => ⟨h.a1, h.a2, h.a3, h.a4, h.b1, h.b23, h.c⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩⟩

theorem genWFRows_of_genWF {d : MachineData} (h : GenWF d = true) : GenWFRows d := by
  obtain ⟨hA, hB, hC⟩ := (genWF_iff d).1 h
  obtain ⟨a1, a2, ha⟩ := (rowA_iff d).1 hA
  exact ⟨a1, a2, fun k hk => (ha k hk).1, fun k hk => (ha k hk).2,
    fun k hk => ((rowB_iff d).1 hB k hk).1, fun k hk => ((rowB_iff d).1 hB k hk).2, (rowC_iff d).1 hC⟩

/-! ## U-C2: `cleanLets` facts -/

theorem cleanLets_length (d : MachineData) (k : Nat) : (cleanLets d k).length = d.ls.length := by
  unfold cleanLets
  suffices ∀ (ls : List (Σ s : SType, Term s)) (acc : List Bool),
      (ls.foldl (fun clean l => clean ++ [reads (fun j => posOk d k clean (d.bpos j))
        (fun j => posOk d k clean (d.vpos j)) l.2]) acc).length = acc.length + ls.length by
    simpa using this d.ls []
  intro ls
  induction ls with
  | nil => intro acc; simp
  | cons l ls ih => intro acc; simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]; omega

theorem reads_mono {okB okV okB' okV' : Nat → Bool}
    (hb : ∀ j, okB j = true → okB' j = true) (hv : ∀ j, okV j = true → okV' j = true) :
    ∀ {s : SType} (t : Term s), reads okB okV t = true → reads okB' okV' t = true := by
  intro s t
  induction t with
  | boolInput j => exact hb j
  | bitsInput w j => exact hv j
  | boolLit _ => intro _; rfl
  | bitsLit _ _ => intro _; rfl
  | bitsNum _ _ => intro _; rfl
  | binary op a b iha ihb => intro h; simp only [reads, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | compare op a b iha ihb => intro h; simp only [reads, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | boolBinary op a b iha ihb => intro h; simp only [reads, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | boolNot a iha => intro h; simp only [reads] at h ⊢; exact iha h
  | boolEq a b iha ihb => intro h; simp only [reads, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | mux c a b ihc iha ihb =>
    intro h; simp only [reads, Bool.and_eq_true] at h ⊢; exact ⟨⟨ihc h.1.1, iha h.1.2⟩, ihb h.2⟩
  | setw _ a iha => intro h; simp only [reads] at h ⊢; exact iha h
  | appCompare _ a b iha ihb => intro h; simp only [reads, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | appBool _ a b iha ihb => intro h; simp only [reads, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | appBool2 _ a b iha ihb => intro h; simp only [reads, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | slice _ _ _ a iha => intro h; simp only [reads] at h ⊢; exact iha h
  | concat a b iha ihb => intro h; simp only [reads, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | concatLitHi _ _ b ihb => intro h; simp only [reads] at h ⊢; exact ihb h
  | concatLitLo a _ _ iha => intro h; simp only [reads] at h ⊢; exact iha h
  | zextMap _ _ a iha => intro h; simp only [reads] at h ⊢; exact iha h
  | sliceF _ _ _ a iha => intro h; simp only [reads] at h ⊢; exact iha h

theorem posOk_mono (d : MachineData) {k k' : Nat} (hk : k ≤ k') {clean clean' : List Bool}
    (hc : ∀ i, clean.getD i false = true → clean'.getD i false = true) (p : Nat) :
    posOk d k clean p = true → posOk d k' clean' p = true := by
  unfold posOk
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rintro ((h | h) | h)
  · exact Or.inl (Or.inl (by omega))
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨h.1, hc _ h.2⟩

theorem getD_true_iff (l : List Bool) (i : Nat) : l.getD i false = true ↔ l[i]? = some true := by
  rw [List.getD_eq_getElem?_getD]
  cases l[i]? with
  | none => simp
  | some b => simp

/-- An argument `let` that is clean for call `k` is clean for every later call `k'`. -/
theorem cleanLets_mono (d : MachineData) {k k' : Nat} (hk : k ≤ k') (l : Nat) :
    (cleanLets d k)[l]? = some true → (cleanLets d k')[l]? = some true := by
  unfold cleanLets
  suffices ∀ (ls : List (Σ s : SType, Term s)) (acc acc' : List Bool), acc.length = acc'.length →
      (∀ i, acc.getD i false = true → acc'.getD i false = true) →
      ∀ i, (ls.foldl (fun clean l => clean ++ [reads (fun j => posOk d k clean (d.bpos j))
          (fun j => posOk d k clean (d.vpos j)) l.2]) acc).getD i false = true →
        (ls.foldl (fun clean l => clean ++ [reads (fun j => posOk d k' clean (d.bpos j))
          (fun j => posOk d k' clean (d.vpos j)) l.2]) acc').getD i false = true by
    have key := this d.ls [] [] rfl (by simp)
    intro h
    exact (getD_true_iff _ _).1 (key l ((getD_true_iff _ _).2 h))
  intro ls
  induction ls with
  | nil => intro acc acc' _ hc i; exact hc i
  | cons x ls ih =>
    intro acc acc' hlen hc i
    simp only [List.foldl_cons]
    refine ih _ _ (by simp [hlen]) ?_ i
    intro i hi
    rw [getD_true_iff] at hi ⊢
    by_cases hi' : i < acc.length
    · rw [List.getElem?_append_left hi'] at hi
      rw [List.getElem?_append_left (hlen ▸ hi')]
      exact (getD_true_iff _ _).1 (hc i ((getD_true_iff _ _).2 hi))
    · rw [List.getElem?_append_right (by omega)] at hi
      rw [List.getElem?_append_right (by omega), ← hlen]
      cases hj : i - acc.length with
      | zero =>
        simp only [hj, List.getElem?_cons_zero] at hi ⊢
        simp only [Option.some.injEq] at hi ⊢
        exact reads_mono (fun j => posOk_mono d hk hc _) (fun j => posOk_mono d hk hc _) x.2 hi
      | succ n => simp [hj] at hi

/-! ## U-C3: placeholder ↔ binder position -/

theorem machClose_machIn (nDecl kI n k i : Nat) (hi : i < nDecl) :
    machClose kI n k 0 (machIn i) = inputExpr (nDecl + kI + n + k) (nDecl - 1 - i) := by
  simp only [machClose, machIn, inputExpr]
  congr 1; omega

theorem machClose_machInstOut (nDecl kI n k j : Nat) (hj : j < kI) :
    machClose kI n k 0 (machInstOut j) = inputExpr (nDecl + kI + n + k) (nDecl + j) := by
  simp only [machClose, machInstOut, inputExpr]
  congr 1; omega

theorem machClose_machSlot (nDecl kI n k i : Nat) (hi : i < n) :
    machClose kI n k 0 (machSlot i) = inputExpr (nDecl + kI + n + k) (nDecl + kI + i) := by
  simp only [machClose, machSlot, inputExpr]
  congr 1; omega

theorem machClose_machLet (nDecl kI n k j : Nat) (hj : j < k) :
    machClose kI n k 0 (machLet j) = inputExpr (nDecl + kI + n + k) (nDecl + kI + n + j) := by
  simp only [machClose, machLet, inputExpr]
  congr 1; omega

/-! ## U-C4: `nIn`, `kD` and the call binder -/

theorem kDOf_add_len (d : MachineData) (h : d.shape.insts.length ≤ d.nIn) :
    kDOf d + d.shape.insts.length = d.nIn := by
  unfold kDOf; omega

/-- `callKind` is the stored result kind of entry `k`, given the binder fact at position `kDOf d + k`
(`ShapeDecomp.callBinder_bs` supplies such a fact for a decomposed shape; it is a hypothesis here). -/
theorem callKind_eq_inst (d : MachineData) {k : Nat} (hk : k < d.shape.insts.length)
    (hn : d.shape.insts.length ≤ d.nIn)
    (hb : (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2) :
    callKind d k = (d.shape.insts[k]'hk).2.2 := by
  have hlt : kDOf d + k < d.nIn := by unfold kDOf; omega
  unfold callKind MachineData.bsIn
  rw [List.getElem?_drop, List.getElem?_take_of_lt hlt]
  rw [hb]
  rfl

end Tools.ShippingGen5Cover
