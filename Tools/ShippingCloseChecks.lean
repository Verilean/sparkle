import Tools.ShippingCloseInstsSome

/-! # The reordering and the checks of `closeInsts`, from facts about the body

`topoBody` succeeds and `closeChecks` holds of its result, given facts about
the closed module's body `mb` and the instance statements `stmts` that do NOT
mention the reordered body: a rank, `woCheck` of `mb`, registers only beside
the combinational statements, the linked writes distinct, each instance's
child found with the ports the order sees — and the design facts, stated on
`mb ++ stmts`. Pure. -/
namespace Tools.ShippingCloseChecks
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingTopoBody Tools.ShippingTopoChecks Tools.ShippingTopoLinked
open Tools.ShippingCloseInstsSome

theorem writesOf_insts : ∀ (l : List Stmt), l.all isInst = true → writesOf l = []
  | [], _ => rfl
  | st :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := writesOf_insts l h.2
    unfold writesOf at ih ⊢
    cases st <;> simp_all [isInst, stmtWrites]

/-- Instance statements after a body do not change `woCheck`. -/
theorem woCheck_append_insts (b : List Stmt) (hb : b.all isInst = true) :
    ∀ (a : List Stmt) (done : List String), woCheck done a = true → woCheck done (a ++ b) = true
  | [], done, _ => by
    induction b generalizing done with
    | nil => rfl
    | cons st b ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hb
      have := ih hb.2 (done ++ stmtWrites st)
      cases st <;> simp_all [isInst, woCheck, stmtReads, stmtWrites]
  | st :: a, done, h => by
    simp only [woCheck, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hw : writesOf (a ++ b) = writesOf a := by
      rw [Tools.ShippingTopoChecks.writesOf_append, writesOf_insts b hb, List.append_nil]
    show woCheck done (st :: (a ++ b)) = true
    simp only [woCheck, Bool.and_eq_true, hw]
    exact ⟨⟨h1, h2⟩, woCheck_append_insts b hb a _ h3⟩

theorem nextKeys_append_insts (a b : List Stmt) (hb : b.all isInst = true) :
    nextKeys (a ++ b) = nextKeys a := by
  have : nextKeys b = [] := by
    induction b with
    | nil => rfl
    | cons st b ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hb
      have := ih hb.2
      unfold nextKeys at this ⊢
      cases st <;> simp_all [isInst]
  unfold nextKeys at this ⊢
  rw [List.flatMap_append, this, List.append_nil]

/-- A statement of the body is combinational or one of the others. -/
theorem mem_split {body : List Stmt} {st : Stmt} (h : st ∈ body) :
    st ∈ combOf body ∨ st ∈ othersOf body := by
  rw [combOf_eq, othersOf_eq]
  by_cases hc : isComb st = true
  · exact Or.inl (List.mem_filter.mpr ⟨h, hc⟩)
  · exact Or.inr (List.mem_filter.mpr ⟨h, by simpa using hc⟩)

theorem noMem_of {body : List Stmt} (hreg : ∀ st ∈ othersOf body, isReg st = true) :
    body.filterMap stmtMemName = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro st hs
  rcases mem_split hs with h | h
  · rw [combOf_eq] at h
    have := (List.mem_filter.mp h).2
    cases st <;> simp_all [isComb, stmtMemName]
  · have := hreg st h
    cases st <;> simp_all [isReg, stmtMemName]

/-- **`topoBody` succeeds and the checks hold**, from facts about the closed
body `mb` and the instance statements `stmts`. -/
theorem closeChecks_of {portNames : List String} {children : List (Module × Design)}
    {mname : String} {d' : Design} {mb stmts : List Stmt}
    (hinst : stmts.all isInst = true) (hpn : portNames.Nodup)
    (hwo : woCheck [] mb = true)
    (rank : Stmt → Nat)
    (hrank : ∀ st ∈ combOf (mb ++ stmts), ∀ r ∈ combReads (byAssignOf (mb ++ stmts)) st,
      r ∈ drivenOf (mb ++ stmts) →
      ∃ st' ∈ combOf (mb ++ stmts), r ∈ combWrites (byAssignOf (mb ++ stmts)) st' ∧
        rank st' < rank st)
    (hreg : ∀ st ∈ othersOf (mb ++ stmts), isReg st = true)
    (hwn : (writesOf (combOf (mb ++ stmts))).Nodup)
    (hkeys : (nextKeys mb).Nodup)
    (hlw : (bodyWrites (moduleByName d'.modules) (combOf (mb ++ stmts))).Nodup)
    (hlD : ∀ n ∈ bodyWrites (moduleByName d'.modules) (combOf (mb ++ stmts)),
      n ∈ drivenOf (mb ++ stmts))
    (hagree : ∀ mn i conns, Stmt.inst mn i conns ∈ mb ++ stmts →
      ∃ child, moduleByName d'.modules mn = some child ∧
        instOuts child.outputs conns =
          combWrites (byAssignOf (mb ++ stmts)) (.inst mn i conns) ∧
        ∀ c ∈ conns, ∃ w, c.2 = Expr.ref w)
    (hnames : children.all (fun c => decide (moduleByName d'.modules c.1.name = some c.1) &&
      c.2.modules.all (fun g => decide (moduleByName d'.modules g.name = some g))) = true)
    (hno : noInstOfB mname (mb ++ stmts) = true)
    (hnoD : d'.modules.all (fun g => noInstOfB mname g.body) = true)
    (hkids : kidsCombB d'.modules (mb ++ stmts) = true) :
    ∃ body, topoBody (mb ++ stmts) = some body ∧
      closeChecks portNames children mname d' stmts (mb ++ stmts) body = true := by
  obtain ⟨sorted, htopo, hperm, hord⟩ := topoBody_some_rank rank hrank
  refine ⟨_, htopo, ?_⟩
  have hcs : ∀ st ∈ sorted, isComb st = true := by
    intro st hs
    have := hperm.subset hs
    rw [combOf_eq] at this
    exact (List.mem_filter.mp this).2
  have hAD : ∀ n, n ∈ byAssignOf (mb ++ stmts) → n ∈ drivenOf (mb ++ stmts) :=
    fun n h => List.mem_append_left _ h
  have hbperm : (mb ++ stmts).Perm (sorted ++ othersOf (mb ++ stmts)) :=
    (perm_split _).trans (hperm.symm.append_right _)
  have hwperm : (writesOf sorted).Perm (writesOf (combOf (mb ++ stmts))) :=
    hperm.flatMap_right _
  unfold closeChecks
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hinst, hpn⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hnames⟩, ?_⟩, hnoD⟩, ?_⟩
  · exact woCheck_append_insts stmts hinst mb [] hwo
  · exact woCheck_ordered _ _ hAD _ hreg sorted [] [] hcs hord (hwperm.nodup_iff.mpr hwn)
      (fun n hn => hwperm.subset hn) (fun n hn => by simp at hn) (fun n hn => by simp at hn)
  · exact isPermOf_complete hbperm
  · exact seqOf_sorted hperm
  · rw [nextKeys_append_insts mb stmts hinst]
    exact hkeys
  · rw [noMem_of hreg]
    exact List.nodup_nil
  · refine linkedOk_ordered _ _ _ hAD _ hreg sorted [] hcs hord
      ((bodyWrites_perm _ hperm).nodup_iff.mpr hlw)
      (fun n hn => hlD n ((bodyWrites_perm _ hperm).subset hn)) (fun n hn => by simp at hn) ?_
    intro mn i conns hm
    have := hperm.subset hm
    rw [combOf_eq] at this
    exact hagree mn i conns (List.mem_filter.mp this).1
  · unfold noInstOfB at hno ⊢
    rw [List.all_eq_true] at hno ⊢
    exact fun st hs => hno st (hbperm.symm.subset hs)
  · unfold kidsCombB at hkids ⊢
    rw [List.all_eq_true] at hkids ⊢
    exact fun st hs => hkids st (hbperm.symm.subset hs)

end Tools.ShippingCloseChecks
