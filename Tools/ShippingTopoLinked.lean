import Tools.ShippingTopoChecks

/-! # `linkedOk` of `topoBody`'s result

`closeInsts` also asks the reordered body to be in the LINKED order
(`linkedOk`): an assignment reading an instance's output comes after the
instance, an instance comes after the assignments driving its arguments, and
nothing is driven twice. Here it follows from the dependency order
`topoBody_some` returns, when the order's view of an instance (the connected
wires no assignment drives are its outputs) agrees with the children's
modules (the outputs are the wires on the child's output ports). Pure. -/
namespace Tools.ShippingTopoLinked
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingTopoBody Tools.ShippingTopoChecks

variable (ch : String → Option Module)

/-- What a statement drives, in the linked view. -/
def linkW : Stmt → List String
  | .assign l _ => [l]
  | st => stmtOuts ch st

theorem bodyWrites_eq : ∀ (L : List Stmt), bodyWrites ch L = L.flatMap (linkW ch)
  | [] => rfl
  | st :: L => by
    have ih := bodyWrites_eq L
    cases st <;> simp [bodyWrites, linkW, ih]

theorem bodyOuts_eq : ∀ (L : List Stmt), bodyOuts ch L = L.flatMap (stmtOuts ch)
  | [] => rfl
  | st :: L => by
    have ih := bodyOuts_eq L
    simp [bodyOuts, ih]

theorem stmtOuts_sub (st : Stmt) : ∀ n ∈ stmtOuts ch st, n ∈ linkW ch st := by
  intro n h
  cases st <;> first | exact h | (simp [stmtOuts] at h)

theorem bodyOuts_sub (L : List Stmt) : ∀ n ∈ bodyOuts ch L, n ∈ bodyWrites ch L := by
  intro n h
  rw [bodyOuts_eq] at h
  rw [bodyWrites_eq]
  obtain ⟨st, hs, hn⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨st, hs, stmtOuts_sub ch st n hn⟩

theorem bodyWrites_append (a b : List Stmt) :
    bodyWrites ch (a ++ b) = bodyWrites ch a ++ bodyWrites ch b := by
  rw [bodyWrites_eq, bodyWrites_eq, bodyWrites_eq, List.flatMap_append]

theorem bodyWrites_regs : ∀ (l : List Stmt), (∀ st ∈ l, isReg st = true) → bodyWrites ch l = []
  | [], _ => rfl
  | st :: l, h => by
    have h1 := h st (List.mem_cons_self ..)
    have ih := bodyWrites_regs l (fun s hs => h s (List.mem_cons_of_mem _ hs))
    cases st <;> simp_all [isReg, bodyWrites, stmtOuts]

theorem linkedOk_regs : ∀ (l : List Stmt), (∀ st ∈ l, isReg st = true) → linkedOk ch l = true
  | [], _ => rfl
  | st :: l, h => by
    have h1 := h st (List.mem_cons_self ..)
    have ih := linkedOk_regs l (fun s hs => h s (List.mem_cons_of_mem _ hs))
    cases st <;> simp_all [isReg, linkedOk]

/-- The linked writes of a permutation. -/
theorem bodyWrites_perm {a b : List Stmt} (h : a.Perm b) :
    (bodyWrites ch a).Perm (bodyWrites ch b) := by
  rw [bodyWrites_eq, bodyWrites_eq]
  exact h.flatMap_right _

/-- **`linkedOk` of a dependency order.** `S`: settled names nothing later
drives. Every instance of `L` has its child (`ch`), its outputs in the
child's view are the order's (`combWrites`), and its connections are
wires. -/
theorem linkedOk_ordered (A D : List String) (hAD : ∀ n, n ∈ A → n ∈ D)
    (others : List Stmt) (hreg : ∀ st ∈ others, isReg st = true) :
    ∀ (L : List Stmt) (S : List String), (∀ st ∈ L, isComb st = true) →
      Ordered A D S L → (bodyWrites ch L).Nodup → (∀ n ∈ bodyWrites ch L, n ∈ D) →
      (∀ n ∈ S, n ∉ bodyWrites ch L) →
      (∀ mn i conns, Stmt.inst mn i conns ∈ L → ∃ child, ch mn = some child ∧
        instOuts child.outputs conns = combWrites A (.inst mn i conns) ∧
        ∀ c ∈ conns, ∃ w, c.2 = Expr.ref w) →
      linkedOk ch (L ++ others) = true
  | [], _, _, _, _, _, _, _ => linkedOk_regs ch others hreg
  | st :: L, S, hc, ho, hnd, hD, hS, hinst => by
    have hrestW : bodyWrites ch (L ++ others) = bodyWrites ch L := by
      rw [bodyWrites_append, bodyWrites_regs ch others hreg, List.append_nil]
    have hready := ho.1
    simp only [readyB, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem,
      Bool.not_eq_true'] at hready
    have hlater : ∀ n, n ∈ combReads A st → n ∈ D → n ∉ bodyWrites ch (st :: L) := by
      intro n hn hd
      rcases hready n hn with hs | hnd'
      · exact hS n hs
      · simp_all
    cases st with
    | assign l r =>
      have hw : bodyWrites ch (Stmt.assign l r :: L) = l :: bodyWrites ch L := rfl
      rw [hw] at hnd hD hS hlater
      have hl : l ∉ bodyWrites ch L := (List.nodup_cons.mp hnd).1
      have ih := linkedOk_ordered A D hAD others hreg L (combWrites A (.assign l r) ++ S)
        (fun s hs => hc s (List.mem_cons_of_mem _ hs)) ho.2 (List.nodup_cons.mp hnd).2
        (fun n hn => hD n (List.mem_cons_of_mem _ hn))
        (by
          intro n hn hL
          rcases List.mem_append.mp hn with h1 | h2
          · have : n = l := by simpa [combWrites, stmtWrites] using h1
            exact hl (this ▸ hL)
          · exact hS n h2 (List.mem_cons_of_mem _ hL))
        (fun mn i conns hm => hinst mn i conns (List.mem_cons_of_mem _ hm))
      show linkedOk ch (Stmt.assign l r :: (L ++ others)) = true
      simp only [linkedOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, ih, and_true]
      refine ⟨?_, ?_⟩
      · have : l ∉ bodyOuts ch (L ++ others) := fun h => hl (hrestW ▸ bodyOuts_sub ch _ l h)
        simpa using this
      · intro n hn
        have hno : n ∉ bodyOuts ch (L ++ others) := by
          intro h
          have hw' : n ∈ bodyWrites ch L := hrestW ▸ bodyOuts_sub ch _ n h
          exact hlater n hn (hD n (List.mem_cons_of_mem _ hw')) (List.mem_cons_of_mem _ hw')
        simpa using hno
    | inst mn i conns =>
      obtain ⟨child, hch, houts, hrefs⟩ := hinst mn i conns (List.mem_cons_self ..)
      have hw : bodyWrites ch (Stmt.inst mn i conns :: L) =
          instOuts child.outputs conns ++ bodyWrites ch L := by
        show stmtOuts ch (Stmt.inst mn i conns) ++ bodyWrites ch L = _
        simp only [stmtOuts, hch]
      rw [hw] at hnd hD hS hlater
      obtain ⟨hnd1, hnd2, hdisj⟩ := List.nodup_append.mp hnd
      have ih := linkedOk_ordered A D hAD others hreg L (combWrites A (.inst mn i conns) ++ S)
        (fun s hs => hc s (List.mem_cons_of_mem _ hs)) ho.2 hnd2
        (fun n hn => hD n (List.mem_append_right _ hn))
        (by
          intro n hn hL
          rcases List.mem_append.mp hn with h1 | h2
          · rw [← houts] at h1
            exact hdisj n h1 n hL rfl
          · exact hS n h2 (List.mem_append_right _ hL))
        (fun mn i conns hm => hinst mn i conns (List.mem_cons_of_mem _ hm))
      show linkedOk ch (Stmt.inst mn i conns :: (L ++ others)) = true
      simp only [linkedOk, hch, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, ih,
        and_true, decide_eq_true_eq, hrestW]
      refine ⟨⟨?_, hnd1⟩, ?_⟩
      · intro n hn
        simpa using fun h => hdisj n hn n h rfl
      · intro c hcm
        obtain ⟨w, hw'⟩ := hrefs c hcm
        obtain ⟨p, e⟩ := c
        simp only [] at hw'
        subst hw'
        simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem]
        by_cases hA : w ∈ A
        · right
          have hread : w ∈ combReads A (.inst mn i conns) := by
            simp only [combReads, List.mem_flatMap]
            exact ⟨(p, .ref w), hcm, by simpa [refsOf] using hA⟩
          have := hlater w hread (hAD w hA)
          simpa using fun h => this (List.mem_append_right _ h)
        · left
          rw [houts]
          simp only [combWrites, List.mem_filterMap]
          exact ⟨(p, .ref w), hcm, by simp [hA]⟩
    | register o c r inp iv =>
      have := hc _ (List.mem_cons_self ..)
      simp [isComb] at this
    | memory =>
      have := hc _ (List.mem_cons_self ..)
      simp [isComb] at this

end Tools.ShippingTopoLinked
