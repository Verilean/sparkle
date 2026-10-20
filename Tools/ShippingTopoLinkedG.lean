import Tools.ShippingTopoLinked

/-! # `linkedOk` of a dependency order — instances with several outputs and a clock

`linkedOk_ordered` asks that the order's view of an instance (`combWrites`:
every connected wire no assignment drives) IS the child's view of its outputs
(`instOuts`). For the general closing that is false: a sequential child's
instance is also connected to `clk` and `rst`, which no assignment drives and
which are no outputs. Here the two views may differ: the child's outputs are
among the order's writes, and a connected wire that is neither assigned nor
one of the instance's outputs (the clock, the reset) is driven by NOTHING in
the body. Any number of outputs per instance. Pure. -/
namespace Tools.ShippingTopoLinkedG
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingTopoBody Tools.ShippingTopoChecks Tools.ShippingTopoLinked

variable (ch : String → Option Module)

/-- **`linkedOk` of a dependency order**, the general form. Every instance of
`L` has its child; its outputs in the child's view are among the order's
writes; a connected wire outside both views of "driven" (not assigned, not an
output of this instance) is not driven in `L` at all; connections are
wires. -/
theorem linkedOk_ordered_G (A D : List String) (hAD : ∀ n, n ∈ A → n ∈ D)
    (others : List Stmt) (hreg : ∀ st ∈ others, isReg st = true) (L0 : List Stmt) :
    ∀ (L : List Stmt) (S : List String), (∀ st ∈ L, st ∈ L0) → (∀ st ∈ L, isComb st = true) →
      Ordered A D S L → (bodyWrites ch L).Nodup → (∀ n ∈ bodyWrites ch L, n ∈ D) →
      (∀ n ∈ S, n ∉ bodyWrites ch L) →
      (∀ mn i conns, Stmt.inst mn i conns ∈ L0 → ∃ child, ch mn = some child ∧
        (∀ w ∈ instOuts child.outputs conns, w ∈ combWrites A (.inst mn i conns)) ∧
        (∀ w ∈ combWrites A (.inst mn i conns), w ∉ instOuts child.outputs conns →
          w ∉ bodyWrites ch L0) ∧
        ∀ c ∈ conns, ∃ w, c.2 = Expr.ref w) →
      (∀ n, n ∈ bodyWrites ch L → n ∈ bodyWrites ch L0) →
      linkedOk ch (L ++ others) = true
  | [], _, _, _, _, _, _, _, _, _ => linkedOk_regs ch others hreg
  | st :: L, S, hsub, hc, ho, hnd, hD, hS, hinst, hW0 => by
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
      have ih := linkedOk_ordered_G A D hAD others hreg L0 L (combWrites A (.assign l r) ++ S)
        (fun s hs => hsub s (List.mem_cons_of_mem _ hs))
        (fun s hs => hc s (List.mem_cons_of_mem _ hs)) ho.2 (List.nodup_cons.mp hnd).2
        (fun n hn => hD n (List.mem_cons_of_mem _ hn))
        (by
          intro n hn hL
          rcases List.mem_append.mp hn with h1 | h2
          · have : n = l := by simpa [combWrites, stmtWrites] using h1
            exact hl (this ▸ hL)
          · exact hS n h2 (List.mem_cons_of_mem _ hL))
        hinst (fun n hn => hW0 n (by rw [hw]; exact List.mem_cons_of_mem _ hn))
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
      obtain ⟨child, hch, hsubO, hextra, hrefs⟩ := hinst mn i conns (hsub _ (List.mem_cons_self ..))
      have hw : bodyWrites ch (Stmt.inst mn i conns :: L) =
          instOuts child.outputs conns ++ bodyWrites ch L := by
        show stmtOuts ch (Stmt.inst mn i conns) ++ bodyWrites ch L = _
        simp only [stmtOuts, hch]
      rw [hw] at hnd hD hS hlater
      obtain ⟨hnd1, hnd2, hdisj⟩ := List.nodup_append.mp hnd
      have hW0' : ∀ n, n ∈ bodyWrites ch L → n ∈ bodyWrites ch L0 :=
        fun n hn => hW0 n (by rw [hw]; exact List.mem_append_right _ hn)
      have ih := linkedOk_ordered_G A D hAD others hreg L0 L (combWrites A (.inst mn i conns) ++ S)
        (fun s hs => hsub s (List.mem_cons_of_mem _ hs))
        (fun s hs => hc s (List.mem_cons_of_mem _ hs)) ho.2 hnd2
        (fun n hn => hD n (List.mem_append_right _ hn))
        (by
          intro n hn hL
          rcases List.mem_append.mp hn with h1 | h2
          · by_cases ho' : n ∈ instOuts child.outputs conns
            · exact hdisj n ho' n hL rfl
            · exact hextra n h1 ho' (hW0' n hL)
          · exact hS n h2 (List.mem_append_right _ hL))
        hinst hW0'
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
        · by_cases ho' : w ∈ instOuts child.outputs conns
          · exact Or.inl ho'
          · right
            have hcw : w ∈ combWrites A (.inst mn i conns) := by
              simp only [combWrites, List.mem_filterMap]
              exact ⟨(p, .ref w), hcm, by simp [hA]⟩
            have := hextra w hcw ho'
            simpa using fun h => this (hW0' w h)
    | register o c r inp iv =>
      have := hc _ (List.mem_cons_self ..)
      simp [isComb] at this
    | memory =>
      have := hc _ (List.mem_cons_self ..)
      simp [isComb] at this

end Tools.ShippingTopoLinkedG
