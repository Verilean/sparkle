import Tools.ShippingRankRun

/-! # The rank of a closed transition whose instances drive several wires

The one-output rank (`rank_of_names`, `rank_of_facts`) reads each statement's
ONE driven name. An instance of a call with several outputs (and of a
sequential child, whose connected `clk` / `rst` no assignment drives either)
has a SET of them. Here:

* `rank_of_names_G`: a rank on names under which every driven read of a
  statement ranks below EVERY name the statement drives orders the
  statements — the statement's rank is the least rank of its writes;
* `rank_of_facts_G`: `rank_of_facts` for instances with any number of
  writes, each write a call's output port with its own bound. It is the
  one-output theorem applied to a list in which every instance is replaced
  by one stand-in per write (the same reads, that one write); nothing about
  the rank is proved again.

Pure. Nothing here says a real transition satisfies the hypotheses. -/
namespace Tools.ShippingRankG
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingSettledSoundness (Acyclic)
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingClosedOrder Tools.ShippingRankNames Tools.ShippingCallsRank Tools.ShippingTopoBody
open Tools.ShippingRankRun Tools.ShippingUnifiedSpine Tools.ShippingMachineCloses

/-! ## The least rank of a statement's writes -/

def minOf (ρ : String → Nat) : List String → Nat
  | [] => 0
  | [x] => ρ x
  | x :: xs => min (ρ x) (minOf ρ xs)

theorem minOf_le (ρ : String → Nat) : ∀ (l : List String) (x : String), x ∈ l → minOf ρ l ≤ ρ x
  | [y], x, h => by
    have : x = y := by simpa using h
    subst this
    exact Nat.le_refl _
  | y :: z :: l, x, h => by
    show min (ρ y) (minOf ρ (z :: l)) ≤ ρ x
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (minOf_le ρ (z :: l) x h)

theorem minOf_mem (ρ : String → Nat) : ∀ (l : List String), l ≠ [] → ∃ x ∈ l, minOf ρ l = ρ x
  | [], h => absurd rfl h
  | [y], _ => ⟨y, List.mem_singleton.mpr rfl, rfl⟩
  | y :: z :: l, _ => by
    obtain ⟨x, hx, he⟩ := minOf_mem ρ (z :: l) (by simp)
    show ∃ x ∈ y :: z :: l, min (ρ y) (minOf ρ (z :: l)) = ρ x
    by_cases hle : ρ y ≤ minOf ρ (z :: l)
    · exact ⟨y, List.mem_cons_self .., Nat.min_eq_left hle⟩
    · exact ⟨x, List.mem_cons_of_mem _ hx, by rw [Nat.min_eq_right (by omega), he]⟩

/-- The rank of a statement: the least rank of the names it drives. -/
def rankMin (A : List String) (ρ : String → Nat) (st : Stmt) : Nat := minOf ρ (combWrites A st)

/-- **A rank on names orders statements with several writes.** -/
theorem rank_of_names_G {body : List Stmt} (ρ : String → Nat)
    (hne : ∀ st ∈ combOf body, combWrites (byAssignOf body) st ≠ [])
    (hρ : ∀ st ∈ combOf body, ∀ l ∈ combWrites (byAssignOf body) st,
      ∀ r ∈ combReads (byAssignOf body) st, r ∈ drivenOf body → ρ r < ρ l) :
    ∀ st ∈ combOf body, ∀ r ∈ combReads (byAssignOf body) st, r ∈ drivenOf body →
      ∃ st' ∈ combOf body, r ∈ combWrites (byAssignOf body) st' ∧
        rankMin (byAssignOf body) ρ st' < rankMin (byAssignOf body) ρ st := by
  intro st hs r hr hd
  obtain ⟨st', hs', hw'⟩ := mem_driven hd
  refine ⟨st', hs', hw', ?_⟩
  obtain ⟨l, hl, he⟩ := minOf_mem ρ _ (hne st hs)
  have h1 := minOf_le ρ _ r hw'
  have h2 := hρ st hs l hl r hr hd
  unfold rankMin
  omega

/-- The rank of a statement: the least rank of the KEPT names it drives. -/
def rankMinK (keep : String → Bool) (A : List String) (ρ : String → Nat) (st : Stmt) : Nat :=
  minOf ρ ((combWrites A st).filter keep)

/-- **A rank on names orders statements**, some writes left out of the rank
(`keep`: an instance's connected `clk` / `rst`, which no statement reads as
a driven name). -/
theorem rank_of_names_K {body : List Stmt} (keep : String → Bool) (ρ : String → Nat)
    (hne : ∀ st ∈ combOf body, (combWrites (byAssignOf body) st).filter keep ≠ [])
    (hkeep : ∀ st ∈ combOf body, ∀ r ∈ combReads (byAssignOf body) st, r ∈ drivenOf body →
      keep r = true)
    (hρ : ∀ st ∈ combOf body, ∀ l ∈ combWrites (byAssignOf body) st, keep l = true →
      ∀ r ∈ combReads (byAssignOf body) st, r ∈ drivenOf body → ρ r < ρ l) :
    ∀ st ∈ combOf body, ∀ r ∈ combReads (byAssignOf body) st, r ∈ drivenOf body →
      ∃ st' ∈ combOf body, r ∈ combWrites (byAssignOf body) st' ∧
        rankMinK keep (byAssignOf body) ρ st' < rankMinK keep (byAssignOf body) ρ st := by
  intro st hs r hr hd
  obtain ⟨st', hs', hw'⟩ := mem_driven hd
  refine ⟨st', hs', hw', ?_⟩
  obtain ⟨l, hl, he⟩ := minOf_mem ρ _ (hne st hs)
  obtain ⟨hl1, hl2⟩ := List.mem_filter.mp hl
  have h1 := minOf_le ρ _ r (List.mem_filter.mpr ⟨hw', hkeep st hs r hr hd⟩)
  have h2 := hρ st hs l hl1 hl2 r hr hd
  unfold rankMinK
  omega

/-! ## One stand-in per write -/

/-- The stand-ins of an instance: one per name it drives, reading what it
reads. -/
def standIns (keep : String → Bool) (A : List String) (st : Stmt) : List Stmt :=
  ((combWrites A st).filter keep).map fun w =>
    Stmt.inst "" "" (("", Expr.ref w) :: (combReads A st).map fun x => ("", Expr.ref x))

theorem inst_write_notA {A : List String} {mn i : String} {conns : List (String × Expr)}
    {w : String} (h : w ∈ combWrites A (.inst mn i conns)) : w ∉ A := by
  simp only [combWrites, List.mem_filterMap] at h
  obtain ⟨⟨p, e⟩, _, he⟩ := h
  cases e <;> simp only [] at he <;> try cases he
  split at he
  · cases he
  · cases he
    simp_all

theorem inst_read_A {A : List String} {mn i : String} {conns : List (String × Expr)}
    {x : String} (h : x ∈ combReads A (.inst mn i conns)) : x ∈ A := by
  simp only [combReads, List.mem_flatMap, List.mem_filter] at h
  obtain ⟨_, _, _, hx⟩ := h
  simpa using hx

theorem standIn_writes {A : List String} {w : String} {rs : List String} (hw : w ∉ A)
    (hrs : ∀ x ∈ rs, x ∈ A) :
    combWrites A (Stmt.inst "" "" (("", Expr.ref w) :: rs.map fun x => ("", Expr.ref x))) = [w] := by
  have : (rs.map fun x => (("", Expr.ref x) : String × Expr)).filterMap (fun (x : String × Expr) =>
      match x.2 with
      | .ref w => if A.contains w then none else some w
      | _ => none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    simp [hrs x hx]
  simp only [combWrites, List.filterMap_cons]
  have hwc : A.contains w = false := by simpa using hw
  simp only [hwc]
  exact congrArg _ this

theorem standIn_reads {A : List String} {w : String} {rs : List String} (hw : w ∉ A)
    (hrs : ∀ x ∈ rs, x ∈ A) :
    combReads A (Stmt.inst "" "" (("", Expr.ref w) :: rs.map fun x => ("", Expr.ref x))) = rs := by
  simp only [combReads, List.flatMap_cons, refsOf]
  have h1 : [w].filter (fun w => A.contains w) = [] := by simp [hw]
  rw [h1, List.nil_append]
  induction rs with
  | nil => rfl
  | cons x rs ih =>
    have hx : A.contains x = true := by simpa using hrs x (List.mem_cons_self ..)
    simp only [List.map_cons, List.flatMap_cons, refsOf, List.filter_cons, hx, if_true,
      List.filter_nil, List.singleton_append]
    exact congrArg _ (ih (fun y hy => hrs y (List.mem_cons_of_mem _ hy)))

set_option maxHeartbeats 1000000 in
/-- **The rank orders the closed body of a real transition**, instances with
any number of writes. Each write of an instance is a call's output port
(`j`) with the bound `c` of that entry; the instance's reads are `let`
ports below the bound. -/
theorem rank_of_facts_G {P : String → Prop} {bnd : Lean.FVarId → Option String}
    {t : Sparkle.IR.AST.Module}
    {bodyB : List Stmt} {w : String} {ls : List Port} {kI n : Nat} {cs : List Nat}
    {al : List (Port × String)} {es : List Lean.Expr} {ws : List Nat}
    {core : String} {stmts comb : List Stmt} {A D : List String} (keep : String → Bool)
    (hbody : t.body = bodyB.reverse ++ [.assign "out" (.ref w)])
    (hacy : Acyclic t.body)
    (hnamed : ∀ l r, Stmt.assign l r ∈ bodyB.reverse → Allocated l ∧ ∀ x ∈ refsOf r, Allocated x)
    (hnw : ∀ l r, Stmt.assign l r ∈ bodyB → ¬ P l)
    (hPls : ∀ p ∈ ls, P p.name) (hlsAlloc : ∀ p ∈ ls, Allocated p.name)
    (hlsNd : (ls.map Port.name).Nodup)
    (hal : al.map (·.1) = ls.drop (kI + n))
    (hfacts : Facts P bnd
      (fun i x => ∀ (idx : Nat) (p : Port), ls[idx]? = some p → x = p.name → okRule kI n cs i idx)
      t.wires t.body bodyB 0 al es ws)
    (hcsK : ∀ j, j < kI → ∃ c, cs[j]? = some c ∧ c ≤ al.length)
    (hcore : Allocated core)
    (hinst : ∀ st ∈ stmts, isInst st = true ∧ ∀ outW ∈ combWrites A st, keep outW = true →
      ∃ (j c : Nat),
      ((ls.take kI).map Port.name)[j]? = some outW ∧ cs[j]? = some c ∧
      ∀ x ∈ combReads A st, ∃ a : Nat, (al.map (·.1.name))[a]? = some x ∧ a < c)
    (hcomb : ∀ st ∈ comb, (∃ l r, st = Stmt.assign l r ∧ Stmt.assign l r ∈ bodyB.reverse) ∨
      (∃ (a : Nat) (pa : Port × String), al[a]? = some pa ∧ st = aliasStmt pa.1 pa.2) ∨
      (∃ l lo wd, st = Stmt.assign l (fieldRhs core lo wd) ∧ ¬ Allocated l) ∨ st ∈ stmts)
    (hD : ∀ x ∈ D, x ∈ writesOf bodyB.reverse ∨ x ∈ al.map (·.1.name) ∨
      x ∈ (ls.take kI).map Port.name ∨ ¬ Allocated x) :
    ∃ pres : List (List Stmt),
      ∀ st ∈ comb, ∀ l ∈ combWrites A st, keep l = true → ∀ r ∈ combReads A st, r ∈ D →
        rho bodyB.reverse pres (al.map (·.1.name)) ((ls.take kI).map Port.name) cs r <
          rho bodyB.reverse pres (al.map (·.1.name)) ((ls.take kI).map Port.name) cs l := by
  -- a stand-in's writes and reads
  have hstand : ∀ st ∈ stmts, ∀ l ∈ combWrites A st,
      combWrites A (Stmt.inst "" "" (("", Expr.ref l) ::
        (combReads A st).map fun x => ("", Expr.ref x))) = [l] ∧
      combReads A (Stmt.inst "" "" (("", Expr.ref l) ::
        (combReads A st).map fun x => ("", Expr.ref x))) = combReads A st := by
    intro st hs l hl
    have hi := (hinst st hs).1
    cases st with
    | inst mn i conns =>
      exact ⟨standIn_writes (inst_write_notA hl) (fun x hx => inst_read_A hx),
        standIn_reads (inst_write_notA hl) (fun x hx => inst_read_A hx)⟩
    | _ => simp [isInst] at hi
  obtain ⟨pres, hsingle, hρ⟩ := rank_of_facts (P := P) (bnd := bnd) (t := t) (bodyB := bodyB)
    (w := w) (ls := ls) (kI := kI) (n := n) (cs := cs) (al := al) (es := es) (ws := ws)
    (core := core) (stmts := stmts.flatMap (standIns keep A))
    (comb := comb.flatMap fun st => if isInst st then standIns keep A st else [st]) (A := A) (D := D)
    hbody hacy hnamed hnw hPls hlsAlloc hlsNd hal hfacts hcsK hcore
    (by
      intro st' hs'
      obtain ⟨st, hs, hm⟩ := List.mem_flatMap.mp hs'
      obtain ⟨l, hlk, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hl, hk⟩ := List.mem_filter.mp hlk
      obtain ⟨j, c, hj, hc, hrd⟩ := (hinst st hs).2 l hl hk
      obtain ⟨hw', hr'⟩ := hstand st hs l hl
      exact ⟨j, l, c, hj, hc, hw', fun x hx => hrd x (by rw [hr'] at hx; exact hx)⟩)
    (by
      intro st' hs'
      obtain ⟨st, hs, hm⟩ := List.mem_flatMap.mp hs'
      by_cases hi : isInst st = true
      · rw [if_pos hi] at hm
        rcases hcomb st hs with ⟨l, r, rfl, _⟩ | ⟨a, pa, _, rfl⟩ | ⟨l, lo, wd, rfl, _⟩ | h
        · simp [isInst] at hi
        · simp [isInst, aliasStmt] at hi
        · simp [isInst] at hi
        · exact Or.inr (Or.inr (Or.inr (List.mem_flatMap.mpr ⟨st, h, hm⟩)))
      · rw [if_neg hi] at hm
        have : st' = st := by simpa using hm
        subst this
        rcases hcomb st' hs with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact absurd (hinst st' h).1 hi)
    hD
  refine ⟨pres, ?_⟩
  intro st hs l hl hkl r hr hd
  by_cases hi : isInst st = true
  · have hst : st ∈ stmts := by
      rcases hcomb st hs with ⟨l, r, rfl, _⟩ | ⟨a, pa, _, rfl⟩ | ⟨l, lo, wd, rfl, _⟩ | h
      · simp [isInst] at hi
      · simp [isInst, aliasStmt] at hi
      · simp [isInst] at hi
      · exact h
    obtain ⟨hw', hr'⟩ := hstand st hst l hl
    refine hρ _ (List.mem_flatMap.mpr ⟨st, hs, ?_⟩) l hw' r (by rw [hr']; exact hr) hd
    rw [if_pos hi]
    exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, hkl⟩, rfl⟩
  · have hm : st ∈ comb.flatMap fun st => if isInst st then standIns keep A st else [st] :=
      List.mem_flatMap.mpr ⟨st, hs, by rw [if_neg hi]; exact List.mem_singleton.mpr rfl⟩
    obtain ⟨l', hl'⟩ := hsingle st hm
    have : l = l' := by
      rw [hl'] at hl
      simpa using hl
    exact hρ st hm l (this ▸ hl') r hr hd

end Tools.ShippingRankG
