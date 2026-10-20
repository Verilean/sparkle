import Tools.ShippingRankNames
import Tools.ShippingCloseMachineFacts

/-! # The rank of a closed transition with one-output calls (pure)

`rho` ranks the combinational statements of a closed machine with one-output
instances, given — as hypotheses about lists — what each kind of statement
reads: a transition statement (by the field whose prefix contains it), a
`let` alias, a next-value / output assignment, an instance. For the
ONE-OUTPUT closing only: every statement drives one name. Nothing here says
a real transition satisfies the hypotheses. -/
namespace Tools.ShippingCallsRank
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingClosedOrder Tools.ShippingRankNames Tools.ShippingTopoBody

/-- In an ordered body, the statement driving a name a prefix drives is in
the prefix. -/
theorem stmt_in_prefix {T pre : List Stmt} (hT : Acyclic T) (hp : pre <+: T) {l : String} {r : Expr}
    (hm : Stmt.assign l r ∈ T) (hl : l ∈ writesOf pre) : Stmt.assign l r ∈ pre := by
  obtain ⟨rest, rfl⟩ := hp
  rcases List.mem_append.mp hm with h | h
  · exact h
  · exact absurd (mem_writes_assign h) (Acyclic.writes_disjoint hT l hl)

theorem mul_lt {b1 b2 M : Nat} (h : b1 < b2) : b1 * (M + 1) < b2 * (M + 1) := by
  have := block_lt (r1 := 0) (r2 := 0) (M := M + 1) h (Nat.succ_pos _)
  simpa using this

set_option maxHeartbeats 1000000 in
/-- **The rank on names orders the closed body's combinational statements.** -/
theorem rank_closed {T : List Stmt} {al : List (Port × String)} {core : String}
    {stmts comb : List Stmt} {A D : List String} {pres : List (List Stmt)}
    {instNames : List String} {cs : List Nat}
    (hT : Acyclic T)
    (hTnamed : ∀ l r, Stmt.assign l r ∈ T → Allocated l ∧ ∀ x ∈ refsOf r, Allocated x)
    (hportsW : ∀ x, x ∈ al.map (·.1.name) ∨ x ∈ instNames → x ∉ writesOf T ∧ Allocated x)
    (hletNd : (al.map (·.1.name)).Nodup) (hinstNd : instNames.Nodup)
    (hdisj : ∀ x ∈ al.map (·.1.name), x ∉ instNames)
    (hpresLen : pres.length = al.length) (hpre : ∀ pre ∈ pres, pre <+: T)
    (hreads : ∀ (i : Nat) (pre : List Stmt), pres[i]? = some pre → ∀ (l : String) (r : Expr),
      Stmt.assign l r ∈ pre → ∀ x ∈ refsOf r,
      (∀ a : Nat, (al.map (·.1.name))[a]? = some x → a < i) ∧
      (∀ j c : Nat, instNames[j]? = some x → cs[j]? = some c → c ≤ i))
    (hcs : ∀ (j : Nat) (x : String), instNames[j]? = some x → ∃ c, cs[j]? = some c ∧ c ≤ al.length)
    (halias : ∀ (a : Nat) (pa : Port × String), al[a]? = some pa → Allocated pa.2 ∧
      (pa.2 ∈ writesOf T → ∃ pre, pres[a]? = some pre ∧ pa.2 ∈ writesOf pre) ∧
      (∀ b : Nat, (al.map (·.1.name))[b]? = some pa.2 → b < a) ∧
      (∀ j c : Nat, instNames[j]? = some pa.2 → cs[j]? = some c → c ≤ a))
    (hcore : Allocated core)
    (hinst : ∀ st ∈ stmts, ∃ (j : Nat) (outW : String) (c : Nat), instNames[j]? = some outW ∧
      cs[j]? = some c ∧
      combWrites A st = [outW] ∧
      ∀ x ∈ combReads A st, ∃ a : Nat, (al.map (·.1.name))[a]? = some x ∧ a < c)
    (hcomb : ∀ st ∈ comb, (∃ l r, st = Stmt.assign l r ∧ Stmt.assign l r ∈ T) ∨
      (∃ (a : Nat) (pa : Port × String), al[a]? = some pa ∧ st = aliasStmt pa.1 pa.2) ∨
      (∃ l lo wd, st = Stmt.assign l (fieldRhs core lo wd) ∧ ¬ Allocated l) ∨ st ∈ stmts)
    (hD : ∀ x ∈ D, x ∈ writesOf T ∨ x ∈ al.map (·.1.name) ∨ x ∈ instNames ∨ ¬ Allocated x) :
    (∀ st ∈ comb, ∃ l, combWrites A st = [l]) ∧
    ∀ st ∈ comb, ∀ l, combWrites A st = [l] → ∀ r ∈ combReads A st, r ∈ D →
      rho T pres (al.map (·.1.name)) instNames cs r <
        rho T pres (al.map (·.1.name)) instNames cs l := by
  -- the rank of a name, by its kind
  have rLet : ∀ (a : Nat) (x : String), (al.map (·.1.name))[a]? = some x →
      rho T pres (al.map (·.1.name)) instNames cs x = (4 * a + 3) * (T.length + 1) := fun a x h =>
    rho_let (hportsW x (Or.inl (List.mem_of_getElem? h))).1 hletNd h
  have rInst : ∀ (j : Nat) (x : String) (c : Nat), instNames[j]? = some x → cs[j]? = some c →
      rho T pres (al.map (·.1.name)) instNames cs x = (4 * c + 1) * (T.length + 1) :=
    fun j x c h hc => rho_inst (hportsW x (Or.inr (List.mem_of_getElem? h))).1
      (fun hl => hdisj x hl (List.mem_of_getElem? h)) hinstNd h hc
  have hKlen : (al.map (·.1.name)).length = al.length := List.length_map ..
  -- a name of the driven set that is allocated: body-driven, a `let` port or a call's output
  have kinds : ∀ x, x ∈ D → Allocated x →
      x ∈ writesOf T ∨ (∃ a : Nat, (al.map (·.1.name))[a]? = some x) ∨
        ∃ j : Nat, instNames[j]? = some x := by
    intro x hx ha
    rcases hD x hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (List.mem_iff_getElem?.mp h))
    · exact Or.inr (Or.inr (List.mem_iff_getElem?.mp h))
    · exact absurd ha h
  refine ⟨?_, ?_⟩
  · intro st hs
    rcases hcomb st hs with ⟨l, r, rfl, _⟩ | ⟨a, pa, _, rfl⟩ | ⟨l, lo, wd, rfl, _⟩ | h
    · exact ⟨l, rfl⟩
    · exact ⟨pa.1.name, rfl⟩
    · exact ⟨l, rfl⟩
    · obtain ⟨j, outW, c, _, _, hw, _⟩ := hinst st h
      exact ⟨outW, hw⟩
  · intro st hs l hl x hx hxD
    rcases hcomb st hs with ⟨l', r, rfl, hm⟩ | ⟨a, pa, hpa, rfl⟩ | ⟨l', lo, wd, rfl, hna⟩ | h
    · -- a transition statement
      have e : l' = l := by simpa [combWrites, stmtWrites] using hl
      subst e
      have hx' : x ∈ refsOf r := hx
      have hlw : l' ∈ writesOf T := mem_writes_assign hm
      rcases kinds x hxD ((hTnamed l' r hm).2 x hx') with hw | ⟨a, ha⟩ | ⟨j, hj⟩
      · exact lt_body_body hT hpre hm hx' hw
      · rw [rLet a x ha]
        refine lt_block_body hT hlw ?_
        have : a + 1 ≤ firstIdx pres l' := le_field (fun i pre hi hlp =>
            (hreads i pre hi l' r (stmt_in_prefix hT (hpre pre (List.mem_of_getElem? hi)) hm hlp)
              x hx').1 a ha)
          (by
            have := (List.getElem?_eq_some_iff.mp ha).1
            omega)
        omega
      · obtain ⟨c, hc, hcK⟩ := hcs j x hj
        rw [rInst j x c hj hc]
        refine lt_block_body hT hlw ?_
        have : c ≤ firstIdx pres l' := le_field (fun i pre hi hlp =>
            (hreads i pre hi l' r (stmt_in_prefix hT (hpre pre (List.mem_of_getElem? hi)) hm hlp)
              x hx').2 j c hj hc)
          (by omega)
        omega
    · -- the alias of `let` `a`
      have e : pa.1.name = l := by simpa [aliasStmt, combWrites, stmtWrites] using hl
      subst e
      have hxe : x = pa.2 := by simpa [aliasStmt, combReads, stmtReads, refsOf] using hx
      subst hxe
      have hla : (al.map (·.1.name))[a]? = some pa.1.name := by
        rw [List.getElem?_map, hpa]
        rfl
      obtain ⟨halloc, hdrv, hlt, hic⟩ := halias a pa hpa
      rw [rLet a _ hla]
      rcases kinds pa.2 hxD halloc with hw | ⟨b, hb⟩ | ⟨j, hj⟩
      · obtain ⟨pre, hpre', hwp⟩ := hdrv hw
        exact lt_body_block hT hw (firstIdx_le hpre' hwp) (by omega)
      · rw [rLet b _ hb]
        exact mul_lt (by have := hlt b hb; omega)
      · obtain ⟨c, hc, _⟩ := hcs j _ hj
        rw [rInst j _ c hj hc]
        exact mul_lt (by have := hic j c hj hc; omega)
    · -- a next-value or output assignment
      have e : l' = l := by simpa [combWrites, stmtWrites] using hl
      subst e
      have hxe : x = core := by simpa [combReads, stmtReads, fieldRhs, refsOf] using hx
      subst hxe
      have hlo : rho T pres (al.map (·.1.name)) instNames cs l' =
          4 * (pres.length + 1) * (T.length + 1) :=
        rho_other (fun h => by
            obtain ⟨r, hr⟩ := Tools.ShippingMachineCloses.mem_of_writes hT h
            exact hna (hTnamed l' r hr).1)
          (fun h => hna (hportsW l' (Or.inl h)).2) (fun h => hna (hportsW l' (Or.inr h)).2)
      rw [hlo]
      rcases kinds x hxD hcore with hw | ⟨a, ha⟩ | ⟨j, hj⟩
      · exact lt_body_block hT hw (firstIdx_le_length pres x) (by omega)
      · rw [rLet a x ha]
        refine mul_lt ?_
        have := (List.getElem?_eq_some_iff.mp ha).1
        omega
      · obtain ⟨c, hc, hcK⟩ := hcs j x hj
        rw [rInst j x c hj hc]
        exact mul_lt (by omega)
    · -- an instance
      obtain ⟨j, outW, c, hj, hc, hw, hrd⟩ := hinst st h
      have e : outW = l := by
        rw [hw] at hl
        simpa using hl
      subst e
      obtain ⟨a, ha, hac⟩ := hrd x hx
      rw [rInst j outW c hj hc, rLet a x ha]
      exact mul_lt (by omega)

end Tools.ShippingCallsRank
