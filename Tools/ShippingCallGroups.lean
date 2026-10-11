import Sparkle.IR.MachineInstG

/-! # The call groups of an entry list

`callGroups keys` (the instances of `closeInstsG`: entries with the same
child and the same argument `let`s are one call) partitions the entry
indices: every group is non-empty, its entries are indices with ONE key, and
the groups together are the indices `0 … keys.length - 1`, each once.
Pure. -/
namespace Tools.ShippingCallGroups
open Sparkle.IR.Machine

/-- What the groups built from the first `n` entries are. -/
structure Groups (keys : List (String × List Nat)) (n : Nat) (gs : List (List Nat)) : Prop where
  head : ∀ g ∈ gs, ∃ (k0 : Nat) (key : String × List Nat), g.head? = some k0 ∧
    ∀ k ∈ g, k < n ∧ keys[k]? = some key
  perm : gs.flatten.Perm (List.range n)

theorem modify_split {α : Type} (f : α → α) : ∀ (gs : List α) (gi : Nat), gi < gs.length →
    ∃ a g b, gs = a ++ g :: b ∧ a.length = gi ∧ gs.modify gi f = a ++ f g :: b
  | g :: gs, 0, _ => ⟨[], g, gs, rfl, rfl, by simp⟩
  | g :: gs, gi + 1, h => by
    obtain ⟨a, g', b, he, hl, hm⟩ := modify_split f gs gi (by simpa using h)
    exact ⟨g :: a, g', b, by rw [he]; rfl, by simp [hl], by simp [hm]⟩

/-- One entry more. -/
theorem Groups.step {keys : List (String × List Nat)} {n : Nat} {gs : List (List Nat)}
    (h : Groups keys n gs) {key : String × List Nat} (hk : keys[n]? = some key) :
    Groups keys (n + 1)
      (match gs.findIdx? (fun g => (g.head? >>= fun k0 => keys[k0]?) == some key) with
       | some gi => gs.modify gi (· ++ [n])
       | none => gs ++ [[n]]) := by
  have mono : ∀ g ∈ gs, ∃ (k0 : Nat) (key : String × List Nat), g.head? = some k0 ∧
      ∀ k ∈ g, k < n + 1 ∧ keys[k]? = some key := by
    intro g hg
    obtain ⟨k0, key', h0, hall⟩ := h.head g hg
    exact ⟨k0, key', h0, fun k hk' => ⟨Nat.lt_succ_of_lt (hall k hk').1, (hall k hk').2⟩⟩
  cases hf : gs.findIdx? (fun g => (g.head? >>= fun k0 => keys[k0]?) == some key) with
  | none =>
    show Groups keys (n + 1) (gs ++ [[n]])
    refine ⟨?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact mono g hg
      · have : g = [n] := by simpa using hg
        subst this
        exact ⟨n, key, rfl, fun k hk' => by
          have : k = n := by simpa using hk'
          subst this
          exact ⟨Nat.lt_succ_self _, hk⟩⟩
    · show (gs ++ [[n]]).flatten.Perm _
      rw [List.flatten_append, List.range_succ]
      simpa using h.perm.append_right [n]
  | some gi =>
    show Groups keys (n + 1) (gs.modify gi (· ++ [n]))
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    obtain ⟨a, g, b, he, hl, hm⟩ := modify_split (· ++ [n]) gs gi hlt
    have hgi : gs[gi] = g := by
      subst hl
      simp [he]
    rw [hgi] at hp
    have hgm : g ∈ gs := by rw [he]; simp
    obtain ⟨k0, key', h0, hall⟩ := h.head g hgm
    have hk0 : k0 ∈ g := List.mem_of_mem_head? h0
    have hkey : key' = key := by
      have := (hall k0 hk0).2
      simp only [h0, Option.bind_eq_bind, Option.bind_some, this, beq_iff_eq,
        Option.some.injEq] at hp
      exact hp
    subst hkey
    refine ⟨?_, ?_⟩
    · intro g' hg'
      show ∃ (k0 : Nat) (key : String × List Nat), g'.head? = some k0 ∧
        ∀ k ∈ g', k < n + 1 ∧ keys[k]? = some key
      rw [hm] at hg'
      rcases List.mem_append.mp hg' with hg' | hg'
      · exact mono g' (by rw [he]; exact List.mem_append_left _ hg')
      · rcases List.mem_cons.mp hg' with rfl | hg'
        · refine ⟨k0, key', ?_, ?_⟩
          · cases g with
            | nil => cases h0
            | cons x g => simpa using h0
          · intro k hk'
            rcases List.mem_append.mp hk' with hk' | hk'
            · exact ⟨Nat.lt_succ_of_lt (hall k hk').1, (hall k hk').2⟩
            · have : k = n := by simpa using hk'
              subst this
              exact ⟨Nat.lt_succ_self _, hk⟩
        · exact mono g' (by rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg'))
    · show (gs.modify gi (· ++ [n])).flatten.Perm _
      rw [hm, List.range_succ]
      have hp' := h.perm
      rw [he] at hp'
      refine List.Perm.trans ?_ (hp'.append_right [n])
      simp only [List.flatten_append, List.flatten_cons, List.append_assoc]
      exact List.Perm.append_left _ (List.Perm.append_left _ List.perm_append_comm)

theorem fold_groups (keys : List (String × List Nat))
    (step : List (List Nat) → (String × List Nat) × Nat → List (List Nat))
    (hstep : ∀ (n : Nat) (gs : List (List Nat)) (x : (String × List Nat) × Nat), Groups keys n gs →
      x.2 = n → keys[n]? = some x.1 → Groups keys (n + 1) (step gs x)) :
    ∀ (xs : List ((String × List Nat) × Nat)) (n : Nat) (gs : List (List Nat)), Groups keys n gs →
      (∀ (i : Nat) (x : (String × List Nat) × Nat), xs[i]? = some x →
        x.2 = n + i ∧ keys[x.2]? = some x.1) →
      Groups keys (n + xs.length) (xs.foldl step gs)
  | [], n, gs, h, _ => h
  | x :: xs, n, gs, h, hx => by
    obtain ⟨h1, h2⟩ := hx 0 x rfl
    have h1' : x.2 = n := by simpa using h1
    rw [List.foldl_cons, List.length_cons, show n + (xs.length + 1) = (n + 1) + xs.length by omega]
    refine fold_groups keys step hstep xs (n + 1) _ (hstep n gs x h h1' (by rw [← h1']; exact h2)) ?_
    intro i y hy
    obtain ⟨e1, e2⟩ := hx (i + 1) y (by simpa using hy)
    exact ⟨by omega, e2⟩

/-- **The call groups partition the entries by key.** -/
theorem callGroups_spec (keys : List (String × List Nat)) :
    Groups keys keys.length (callGroups keys) := by
  have h : ∀ (step : List (List Nat) → (String × List Nat) × Nat → List (List Nat)),
      (∀ (n : Nat) (gs : List (List Nat)) (x : (String × List Nat) × Nat), Groups keys n gs →
        x.2 = n → keys[n]? = some x.1 → Groups keys (n + 1) (step gs x)) →
      Groups keys keys.length (keys.zipIdx.foldl step []) := by
    intro step hstep
    have := fold_groups keys step hstep keys.zipIdx 0 [] ⟨fun g hg => by simp at hg, by simp⟩
      (by
        intro i x hx
        rw [List.getElem?_zipIdx] at hx
        cases hk : keys[i]? with
        | none => rw [hk] at hx; cases hx
        | some key =>
          rw [hk] at hx
          simp only [Option.map_some, Option.some.injEq] at hx
          subst hx
          exact ⟨by simp, by simpa using hk⟩)
    rw [Nat.zero_add, List.length_zipIdx] at this
    exact this
  unfold callGroups
  exact h _ (by
    intro n gs x h hx hk
    obtain ⟨key, k⟩ := x
    simp only [] at hx hk
    subst hx
    exact h.step hk)

end Tools.ShippingCallGroups
