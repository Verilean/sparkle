import Std.Data.String.ToNat

/-! # Instance names of different call groups are different

`closeInstsG` names the instance of call group `gi` `inst{gi}_{child}` and
checks the instance names distinct. They are, whatever the children's names:
the decimal digits of `gi` end at the first `_`. Pure. -/
namespace Tools.ShippingInstNames

theorem append_cons_inj {α : Type} {c : α} : ∀ {l1 l2 r1 r2 : List α}, c ∉ l1 → c ∉ l2 →
    l1 ++ c :: r1 = l2 ++ c :: r2 → l1 = l2
  | [], [], _, _, _, _, _ => rfl
  | [], y :: l2, _, _, _, h2, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self ..) h2
  | x :: l1, [], _, _, h1, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self ..) h1
  | x :: l1, y :: l2, _, _, h1, h2, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rw [h.1, append_cons_inj (fun hm => h1 (List.mem_cons_of_mem _ hm))
      (fun hm => h2 (List.mem_cons_of_mem _ hm)) h.2]

/-- **The group index is read off the instance name.** -/
theorem instName_inj {a b : Nat} {x y : String} (h : s!"inst{a}_{x}" = s!"inst{b}_{y}") :
    a = b := by
  have h' := congrArg String.toList h
  simp [String.toList_append] at h'
  have e : (toString "_").toList = ['_'] := by decide
  rw [e] at h'
  have hd := append_cons_inj (c := '_') Nat.underscore_not_in_toDigits
    Nat.underscore_not_in_toDigits h'
  exact Nat.repr_injective (by rw [Nat.repr_eq_ofList_toDigits, Nat.repr_eq_ofList_toDigits, hd])

end Tools.ShippingInstNames
