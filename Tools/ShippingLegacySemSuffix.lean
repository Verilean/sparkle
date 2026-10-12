import Tools.ShippingNameSep

/-! # The suffix tests on a printed name, without evaluating `Name.toString`

The legacy handlers test the head's name by the suffix of its printed form
(`name.toString.endsWith ".register"`, …). `Name.toString` with escaping does
not reduce in the kernel; `Tools/ShippingNameSep.lean` proves instead that the
printed name is one of finitely many candidate renderings (`toString_mem`).

**Proved here** (`endsWith_false_of`): if no candidate rendering of `c` ends
with `suffix`, the printed name does not. The premise is a closed Boolean
over the candidates; whether it EVALUATES (by `decide`) depends on
`String.endsWith` reducing on literals, which this file does not use. -/
namespace Tools.ShippingLegacySem

/-- The printed name does not end with `suffix` when no candidate does. -/
theorem endsWith_false_of (c : Lean.Name) (suffix : String)
    (h : ((Tools.ShippingNameSep.cands c).all fun x => !x.endsWith suffix) = true) :
    c.toString.endsWith suffix = false := by
  have h1 := List.all_eq_true.mp h _ (Tools.ShippingNameSep.toString_mem c)
  have h2 : (!c.toString.endsWith suffix) = true := h1
  cases hb : c.toString.endsWith suffix with
  | false => rfl
  | true =>
    rw [hb] at h2
    exact absurd h2 (by decide)

end Tools.ShippingLegacySem
