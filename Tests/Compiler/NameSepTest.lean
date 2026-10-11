import Tools.ShippingNameSep

/-! # Name separation: does the kernel evaluate the candidate check? (N1)

`Tools.ShippingNameSep.toString_ne` turns `sepB a b = true` into
`a.toString ≠ b.toString`. Whether `decide` can evaluate `sepB` on real
names, and how long it takes (`2^k` candidates per name of `k` components),
is what this file measures. The examples are ordered from cheap to
expensive; a failure of a later one does not invalidate the earlier ones.

The `#eval` lines are compiled evidence only (prefixed `NAMESEP`): the
candidate lists, the check on the same pairs, and the collision that shows
`toString` is not injective on all names. -/
namespace Tests.Compiler.NameSepTest
open Tools.ShippingNameSep

#eval IO.println s!"NAMESEP cands a.b = {cands `a.b}"
#eval IO.println s!"NAMESEP sepB pick caller = {sepB `pick `caller}"
#eval IO.println s!"NAMESEP sepB same name = {sepB `pick `pick}"
#eval IO.println s!"NAMESEP collision: {(Lean.Name.mkSimple "a».b").toString} vs {(Lean.Name.mkStr (Lean.Name.mkSimple "a»") "b").toString}"
#eval IO.println s!"NAMESEP collision sepB = {sepB (Lean.Name.mkSimple "a».b") (Lean.Name.mkStr (Lean.Name.mkSimple "a»") "b")}"
#eval IO.println s!"NAMESEP long pair = {sepB `Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt}"

-- one component each: 2 × 2 comparisons
example : (`pick : Lean.Name).toString ≠ (`caller : Lean.Name).toString :=
  toString_ne (by decide)

-- two components each: 4 × 4
example : (`A.pick : Lean.Name).toString ≠ (`A.caller : Lean.Name).toString :=
  toString_ne (by decide)

-- the shape of `hnames`, three one-component names
example : ∀ c ∈ [(`pick : Lean.Name), `pickD, `cnt], ∀ c' ∈ [(`pick : Lean.Name), `pickD, `cnt],
    c.toString = c'.toString → c = c' :=
  hnames_of _ (by decide)

-- the shape of `hfresh`, with an instance-name format
example : "out" ≠ (fun x => "inst0_" ++ x) (`pick : Lean.Name).toString :=
  fresh_of `pick (fun x => "inst0_" ++ x) "out" (by decide)

-- five components each: 32 × 32 comparisons of ~50-character strings
example : (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent : Lean.Name).toString ≠
    (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name).toString :=
  toString_ne (by decide)

end Tests.Compiler.NameSepTest
