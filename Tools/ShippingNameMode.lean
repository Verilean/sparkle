import Lean

/-! # Which proof the closing generators give the name conditions (round par/b-30)

WRITTEN, NOT BUILT.

Since round par/b-30 the generators of the closing theorems
(`Tools/ShippingMachineClosesAtGen.lean`, `…AtGenG.lean`,
`Tools/ShippingChildIfaceGen.lean`) discharge the name conditions from the
distinctness of the DECLARATION names (`Tools.ShippingNameDischarge`:
`names_inj`, `parent_ne`, `not_mem_map`, `disjoint_map`, with `decide` on
`Lean.Name`s). The previous proofs — a Boolean check on the candidate
renderings of `Name.toString` (`Tools.ShippingNameSep`) — stay reachable for
one round, to compare the two on one tree:

    set_option shipping.nameCandidates true in …

Both options change only what a generator DOES; no theorem depends on them. -/

/-- `true`: the closing generators take the PREVIOUS path for the name
conditions (`Tools.ShippingNameSep`: candidate renderings; a binder where
that check fails). Default `false`: `Tools.ShippingNameDischarge` on
`Lean.Name`s (a binder only where the condition on the names is false). -/
register_option shipping.nameCandidates : Bool := { defValue := false }

/-- A suffix for the names `c.closes_deep` / `c.iface_deep` that
`Tools.ShippingChildIfaceGen.closesDeep` generates (default: none). With a
suffix, a second set of the deep closings can be generated beside the first
— e.g. under `shipping.nameCandidates` — and their statements compared. -/
register_option shipping.deepSuffix : String := { defValue := "" }
