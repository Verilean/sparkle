import Tools.ShippingGen2OneOutTop
set_option autoImplicit false

/-! # S4 stage B: axiom audit (scripts/gen2/S4_STAGEB_FREEZE.md rev1)

UNBUILT at the time of writing (lakefile entry not added).

Axiom audit of every stage-B declaration: the two names lemmas (Tools/ShippingGen2OneOutNames.lean) and the four of
Tools/ShippingGen2OneOutTop.lean. Expected: no `sorryAx`, no extra axiom (only the standard `propext` /
`Classical.choice` / `Quot.sound`), no `Lean.ofReduceBool` (no `native_decide`). -/

-- the names lemmas (Tools/ShippingGen2OneOutNames.lean)
#print axioms Tools.ShippingGen2.machPorts_names_indep
#print axioms Tools.ShippingGen2.ranA_inputs_machPorts

-- stage B (Tools/ShippingGen2OneOutTop.lean)
#print axioms Tools.ShippingGen2.core_callPorts_oneA
#print axioms Tools.ShippingGen2.oneOutWidthAt
#print axioms Tools.ShippingGen2.core_instOutWidthsOk_oneA
#print axioms Tools.ShippingGen2.oneOut_topShips
