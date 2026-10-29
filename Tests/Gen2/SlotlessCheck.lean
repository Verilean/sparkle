import Tools.ShippingGen2SlotlessLeaf
import Tools.ShippingGen2CombKid
set_option autoImplicit false

/-! # M2-step axiom audit: S1, S2-c, S2 (slotless leaf), S4 pure lemmas (STEP_IFACE_FREEZE rev3, STEP_S2C_FREEZE) -/

#print axioms Tools.ShippingGen2Comb.runModule_seed_local
#print axioms Tools.ShippingGen2.slotless_closed_full
#print axioms Tools.ShippingGen2.slotless_closed_ofRun
#print axioms Tools.ShippingGen2.runModule_rst_irrel
#print axioms Tools.ShippingGen2.slotless_inputs_alloc_ofRun
#print axioms Tools.ShippingGen2.slotlessLeaf_topShips_of_LB
#print axioms Tools.ShippingGen2.slotlessLeaf_childShips_of_LB
#print axioms Tools.ShippingGen2.slotlessLeaf_ships
#print axioms Tools.ShippingGen2.evalAssigns_mems_irrel
#print axioms Tools.ShippingGen2.Pkg.src_get
#print axioms Tools.ShippingGen2.childFn_of_combRun
#print axioms Tools.ShippingGen2.combS_pointwise
#print axioms Tools.ShippingGen2.childRunN_of_seq
#print axioms Tools.ShippingGen2.childRunN_iff_seq
#print axioms Tools.ShippingGen2.not_seq_and_comb
