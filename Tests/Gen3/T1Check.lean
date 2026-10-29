import Tools.ShippingGen2T1
set_option autoImplicit false

/-! # M3 lead: axiom audit of the CONDITIONAL skeleton (scripts/gen2/T1_CONNECT_FREEZE.md, approved eae85955)

`t1_of_step` is conditional on `StepStmt`, `KeepChildStmt`, `ServedShips0Stmt`, `NoTopStmt` (and `LimitStmt`,
discharged in `t1_of_step'`). Not M2/M3 completion. -/

#print axioms Tools.ShippingGen2.limitStmt_proved
#print axioms Tools.ShippingGen2.servedShipsStmt_of_0
#print axioms Tools.ShippingGen2.childShips_congr
#print axioms Tools.ShippingGen2.ihAt_limit
#print axioms Tools.ShippingGen2.ihAt_step
#print axioms Tools.ShippingGen2.ih_all
#print axioms Tools.ShippingGen2.t1_of_step
#print axioms Tools.ShippingGen2.t1_of_step'
