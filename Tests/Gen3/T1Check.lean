import Tools.ShippingGen2T1
set_option autoImplicit false

/-! # M3 lead: axiom audit of the CONDITIONAL skeleton (scripts/gen2/T1_CONNECT_FREEZE.md, approved eae85955;
PF revision scripts/gen2/GPOST_FREEZE.md §3, §7)

`t1_of_stepPF` is conditional on `StepStmt`, `KeepChildStmt`, `ServedShips0Stmt`, `PostFactsStmt` (and `LimitStmt`,
discharged in `t1_of_stepPF'`). Not M2/M3 completion. The former `NoTopStmt` names (`ihAt_step`, `ih_all`,
`t1_of_step`, `t1_of_step'`) are retired (GPOST_FREEZE §10). -/

#print axioms Tools.ShippingGen2.limitStmt_proved
#print axioms Tools.ShippingGen2.servedShipsStmt_of_0
#print axioms Tools.ShippingGen2.childShips_congr
#print axioms Tools.ShippingGen2.ihAt_limit
#print axioms Tools.ShippingGen2.ihAt_stepPF
#print axioms Tools.ShippingGen2.ih_allPF
#print axioms Tools.ShippingGen2.t1_of_stepPF
#print axioms Tools.ShippingGen2.t1_of_stepPF'
#print axioms Tools.ShippingGen2.shipsRes_old
#print axioms Tools.ShippingGen2.invAt_old
#print axioms Tools.ShippingGen2.servedP_old
#print axioms Tools.ShippingGen2.stepStmt_of_old
