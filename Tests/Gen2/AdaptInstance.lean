import Tools.ShippingGen2Adapt
import Tests.Gen2.CallDecInstance
set_option autoImplicit false

/-! # U-ADAPT check: `topshare2` re-derived POINTWISE (G3GEN_CALL_PLAN.md rev1 §4)

For each call `k` separately, `CallDec` from that call's `HPointAt` (built from call `k`'s body of the existing
`b_topshare2_hFP`, through `tm2_hF`) and the k-local data rows (`callArgsOkAt`, arity), by `decide`. No global
width/arity table is used. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen2.AdaptInstance
open Tools.ShippingGen2 Tests.Gen2.CallDecInstance
open Tools.ShippingQuadComposed Tests.Compiler.QuadCallsTest Tests.Compiler.SharedLeafGenTest

theorem tm2_callDec_at : ∀ (k : Nat) (hk : k < tm2Pkg.d.shape.insts.length),
    ∃ q, P2 (tm2Pkg.d.shape.insts[k]).1 = some q ∧ CallDec tm2Pkg q k := by
  intro k hk
  have Q := b_quadAll
  have hnone : (tm2Pkg.d.shape.instOrigins.getD k .ord).child? = none := by
    have hlt : k < tm2Pkg.d.shape.instTagged.length := by
      rw [Tools.ShippingInstTagged.instTagged_length]; exact hk
    have h := Q.hP.child _ (List.getElem_mem hlt)
    rw [Tools.ShippingInstTagged.instTagged_getElem_snd] at h
    simpa [Tools.ShippingInstTagged.originAt] using h
  have hH := hPointAt_of_callFactF_at P2 tm2Pkg k (fun i bools bits hk => tm2_hF i bools bits k hk)
  have hl4 : tm2Pkg.d.shape.insts.length = 4 := Q.hP.len4
  rcases quad_insts_mem Q.hP k hk with hn | hn
  · have hP : P2 (tm2Pkg.d.shape.insts[k]).1 = some wQPkg := by
      rw [show (tm2Pkg.d.shape.insts[k]).1 = _ from hn]; simp [P2]
    refine ⟨wQPkg, hP, callDec_of_hPointAt_at P2 tm2Pkg wQPkg k hk hP hnone hH Q.hP.ok Q.hP.callsOk Q.hP.slots
      ?_ ?_⟩
    · have : k < 4 := hl4 ▸ hk
      interval_cases k <;> first | decide | decide +kernel
    · have : k < 4 := hl4 ▸ hk
      interval_cases k <;> first | decide | decide +kernel
  · have hP : P2 (tm2Pkg.d.shape.insts[k]).1 = some wPPkg := by
      rw [show (tm2Pkg.d.shape.insts[k]).1 = _ from hn]; simp [P2, hne.symm]
    refine ⟨wPPkg, hP, callDec_of_hPointAt_at P2 tm2Pkg wPPkg k hk hP hnone hH Q.hP.ok Q.hP.callsOk Q.hP.slots
      ?_ ?_⟩
    · have : k < 4 := hl4 ▸ hk
      interval_cases k <;> first | decide | decide +kernel
    · have : k < 4 := hl4 ▸ hk
      interval_cases k <;> first | decide | decide +kernel

#print axioms Tools.ShippingGen2.callArgsOkAt_width
#print axioms Tools.ShippingGen2.call_inRange_at
#print axioms Tools.ShippingGen2.callDec_of_hPointAt_at
#print axioms Tools.ShippingGen2.hPointAt_of_callFactF_at
#print axioms tm2_callDec_at

end Tests.Gen2.AdaptInstance
