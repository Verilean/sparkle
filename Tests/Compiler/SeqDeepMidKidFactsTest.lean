import Tests.Compiler.SeqDeepMidFactsTest
import Tools.ShippingSeqChildDeepKidFactsA
-- BUILT (unit SR3q): q2 exit 0 (in-test audit THROWS on failure; standard axioms for cnt_kidFactsA, mid_kidFactsA).
-- SCOPE (binding): the CHILD `mid` of the depth-2 chain `grand -> mid -> cnt` (callee `cnt`, a leaf register machine).
-- `cnt_kidFactsA`: `KidFactsA` of the leaf `cnt` at EVERY depth (its fields from the `leaf_real_*A` lemmas).
-- `mid_kidFactsA`: `KidFactsA O mid … (n + 1)`, ALL nine fields (outsIn, outTys, kidA, kidR, masked, portsIn, inW, clk, check),
-- from `deepChild_kidFactsA`; relative to `O`, `T : RefLawsATele` (ADDED boundary), `MachineDefines` of `mid` / `cnt`, `mid_closesA`.
-- RealChildA is a history of past synthesis results, not freshness; not runtime fit.  The depth-2 grand generator stays REFUSED.
namespace Tests.Compiler.SeqDeepMidKidFactsTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingSeqChildDeepKidFactsA (KidFactsA)
open Tests.Compiler.SeqDeepMidTest Tests.Compiler.SeqDeepMidFactsTest

section
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

set_option maxHeartbeats 4000000 in
/-- **`KidFactsA` of the leaf `cnt`, every depth** (`ins = [1]`, the declared width of its one argument). -/
theorem cnt_kidFactsA (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) (n : Nat) :
    KidFactsA O ``cnt cnt.machineData.shape.layout.outs [1] n := by
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``cnt cnt.machineData.shape :=
    fun mc cc => cnt.machine_closes mc _ cc _
  have hon : ∀ o ∈ cnt.machineData.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
    fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (Tests.Compiler.KidsPassLeafTest.cnt_outs_clean o ho)
  have hdw : Tools.ShippingPortWidthsPure.declWidths cnt.machineData = [1] := by first | decide | decide +kernel
  exact
  { outsIn := fun y hy =>
      (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O cnt.machineData cnt.machine_ok cnt.machine_body
        (by decide) (by decide) hR0 hcl hy).outsIn
    outTys := fun y hy =>
      Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA (O := O) cnt.machineData cnt.machine_ok cnt.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0
        (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => cnt.machine_closes mctx' _ cctx' _ (Tools.ShippingChildInv.profLogIO b) w r w' hr) hy
    kidA := fun y hy =>
      Tools.ShippingParentRunFactsA.leaf_real_kidAA O cnt.machineData cnt.machine_ok cnt.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0 hcl hy
    kidR := fun y hy =>
      Tools.ShippingParentRunFactsA.leaf_real_kidRA O cnt.machineData cnt.machine_ok cnt.machine_body
        (by decide) (by decide) hR0 hcl hy
    masked := fun y hy =>
      Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA (nDecl := cnt.machineData.nIn) O cnt.machineData
        cnt.machine_ok cnt.machine_body (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        hR0 hcl hy
    portsIn := fun y hy =>
      Tools.ShippingParentDesignFA.leaf_real_portsInA O cnt.machineData cnt.machine_ok cnt.machine_body
        (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hon (by decide) hy
    inW := fun y hy j q hq => by
      obtain ⟨wd, h1, h2⟩ := Tools.ShippingParentDesignFA.leaf_real_inWidthsA O cnt.machineData cnt.machine_ok
        cnt.machine_body (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy j q hq
      rw [hdw] at h1
      exact ⟨wd, h1, h2⟩
    clk := fun y hy =>
      Tools.ShippingParentDesignFA.leaf_real_clkA O cnt.machineData cnt.machine_ok cnt.machine_body
        (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy
    check := fun y hy ms _ _ => by
      have hK := Tools.ShippingParentDesignFA.leaf_real_kidK_regA O cnt.machineData cnt.machine_ok cnt.machine_body
        (nDecl := cnt.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) (by decide) hR0 hcl hon (by decide) hy
      exact ⟨hK.1 _ n, fun g hg => hK.2 g hg _ n⟩ }

set_option maxHeartbeats 4000000 in
/-- **`KidFactsA` of the non-leaf child `mid` at depth `n + 1`**: all nine fields over `RealChildA O mid y`.  The grandchild
`cnt` is supplied by `cnt_kidFactsA` at depths `n` and `n + 1`. -/
theorem mid_kidFactsA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    KidFactsA O ``mid mid.machineData.shape.layout.outs
      (Tools.ShippingCallsChildPorts.argWidths mid.machineData 2) (n + 1) := by
  have hn := mid_insts_cnt
  exact Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidFactsA O T mid.machineData mid.machine_ok
    mid.machine_body (nDecl := 2) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    2 (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun _ => cnt.machineData.shape.layout.outs) (fun _ => [1]) n
    (fun k hk => by rw [hn k hk]; exact cnt_kidFactsA O hR0 n)
    (fun k hk => by rw [hn k hk]; exact cnt_kidFactsA O hR0 (n + 1))
    (by first | decide | decide +kernel) mid_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (mid_outChars o ho)) mid_outScalar
    (mid_hsep O hR0) entry
    (fun _ _ hA' => mid_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0))

end

open Lean Elab Command Meta Term in
open Tests.Compiler.ChildVertAuditTest in
run_cmd Lean.Elab.Command.liftTermElabM do
  for nm in [``cnt_kidFactsA, ``mid_kidFactsA] do
    stdAxioms nm
  let cl ← depClosure ``mid_kidFactsA
  for must in [``Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidFactsA, ``Tools.ShippingSeqChildDeepKidFactsA.core_outsIn_ranA,
      ``Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidCheckA_loc, ``Tools.ShippingSeqChildDeepKidCheckA.kids_designCheck_inA,
      ``Tools.ShippingSeqChildDeepMaskedA.deepChild_outsMaskedA, ``Tools.ShippingParentDesignFA.core_clk_ranA, ``mid_closesA] do
    unless cl.contains must do throwError "SR3q AUDIT FAILED: {must} not in the closure of mid_kidFactsA"
  let bad := cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
     `Tools.ShippingKidFacts.KidFacts].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR3q AUDIT FAILED: old boundary / old KidFacts in closure: {bad}"
  logInfo m!"SR3q: mid_kidFactsA axioms standard; closure has deepChild_kidFactsA, core_outsIn_ranA, deepChild_kidCheckA_loc; no old boundary / GenKid / KidFacts"

#print axioms cnt_kidFactsA
#print axioms mid_kidFactsA

end Tests.Compiler.SeqDeepMidKidFactsTest
