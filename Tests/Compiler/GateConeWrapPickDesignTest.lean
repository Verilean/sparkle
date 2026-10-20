import Tests.Compiler.GateConeWrapPickSourceTest
import Tools.ShippingGateWalkE
import Tools.ShippingGateTypedFinalI
import Tools.ShippingGateDesignRun
import Tools.ShippingGateDesignPost
import Tools.ShippingGateOutPort
import Tools.ShippingGateCombSide
import Tools.ShippingGateOptComb
import Tools.ShippingGateNamesFinal
import Tools.ShippingGateDesignAll
import Tools.ShippingGatePorts
import Tools.ShippingCombKidText
import Tools.ShippingCallsGate

/-! # `wrapPick` at the design level, EVERY closed run (worker N, round 16)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeWrapPickDesignTest`;
not in `Tests.AllTests`).

`wrapPick sel x := pick sel x` (binders `sel : BitVec 2`, `x : BitVec 8`, no
domain binder); `pick` is a MIXED-gate child. The round-11..15 chain of the
seven other gate parents (design walk → names walk → typed walk → all-run),
lifted to `wrapPick`. Differences, each handled by a NEW lemma (old ones kept):

* the call has no domain argument: the body is `instEN pick [] sel [x]`
  (spine `[sel, x]`, BOTH ports). The instance nodes of the three walks read
  the ports as `rest`; here `desW_instE` / `namW_instE` / `typW_instE`
  (`Tools/ShippingGateWalkE.lean`) at the split `[] ++ [sel, x]`;
* the child facts of `pick` are the MIXED-gate ones (`pick_kid`):
  `InstLeafOk` from `Tools.ShippingGateKid.kidFacts_of_gate'`, `ChildComb` /
  name from `Tools.ShippingCallsGate.childFull_of_real`, the children's check
  from `Tools.ShippingCombKidText.gate_real_kidK`, `GateChildPorts` from
  `Tools.ShippingGatePorts.gate_real_ports` (the input widths `[2, 8]`, the
  output width `8`: `pick_w`);
* the typing is NOT constant (`sel` 2 bits, `x` 8 bits) and depends on which
  fresh id is `sel`: OBSTACLE for the round-14 `gate_typedFacts` (its `τ` is
  fixed before the ids; no fixed `τ` types both `[a, b]` and `[b, a]`).
  Resolved by `Tools.ShippingGateParentRun.gate_typedFactsI` (`∃ τ` per
  instantiation, `Tools/ShippingGateTypedFinalI.lean`) with `pickτ i0`
  (`2` on `.fvar i0`, `8` elsewhere).

**`wrapPick_gate_designSVall`**: premises the run, `GateDefines` (the
separate gate-only reflection class, as for the seven), `ChildBnd`,
`EntryDefines … pick pick.gateValue` (ALLOWED). Conclusion: the cone facts,
`DesignHasChild`, `PostKeeps`, and — under the input reading
(`Admissible` / `prepare … .bits`) and `DesignSideR` (run-level bounds,
unchanged) — a closed run of `checkedOptimize b` over the returned design
showing `((wrapPick sS xS).val j).toNat` on `out` AND every closed run from the
same seeding and states has length `T` and shows the source. The shape of
`wrapAdd_gate_designSVall` (`Tests/Compiler/GateConeDesignAllTest.lean`) with
the 2-bit `sel` signal. -/
namespace Sparkle.Tests.Compiler.GateConeWrapPickDesignTest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineInstTest (pick)
open Sparkle.Tests.Compiler.SlotlessParentProbeTest (wrapPick)
open Sparkle.Tests.Compiler.GateConeWrapPickTest
open Sparkle.Tests.Compiler.GateConeWrapPickSourceTest
open Tools.ShippingUnifiedSource
open Tools.ShippingUnifiedMeaning (Value)
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingGateParentRun
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (ChildBnd CacheInv Res RealChild RefLaws)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingFirstGateKid (ownChild)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingGateDesignLift (DesignHasChild PostKeeps)
open Tools.ShippingMixedEntrySoundness (prepare start)

/-! ## The child `pick` (a mixed-gate child) -/

set_option maxRecDepth 8192 in
/-- `KidFacts` of a real `pick` entry (the call of `wrapPick_gate_cone_runKT`). -/
theorem pick_kidFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (centry : EntryDefines mctx mref cctx cref ``pick
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateValue)
    {y : Res} (hreal : RealChild mref cref ``pick y) (v : Value) (hv : v.kind.width = 8) :
    KidFacts (ownChild y) pickTermSem ``pick 2 v y :=
  Tools.ShippingGateKid.kidFacts_of_gate' (F := pickF) centry
    Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_old
    Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_peel
    Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide))
    (by decide) (fun _ _ => rfl) hreal pickTermSem 2 (by decide) v (hv.trans rfl)
    pickTermSem_hC

set_option maxRecDepth 8192 in
/-- **Every `pick` entry of a `CacheInv` cache** has the instance leaf's
requirements (`InstLeafOk`, two inputs, the output `out : bitVector 8`), a
combinational closed module (`ChildComb`) not named like the parent `f`, the
children's check at every depth, and the gate child's port facts. -/
theorem pick_kid {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {f : Lean.Name}
    (centry : EntryDefines mctx mref cctx cref ``pick
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateValue)
    (hne : ``pick ≠ f) :
    ∀ mF : Std.HashMap Lean.Name Res, CacheInv mref cref mF → ∀ y : Res,
      mF.get? ``pick = some y →
      InstLeafOk (ChildGN ``pick mF) 2 y ∧ Tools.ShippingGateChildComb.ChildComb y.1 ∧
        y.1.name ≠ Sparkle.IR.ModuleName.ofDecl f ∧
        (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (k : Nat),
          Tools.ShippingChecksDesign.kidCheck C k y.1 = true) ∧
        Tools.ShippingGatePorts.GateChildPorts ``pick
          Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateBinders
          Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateSort.width y.1 := by
  intro mF hcache y hy
  have hreal : RealChild mref cref ``pick y := hcache ``pick y hy
  have full := Tools.ShippingCallsGate.childFull_of_real centry
    Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_old
    Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_peel
    Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) hreal
  obtain ⟨cwe, outName, wOut, hdc, hnoclk, -, houts, -, hlen, hwidth, -, -⟩ :=
    pick_kidFacts centry hreal (.bits 8 0) rfl
  have hw8 : wOut = 8 := hwidth.symm
  refine ⟨⟨⟨y, hy, rfl⟩, hdc, hnoclk, hlen, outName, wOut, houts, ?_⟩, full.comb, ?_, ?_, ?_⟩
  · rw [hw8]
    decide
  · rw [full.name]
    exact Tools.ShippingModuleName.ofDecl_ne hne
  · exact (Tools.ShippingCombKidText.gate_real_kidK centry
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_old
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_peel
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_wf
      (Tools.ShippingGateChild.bool_positions (by decide))
      (Tools.ShippingGateChild.bits_positions (by decide)) hreal).1
  · exact Tools.ShippingGatePorts.gate_real_ports centry
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_old
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_peel
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_wf
      (Tools.ShippingGateChild.bool_positions (by decide))
      (Tools.ShippingGateChild.bits_positions (by decide)) hreal

/-- The child facts in the form `gate_combFacts` asks. -/
theorem pick_kidN {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {f : Lean.Name}
    (centry : EntryDefines mctx mref cctx cref ``pick
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateValue)
    (hne : ``pick ≠ f) :
    ∀ mF : Std.HashMap Lean.Name Res, CacheInv mref cref mF → ∀ y : Res,
      mF.get? ``pick = some y →
      InstLeafOk (ChildGN ``pick mF) 2 y ∧ Tools.ShippingGateChildComb.ChildComb y.1 ∧
        y.1.name ≠ Sparkle.IR.ModuleName.ofDecl f ∧
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (k : Nat),
          Tools.ShippingChecksDesign.kidCheck C k y.1 = true := by
  intro mF hcache y hy
  obtain ⟨h1, h2, h3, h4, -⟩ := pick_kid centry hne mF hcache y hy
  exact ⟨h1, h2, h3, h4⟩

/-- The child facts in the form `gate_typedFactsI` asks. -/
theorem pick_kidT {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {f : Lean.Name}
    (centry : EntryDefines mctx mref cctx cref ``pick
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateValue)
    (hne : ``pick ≠ f) :
    ∀ mF : Std.HashMap Lean.Name Res, CacheInv mref cref mF → ∀ y : Res,
      mF.get? ``pick = some y →
      InstLeafOk (ChildGN ``pick mF) 2 y ∧ Tools.ShippingGateChildComb.ChildComb y.1 ∧
        y.1.name ≠ Sparkle.IR.ModuleName.ofDecl f ∧
        Tools.ShippingGatePorts.GateChildPorts ``pick
          Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateBinders
          Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateSort.width y.1 := by
  intro mF hcache y hy
  obtain ⟨h1, h2, h3, -, h5⟩ := pick_kid centry hne mF hcache y hy
  exact ⟨h1, h2, h3, h5⟩

/-- `pick`'s port widths: the inputs `[2, 8]` in order, the output `8`. -/
def PickW (m : Sparkle.IR.AST.Module) : Prop :=
  m.inputs.map (fun p => p.ty.bitWidth) = [2, 8] ∧ ∀ p ∈ m.outputs, p.ty.bitWidth = 8

set_option maxRecDepth 8192 in
/-- `pick`'s port widths, from its `GateChildPorts` facts (the gate's binders
`[sel : bits 2, x : bits 8]`, the sort of width 8; by evaluation). -/
theorem pick_w {m : Sparkle.IR.AST.Module}
    (h : Tools.ShippingGatePorts.GateChildPorts ``pick
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateBinders
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateSort.width m) : PickW m := by
  refine ⟨?_, fun p hp => ?_⟩
  · have h1 : m.inputs.map (fun p => p.ty.bitWidth) =
        (m.inputs.map (·.ty)).map Sparkle.IR.Type.HWType.bitWidth := by
      rw [List.map_map]
      try rfl
    rw [h1, h.inTys]
    first
      | rfl
      | decide
  · rw [(h.outWidth p hp).2]
    first
      | rfl
      | decide

/-- The width premise of `typW_instE` for a call of `pick` on `[a, b]`. -/
theorem pick_ws {τ : Lean.Expr → Nat} {mF : Std.HashMap Lean.Name Res} {a b e : Lean.Expr}
    (hwd : ∀ y : Res, mF.get? ``pick = some y → PickW y.1)
    (ha : τ a = 2) (hb : τ b = 8) (he : τ e = 8) :
    ∀ y : Res, mF.get? ``pick = some y →
      (∀ pe ∈ y.1.inputs.zip [a, b], τ pe.2 = pe.1.ty.bitWidth) ∧
      ∀ p ∈ y.1.outputs, p.ty.bitWidth = τ e := by
  intro y hy
  obtain ⟨hin, hout⟩ := hwd y hy
  refine ⟨?_, fun p hp => by rw [he]; exact hout p hp⟩
  generalize y.1.inputs = ins at hin ⊢
  rcases ins with _ | ⟨p0, _ | ⟨p1, ins⟩⟩
  · simp at hin
  · simp at hin
  rcases ins with _ | ⟨p2, ins⟩
  rotate_left
  · simp at hin
  try simp only [List.map_cons, List.map_nil] at hin
  obtain ⟨h0, h1'⟩ := List.cons.inj hin
  obtain ⟨h1, -⟩ := List.cons.inj h1'
  intro pe hpe
  have hpe' : pe = (p0, a) ∨ pe = (p1, b) := by
    first
      | simpa using hpe
      | (simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
          or_false] at hpe
         exact hpe)
  rcases hpe' with rfl | rfl
  · exact ha.trans h0.symm
  · exact hb.trans h1.symm

/-! ## The typing of the cone: `sel` is 2 bits, `x` and the call 8 bits -/

/-- `2` on the first binder `.fvar i0` (`sel`), `8` elsewhere. -/
noncomputable def pickτ (i0 : FVarId) (e : Lean.Expr) : Nat :=
  @ite Nat (e = Lean.Expr.fvar i0) (Classical.propDecidable _) 2 8

/-! ## The three walks of `wrapPick`'s body -/

theorem wrapPick_desW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``pick = true)
    (hleaf : ∀ y : Res, mF.get? ``pick = some y → InstLeafOk G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = wrapPickBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapPickBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))).context
      G (Sparkle.IR.ModuleName.ofDecl ``wrapPick)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapPickBody) true := by
  have len2 : ids.length = 2 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len2
  rcases ids with _ | ⟨i1, ids⟩
  · cases len2
  rcases ids with _ | ⟨i2, ids⟩
  rotate_left
  · simp at len2
  obtain ⟨z0, hz0⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
    (wrapPickBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))
    `sel (.bits 2) i0 nd (by simp [wrapPickBinders]) (by decide)
  obtain ⟨z1, hz1⟩ := prepare_lookup_hit (fun _ => false) (fun _ _ => 0)
    (wrapPickBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))
    `x (.bits 8) i1 nd (by simp [wrapPickBinders]) (by decide)
  have h1 : 1 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 1) + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h1).symm
  have hbody : instFVars ([i0, i1].map Lean.Expr.fvar).toArray 0 wrapPickBody =
      instEN ``pick [] (.fvar i0) [.fvar i1] := rfl
  rw [hbody, hfl]
  refine desW_instE (tenv := envR) (mn := ``pick) (lvls := []) (dom := .fvar i0)
    (rest := [.fvar i1]) (pre := []) (argsE := [.fvar i0, .fvar i1])
    L hD (translateFuelLimit - 1) rfl rfl rfl rfl tagR hleaf ?_
  intro k hk
  rcases k with _ | k
  · exact ⟨false, desW_fvar (tenv := envR) L hz0 _⟩
  · rcases k with _ | k
    · exact ⟨false, desW_fvar (tenv := envR) L hz1 _⟩
    · exact absurd hk (by simp)

theorem wrapPick_namW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``pick = true)
    (hleaf : ∀ y : Res, mF.get? ``pick = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = wrapPickBinders.length) :
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapPickBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))).context
      G (prepInsN wrapPickBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``wrapPick))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapPickBody) := by
  have len2 : ids.length = 2 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len2
  rcases ids with _ | ⟨i1, ids⟩
  · cases len2
  rcases ids with _ | ⟨i2, ids⟩
  rotate_left
  · simp at len2
  obtain ⟨z0, hz0, hz0I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (wrapPickBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))
    `sel (.bits 2) i0 nd (by simp [wrapPickBinders]) (by decide)
  obtain ⟨z1, hz1, hz1I⟩ := prepare_lookup_hitI (fun _ => false) (fun _ _ => 0)
    (wrapPickBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))
    `x (.bits 8) i1 nd (by simp [wrapPickBinders]) (by decide)
  have h1 : 1 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 1) + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h1).symm
  have hbody : instFVars ([i0, i1].map Lean.Expr.fvar).toArray 0 wrapPickBody =
      instEN ``pick [] (.fvar i0) [.fvar i1] := rfl
  rw [hbody, hfl]
  refine namW_instE (tenv := envR) (mn := ``pick) (lvls := []) (dom := .fvar i0)
    (rest := [.fvar i1]) (pre := []) (argsE := [.fvar i0, .fvar i1])
    L hD (translateFuelLimit - 1) rfl rfl rfl rfl tagR hleaf ?_
  intro k hk
  rcases k with _ | k
  · exact namW_fvar (tenv := envR) L hz0 hz0I _
  · rcases k with _ | k
    · exact namW_fvar (tenv := envR) L hz1 hz1I _
    · exact absurd hk (by simp)

/-- **The typed walk of `wrapPick`'s body, under the typing `pickτ i0` of
ITS instantiation** (the call's arguments `sel`, `x` have the widths 2 and 8
of `pick`'s input ports, the call the width 8 of its output port). -/
theorem wrapPick_typW {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``pick = true)
    (hleaf : ∀ y : Res, mF.get? ``pick = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``pick = some y → PickW y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = wrapPickBinders.length) :
    ∃ τ : Lean.Expr → Nat,
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapPickBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))).context
      G (prepPortsT wrapPickBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``wrapPick)) τ
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapPickBody) := by
  have len2 : ids.length = 2 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len2
  rcases ids with _ | ⟨i1, ids⟩
  · cases len2
  rcases ids with _ | ⟨i2, ids⟩
  rotate_left
  · simp at len2
  have hne : i1 ≠ i0 := by
    intro h
    apply (List.nodup_cons.mp nd).1
    rw [h]
    exact List.mem_singleton_self _
  obtain ⟨z0, hz0, hz0P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (wrapPickBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))
    `sel 2 i0 nd (by simp [wrapPickBinders])
  obtain ⟨z1, hz1, hz1P⟩ := prepare_lookup_hitB (fun _ => false) (fun _ _ => 0)
    (wrapPickBinders.zip [i0, i1])
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))
    `x 8 i1 nd (by simp [wrapPickBinders])
  -- the typing: `2` on `sel`, `8` on `x` and on the call
  have hτ0 : pickτ i0 (.fvar i0) = 2 := by
    unfold pickτ
    exact if_pos rfl
  have hτ1 : pickτ i0 (.fvar i1) = 8 := by
    unfold pickτ
    refine if_neg ?_
    intro h
    apply hne
    first
      | exact Lean.Expr.fvar.inj h
      | (cases h; rfl)
      | injection h
  have hτc : pickτ i0 (instEN ``pick [] (.fvar i0) [.fvar i1]) = 8 := by
    unfold pickτ
    refine if_neg ?_
    intro h
    first
      | cases h
      | exact Lean.Expr.noConfusion h
      | simp [instEN] at h
  have hs0 : ScalT (.bitVector 2) (pickτ i0 (.fvar i0)) := by
    rw [hτ0]
    exact ⟨by decide, Or.inr rfl⟩
  have hs1 : ScalT (.bitVector 8) (pickτ i0 (.fvar i1)) := by
    rw [hτ1]
    exact ⟨by decide, Or.inr rfl⟩
  refine ⟨pickτ i0, ?_⟩
  have h1 : 1 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 1) + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h1).symm
  have hbody : instFVars ([i0, i1].map Lean.Expr.fvar).toArray 0 wrapPickBody =
      instEN ``pick [] (.fvar i0) [.fvar i1] := rfl
  rw [hbody, hfl]
  refine typW_instE (tenv := envR) (mn := ``pick) (lvls := []) (dom := .fvar i0)
    (rest := [.fvar i1]) (pre := []) (argsE := [.fvar i0, .fvar i1])
    L hD (translateFuelLimit - 1) rfl rfl rfl rfl tagR hleaf
    (pick_ws hwd hτ0 hτ1 hτc) ?_
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact typW_fvar (tenv := envR) L hz0 hz0P hs0 _
  rcases List.mem_cons.mp ha with rfl | ha
  · exact typW_fvar (tenv := envR) L hz1 hz1P hs1 _
  exact absurd ha List.not_mem_nil

theorem wrapPick_walk2 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``pick = true)
    (hleaf : ∀ y : Res, mF.get? ``pick = some y → InstLeafOk2 G 2 y)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = wrapPickBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapPickBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))).context
      G (Sparkle.IR.ModuleName.ofDecl ``wrapPick)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapPickBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapPickBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))).context
      G (prepInsN wrapPickBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``wrapPick))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapPickBody) :=
  ⟨wrapPick_desW L hD tagR (fun y hy => (hleaf y hy).1) cache ids nd len,
    wrapPick_namW L hD tagR hleaf cache ids nd len⟩

theorem wrapPick_walk3 {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {mF : Std.HashMap Lean.Name Res}
    {G : Sparkle.IR.AST.Module → Prop}
    (tagR : Sparkle.Compiler.isHardwareModule envR ``pick = true)
    (hleaf : ∀ y : Res, mF.get? ``pick = some y → InstLeafOk2 G 2 y)
    (hwd : ∀ y : Res, mF.get? ``pick = some y → PickW y.1)
    (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId) (nd : ids.Nodup)
    (len : ids.length = wrapPickBinders.length) :
    DesW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapPickBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))).context
      G (Sparkle.IR.ModuleName.ofDecl ``wrapPick)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapPickBody) true ∧
    NamW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapPickBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))).context
      G (prepInsN wrapPickBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``wrapPick))
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapPickBody) ∧
    ∃ τ : Lean.Expr → Nat,
    TypW L mF D (translateFuelFix (translateStep envR) translateFuelLimit)
      (prepare (fun _ => false) (fun _ _ => 0) (wrapPickBinders.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick))).context
      G (prepPortsT wrapPickBinders ids cache (Sparkle.IR.ModuleName.ofDecl ``wrapPick)) τ
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapPickBody) :=
  ⟨wrapPick_desW L hD tagR (fun y hy => (hleaf y hy).1) cache ids nd len,
    wrapPick_namW L hD tagR hleaf cache ids nd len,
    wrapPick_typW L hD tagR hleaf hwd cache ids nd len⟩

/-! ## Obstacle (A) and the core module's `ModOk` -/

set_option maxRecDepth 8192 in
/-- **`wrapPick`: the cone at the source, obstacle (A) and `ModOk`** — the text
of `wrapAdd_gate_designA` with the mixed-gate child facts (`pick_kid`) and the
source observation (`wrapPickObservesC_of_T`). -/
theorem wrapPick_gate_designA {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``wrapPick) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``wrapPick wrapPickBinders wrapPickBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``pick
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``pick = true ∧
      mF.get? ``pick = some y ∧ WrapPickObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ ModOk (Sparkle.IR.ModuleName.ofDecl ``wrapPick) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry,
    hdes⟩ := gate_cone_runGED hr gdef bnd
  have tagR := wrapPick_tag hacc
  obtain ⟨y, hy⟩ := hentry ``pick
    (fun L' _ hD ids len => wrapPick_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``pick y := hcache ``pick y hy
  have fin := hdes (ChildGN ``pick mF)
    (fun L' _ hD cache ids nd len =>
      wrapPick_desW L' hD tagR
        (fun y' hy' => (pick_kid (f := ``wrapPick) centry (by decide) mF hcache y' hy').1)
        cache ids nd len)
    (binders_pos_of_all rfl)
  exact ⟨M, envR, mF, y, hpost, hcache, tagR, hy,
    wrapPickObservesC_of_T (wrapPick_coneKT hcone tagR hy (fun v hv =>
      pick_kidFacts centry hreal v hv)),
    designHasChild_of_final fin (childGN_eq hy)
      (pick_kid (f := ``wrapPick) centry (by decide) mF hcache y hy).2.2.1 hmods,
    fin.mod⟩

/-! ## The design level, every closed run -/

set_option maxRecDepth 8192 in
/-- **`wrapPick` at the design level, EVERY closed run** (the form of
`wrapAdd_gate_designSVall`): a closed run of the emitted texts showing
`((wrapPick sS xS).val j).toNat` on `out` exists, and every closed run from the
same seeding and states has length `T` and shows it. Derived on the way, as for
the seven: (B) `PostKeeps` (`postKeeps_of_modOk`), (C) `OptKeepsOut`
(`optKeepsOut_comb_post`, `gate_out_port`), `hierGate`, the six facts of
`gate_combFacts`, `hierTyped` and `designSideB3` (`gate_typedFactsI`, typing
per instantiation). Premises: the run, `GateDefines` (separate gate-only
class), `ChildBnd`, `EntryDefines` of `pick` (ALLOWED). Left on the design
part: the input reading and `DesignSideR` (run-level bounds), as for the
seven. -/
theorem wrapPick_gate_designSVall {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``wrapPick) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``wrapPick wrapPickBinders wrapPickBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``pick
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
      (y : Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``pick = true ∧
      mF.get? ``pick = some y ∧ WrapPickObservesC (ownChild y) M ∧
      DesignHasChild design.modules y ∧ PostKeeps b M ∧
      (∃ (i0 i1 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
        ∀ (sS : Signal defaultDomain (BitVec 2)) (xS : Signal defaultDomain (BitVec 8)) (T : Nat)
          (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
          (kids : String → Tools.ShippingHierState.KidState),
          (∀ t st, t < T → ∃ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
            Tools.ShippingMixedEntrySoundness.Admissible bools bits (seedIn b ins t st)
              (wrapPickBinders.zip [i0, i1])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``wrapPick)) ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (wrapPickBinders.zip [i0, i1])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``wrapPick))).bits i0 =
              some ⟨2, sS.val (T - 1 - t)⟩ ∧
            (Tools.ShippingMixedEntrySoundness.prepare bools bits
              (wrapPickBinders.zip [i0, i1])
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl ``wrapPick))).bits i1 =
              some ⟨8, xS.val (T - 1 - t)⟩) →
          Tools.ShippingGateCombSide.DesignSideR design.modules b ins st0 kids →
          (∃ envsO, Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
            envsO.length = T ∧
            ∀ (j : Nat) (hj : j < envsO.length),
              (envsO[j]'hj) "out" = ((wrapPick sS xS).val j).toNat) ∧
          ∀ envs', Tools.ShippingDesignSV.DesignSV
              (Tools.ShippingMachineLinked.childMap design.modules) 0
              (Sparkle.IR.OptCheck.checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
            envs'.length = T ∧
            ∀ (j : Nat) (hj : j < envs'.length),
              (envs'[j]'hj) "out" = ((wrapPick sS xS).val j).toNat) := by
  obtain ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hmod⟩ :=
    wrapPick_gate_designA hr gdef bnd centry
  have hB : PostKeeps b M := Tools.ShippingGateDesignPost.postKeeps_of_modOk hmod hpost
  have hg : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingGateCombSide.hierGate_of_modOk hmod hpost
  have houtP := Tools.ShippingGateOutPort.gate_out_port hr gdef bnd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tools.ShippingGateParentRun.gate_combFacts (c := ``pick)
    (n := 2) hr gdef bnd (pick_kidN centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      wrapPick_walk2 L' hD' (wrapPick_tag hacc) hleaf cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  obtain ⟨hty, hDB⟩ := Tools.ShippingGateParentRun.gate_typedFactsI (c := ``pick) (n := 2)
    hr gdef bnd (pick_kidT centry (by decide))
    (fun envR' hacc mF' hleaf L' D' hD' cache' ids nd len =>
      wrapPick_walk3 L' hD' (wrapPick_tag hacc) (fun y' hy' => (hleaf y' hy').1)
        (fun y' hy' => pick_w (hleaf y' hy').2) cache' ids nd len)
    (Tools.ShippingGateParentRun.binders_pos_of_all rfl)
  have hSB := Tools.ShippingGateParentRun.combSideB_ofN h1 h2 h3 h4 h5 hty
  have hDB4 := Tools.ShippingGateParentRun.designSideB_of3 hDB h6
  have hC := Tools.ShippingGateOptComb.optKeepsOut_comb_post hB
    (Tools.ShippingGateCombSide.combOptSide_of_B hg hSB) houtP
  refine ⟨M, envR, mF, y, hpost, hcache, tagR, hy, hobs, hA, hB, ?_⟩
  obtain ⟨i0, i1, cache, H⟩ := hobs
  refine ⟨i0, i1, cache, ?_⟩
  intro sS xS T ins st0 mems kids hin hR
  obtain ⟨envsO, hD, hlen, hob⟩ := Tools.ShippingGateDesignLift.gate_designSV_of_steps hA hB hC
    (T := T) (ins := ins) (st0 := st0) (mems := mems) (kids := kids)
    (G := fun s => ((wrapPick sS xS).val s).toNat)
    (fun k st mems' hk => by
      obtain ⟨bools, bits, adm, ha, hb⟩ := hin k st hk
      obtain ⟨⟨result, hev, hout⟩, hlink⟩ :=
        H bools bits (seedIn b ins k st) sS xS (T - 1 - k) mems' adm ha hb
      exact ⟨result, hev, hout, hlink⟩)
    (Tools.ShippingGateCombSide.designSide_of_R hg hSB hDB4 hR)
  exact ⟨⟨envsO, hD, hlen, hob⟩,
    Tools.ShippingGateDesignAll.gate_sv_all hg h1 h2 h3 h4 h5 h6 hDB hR hD
      (fun e => e.length = T ∧ ∀ (j : Nat) (hj : j < e.length),
        (e[j]'hj) "out" = ((wrapPick sS xS).val j).toNat)
      ⟨hlen, hob⟩⟩

end Sparkle.Tests.Compiler.GateConeWrapPickDesignTest

#print axioms Sparkle.Tests.Compiler.GateConeWrapPickDesignTest.pick_kid
#print axioms Sparkle.Tests.Compiler.GateConeWrapPickDesignTest.pick_w
#print axioms Sparkle.Tests.Compiler.GateConeWrapPickDesignTest.wrapPick_typW
#print axioms Sparkle.Tests.Compiler.GateConeWrapPickDesignTest.wrapPick_gate_designA
#print axioms Sparkle.Tests.Compiler.GateConeWrapPickDesignTest.wrapPick_gate_designSVall
