import Tests.Compiler.SeqDeepMidKidFactsTest
import Tools.ShippingSeqParentKidFactsA
import Tools.ShippingSeqChildDeepIfacePA
-- BUILT (unit SR3r): r11 exit 0 (r8 exit 1: callsOk nDecl 2 is false for grand, nDecl = 1; r10 exit 1: depth argument n vs n + 1). In-test audit THROWS on failure.
-- SCOPE (binding): the PARENT `grand` of the depth-2 chain `grand -> mid -> cnt` (child `mid` has a grandchild `cnt`).
-- PROVED here, relative to `O`, `T : RefLawsATele` (ADDED boundary), `hA : AdmCtx`, a returning core run of `grand`
-- (`hcore`/`hpost`), `MachineDefines` of `grand` / `mid` / `cnt`, and the start-world data `hw`/`hc` (the content of what the
-- single-depth generator calls `epA_Bnd`, spelled out; NOT a proof that it holds):
--   * `mid_ifaceP`: `ChildIfaceP` of a `RealChildA O mid y` with the NON-EMPTY served design `y.2` (names `[ofDecl cnt]`).
--   * `grand_closesA`: `MachineClosesAtA` for `grand` via `machineClosesAtA_of_memKids'`, the child interface = `mid_ifaceP`
--     (NOT the leaf interface); NAME SEPARATION supplied explicitly (`ofDecl_ne` for `mid`/`cnt` against `grand`, `hsep` by `decide`).
--   * `grand_runFacts`, `grand_outsCheck`, `grand_kidsMasked`, `grand_designCheck`: the four parent obligations, from
--     `mid_kidFactsA` (a `KidFactsA` bundle) through `Tools.ShippingSeqParentKidFactsA.kidsA_*`.
-- "structure complete" (`KidFactsA`, SR3q) is kept separate from "depth-2 endpoint complete": NOT claimed (no `epA_Bnd`, no trace /
-- `soundL` / `composed` at depth 2); the depth-2 generator stays REFUSED.
-- RealChildA is a history of past synthesis results, not freshness; not runtime fit.
namespace Tests.Compiler.SeqDeepGrandKidFactsTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tools.ShippingMachineLinked (childMap)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tests.Compiler.SeqDeepMidTest Tests.Compiler.SeqDeepMidFactsTest Tests.Compiler.SeqDeepMidKidFactsTest

theorem grand_insts_mid : ∀ (k : Nat) (hk : k < grand.machineData.shape.insts.length),
    (grand.machineData.shape.insts[k]).1 = ``mid ∧ originAt grand.machineData.shape k = .field k := by
  first | decide | decide +kernel

theorem grand_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk grand.machineData 1
      (fun _ => Tools.ShippingCallsChildPorts.argWidths mid.machineData 2) = true := by
  first | decide | decide +kernel

theorem grand_callWidths :
    Tools.ShippingCallWidths.callWidthsOk grand.machineData 1 (fun _ => mid.machineData.shape.layout.outs) = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem grand_outChars : ∀ o ∈ grand.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem grand_outScalar : ∀ o ∈ grand.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

section
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- The leaf grandchild `cnt`: the modules of a `RealChildA O cnt y'` and their instances name `[ofDecl cnt]` only. -/
theorem mid_hgk (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    ∀ (k : Nat) (hk : k < mid.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (mid.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ∈ [Sparkle.IR.ModuleName.ofDecl ``cnt] ∧
        ∀ mn i conns, Sparkle.IR.AST.Stmt.inst mn i conns ∈ g.body → mn ∈ [Sparkle.IR.ModuleName.ofDecl ``cnt] := by
  intro k hk y' hy g hg
  rw [mid_insts_cnt k hk] at hy
  have hI := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O cnt.machineData cnt.machine_ok cnt.machine_body
    (by decide) (by decide) hR0 (fun mc cc => cnt.machine_closes mc _ cc _) hy
  rcases List.mem_cons.mp hg with e | hin
  · subst e
    refine ⟨by rw [hI.name]; exact List.mem_singleton_self _, fun mn i conns hm => ?_⟩
    have := List.all_eq_true.mp hI.seqOk _ hm
    simp [Sparkle.IR.OptCheck.seqStmtOk] at this
  · rw [hI.design] at hin
    cases hin

set_option maxHeartbeats 4000000 in
/-- **`ChildIfaceP` of a `RealChildA O mid y`, with the NON-EMPTY served design** (the grandchild `cnt`'s module). -/
theorem mid_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``mid y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``mid) (Tools.ShippingMachineEntry.machNIn mid.machineData.shape)
      (mid.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl ``cnt] y.1 y.2 :=
  Tools.ShippingSeqChildDeepIfacePA.deepChild_ifaceP O T mid.machineData mid.machine_ok mid.machine_body (nDecl := 2)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide)) 2
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    _ (mid_hgk O hR0) (mid_hsep O hR0) entry
    (fun _ _ hA' => mid_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAtA grand`** (general closing; callee `mid`, which has a grandchild): the child interface is
`mid_ifaceP` (non-empty design); name separation is supplied here (`mid ≠ grand`, `cnt ≠ grand` for the served design's names,
`hsep`/`hdisjD` by the one callee). -/
theorem grand_closesA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``grand grand.machineData.shape := by
  have hent := grand_insts_mid
  have hkid : ∀ (k : Nat) (hk : k < grand.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt grand.machineData.shape k)
        (grand.machineData.shape.insts[k]).1 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``mid) (Tools.ShippingMachineEntry.machNIn mid.machineData.shape)
        (mid.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl ``cnt] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    rw [ho] at hy
    rcases hy with hy | ⟨-, hre⟩
    · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · rw [hn] at hre
      exact mid_ifaceP O T hM hR0 hre
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := 1) O T hA grand.machineData
    grand.machine_ok grand.machine_body (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun _ => Sparkle.IR.ModuleName.ofDecl ``mid) (fun _ => Tools.ShippingMachineEntry.machNIn mid.machineData.shape)
    (fun _ => mid.machineData.shape.layout.outs.map (·.name)) (fun _ => [Sparkle.IR.ModuleName.ofDecl ``cnt])
    hkid (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun k hk k' hk' _ => by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (by decide : ``mid ≠ ``grand))
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ grand.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => Tools.ShippingModuleName.ofDecl_ne (by decide : ``cnt ≠ ``grand) (List.mem_singleton.mp hx).symm)
    (fun k hk k' hk' hne => (hne (by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)).elim)

/-- `grand`'s run (the `MachineRanA` of a returning core run), with the closing supplied by `grand_closesA`. -/
theorem grand_ranA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``grand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``grand grand.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx ``grand grand.machineData.shape raw D :=
  Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (grand_closesA O T hA hM hR0) hw hc

/-- **`KidFactsA` of every call entry of `grand`** at depth `n + 1`: `mid_kidFactsA` (SR3q), the one callee `mid`. -/
theorem grand_hkid (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    ∀ (k : Nat) (hk : k < grand.machineData.shape.insts.length),
      Tools.ShippingSeqChildDeepKidFactsA.KidFactsA O (grand.machineData.shape.insts[k]).1
        ((fun _ => mid.machineData.shape.layout.outs) k)
        ((fun _ => Tools.ShippingCallsChildPorts.argWidths mid.machineData 2) k) (n + 1) := by
  intro k hk
  rw [(grand_insts_mid k hk).1]
  exact mid_kidFactsA O T n hM hR0

set_option maxHeartbeats 4000000 in
/-- **`RunFacts` of `grand`'s module** from `mid_kidFactsA`. -/
theorem grand_runFacts (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``grand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``grand grand.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  Tools.ShippingSeqParentKidFactsA.kidsA_runFacts O grand.machineData grand.machine_ok grand.machine_body
    (nDecl := 1) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun _ => mid.machineData.shape.layout.outs) (fun _ => Tools.ShippingCallsChildPorts.argWidths mid.machineData 2) (n + 1)
    (grand_hkid O T n hM hR0) grand_callWidths hpost (grand_ranA O T hA hM hR0 hcore entry hw hc)

set_option maxHeartbeats 4000000 in
/-- **`outsCheck` of `grand`'s module at depth `n + 1`**; the statement-kind gate is the `gate` of `grand_runFacts`. -/
theorem grand_outsCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``grand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``grand grand.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) (n + 1) (checkedOptimize b) = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_outsCheck O grand.machineData grand.machine_ok grand.machine_body
    (nDecl := 1) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun _ => mid.machineData.shape.layout.outs) (fun _ => Tools.ShippingCallsChildPorts.argWidths mid.machineData 2) (n + 1)
    (grand_hkid O T n hM hR0) hpost (grand_ranA O T hA hM hR0 hcore entry hw hc)
    (grand_runFacts O T n hA hM hR0 hcore hpost entry hw hc).gate

set_option maxHeartbeats 4000000 in
/-- **`kidsMaskedN`** of `grand`'s design from `KidFactsA.masked` of `mid`. -/
theorem grand_kidsMasked (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``grand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``grand grand.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_maskedN O grand.machineData grand.machine_ok grand.machine_body
    (nDecl := 1) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun _ => mid.machineData.shape.layout.outs) (fun _ => Tools.ShippingCallsChildPorts.argWidths mid.machineData 2) (n + 1)
    (grand_hkid O T n hM hR0) hpost (grand_ranA O T hA hM hR0 hcore entry hw hc)

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of `grand`'s module at depth `n + 1`**, the children's check from `mid_kidFactsA.check`. -/
theorem grand_designCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``grand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``grand grand.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) (n + 1) (checkedOptimize b) = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_designCheck O grand.machineData grand.machine_ok grand.machine_body
    (nDecl := 1) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun _ => mid.machineData.shape.layout.outs) (fun _ => Tools.ShippingCallsChildPorts.argWidths mid.machineData 2) (n + 1)
    (grand_hkid O T n hM hR0) grand_callWidths grand_callArgs hpost (grand_ranA O T hA hM hR0 hcore entry hw hc)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (grand_outChars o ho)) grand_outScalar

end

open Lean Elab Command Meta Term in
open Tests.Compiler.ChildVertAuditTest in
run_cmd Lean.Elab.Command.liftTermElabM do
  for nm in [``mid_ifaceP, ``grand_closesA, ``grand_runFacts, ``grand_outsCheck, ``grand_kidsMasked, ``grand_designCheck] do
    stdAxioms nm
  let cl ← depClosure ``grand_designCheck
  for must in [``mid_kidFactsA, ``Tools.ShippingSeqParentKidFactsA.kidsA_designCheck, ``grand_closesA, ``mid_ifaceP,
      ``Tools.ShippingSeqChildDeepIfacePA.deepChild_ifaceP, ``Tools.ShippingModuleName.ofDecl_ne] do
    unless cl.contains must do throwError "SR3r AUDIT FAILED: {must} not in the closure of grand_designCheck"
  let cl2 ← depClosure ``grand_closesA
  for must in [``mid_ifaceP, ``Tools.ShippingSeqChildDeepIfacePA.deepChild_ifaceP, ``Tools.ShippingModuleName.ofDecl_ne] do
    unless cl2.contains must do throwError "SR3r AUDIT FAILED: {must} not in the closure of grand_closesA"
  for nm in [`Tools.ShippingSeqChildIfaceA.seqChild_of_realA] do
    -- the leaf interface is used only for the grandchild `cnt` inside `mid_hgk`, never as the child interface of `grand`
    unless (← depClosure ``mid_ifaceP).contains nm do throwError "SR3r AUDIT FAILED: expected grandchild use of {nm}"
  let bad := cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
     `Tools.ShippingKidFacts.KidFacts].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR3r AUDIT FAILED: old boundary / old KidFacts in closure: {bad}"
  logInfo m!"SR3r: grand_* axioms standard; closure has mid_kidFactsA, kidsA_designCheck, mid_ifaceP (non-empty design), ofDecl_ne; no old boundary / GenKid / KidFacts"

#print axioms mid_ifaceP
#print axioms grand_closesA
#print axioms grand_runFacts
#print axioms grand_outsCheck
#print axioms grand_kidsMasked
#print axioms grand_designCheck

end Tests.Compiler.SeqDeepGrandKidFactsTest
