import Tools.ShippingMemKidCore
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # The old `core_*` statements re-derived from their `M` copies, first half (round par/b-16)

`Tools/ShippingMemKidCore.lean` holds scripted COPIES of ten built `core_*`
theorems (suffix `M`: the child predicate `Kid` in place of `RealChild`,
`hnomem` dropped or replaced by `hfne`). The copies do not follow the
originals. This file pays the part of that debt that CAN be paid without
touching an existing file: for every pair where the old statement is a
corollary of the `M` statement, the OLD statement, verbatim, is proved from
the `M` theorem as `<old>_fromM`. The old theorems are not changed and not
used here; nothing consumes `<old>_fromM` yet (the replacement of the old
proofs is a proposal — `docs/parallel/B-unify-core.md`).

The bridge (once, below): under

    hnomem : ∀ x ∈ shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true

a kid of a call entry is a real child (`real_of_kid`; `kid_iff_real_of_nomem`
is the equivalence at one name).

RE-DERIVED here (old statement already had `hfne`; the `M` copy only DROPS
`hnomem`): `core_raw_facts`, `core_outsExtracted`, `core_callPorts`,
`core_instOutWidthsOk`, `core_hierGate`, `core_runFacts`. The second half
(`core_callConns`, `core_portsMatch_raw`, `core_kidsPass_deep`,
`core_designCheck_run`) is `Tools/ShippingCoreFromMPorts.lean`.

NOT re-derived, and NOT corollaries (seven): `core_kids_facts`,
`core_linkedWF`, `core_instOuts_not_assigned`, `core_outsCheck_all_gate`,
`core_closed_typedIn`, `core_clk`, `core_kids_self`. Their old statements
have NO `hfne`: they hold of a one-output closing (`instFields = []`, closed
by `closeInsts`) too, where the `M` copy — which REPLACED `hnomem` by
`hfne : d.shape.instFields ≠ []` — says nothing. Per theorem (file:line) in
the note.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingCoreFromM
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMemKid

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! The bridge (`kid_iff_real_of_nomem`, `real_of_kid`, `kid_of_real`) is in
`Tools/ShippingKid.lean` since round par/b-24: same names, same namespace. -/

/-! ## `Tools/ShippingChecksRaw.lean` -/

section
open Tools.ShippingChecksRaw

/-- `core_raw_facts` (`Tools/ShippingChecksRaw.lean:131`), its statement VERBATIM, from
`core_raw_factsM` (`Tools/ShippingMemKidCore.lean:293`): no child predicate in the statement; `hnomem` is not used. -/
theorem core_raw_facts_fromM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true := by
  exact core_raw_factsM (hagree := (Tools.ShippingInstTagged.tagsAgree_of_nomem hnomem)) d ok hbody hC hslots hdomB hins hsl hfne outTy hB hcore hpost entry closes

end

/-! ## `Tools/ShippingChecksOuts.lean` -/

section
open Tools.ShippingChecksOuts

/-- `core_outsExtracted` (`Tools/ShippingChecksOuts.lean:86`), its statement VERBATIM, from
`core_outsExtractedM` (`Tools/ShippingMemKidCore.lean:528`): `hkidP` is asked of kids; a kid of a non-memory entry is a real child. -/
theorem core_outsExtracted_fromM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true := by
  exact core_outsExtractedM (hagree := (Tools.ShippingInstTagged.tagsAgree_of_nomem hnomem)) d ok hbody hC hslots hdomB hins hfne outTy
    (fun k hk y hy => hkidP k hk y (real_of_kid hnomem hk hy))
    hB hcore hpost entry closes

end

/-! ## `Tools/ShippingChecksWidths.lean` -/

section
open Tools.ShippingChecksWidths

/-- `core_callPorts` (`Tools/ShippingChecksWidths.lean:104`), its statement VERBATIM, from
`core_callPortsM` (`Tools/ShippingMemKidCore.lean:708`): `hkidP` bridged; the kid of the conclusion is a real child under `hnomem`. -/
theorem core_callPorts_fromM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        ∀ p ∈ mc.outputs, ∀ x, (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
            RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
            p.name = d.shape.instFields.getD k "" ∧
            ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
              Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth := by
  intro mn iname conns hmem
  obtain ⟨mc, hmc, hrest⟩ := core_callPortsM (hagree := (Tools.ShippingInstTagged.tagsAgree_of_nomem hnomem)) d ok hbody hC hslots hdomB hins hfne outTy
    (fun k hk y hy => hkidP k hk y (real_of_kid hnomem hk hy))
    hB hcore hpost entry closes mn iname conns hmem
  refine ⟨mc, hmc, ?_⟩
  intro p hp x hx
  obtain ⟨k, hk, y, hkid, hr⟩ := hrest p hp x hx
  exact ⟨k, hk, y, real_of_kid hnomem hk hkid, hr⟩

/-- `core_instOutWidthsOk` (`Tools/ShippingChecksWidths.lean:271`), its statement VERBATIM, from
`core_instOutWidthsOkM` (`Tools/ShippingMemKidCore.lean:876`): `hkidP`, `hkidW` bridged. -/
theorem core_instOutWidthsOk_fromM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingHierOpen.instOutWidthsOk (childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true := by
  exact core_instOutWidthsOkM (hagree := (Tools.ShippingInstTagged.tagsAgree_of_nomem hnomem)) d ok hbody hC hslots hdomB hins hfne outTy
    (fun k hk y hy => hkidP k hk y (real_of_kid hnomem hk hy))
    (fun k hk y hy => hkidW k hk y (real_of_kid hnomem hk hy))
    hB hcore hpost entry closes

/-- `core_hierGate` (`Tools/ShippingChecksWidths.lean:365`), its statement VERBATIM, from
`core_hierGateM` (`Tools/ShippingMemKidCore.lean:927`): no child predicate in the statement; `hnomem` is not used. -/
theorem core_hierGate_fromM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Sparkle.IR.RefineCheck.hierGate b = true := by
  exact core_hierGateM (hagree := (Tools.ShippingInstTagged.tagsAgree_of_nomem hnomem)) d ok hbody hC hslots hdomB hins hfne outTy hB hcore hpost entry closes

end

/-! ## `Tools/ShippingChecksRunFacts.lean` -/

section
open Tools.ShippingChecksRunFacts

/-- `core_runFacts` (`Tools/ShippingChecksRunFacts.lean:42`), its statement VERBATIM, from
`core_runFactsM` (`Tools/ShippingMemKidCore.lean:988`): `hkidP`, `hkidW` bridged. -/
theorem core_runFacts_fromM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b := by
  exact core_runFactsM (hagree := (Tools.ShippingInstTagged.tagsAgree_of_nomem hnomem)) d ok hbody hC hslots hdomB hins hsl hfne outTy
    (fun k hk y hy => hkidP k hk y (real_of_kid hnomem hk hy))
    (fun k hk y hy => hkidW k hk y (real_of_kid hnomem hk hy))
    hB hcore hpost entry closes

end

end Tools.ShippingCoreFromM
