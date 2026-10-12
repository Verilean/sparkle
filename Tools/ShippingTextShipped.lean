import Tools.ShippingPrintGuard
import Tools.ShippingClosedTyped
import Tools.ShippingChecksRunFacts

/-! # The text conjuncts of the SHIPPED module, with the print guard (branch `fix/opt-fallback`)

With `Sparkle.IR.PrintGuard.printOk` among the guards of `keepGuarded`:

* `checkedOptimize_print`: for a module passing the statement-kind gate,
  the shipped module is the input module or passes the print guard (the
  three ways `checkedOptimize b = b`: the check does not bind, the
  interface check refuses the candidate, a guard — G2, G4 or the print
  guard — replaced the candidate by `b`).
* `core_text_shipped`: conjuncts 2 and 3 of `textCheckI` of
  `checkedOptimize b`, from the core run (the hypotheses of
  `core_text_raw`, and `hfne` for the gate): fallback → `core_text_raw`;
  accepted → `printOk_sound`.
* `core_designCheck_rest2` (pure): `designCheck` of the shipped module from
  `RunFacts C b` and `TypedIn b`, with ONLY `hports` and `hkids` left.
* `core_designCheck_run`: the same from the core run (the hypotheses of
  `core_runFacts`, the two data conditions on the output ports), `hports`
  and `hkids` left.
* `portsMatchB_of`: the Boolean connection check from its Prop form and the
  resolution of the instances (for conjunct 7; see
  `docs/parallel/G1-portsMatch.md`).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingTextShipped
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
open Sparkle.IR.RefineCheck (mergeChecked hierBinds hierGate hierRefineCheck)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The shipped module is the input module or passes the print guard.** -/
theorem checkedOptimize_print {b : Sparkle.IR.AST.Module} (hgate : hierGate b = true) :
    checkedOptimize b = b ∨ Sparkle.IR.PrintGuard.printOk (checkedOptimize b) = true := by
  by_cases hbind : hierBinds b = true
  · rw [Tools.ShippingGuardsSound.checkedOptimize_binding hbind]
    by_cases hacc : hierRefineCheck b
        (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
    · rw [if_pos hacc]
      exact Sparkle.IR.HierCheck.deinline_print b (Sparkle.IR.Optimize.optimizeModule b)
    · rw [if_neg hacc]
      exact Or.inl rfl
  · have hb0 : hierBinds b = false := by simpa using hbind
    exact Or.inl (Tools.ShippingGuardsSound.checkedOptimize_not_binding hgate hb0)

/-- Conjuncts 2 and 3 of `textCheckI` of the shipped module, from the same
of the input module. -/
theorem text_shipped_of {b : Sparkle.IR.AST.Module} (hgate : hierGate b = true)
    (hraw : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
        (Tools.ShippingDesignSV.weS b) b.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames b.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth b x == Tools.ShippingDesignSV.weS b x) = true) :
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf (checkedOptimize b))
        (Tools.ShippingDesignSV.weS (checkedOptimize b)) (checkedOptimize b).body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames (checkedOptimize b).body).all
        (fun x => Sparkle.IR.RegDedup.declWidth (checkedOptimize b) x ==
          Tools.ShippingDesignSV.weS (checkedOptimize b) x) = true := by
  rcases checkedOptimize_print hgate with e | e
  · rw [e]
    exact hraw
  · exact Tools.ShippingPrintGuard.printOk_sound e

set_option maxHeartbeats 4000000 in
/-- **Conjuncts 2 and 3 of `textCheckI` of the SHIPPED module, from the core
run.** No check premise. -/
theorem core_text_shipped {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf (checkedOptimize b))
        (Tools.ShippingDesignSV.weS (checkedOptimize b)) (checkedOptimize b).body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames (checkedOptimize b).body).all
        (fun x => Sparkle.IR.RegDedup.declWidth (checkedOptimize b) x ==
          Tools.ShippingDesignSV.weS (checkedOptimize b) x) = true :=
  text_shipped_of
    (Tools.ShippingChecksWidths.core_hierGate d ok hbody hC hslots hdomB hins hfne outTy hnomem
      hB hcore hpost entry closes)
    (Tools.ShippingClosedTyped.core_text_raw d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes hon hoty)

/-- **`designCheck` of the shipped module, at every depth, with the
structural AND the text conjuncts derived**: only the connection widths and
the children's check are left. -/
theorem core_designCheck_rest2
    {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {b : Sparkle.IR.AST.Module}
    (h : Tools.ShippingGuardsSound.RunFacts C b) (ht : Tools.ShippingTextTyped.TypedIn b)
    (n : Nat)
    (hports : Tools.ShippingDesignSV.portsMatchB C (checkedOptimize b) = true)
    (hkids : Tools.ShippingDesignSV.kidsPass C (Tools.ShippingChecksDesign.kidCheck C n)
      (checkedOptimize b).body = true) :
    Tools.ShippingDesignSV.designCheck C n (checkedOptimize b) = true := by
  obtain ⟨h2, h3⟩ := text_shipped_of h.gate ht.seqCheck
  exact Tools.ShippingChecksDesign.core_designCheck_rest h n h2 h3 hports hkids

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of the shipped module from the core run**: the
hypotheses of `core_runFacts`, the two data conditions on the output ports,
and — the only check premises left — the connection widths and the
children's check. -/
theorem core_designCheck_run {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
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
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (n : Nat)
    (hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) = true)
    (hkids : Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n)
      (checkedOptimize b).body = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true :=
  core_designCheck_rest2
    (Tools.ShippingChecksRunFacts.core_runFacts d ok hbody hC hslots hdomB hins hsl hfne outTy
      hnomem hkidP hkidW hB hcore hpost entry closes)
    (Tools.ShippingClosedTyped.core_closed_typedIn d ok hbody hC hslots hdomB hins outTy hnomem
      hB hcore hpost entry closes hon hoty)
    n hports hkids

/-- **The Boolean connection check from its Prop form**, for a body whose
instances resolve. -/
theorem portsMatchB_of
    {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {o : Sparkle.IR.AST.Module} (h : Tools.ShippingDesignSV.PortsMatch C o)
    (hres : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → (C mn).isSome = true) :
    Tools.ShippingDesignSV.portsMatchB C o = true := by
  unfold Tools.ShippingDesignSV.portsMatchB
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    obtain ⟨cw, hc⟩ := Option.isSome_iff_exists.mp (hres mn iname conns hst)
    obtain ⟨child, cwe⟩ := cw
    simp only [hc]
    rw [List.all_eq_true]
    intro cn hcm
    cases hc2 : cn.2 with
    | ref x =>
      have hw := h mn iname conns child cwe hst hc cn hcm x hc2
      simp [hc2, hw]
    | _ => simp [hc2]
  | _ => rfl

end Tools.ShippingTextShipped
