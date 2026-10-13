import Tools.ShippingKidFacts
import Tools.ShippingKidFactsRan
import Tools.ShippingMachineSeqLinkedRan
import Tools.ShippingMachineRan
import Tools.ShippingChecksRun2
import Tools.ShippingHierGateAny
import Tools.ShippingCallsChildPorts
import Tools.ShippingCallsPortsG

/-! # The statements of the split lemmas, PINNED (round par/g-1)

WRITTEN, NOT BUILT. TARGET-ONLY; not in `Tests.AllTests`. ASSERTING: any
drift of a pinned statement is an elaboration error of this file.

Round par/g-1 splits the base lemmas of the design-level chain into a tail
over `Tools.ShippingMachineRan.MachineRan` and a corollary at the all-worlds
closing. The corollary must have the BUILT statement. This file states, for
every theorem below, the statement AS IT WAS at the base commit `f1ed620f`
(copied by script from `git show f1ed620f:<file>`, the theorem's binders
turned into a `∀`), and checks it two ways:

1. `example : <old statement> := @<name>` — the present constant has that
   type up to definitional equality (binder order and types; binder NAMES and
   implicitness are not seen by this check);
2. a `run_cmd` that reads the present constant's leading binders and
   compares their NAMES and KINDS (`e` explicit, `i` implicit, `c` instance)
   with the list parsed from the old text — the part check 1 does not see.

| theorem | file | this round | binders |
|---|---|---|---|
| `Tools.ShippingChecksCore.core_kids_facts` | `Tools/ShippingChecksCore.lean` | split | 25 |
| `Tools.ShippingMemKid.core_kids_factsM` | `Tools/ShippingChecksCore.lean` | split | 25 |
| `Tools.ShippingMemKid.core_raw_factsM` | `Tools/ShippingChecksRaw.lean` | split | 26 |
| `Tools.ShippingMemKid.core_hierGateM` | `Tools/ShippingChecksWidths.lean` | split | 25 |
| `Tools.ShippingMemKid.core_callPortsM` | `Tools/ShippingChecksWidths.lean` | split | 26 |
| `Tools.ShippingClosedTyped.core_closed_typedIn` | `Tools/ShippingClosedTyped.lean` | split | 27 |
| `Tools.ShippingChecksOuts.core_outsExtracted` | `Tools/ShippingChecksOuts.lean` | split | 27 |
| `Tools.ShippingChecksRun2.kidsDesign_real` | `Tools/ShippingChecksRun2.lean` | not edited | 25 |
| `Tools.ShippingCoreClk.core_clk` | `Tools/ShippingCoreClk.lean` | split | 26 |
| `Tools.ShippingKidsSelf.core_kids_self` | `Tools/ShippingKidsSelf.lean` | split | 22 |
| `Tools.ShippingHierGateAny.core_hierGate_any` | `Tools/ShippingHierGateAny.lean` | not edited | 25 |
| `Tools.ShippingCallsChildPorts.core_calls_ports₁` | `Tools/ShippingCallsChildPorts.lean` | not edited | 34 |
| `Tools.ShippingCallsPortsG.core_calls_portsG` | `Tools/ShippingCallsPortsG.lean` | not edited | 34 |
| `Tools.ShippingLinkedFresh.core_linkedWF` | `Tools/ShippingLinkedFresh.lean` | split | 25 |
| `Tools.ShippingPortsMatchRaw.core_callConns` | `Tools/ShippingPortsMatchRaw.lean` | split | 26 |
| `Tools.ShippingMachineTraceX.synthesizeCombinationalCore_machine_soundRA` | `Tools/ShippingMachineTraceX.lean` | split | 25 |
| `Tools.ShippingMachineTraceX.machine_trace_lets_of_streamBRA` | `Tools/ShippingMachineTraceX.lean` | split | 25 |
| `Tools.ShippingMachineRan.machineRan_of_closes` | `Tools/ShippingMachineRan.lean` | moved | 14 |
| `Tools.ShippingMachineRan.core_kids_self_ran` | `Tools/ShippingMachineRan.lean` | re-proved | 17 |
| `Tools.ShippingMachineRan.core_kids_self_of_closes` | `Tools/ShippingMachineRan.lean` | not edited | 22 |

"split": the proof is now `<name>_ran … (machineRan_of_closes …)`; "moved":
the declaration is in `Tools/ShippingMachineRanBase.lean` under the same full
name; "re-proved": the proof is now one application of the split lemma; "not
edited": pinned all the same (four of the thirteen lemmas listed in
`docs/parallel/A-outermost-form.md` are not on the endpoint's path and were
left alone — `docs/parallel/G-mixdeep-outermost.md`).

The `open` lists of each section are the original namespace's (statements
resolve as they do there); the namespace itself is opened, not entered.

The last `run_cmd` also asserts that every `_ran` form exists and that the
`_ran` forms and the pinned theorems depend on the standard axioms only. -/
namespace Tests.Compiler.RanSplitStatementsTest

section Pin0
open Tools.ShippingChecksCore
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

-- Tools.ShippingChecksCore.core_kids_facts (Tools/ShippingChecksCore.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    M.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ b.body = M.body ∧ b.outputs = M.outputs ∧
    (∀ mn i conns, Stmt.inst mn i conns ∈ M.body → ∃ mc, moduleByName D.modules mn = some mc) ∧
    (∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      ∀ g2 ∈ y.1 :: y.2.modules, ∃ g' ∈ D.modules, g'.name = g2.name) ∧
    Tools.ShippingDesignSVBack.outsAssigned b = true :=
  @Tools.ShippingChecksCore.core_kids_facts

end Pin0

section Pin1
open Tools.ShippingMemKid
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
open Tools.ShippingChecksCore

-- Tools.ShippingMemKid.core_kids_factsM (Tools/ShippingChecksCore.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hfne : d.shape.instFields ≠ [])
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    M.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ b.body = M.body ∧ b.outputs = M.outputs ∧
    (∀ mn i conns, Stmt.inst mn i conns ∈ M.body → ∃ mc, moduleByName D.modules mn = some mc) ∧
    (∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      ∀ g2 ∈ y.1 :: y.2.modules, ∃ g' ∈ D.modules, g'.name = g2.name) ∧
    Tools.ShippingDesignSVBack.outsAssigned b = true :=
  @Tools.ShippingMemKid.core_kids_factsM

end Pin1

section Pin2
open Tools.ShippingMemKid
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
open Tools.ShippingChecksRaw

-- Tools.ShippingMemKid.core_raw_factsM (Tools/ShippingChecksRaw.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
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
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true :=
  @Tools.ShippingMemKid.core_raw_factsM

end Pin2

section Pin3
open Tools.ShippingMemKid
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

-- Tools.ShippingMemKid.core_hierGateM (Tools/ShippingChecksWidths.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    Sparkle.IR.RefineCheck.hierGate b = true :=
  @Tools.ShippingMemKid.core_hierGateM

end Pin3

section Pin4
open Tools.ShippingMemKid
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

-- Tools.ShippingMemKid.core_callPortsM (Tools/ShippingChecksWidths.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        ∀ p ∈ mc.outputs, ∀ x, (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
            Kid mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
            p.name = d.shape.instFields.getD k "" ∧
            ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
              Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth :=
  @Tools.ShippingMemKid.core_callPortsM

end Pin4

section Pin5
open Tools.ShippingClosedTyped
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

-- Tools.ShippingClosedTyped.core_closed_typedIn (Tools/ShippingClosedTyped.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    -- the two data conditions on the output ports
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true),
    Tools.ShippingTextTyped.TypedIn b :=
  @Tools.ShippingClosedTyped.core_closed_typedIn

end Pin5

section Pin6
open Tools.ShippingChecksOuts
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

-- Tools.ShippingChecksOuts.core_outsExtracted (Tools/ShippingChecksOuts.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
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
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true :=
  @Tools.ShippingChecksOuts.core_outsExtracted

end Pin6

section Pin7
open Tools.ShippingChecksRun2
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

-- Tools.ShippingChecksRun2.kidsDesign_real (Tools/ShippingChecksRun2.lean): not edited
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (namesK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2)
    (hself : (Sparkle.IR.ModuleName.ofDecl c) ∉ namesOf d namesK)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    ∀ g ∈ design.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) :=
  @Tools.ShippingChecksRun2.kidsDesign_real

end Pin7

section Pin8
open Tools.ShippingCoreClk
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

-- Tools.ShippingCoreClk.core_clk (Tools/ShippingCoreClk.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hsl : d.shape.layout.slots ≠ [])
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1 :=
  @Tools.ShippingCoreClk.core_clk

end Pin8

section Pin9
open Tools.ShippingKidsSelf
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

-- Tools.ShippingKidsSelf.core_kids_self (Tools/ShippingKidsSelf.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 :=
  @Tools.ShippingKidsSelf.core_kids_self

end Pin9

section Pin10
open Tools.ShippingHierGateAny
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

-- Tools.ShippingHierGateAny.core_hierGate_any (Tools/ShippingHierGateAny.lean): not edited
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    Sparkle.IR.RefineCheck.hierGate b = true :=
  @Tools.ShippingHierGateAny.core_hierGate_any

end Pin10

section Pin11
open Tools.ShippingCallsChildPorts
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
open Tools.ShippingPortWidthsPure

-- Tools.ShippingCallsChildPorts.core_calls_ports₁ (Tools/ShippingCallsChildPorts.lean): not edited
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hsl : d.shape.layout.slots ≠ [])
    -- the argument split (the data conditions of `kidsChild_iface`)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    CallsPorts c d kD b :=
  @Tools.ShippingCallsChildPorts.core_calls_ports₁

end Pin11

section Pin12
open Tools.ShippingCallsPortsG
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
open Tools.ShippingPortWidthsPure
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)

-- Tools.ShippingCallsPortsG.core_calls_portsG (Tools/ShippingCallsPortsG.lean): not edited
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hsl : d.shape.layout.slots ≠ [])
    -- the argument split (the data conditions of `kidsChild_iface`)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    CallsPorts c d kD b :=
  @Tools.ShippingCallsPortsG.core_calls_portsG

end Pin12

section Pin13
open Tools.ShippingLinkedFresh
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
open Tools.ShippingHierOpen (linkedWF bodyInstOuts stmtInstOuts linkedWrites instOutWires)

-- Tools.ShippingLinkedFresh.core_linkedWF (Tools/ShippingLinkedFresh.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    Tools.ShippingHierOpen.linkedWF (childMap D.modules) b.body = true :=
  @Tools.ShippingLinkedFresh.core_linkedWF

end Pin13

section Pin14
open Tools.ShippingPortsMatchRaw
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

-- Tools.ShippingPortsMatchRaw.core_callConns (Tools/ShippingPortsMatchRaw.lean): split
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
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
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        (∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
          RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1) ∧
        ∀ pn x, (pn, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          (isSeqChild mc = true ∧ ((pn = "clk" ∧ x = "clk") ∨ (pn = "rst" ∧ x = "rst"))) ∨
          (x ∈ b.wires.map (·.name) ∧
            ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
              RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
              ((pn = d.shape.instFields.getD k "" ∧ (∃ p ∈ mc.outputs, p.name = pn) ∧
                  ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
                    Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth) ∨
                (∃ (j : Nat) (q : Port) (a : Nat) (bn : Name × MixedGateBinder),
                  (inPortsOf mc)[j]? = some q ∧ q.name = pn ∧
                  ((d.shape.insts[k]).2.1)[j]? = some a ∧
                  d.shape.binders[nDecl + (d.shape.insts.length +
                    (d.shape.layout.slots.length + a))]? = some bn ∧
                  Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth))) :=
  @Tools.ShippingPortsMatchRaw.core_callConns

end Pin14

section Pin15
open Tools.ShippingMachineTraceX
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST

-- Tools.ShippingMachineTraceX.synthesizeCombinationalCore_machine_soundRA (Tools/ShippingMachineTraceX.lean): split
example : ∀ {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Design}
    {shape : MachineShape} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref declName shape)
    (hsyn : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hbs : shape.binders = bsIn ++ slotBs ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outsOk : ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (shape.layout.outs.map (·.name)).Nodup),
    MachinePreservesX (ServedReal mctx mref cctx cref declName shape m d)
      declName shape bsIn slotBs letBs m d :=
  @Tools.ShippingMachineTraceX.synthesizeCombinationalCore_machine_soundRA

end Pin15

section Pin16
open Tools.ShippingMachineTraceX
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST

-- Tools.ShippingMachineTraceX.machine_trace_lets_of_streamBRA (Tools/ShippingMachineTraceX.lean): split
example : ∀ {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig)
    (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (stream : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∃ σ : Nat → HList (tys d.ss), σ 0 = inits ∧
        (∀ t, σ (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) t (σ t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) t (σ t)).v
            (d.vpos j) w) d.nexts) ∧
        (∀ j, (src i bools bits).map (fun f => f j) =
          d.outs.map fun o => enc o.1 (eval
            (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) j (σ j)).b
              (d.bpos k))
            (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) j (σ j)).v
              (d.vpos k) w) o.2)) ∧
        ∀ (j q : Nat) (g : Nat → Nat) (l : Σ s : SType, Term s),
          (lsrc i bools bits)[q]? = some g → d.ls[q]? = some l →
          g j = enc l.1 (eval
            (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) j (σ j)).b
              (d.bpos k))
            (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) j (σ j)).v
              (d.vpos k) w) l.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref declName d.shape)
    (hsyn : Tools.ShippingChildInv.ChildBnd mref cref w),
    MachineTraceLBX (ServedReal mctx mref cctx cref declName d.shape m design)
      declName d m design dom src ext extB lsrc :=
  @Tools.ShippingMachineTraceX.machine_trace_lets_of_streamBRA

end Pin16

section Pin17
open Tools.ShippingMachineRan
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
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingCacheCoherentRun (Prov)

-- Tools.ShippingMachineRan.machineRan_of_closes (Tools/ShippingMachineRan.lean): moved
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} {shape : MachineShape}
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c shape)
    (hB : ChildBnd mref cref w)
    (closes : MachineClosesAt mctx mref cctx cref c shape),
    MachineRan mctx mref cctx cref c shape M D :=
  @Tools.ShippingMachineRan.machineRan_of_closes

end Pin17

section Pin18
open Tools.ShippingMachineRan
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
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingCacheCoherentRun (Prov)

-- Tools.ShippingMachineRan.core_kids_self_ran (Tools/ShippingMachineRan.lean): re-proved
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {M : Sparkle.IR.AST.Module} {D : Design}
    (ran : MachineRan mctx mref cctx cref c d.shape M D),
    ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 :=
  @Tools.ShippingMachineRan.core_kids_self_ran

end Pin18

section Pin19
open Tools.ShippingMachineRan
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
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingCacheCoherentRun (Prov)

-- Tools.ShippingMachineRan.core_kids_self_of_closes (Tools/ShippingMachineRan.lean): not edited
example : ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
{c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape),
    ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 :=
  @Tools.ShippingMachineRan.core_kids_self_of_closes

end Pin19

/-- The leading binders of each pinned theorem, as parsed from the OLD text:
name and kind (`e` explicit, `i` implicit, `c` instance). The first four of
the `variable`-bound theorems are the section variables, in their order. -/
def expected : List (Lean.Name × List (String × String)) := [
  (`Tools.ShippingChecksCore.core_kids_facts,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("outTy", "e"), ("hnomem", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingMemKid.core_kids_factsM,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("outTy", "e"), ("hfne", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingMemKid.core_raw_factsM,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("hsl", "e"), ("hfne", "e"), ("outTy", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingMemKid.core_hierGateM,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("hfne", "e"), ("outTy", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingMemKid.core_callPortsM,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("hfne", "e"), ("outTy", "e"), ("hkidP", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingClosedTyped.core_closed_typedIn,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("outTy", "e"), ("hnomem", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e"), ("hon", "e"), ("hoty", "e")]),
  (`Tools.ShippingChecksOuts.core_outsExtracted,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("hfne", "e"), ("outTy", "e"), ("hnomem", "e"), ("hkidP", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingChecksRun2.kidsDesign_real,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("namesK", "e"), ("hnomem", "e"), ("hkid", "e"), ("hself", "e"), ("w", "i"), ("w'", "i"), ("b", "i"), ("design", "i"), ("hw", "e"), ("hr", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingCoreClk.core_clk,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("outTy", "e"), ("hnomem", "e"), ("hsl", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingKidsSelf.core_kids_self,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("hnomem", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingHierGateAny.core_hierGate_any,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("outTy", "e"), ("hnomem", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingCallsChildPorts.core_calls_ports₁,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("hf", "e"), ("outTy", "e"), ("hnomem", "e"), ("hsl", "e"), ("kD", "e"), ("hkD", "e"), ("hIlen", "e"), ("hSL", "e"), ("hSlen", "e"), ("hLlen", "e"), ("hNIn", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingCallsPortsG.core_calls_portsG,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("hfne", "e"), ("outTy", "e"), ("hnomem", "e"), ("hsl", "e"), ("kD", "e"), ("hkD", "e"), ("hIlen", "e"), ("hSL", "e"), ("hSlen", "e"), ("hLlen", "e"), ("hNIn", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingLinkedFresh.core_linkedWF,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("outTy", "e"), ("hnomem", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingPortsMatchRaw.core_callConns,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("hfne", "e"), ("outTy", "e"), ("hnomem", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("b", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("hpost", "e"), ("entry", "e"), ("closes", "e")]),
  (`Tools.ShippingMachineTraceX.synthesizeCombinationalCore_machine_soundRA,
    [("declName", "i"), ("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("w", "i"), ("w'", "i"), ("m", "i"), ("d", "i"), ("shape", "i"), ("bsIn", "i"), ("slotBs", "i"), ("letBs", "i"), ("hr", "e"), ("entry", "e"), ("closes", "e"), ("hsyn", "e"), ("hbs", "e"), ("hlets", "e"), ("positive", "e"), ("slotKinds", "e"), ("letKinds", "e"), ("layW", "e"), ("outsOk", "e"), ("outsNodup", "e")]),
  (`Tools.ShippingMachineTraceX.machine_trace_lets_of_streamBRA,
    [("declName", "i"), ("d", "e"), ("ι", "i"), ("dom", "e"), ("inits", "e"), ("src", "e"), ("lsrc", "e"), ("ok", "e"), ("hbody", "e"), ("hinit", "e"), ("ext", "e"), ("extB", "e"), ("stream", "e"), ("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("w", "i"), ("w'", "i"), ("m", "i"), ("design", "i"), ("hr", "e"), ("entry", "e"), ("closes", "e"), ("hsyn", "e")]),
  (`Tools.ShippingMachineRan.machineRan_of_closes,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("shape", "i"), ("w", "i"), ("w1", "i"), ("M", "i"), ("D", "i"), ("hcore", "e"), ("entry", "e"), ("hB", "e"), ("closes", "e")]),
  (`Tools.ShippingMachineRan.core_kids_self_ran,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("hnomem", "e"), ("M", "i"), ("D", "i"), ("ran", "e")]),
  (`Tools.ShippingMachineRan.core_kids_self_of_closes,
    [("mctx", "i"), ("mref", "i"), ("cctx", "i"), ("cref", "i"), ("c", "i"), ("d", "e"), ("ok", "e"), ("hbody", "e"), ("nDecl", "i"), ("hC", "e"), ("hslots", "e"), ("hdomB", "e"), ("hins", "e"), ("hnomem", "e"), ("w", "i"), ("w1", "i"), ("M", "i"), ("D", "i"), ("hB", "e"), ("hcore", "e"), ("entry", "e"), ("closes", "e")])
]

/-- The `_ran` forms this round adds. -/
def ranForms : List Lean.Name := [
  `Tools.ShippingChecksCore.core_kids_facts_ran,
  `Tools.ShippingMemKid.core_kids_factsM_ran,
  `Tools.ShippingMemKid.core_raw_factsM_ran,
  `Tools.ShippingMemKid.core_hierGateM_ran,
  `Tools.ShippingMemKid.core_callPortsM_ran,
  `Tools.ShippingClosedTyped.core_closed_typedIn_ran,
  `Tools.ShippingChecksOuts.core_outsExtracted_ran,
  `Tools.ShippingCoreClk.core_clk_ran,
  `Tools.ShippingKidsSelf.core_kids_self_ran,
  `Tools.ShippingLinkedFresh.core_linkedWF_ran,
  `Tools.ShippingLinkedFresh.core_instOuts_not_assigned_ran,
  `Tools.ShippingPortsMatchRaw.core_callConns_ran,
  `Tools.ShippingMachineTraceX.synthesizeCombinationalCore_machine_soundRA_ran,
  `Tools.ShippingMachineTraceX.machine_trace_lets_of_streamBRA_ran,
  `Tools.ShippingChecksCoreGate.core_outsCheck_all_gate_ran,
  `Tools.ShippingChecksWidths.core_hierGate_ran,
  `Tools.ShippingChecksWidths.core_callPorts_ran,
  `Tools.ShippingChecksWidths.core_instOutWidthsOk_ran,
  `Tools.ShippingChecksRaw.core_raw_facts_ran,
  `Tools.ShippingChecksRunFacts.core_runFacts_ran,
  `Tools.ShippingPortsMatchRaw.core_portsMatch_raw_ran,
  `Tools.ShippingKidsSelf.core_kidsMaskedN_top_ran,
  `Tools.ShippingKidsSelf.core_kidsPass_deep_ran,
  `Tools.ShippingTextShipped.core_designCheck_run_ran,
  `Tools.ShippingKidFacts.kids_runFacts_ran,
  `Tools.ShippingKidFacts.kids_outsCheck_ran,
  `Tools.ShippingKidFacts.kids_maskedN_ran,
  `Tools.ShippingKidFacts.kids_designCheck_ran,
  `Tools.ShippingMachineCausal.machine_traceL_of_loop_causalRA_ran,
  `Tools.ShippingMachineCausal.machine_traceL_of_comb_callsRA_ran,
  `Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA_ran]

/-- The kind letter of a binder. -/
def kindOf (b : Lean.BinderInfo) : String :=
  match b with
  | Lean.BinderInfo.default => "e"
  | Lean.BinderInfo.implicit => "i"
  | Lean.BinderInfo.strictImplicit => "s"
  | Lean.BinderInfo.instImplicit => "c"

/-- Standard axioms only, an error otherwise. -/
def stdAxioms (n : Lean.Name) : Lean.Meta.MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let mut nOk : Nat := 0
  for (n, bs) in expected do
    let some ci := (← Lean.getEnv).find? n | throwError "{n}: missing"
    let got ← Lean.Meta.forallBoundedTelescope ci.type (some bs.length) fun xs _ => do
      let mut out : List (String × String) := []
      for x in xs do
        let d ← x.fvarId!.getDecl
        out := out ++ [(d.userName.toString, kindOf d.binderInfo)]
      pure out
    unless got.length == bs.length do
      throwError "{n}: {got.length} leading binders, the old statement has {bs.length}"
    -- an instance binder has no name in the old text: its kind only
    let same := (got.zip bs).all fun (g, b) => g.2 == b.2 && (b.2 == "c" || g.1 == b.1)
    unless same do
      throwError "{n}: binder names / kinds changed.\nnow: {toString got}\nold: {toString bs}"
    stdAxioms n
    nOk := nOk + 1
  for n in ranForms do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    stdAxioms n
    let ci ← Lean.getConstInfo n
    for c in [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingMachineEntry.MachineCloses] do
      if (ci.type.find? (·.isConstOf c)).isSome then
        throwError "{n}: its statement mentions {c}"
    unless (ci.type.find? (·.isConstOf ``Tools.ShippingMachineRan.MachineRan)).isSome do
      throwError "{n}: its statement does not mention MachineRan"
  Lean.logInfo m!"RAN SPLIT STATEMENTS: {nOk} pinned theorems have their old statement (type by the examples above, leading binder names and kinds by this check) and the standard axioms; {ranForms.length} _ran forms present, on the standard axioms, each stated with MachineRan and without MachineClosesAt / MachineCloses"

end Tests.Compiler.RanSplitStatementsTest
