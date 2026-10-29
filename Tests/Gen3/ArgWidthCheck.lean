import Tools.ShippingGen3ArgWidth
import Tests.Gen3.ExpectedType
import Tests.Compiler.ShippingMachineLinkedTest
set_option autoImplicit false
-- NOT BUILT (written without running Lean; the integrator builds it on the cluster).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # U-ARGW-PARENT checks (scripts/gen3/UARGW_PARENT_SURVEY.md §5)

1. **Expected types.** `core_inputWidth_A`, `argWidth_of_mapM`, `core_callArgPorts_oneA`, `core_callArgPorts_ranA`
   compared MECHANICALLY (`Tests.Gen3.ExpectedType.checkExpected`) against independent `Expected…` statements (survey §2
   text; `argWidth_of_mapM` is the shared lemma of the approved wording sync). MUTANTS (post-processing premise dropped,
   width read in the raw module `M`, transition index without `machNIn`, binder index without the call block `kI`)
   must FAIL.
2. **P1** (conditional application): `core_callArgPorts_oneA` instantiated with the package-level premises an existing
   consumer holds (`p.ok`, `p.body_eq`; the rest universally quantified). No run is exhibited.
3. **P2** (data only, not L6): `callerL`'s argument lets of call 0 have binder widths `[16, 2]` at the `callArgsOkAt`
   index `1 + (1 + (1 + a))`, and `pickByteH`'s package port widths are `[16, 2]`.
4. **N1** why `huniq` (o18) is needed: `declWidth` reads the FIRST wire of a name (`List.find?`), so a module declaring
   `x` twice (8 then 16 bits) has `declWidth … "x" = 8 ≠ 16`.
5. Axioms: `checkAxioms` (standard only) and `#print axioms`. -/

namespace Tests.Gen3.ArgWidthCheck
open Tools.ShippingGen3ArgWidth
open Tests.Gen3.ExpectedType

section Expected
-- the opens of Tools/ShippingGen3ArgWidth.lean (= OneOutTop:26-45)
open Lean hiding Module
open Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIfaceA Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingCallWidthsChildRealA Tools.ShippingChildBndCore
open Tools.ShippingChecksCore Tools.ShippingLinkedFresh Tools.ShippingClosedTyped Tools.ShippingParentRanA
open Tools.ShippingParentTailsA Tools.ShippingParentDesignA
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingChecksWidths Tools.ShippingChecksOuts Tools.ShippingChecksRaw Tools.ShippingChecksRun

def ExpectedCore : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)),
    ∀ (e : Nat) (w : String),
      ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape + e]? = some w →
      ∃ bn, d.shape.binders[nDecl + e]? = some bn ∧
        Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth

def ExpectedMapM : Prop :=
  ∀ {names : List String} {nIn kI n nDecl : Nat}
    {binders : List (Name × MixedGateBinder)} {b : Sparkle.IR.AST.Module}
    (hW : ∀ (e : Nat) (w : String), names[nIn + e]? = some w →
      ∃ bn, binders[nDecl + e]? = some bn ∧ Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth)
    {args : List Nat} {argWs : List String}
    (hm : args.mapM (fun j => names[nIn + kI + n + j]?) = some argWs),
    ∀ (j a : Nat) (w : String), args[j]? = some a → argWs[j]? = some w →
      ∃ bn, binders[nDecl + (kI + (n + a))]? = some bn ∧
        Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth

def ExpectedOneA : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)),
    ∀ (k : Nat) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
      Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        ((machPorts c ids cache d.shape.binders).map (·.name)) k args mc st →
      ∀ (argWs : List String),
        args.mapM (fun j => ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape +
          d.shape.insts.length + d.shape.layout.slots.length + j]?) = some argWs →
        ∀ (j a : Nat) (w : String), args[j]? = some a → argWs[j]? = some w →
          ∃ bn, d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some bn ∧
            Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth

def ExpectedRanA : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)),
    ∀ (args : List Nat) (outs : List (Nat × String)) (mc : Sparkle.IR.AST.Module) (st : Stmt),
      Tools.ShippingMachineInstG.CallStmtG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        ((machPorts c ids cache d.shape.binders).map (·.name)) args outs mc st →
      ∀ (argWs : List String),
        args.mapM (fun j => ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape +
          d.shape.insts.length + d.shape.layout.slots.length + j]?) = some argWs →
        ∀ (j a : Nat) (w : String), args[j]? = some a → argWs[j]? = some w →
          ∃ bn, d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some bn ∧
            Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth

/-! ### Mutants (each must be REJECTED) -/

/-- The core without the post-processing premise `hpost` (then `b` is unrelated to the run). -/
def MutCoreNoPost : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)),
    ∀ (e : Nat) (w : String),
      ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape + e]? = some w →
      ∃ bn, d.shape.binders[nDecl + e]? = some bn ∧
        Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth

/-- The core reading the width in the RAW module `M` (not the shipped `b`). -/
def MutCoreRaw : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)),
    ∀ (e : Nat) (w : String),
      ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape + e]? = some w →
      ∃ bn, d.shape.binders[nDecl + e]? = some bn ∧
        Sparkle.IR.RegDedup.declWidth M w = (kindTy bn.2).bitWidth

/-- The core at the raw port index `e` (the declaration's ports not skipped). -/
def MutCoreIdx : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)),
    ∀ (e : Nat) (w : String),
      ((machPorts c ids cache d.shape.binders).map (·.name))[e]? = some w →
      ∃ bn, d.shape.binders[nDecl + e]? = some bn ∧
        Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth

/-- The one-output corollary at a binder index WITHOUT the call block `kI`. -/
def MutOneIdx : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)),
    ∀ (k : Nat) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
      Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        ((machPorts c ids cache d.shape.binders).map (·.name)) k args mc st →
      ∀ (argWs : List String),
        args.mapM (fun j => ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape +
          d.shape.insts.length + d.shape.layout.slots.length + j]?) = some argWs →
        ∀ (j a : Nat) (w : String), args[j]? = some a → argWs[j]? = some w →
          ∃ bn, d.shape.binders[nDecl + (d.shape.layout.slots.length + a)]? = some bn ∧
            Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth

/-- The group corollary reading the width in the RAW module `M`. -/
def MutRanRaw : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)),
    ∀ (args : List Nat) (outs : List (Nat × String)) (mc : Sparkle.IR.AST.Module) (st : Stmt),
      Tools.ShippingMachineInstG.CallStmtG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        ((machPorts c ids cache d.shape.binders).map (·.name)) args outs mc st →
      ∀ (argWs : List String),
        args.mapM (fun j => ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape +
          d.shape.insts.length + d.shape.layout.slots.length + j]?) = some argWs →
        ∀ (j a : Nat) (w : String), args[j]? = some a → argWs[j]? = some w →
          ∃ bn, d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some bn ∧
            Sparkle.IR.RegDedup.declWidth M w = (kindTy bn.2).bitWidth

/-- **P1** the one-output corollary accepts the package-level premises (`Pkg.ok`, `Pkg.body_eq`) of an existing
consumer (`oneOut_topShips`); every run premise stays universally quantified. -/
example {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} (p : Tools.ShippingGen2.Pkg ι dom)
    (hC : p.d.callsOk p.kD = true) (hslots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ p.d.shape.binders.drop p.kD, b.2 ≠ .domain)
    (hins : p.d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx p.decl p.d.shape M D)
    {ids : List FVarId} (hlen : ids.length = p.d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)) :=
  core_callArgPorts_oneA O p.d p.ok p.body_eq hC hslots hdomB hins hpost ran hlen cache

end Expected

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``core_inputWidth_A ``ExpectedCore
  checkExpected ``argWidth_of_mapM ``ExpectedMapM
  checkExpected ``core_callArgPorts_oneA ``ExpectedOneA
  checkExpected ``core_callArgPorts_ranA ``ExpectedRanA
  checkMutant ``core_inputWidth_A ``MutCoreNoPost
  checkMutant ``core_inputWidth_A ``MutCoreRaw
  checkMutant ``core_inputWidth_A ``MutCoreIdx
  checkMutant ``core_callArgPorts_oneA ``MutOneIdx
  checkMutant ``core_callArgPorts_ranA ``MutRanRaw

/-! ## P2: `callerL` data (data only; not L6) -/

open Sparkle.Tests.Compiler.ShippingMachineLinkedTest

set_option maxRecDepth 100000

theorem callerL_hk : 0 < callerL.machineData.shape.insts.length := by
  first | decide | decide +kernel

/-- The binder widths at the `callArgsOkAt` index `nDecl + (kI + (n + a))` = `1 + (1 + (1 + a))` of call 0's
argument lets. -/
theorem callerL_argWidths :
    (callerL.machineData.shape.insts[0]'callerL_hk).2.1.map (fun a =>
      (callerL.machineData.shape.binders[1 + (1 + (1 + a))]?).map
        (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)) = [some 16, some 2] := by
  first | decide | decide +kernel

abbrev U := fun _ : Unit => Sparkle.Core.Domain.defaultDomain

/-- `pickByteH`'s comb package (as Tests/Gen2/DataBridgeCheck.lean:37-43; copied, not imported). -/
noncomputable def pbhC : Tools.ShippingGen2.CombPkg Unit U :=
  { decl := ``pickByteH, d := pickByteH.machineData, kD := pickByteH.machineData.bsIn.length,
    inits := pickByteH.machineInits, src := pickByteH.machineSource,
    facts := ⟨pickByteH.machine_ok, pickByteH.machine_body, pickByteH.machine_inits, pickByteH.machine_next,
      pickByteH.machine_result⟩ }

noncomputable abbrev pbhPkg : Tools.ShippingGen2.Pkg Unit U := .comb pbhC

/-- `pickByteH`'s package port widths (= `Pkg.portWidths`, Adapt:80, by definition). -/
theorem pbh_portWidths :
    pbhPkg.ports.map (fun b => (Tools.ShippingMachineEntry.kindTy b.2).bitWidth) = [16, 2] := by
  first | decide | decide +kernel

/-! ## N1: `declWidth` reads the first wire of a name -/

def dupM : Sparkle.IR.AST.Module :=
  { name := "dup", inputs := [], outputs := [],
    wires := [{ name := "x", ty := .bitVector 8 }, { name := "x", ty := .bitVector 16 }], body := [] }

theorem dupM_width : Sparkle.IR.RegDedup.declWidth dupM "x" = 8 := by
  first | rfl | decide

theorem dupM_not16 : Sparkle.IR.RegDedup.declWidth dupM "x" ≠ 16 := by
  rw [dupM_width]; decide

/-! ## Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``core_inputWidth_A, ``argWidth_of_mapM, ``core_callArgPorts_oneA, ``core_callArgPorts_ranA,
      ``callerL_hk, ``callerL_argWidths, ``pbh_portWidths, ``dupM_width, ``dupM_not16] do
    checkAxioms n

#print axioms core_inputWidth_A
#print axioms argWidth_of_mapM
#print axioms core_callArgPorts_oneA
#print axioms core_callArgPorts_ranA
#print axioms callerL_argWidths
#print axioms pbh_portWidths
#print axioms dupM_not16

end Tests.Gen3.ArgWidthCheck
