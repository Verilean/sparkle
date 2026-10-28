import Tests.Compiler.QClosesTest
import Tools.ShippingC4InitW
import Tools.ShippingSrm33Core
set_option Elab.async false
set_option autoImplicit false
-- C5 ASSEMBLY (issue sparkle-gen-c5-assembly), STAGED, as Tests/Compiler/C4ShipsTest.lean for C4. The frozen C5 statement
-- (scripts/c5/C5_STATEMENT.lean.txt) for QSharedLeafParent, assembled from Tools.ShippingSrm33.machine_ships_hierC_noHstR with
-- soundL <- QCloses.soundLA_of_class; facts / Bd <- kidsNC_runFacts / kidsNC_maskedN + QCloses.q_hkid + QCloses.ranA_of_class;
-- hinitW <- hinitW_of_ok; Bnd <- QBnd P (contract binders). STAGED: `composed` is the ONE named hypothesis HComposedQ P until
-- Q-COMPOSED (and Q-HCALLS) land. NOT the final C5.
namespace Tests.Compiler.QShips
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.OptCheck Sparkle.IR.HierCheck Sparkle.IR.Semantics
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineAuto Tools.ShippingMachineDepth
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun
open Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMixedSourceBridge
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Tests.Compiler.CDef Tests.Compiler.QDef

/-- the run boundary of the class: the contract binders of the C5 (= C4) statement, at the run's contexts -/
def QBnd (P : QSharedLeafParent) : CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape ∧
    (∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape) ∧
    JQC O 0 w

/-- STAGED named hypothesis: exactly the `composed` binder of machine_ships_hierC_noHstR at n := 2, Bnd := QBnd P, C := True
(the G-COMPOSED target; to be supplied by composedNWRegs_of_class) -/
def HComposedQ (P : QSharedLeafParent) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {b : Sparkle.IR.AST.Module},
    RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (m, design) w' →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule m ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule m)) →
    MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape →
    True →
    QBnd P mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
    Tools.ShippingSrm28.ComposedNWRegs 2 P.top.decl P.top.d P.nDecl m design (fun _ : Unit => defaultDomain)
      P.top.src P.top.extS P.top.extBS
      (fun regs => ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        P.top.d.shape.layout.slots[k]? = some f → f.width ≤ declWidth b r)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **G-MASK** (generic): kidsMaskedN of the run's design -/
theorem kidsMasked_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    {w w1 : Void IO.RealWorld} {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    kidsMaskedN D.modules b.body = true :=
  Tools.ShippingSrm4Parent.kidsNC_maskedN O P.top.d P.pdata.ok P.pdata.body (nDecl := P.nDecl) P.pdata.callsOk
    P.pdata.slots P.pdata.domB P.pdata.insts_ne P.pdata.fne P.outTy P.noMem P.outsOf P.insOf
    (Tests.Compiler.QCloses.q_hkid P O T entryL entryW) hpost
    (Tests.Compiler.QCloses.ranA_of_class P O T hA entryL entryW entry hcore hw)

/-- **RunFacts** (generic) -/
theorem runFacts_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    {w w1 : Void IO.RealWorld} {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  Tools.ShippingSrm4Parent.kidsNC_runFacts O P.top.d P.pdata.ok P.pdata.body (nDecl := P.nDecl) P.pdata.callsOk
    P.pdata.slots P.pdata.domB P.pdata.insts_ne P.slotsNe P.pdata.fne P.outTy P.noMem P.outsOf P.insOf
    (Tests.Compiler.QCloses.q_hkid P O T entryL entryW) P.cw hpost
    (Tests.Compiler.QCloses.ranA_of_class P O T hA entryL entryW entry hcore hw)

/-- **C5 (STAGED on `HComposedQ P`)**: the frozen C5 statement with the one staged hypothesis `hcomp`. -/
theorem qSharedLeaf_ships_of_composed (P : QSharedLeafParent) (hcomp : HComposedQ P)
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (T : Tools.ShippingChildInvA.RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    (hw : JQC O 0 w)
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = P.top.d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = P.top.d.ss.length ∧
      ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
        (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
        (T' : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
        (kids : String → KT 2),
        (∀ t st, t < T' → SourceInputs P.top.decl (P.top.d.bsIn.take P.nDecl) ids cache
          (fun j => (P.top.extBS i bools bits j).val (T' - 1 - t))
          (fun j n => (P.top.extS i bools bits j n).val (T' - 1 - t)) (seedIn b ins t st)) →
        (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
        (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          P.top.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        ResetNk 2 raw D kids →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
        (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
          st0 x < 2 ^ declWidth b x) →
        ∃ envsO, runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b))
            (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T'
            ⟨st0, mems, kids⟩ = some envsO ∧
          envsO.length = T' ∧
          ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            P.top.d.shape.layout.outs[k]? = some o → (P.top.src i bools bits)[k]? = some f →
            (envsO[j]'hj) o.name = f j :=
  Tools.ShippingSrm33.machine_ships_hierC_noHstR (n := 2) (fun D => KSn_local (childMap D.modules) 2)
    (QBnd P) (fun _ _ _ _ => True) (fun (b : Sparkle.IR.AST.Module) (D : Design) => kidsMaskedN D.modules b.body = true)
    (fun _ _ => True)
    (fun b D hok => KSn_boundedIn D.modules b.body hok 2)
    (true_inv _) P.top.d (kD := P.nDecl)
    (lsrc := P.top.lsrc) (srcL := P.top.src) (extL := P.top.extS) (extBL := P.top.extBS)
    (fun hrun hentry _ hB => by
      obtain ⟨O', T'', hA', entryL', entryW', hw'⟩ := hB
      exact Tests.Compiler.QCloses.soundLA_of_class P O' T'' hA' entryL' entryW' hentry hw' hrun)
    (fun hrun hpost' hentry hc hB hmf => hcomp hrun hpost' hentry hc hB hmf)
    P.outTy (Tools.ShippingC4InitW.hinitW_of_ok P.top.d P.pdata.ok) hcore hpost entry trivial
    (fun hB => by
      obtain ⟨O', T'', hA', entryL', entryW', hw'⟩ := hB
      exact runFacts_of_class P O' T'' hA' entryL' entryW' entry hcore hpost hw')
    ⟨O, T, hA, entryL, entryW, hw⟩
    (kidsMasked_of_class P O T hA entryL entryW entry hcore hpost hw)

#print axioms kidsMasked_of_class
#print axioms runFacts_of_class
#print axioms qSharedLeaf_ships_of_composed

end Tests.Compiler.QShips
