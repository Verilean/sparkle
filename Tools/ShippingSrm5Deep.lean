import Tools.ShippingSrm5TransferM
import Tools.ShippingSrm4Kid
-- UNBUILT (unit SRM5)
-- SCOPE (binding): the per-CALLEE height fact `KidHeight O c rk f` (every `RealChildA O c y` has its OWN module `y.1` checked by `hcheck` at fuel `f`: the kid's module only, not its served design) and its derivation for a callee
-- with memory and/or ordinary calls: `deepChild_kidHeightAM` (the height analogue of `deepChild_kidFactsNC`, from `deepChild_ranAM` + `kids_hcheck_inAM`) and `memCallee_kidHeight` (the analogue of `memCallee_kidFactsNC`, over `MemCalleeData`).
-- PREMISES (named): the callee's rank `rk (ofDecl c) = some (h + 1)` (`hrb`), `hrkmem` (built memory modules are at height 0), the ranks of the ordinary kids `hrk` (at their `nameK k`, read off `hord`'s `ChildIfaceP.name`), `hKidH` (the height fact of each ordinary kid),
-- `hargs` (the decidable call-argument table, as the parent's `topshareM_ca`), and the old ones of `memCallee_kidFactsNC`.  `RealChildA` is a history of past synthesis results, not freshness or runtime fit.
-- No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.

namespace Tools.ShippingSrm5Deep
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildBndCore Tools.ShippingChildRunAKids
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineClosesData Tools.ShippingMachineCloses Tools.ShippingMachineAuto
open Tools.ShippingMemCloses Tools.ShippingCallsMemA
open Tools.ShippingSrm3Iface Tools.ShippingSrm3Callee Tools.ShippingSrm4Core6 Tools.ShippingSrm4Kid
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Tools.ShippingInstStmtG
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingMemKid (memOuts memIns)
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingSrm5Height

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The height fact of a callee**: every `RealChildA O c y` has its own module checked by `hcheck` at fuel `f`, against every module list resolving `y` and its served design as themselves. -/
def KidHeight (O : RefLawsAOps MkRefd mref cref) (c : Name) (rk : String → Option Nat) (f : Nat) : Prop :=
  ∀ y : Res, RealChildA O c y → ∀ ms : List Sparkle.IR.AST.Module,
    moduleByName ms y.1.name = some y.1 → (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
    hcheck (childMap ms) rk f y.1 = true

theorem post_name {M b : Sparkle.IR.AST.Module}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) :
    b.name = M.name := by
  rcases hpost with h | h
  · rw [h]; exact Tools.ShippingMachineDepthRun.dropZW_name M
  · rw [h]; exact (Tools.ShippingMachineDepthRun.mergeChecked_name _).trans (Tools.ShippingMachineDepthRun.dropZW_name M)

/-- **`KidHeight` of a non-leaf callee `c`** (general closing, a register, call entries memory and/or ordinary): from `KidFactsTNC` of its call entries' callees (`hlo`), the two call-width tables (`hcw`, `hargs`),
its rank (`hrb`), memory at height 0 (`hrkmem`) and the ordinary kids' ranks and height facts (`hrank`, `hkidH`). -/
theorem deepChild_kidHeightAM (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat)
    (hlo : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsTNC O (originAt d.shape k) (d.shape.insts[k]).1 (kidOuts k) (kidIns k))
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    (rk : String → Option Nat) (h f : Nat) (hrb : rk (Sparkle.IR.ModuleName.ofDecl c) = some (h + 1))
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hrank : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y' → ∃ r, rk y'.1.name = some r ∧ r ≤ h)
    (hkidH : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y' → ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y'.1.name = some y'.1 →
      (∀ g ∈ y'.2.modules, moduleByName ms g.name = some g) →
      hcheck (childMap ms) rk f y'.1 = true) :
    KidHeight O c rk (f + 1) := by
  intro y hy ms _hy1 hy2
  obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ :=
    Tools.ShippingSrm4Core5.deepChild_ranAM O T d ok hbody hC hslots hdomB hins hfne outTy hsep entry closes hy
  have hmsD : ∀ g ∈ D.modules, moduleByName ms g.name = some g := fun g hg => hy2 g (by rw [hdes]; exact hg)
  have hMn := (Tools.ShippingSrm3Iface.core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran).1
  have hrb' : rk y.1.name = some (h + 1) := by rw [post_name hpost, hMn]; exact hrb
  have hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, (∀ q ∈ inPortsOf y'.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst" := fun k hk y' hre => (hlo k hk).outsIn y' hre
  have hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y' → Tools.ShippingLeafTyped.PortsIn y'.1 :=
    fun k hk y' hre => (hlo k hk).portsIn y' hre
  have hkidW := Tools.ShippingSrm4Core6.hkidW_of_dataAM O hcw (fun k hk y' hre => (hlo k hk).outTys y' hre)
  exact Tools.ShippingSrm5TransferM.kids_hcheck_inAM O d ok hbody hC hslots hdomB hins hsl hfne outTy hkidP hkidW hkidT
    hargs (fun k hk y' hre => (hlo k hk).inW y' hre) (fun k hk y' hre => (hlo k hk).clk y' hre) hpost ran hon hoty ms hmsD
    rk h f hrb' hrkmem hrank hkidH

/-- **`KidHeight` of a callee with memory and/or ordinary calls** (over `MemCalleeData`): the height analogue of `memCallee_kidFactsNC`.  The ordinary kids' ranks are read off `hord`'s `ChildIfaceP.name`
(`hrk`: the rank table at `nameK k`). -/
theorem memCallee_kidHeight (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {d : MachineData} {C : Name} {n : Nat} {nameK : Nat → String} {nk : Nat → Nat}
    {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData d C n nameK nk outsK namesK names)
    (hord : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y → ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat)
    (hmemT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (cb : Bool) (aw dw : Nat),
      (originAt d.shape k).child? = some (memModule cb aw dw) → kidOuts k = memOuts dw ∧ kidIns k = memIns aw dw)
    (hKid : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none →
      KidFactsNC O (d.shape.insts[k]).1 (kidOuts k) (kidIns k))
    (hcw : Tools.ShippingCallWidths.callWidthsOk d n kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d n kidIns = true)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (entry : MachineDefines mctx mref cctx cref C d.shape)
    (rk : String → Option Nat) (h f : Nat) (hrb : rk (Sparkle.IR.ModuleName.ofDecl C) = some (h + 1))
    (hrkmem : ∀ (cb : Bool) (aw dw : Nat), rk (memModule cb aw dw).1.name = some 0)
    (hrk : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none →
      ∃ r, rk (nameK k) = some r ∧ r ≤ h)
    (hKidH : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none →
      KidHeight O (d.shape.insts[k]).1 rk f) :
    KidHeight O C rk (f + 1) :=
  deepChild_kidHeightAM O T d hC.ok hC.body (nDecl := n) hC.callsOk hC.slots hC.domB hC.insts_ne hC.slotsNe hC.fne hC.outTy
    kidOuts kidIns
    (fun k hk => by
      cases hcc : (originAt d.shape k).child? with
      | some md =>
        obtain ⟨cb, aw, dw, -, hmd⟩ := origin_mem_of_child hcc
        subst hmd
        obtain ⟨e1, e2⟩ := hmemT k hk cb aw dw hcc
        rw [e1, e2]
        exact memKidTNC_facts hcc
      | none => exact (hKid k hk hcc).toT hcc)
    hcw hargs hon hoty (memCallee_hsep O hC hord) entry
    (fun m c hA => memCallee_closesA O T hA hC (hord m c hA))
    rk h f hrb hrkmem
    (fun k hk y' hnone hre => by
      obtain ⟨m', c', hA'⟩ := adm_of_realChildA hre
      have hI := hord m' c' hA' k hk y' hnone hre
      obtain ⟨r, hr1, hr2⟩ := hrk k hk hnone
      exact ⟨r, by rw [hI.name]; exact hr1, hr2⟩)
    (fun k hk y' hnone hre ms hy1 hy2 => hKidH k hk hnone y' hre ms hy1 hy2)

end Tools.ShippingSrm5Deep

#print axioms Tools.ShippingSrm5Deep.deepChild_kidHeightAM
#print axioms Tools.ShippingSrm5Deep.memCallee_kidHeight
