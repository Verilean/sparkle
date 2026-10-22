import Tools.ShippingSrm4Core6
import Tools.ShippingSrm3Callee
-- UNBUILT (unit SRM4): see REPORT-SRM4.md for the run names and exits.
-- SCOPE (binding, residue R2): `KidFactsNC` (all fields of `KidFactsA` but `check`, see `Tools/ShippingSrm4Check.lean` for why) of a `RealChildA O C y` of a callee `C` whose call entries are MEMORY entries (the origin builds the
-- memory module) and/or ordinary callees, A-form: `deepChild_kidFactsNC` of `Tools/ShippingSrm4Core6.lean` (the `hnomem`-free copies of the `core_*_ranA` chain, scripted by `.cluster/logs/port_srm4.py`) applied to a
-- `MemCalleeData`; `hsep` DERIVED from the interfaces (`hord`) and the table facts; `closes` DERIVED by `memCallee_closesA`.
-- PREMISES (named): `MemCalleeData` (decidable data), `hord` (the `ChildIfaceP` of the ordinary kids' results: `leafKid_ifaceP` for a plain leaf, `memCallee_ifaceP` for a kid that itself has a memory child), `hKid` (`KidFactsNC` of
-- each ordinary kid: for a plain leaf `leaf_kidFactsA` minus `check`, for a callee over a memory leaf this theorem), `hmemT` (the kid tables at a memory entry), `hcw` / `hon` / `hoty` (decidable), `entry`, `O`, `T`.
-- NOT proved: the `check` field (OPEN; the obstruction is `Tools.ShippingSrm4Check.kidFactsA_check_false`), anything about the parent's designCheck.
-- `RealChildA` is a history of past synthesis results, not freshness or semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no new law / field, no heartbeat option.

namespace Tools.ShippingSrm4Kid
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildBndCore Tools.ShippingChildRunAKids
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineClosesData Tools.ShippingMachineCloses Tools.ShippingMachineAuto
open Tools.ShippingMemCloses Tools.ShippingCallsMemA
open Tools.ShippingSrm3Iface Tools.ShippingSrm3Callee Tools.ShippingSrm4Core6
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingMemKid (memOuts memIns)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`hsep` of a callee with memory and/or ordinary calls**: no module of a kid's result (or design) is named like the callee. -/
theorem memCallee_hsep (O : RefLawsAOps MkRefd mref cref) {d : MachineData} {C : Name} {n : Nat} {nameK : Nat → String} {nk : Nat → Nat}
    {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData d C n nameK nk outsK namesK names)
    (hord : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y → ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl C) := by
  intro k hk y' hy' g hg
  cases hcc : (originAt d.shape k).child? with
  | some md =>
    obtain ⟨cb, aw, dw, -, hmd⟩ := origin_mem_of_child hcc
    have hye : y' = md := KidTA.mem' hy' hcc
    obtain ⟨e1, -, -, -⟩ := memT_of hC hk hcc
    have hgname : g.name = nameK k := by
      rcases List.mem_cons.mp hg with h | h
      · rw [h, hye, e1]
      · rw [hye, hmd] at h
        rw [Tools.ShippingMemKid.mem_design h, e1, hmd]
    rw [hgname]
    exact hC.parent k hk
  | none =>
    have hre : RealChildA O (d.shape.insts[k]).1 y' := KidTA.real' hy' hcc
    obtain ⟨m', c', hA'⟩ := adm_of_realChildA hre
    exact sep_of_iface (hord m' c' hA' k hk y' hcc hre) (hC.parent k hk) (hC.parentD k hk) g hg

/-- **`KidFactsNC` of a `RealChildA O C y` of a callee with memory and/or ordinary calls.** -/
theorem memCallee_kidFactsNC (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (entry : MachineDefines mctx mref cctx cref C d.shape) :
    KidFactsNC O C d.shape.layout.outs (argWidths d n) :=
  deepChild_kidFactsNC O T d hC.ok hC.body (nDecl := n) hC.callsOk hC.slots hC.domB hC.insts_ne hC.slotsNe hC.fne hC.outTy
    n hC.hkD hC.hIlen hC.hSL hC.hSlen hC.hLlen hC.hNIn kidOuts kidIns
    (fun k hk => by
      cases hcc : (originAt d.shape k).child? with
      | some md =>
        obtain ⟨cb, aw, dw, -, hmd⟩ := origin_mem_of_child hcc
        subst hmd
        obtain ⟨e1, e2⟩ := hmemT k hk cb aw dw hcc
        rw [e1, e2]
        exact memKidTNC_facts hcc
      | none => exact (hKid k hk hcc).toT hcc)
    hcw hon hoty (memCallee_hsep O hC hord) entry
    (fun m c hA => memCallee_closesA O T hA hC (hord m c hA))

/-- the built memory module determines its parameters -/
theorem memModule_inj {cb cb' : Bool} {aw aw' dw dw' : Nat} (h : memModule cb aw dw = memModule cb' aw' dw') :
    cb = cb' ∧ aw = aw' ∧ dw = dw' := by
  have hn0 : (memModule cb aw dw).1.name = (memModule cb' aw' dw').1.name :=
    congrArg (fun (m : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) => m.1.name) h
  exact Tools.ShippingModuleName.ofMem_injective hn0

/-- `KidFactsA` gives `KidFactsNC` (the `check` field is dropped) -/
theorem KidFactsA.toNC {O : RefLawsAOps MkRefd mref cref} {c : Name} {outs : List OutField} {ins : List Nat} {n : Nat}
    (h : Tools.ShippingSeqChildDeepKidFactsA.KidFactsA O c outs ins n) : KidFactsNC O c outs ins :=
  { outsIn := h.outsIn, outTys := h.outTys, kidA := h.kidA, kidR := h.kidR, masked := h.masked, portsIn := h.portsIn,
    inW := h.inW, clk := h.clk }

end Tools.ShippingSrm4Kid

#print axioms Tools.ShippingSrm4Kid.memCallee_kidFactsNC
#print axioms Tools.ShippingSrm4Kid.memCallee_hsep
#print axioms Tools.ShippingSrm4Core6.deepChild_kidFactsNC
