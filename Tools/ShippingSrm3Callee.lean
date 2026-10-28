import Tools.ShippingSrm3Iface
import Tools.ShippingQuadLeafGeneric
-- BUILT (unit SRM3): b8 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM3.md.
-- SCOPE (binding): a callee `d` (named `C`) with calls whose entries are MEMORY entries (the origin builds the module: `InstOrigin.child? = some md`) and/or ORDINARY calls (`RealChildA` of a callee), on the A-form
-- side (`RealChildA`, `MachineRanA`, `MachineClosesAtA`; nothing of the old-form `RealChild` / `MachineRan` / `MachineClosesAt`).
-- PROVED here: `memCallee_closesA` (`MachineClosesAtA` of such a callee: `machineClosesAtA_of_memKids'` with the memory half of its `hkid` DERIVED by `memIface`; the ordinary half is the premise `hord`),
-- `memCallee_ifaceP` (`ChildIfaceP` of a `RealChildA O C y` of such a callee: `deepChild_ifaceP_M`, with `hgk` / `hsep` DERIVED from `hord` and the table facts), `leafKid_ifaceP` (`ChildIfaceP` of a plain leaf's
-- `RealChildA`, the ordinary kid of `wrapQ`).
-- PREMISES (named): `MemCalleeData` (decidable data of the stored `machineData` and of the per-kid tables), `hord` (the interface of the ordinary kids' results: for a plain leaf `leafKid_ifaceP`, for a kid that itself has a memory
-- child `memCallee_ifaceP` of that kid), `entry` (`MachineDefines`), `O`, `T`.  `RealChildA` is a history of past synthesis results, not freshness, not runtime fit.  The examples do not make the class complete.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

namespace Tools.ShippingSrm3Callee
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildBndCore Tools.ShippingChildRunAKids
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMemCloses Tools.ShippingCallsMemA Tools.ShippingCallsMemPinned
open Tools.ShippingSrm3Iface
open Tools.ShippingQuadLeafGeneric (LeafData leafNk)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Tools.ShippingMachineAuto Tools.ShippingMixedEntrySoundness

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The decidable data of a callee `d` (named `C`, `n` declared inputs) with memory and/or ordinary calls: the data facts of `LeafCalleeData`, and the per-kid tables (`nameK` the module name of kid `k`'s result,
`nk` its argument count, `outsK` its output names, `namesK` the names of its design's modules) with the facts the closing and the interface ask of them.  `names` are the module names of the callee's own design. -/
structure MemCalleeData (d : MachineData) (C : Name) (n : Nat) (nameK : Nat → String) (nk : Nat → Nat)
    (outsK namesK : Nat → List String) (names : List String) : Prop where
  ok : d.ok = true
  body : d.shape.body = quote d.dom
    (fun j => inputExpr d.shape.binders.length (d.bpos j))
    (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  alias : d.letsAliasOk = true
  callsOk : d.callsOk n = true
  slots : d.ss.length = d.shape.layout.slots.length
  domB : ∀ b ∈ d.shape.binders.drop n, b.2 ≠ .domain
  insts_ne : d.shape.insts ≠ []
  fne : d.shape.instFields ≠ []
  outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width
  slotsNe : d.shape.layout.slots ≠ []
  hkD : n ≤ d.bsIn.length
  hIlen : (d.bsIn.drop n).length = d.shape.insts.length
  hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain
  hSlen : d.slotBs.length = d.shape.layout.slots.length
  hLlen : d.letBs.length = d.shape.layout.lets
  hNIn : machNIn d.shape = ((d.bsIn.take n).filter (fun b => b.2 != .domain)).length
  argsN : ∀ (k : Nat) (hk : k < d.shape.insts.length), nk k = (d.shape.insts[k]).2.1.length
  fieldOut : ∀ (k : Nat), k < d.shape.insts.length → d.shape.instFields.getD k "" ∈ outsK k
  fieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat) (hk' : k' < d.shape.insts.length),
    (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
    memKey (originAt d.shape k) = memKey (originAt d.shape k') →
    (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
    d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k'
  sepK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat) (hk' : k' < d.shape.insts.length),
    nameK k = nameK k' → (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
      memKey (originAt d.shape k) = memKey (originAt d.shape k')
  parent : ∀ k, k < d.shape.insts.length → nameK k ≠ Sparkle.IR.ModuleName.ofDecl C
  outHead : ∀ o ∈ d.shape.layout.outs, o.name.toList.head? ≠ some 'i'
  parentD : ∀ k, k < d.shape.insts.length → Sparkle.IR.ModuleName.ofDecl C ∉ namesK k
  disjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat) (hk' : k' < d.shape.insts.length),
    ¬ ((d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧ memKey (originAt d.shape k) = memKey (originAt d.shape k')) →
    nameK k ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k'
  /-- a memory entry's tables are those of the built memory module -/
  memT : ∀ (k : Nat), k < d.shape.insts.length → (originAt d.shape k).child?.all
    (fun y => decide (nameK k = y.1.name ∧ nk k = 4 ∧ outsK k = ["out"] ∧ namesK k = [y.1.name])) = true
  /-- an ordinary entry's result module and design modules are named in `names` -/
  nameIn : ∀ (k : Nat), k < d.shape.insts.length → (originAt d.shape k).child? = none →
    nameK k ∈ names ∧ ∀ x ∈ namesK k, x ∈ names
  /-- the name of the module a memory entry builds is in `names` and is not the callee's own -/
  memNames : ∀ (k : Nat), k < d.shape.insts.length → (originAt d.shape k).child?.all
    (fun y => decide (y.1.name ∈ names) && decide (y.1.name ≠ Sparkle.IR.ModuleName.ofDecl C)) = true

/-- the tables of the built memory module at a memory entry -/
theorem memT_of {d : MachineData} {C : Name} {n : Nat} {nameK : Nat → String} {nk : Nat → Nat}
    {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData d C n nameK nk outsK namesK names) {k : Nat} (hk : k < d.shape.insts.length) {y : Res}
    (hc : (originAt d.shape k).child? = some y) :
    nameK k = y.1.name ∧ nk k = 4 ∧ outsK k = ["out"] ∧ namesK k = [y.1.name] := by
  have h := hC.memT k hk
  rw [hc] at h
  simpa only [Option.all_some, decide_eq_true_eq] using h

/-- **`MachineClosesAtA` of a callee with memory and/or ordinary calls**: `machineClosesAtA_of_memKids'`; the interface of a MEMORY kid is DERIVED (`memIface`), that of an ORDINARY kid is `hord`. -/
theorem memCallee_closesA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {d : MachineData} {C : Name} {n : Nat} {nameK : Nat → String} {nk : Nat → Nat}
    {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData d C n nameK nk outsK namesK names)
    (hord : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y → ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx C d.shape := by
  intro tenv
  exact machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := n) O T hA d hC.ok hC.body hC.alias hC.callsOk hC.slots hC.domB
    hC.fne nameK nk outsK namesK
    (fun k hk y hy => by
      rcases hy with hc | ⟨hc, hre⟩
      · obtain ⟨cb, aw, dw, -, hyy⟩ := origin_mem_of_child hc
        obtain ⟨e1, e2, e3, e4⟩ := memT_of hC hk hc
        subst hyy
        rw [e1, e2, e3, e4]
        exact Tools.ShippingMemCloses.memIface cb aw dw
      · exact hord k hk y hc hre)
    hC.argsN hC.fieldOut hC.fieldsNd hC.sepK hC.parent
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head (hC.outHead o ho) gi _)
    hC.parentD hC.disjD

/-- a `RealChildA` was produced in an admissible context -/
theorem adm_of_realChildA {O : RefLawsAOps MkRefd mref cref} {c : Name} {y : Res} (h : RealChildA O c y) :
    ∃ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr => exact ⟨mctx', cctx', adm⟩

/-- the interface of a kid gives `hgk`'s clause -/
theorem gk_of_iface {nm : String} {nArgs : Nat} {outs nms names : List String} {y : Res}
    (h : ChildIfaceP nm nArgs outs nms y.1 y.2) (hnm : nm ∈ names) (hsub : ∀ x ∈ nms, x ∈ names) :
    ∀ g ∈ y.1 :: y.2.modules, g.name ∈ names ∧ ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ names := by
  intro g hg
  refine ⟨?_, fun mn i conns hm => hsub _ (h.closed g hg mn i conns hm)⟩
  rcases List.mem_cons.mp hg with e | e
  · rw [e, h.name]; exact hnm
  · exact hsub _ (h.desNames g e)

/-- the interface of a kid gives `hsep`'s clause -/
theorem sep_of_iface {nm : String} {nArgs : Nat} {outs nms : List String} {y : Res} {own : String}
    (h : ChildIfaceP nm nArgs outs nms y.1 y.2) (hnm : nm ≠ own) (hown : own ∉ nms) :
    ∀ g ∈ y.1 :: y.2.modules, g.name ≠ own := by
  intro g hg e
  rcases List.mem_cons.mp hg with e' | e'
  · rw [e', h.name] at e; exact hnm e
  · exact hown (e ▸ h.desNames g e')

/-- **`ChildIfaceP` of a `RealChildA O C y` of a callee with memory and/or ordinary calls** (`deepChild_ifaceP_M`; `hgk` / `hsep` DERIVED from `hord` and the table facts; `closes` DERIVED by `memCallee_closesA`).
`hord` is asked in every admissible context (as `closes` of `deepChild_ifaceP` is). -/
theorem memCallee_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {d : MachineData} {C : Name} {n : Nat} {nameK : Nat → String} {nk : Nat → Nat}
    {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData d C n nameK nk outsK namesK names)
    (hord : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y → ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
    (entry : MachineDefines mctx mref cctx cref C d.shape)
    {y : Res} (h : RealChildA O C y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl C) (machNIn d.shape)
      (d.shape.layout.outs.map (·.name)) names y.1 y.2 := by
  refine deepChild_ifaceP_M O T d hC.ok hC.body (nDecl := n) hC.callsOk hC.slots hC.domB hC.insts_ne hC.fne hC.outTy
    hC.slotsNe n hC.hkD hC.hIlen hC.hSL hC.hSlen hC.hLlen hC.hNIn names ?_ ?_ hC.memNames entry
    (fun mctx' cctx' hA' => memCallee_closesA O T hA' hC (hord mctx' cctx' hA')) h
  · intro k hk y' hc hre
    obtain ⟨hn, hs⟩ := hC.nameIn k hk hc
    obtain ⟨m', c', hA'⟩ := adm_of_realChildA hre
    exact gk_of_iface (hord m' c' hA' k hk y' hc hre) hn hs
  · intro k hk y' hc hre
    obtain ⟨m', c', hA'⟩ := adm_of_realChildA hre
    exact sep_of_iface (hord m' c' hA' k hk y' hc hre) (hC.parent k hk) (hC.parentD k hk)

/-- **`ChildIfaceP` of a plain leaf's `RealChildA`** (the ordinary kid of a callee next to a memory child; the leaf has no instances, so its design is empty and its `names` are `[]`). -/
theorem leafKid_ifaceP (O : RefLawsAOps MkRefd mref cref) {dG : MachineData} {G : Name} (hG : LeafData dG)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {y : Res} (hre : RealChildA O G y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl G) (leafNk dG) (dG.shape.layout.outs.map (·.name)) [] y.1 y.2 :=
  Tools.ShippingCallsKidsD.ChildIfaceD.toP
    (Tools.ShippingCallsKidsD.ChildIfaceG.toD
      (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O dG hG.ok hG.body hG.insts hG.outTy hR0 hcl hre))
    (fun hx => nomatch hx)

end Tools.ShippingSrm3Callee

#print axioms Tools.ShippingSrm3Callee.memCallee_closesA
#print axioms Tools.ShippingSrm3Callee.memCallee_ifaceP
#print axioms Tools.ShippingSrm3Callee.gk_of_iface
#print axioms Tools.ShippingSrm3Callee.sep_of_iface
#print axioms Tools.ShippingSrm3Callee.leafKid_ifaceP
