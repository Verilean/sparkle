import Tools.ShippingSrm12Corr
-- UNBUILT (unit SRM15): no build run yet (see REPORT-SRM15.md for the run names and exits once built).
-- SCOPE (SRM15): the GENERIC supply of SRM12's `hgraph` / `hname` premises of `ran_designCorr` (Tools/ShippingSrm12Corr.lean).  For `topshareM`/`topshareQ` both premises are already supplied inside SRM12's instance theorems
-- (`gM_top_callees`/`gQ_top_callees`, and the kids' `ChildIfaceP.name`); nothing here is a new discharge for those two designs.  What is new is the GENERIC statement:
--  * `graphOf ds`: the call graph read from a declaration list `ds : List (Name × MachineData)` (entry `(c, d.shape.instTagged)`);
--  * `FirstOcc ds c d`: the EXACT condition for `hgraph` -- the first entry of `ds` named `c` is `(c, d)`;  `callees_graphOf` : `FirstOcc ds c d → callees (graphOf ds) c = some d.shape.instTagged`;
--  * `hname_of_iface`: `hname` follows from the EXISTING per-kid interface fact (`ChildIfaceP (ofDecl callee) …`, its `.name` field);
--  * `ran_designCorr_of_graphOf`: `ran_designCorr` with the graph `graphOf ds`, the binders `hgraph`/`hname` REPLACED BY `FirstOcc` and the per-kid `ChildIfaceP` fact (`hkids` is UNCHANGED, still a premise);
--  * `GraphCovers`, `DefsProv`: provenance Props, stated, NOT derived (PREMISES where used).
-- NOT claimed: an arbitrary graph; that `ds` lists the right declarations; that the kids' interface facts hold.  No `sorry`, no `axiom`, no `native_decide`.
set_option autoImplicit false
namespace Tools.ShippingSrm15Graph
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildBndCore Tools.ShippingChildRunAKids
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineClosesData Tools.ShippingMachineCloses Tools.ShippingMachineAuto
open Tools.ShippingMemCloses Tools.ShippingCallsMemA
open Tools.ShippingSrm3Iface Tools.ShippingSrm3Callee Tools.ShippingSrm12Corr
open Sparkle.IR.ModuleName (ofDecl)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingSrm7Rank (Kid CallGraph callees)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the call graph READ from a declaration list: entry `(c, d.shape.instTagged)` for every `(c, d)` -/
def graphOf (ds : List (Name × MachineData)) : CallGraph :=
  ds.map fun p => (p.1, p.2.shape.instTagged)

/-- **The exact condition for `hgraph`**: the first entry of `ds` whose name is `c` is `(c, d)` -/
def FirstOcc (ds : List (Name × MachineData)) (c : Name) (d : MachineData) : Prop :=
  ds.find? (fun p => p.1 == c) = some (c, d)

theorem callees_graphOf (ds : List (Name × MachineData)) (c : Name) (d : MachineData) (h : FirstOcc ds c d) :
    callees (graphOf ds) c = some d.shape.instTagged := by
  induction ds with
  | nil => simp [FirstOcc] at h
  | cons a t ih =>
    obtain ⟨c0, d0⟩ := a
    unfold FirstOcc at h
    by_cases hc : (c0 == c) = true
    · simp only [List.find?_cons, hc] at h
      have h' := Option.some.inj h
      have hp := Prod.mk.inj h'
      rw [← hp.1, ← hp.2] at *
      simp [graphOf, Tools.ShippingSrm7Rank.callees, hc]
    · have hf : (c0 == c) = false := by simpa using hc
      simp only [List.find?_cons, hf] at h
      simp [graphOf, Tools.ShippingSrm7Rank.callees, hf]
      exact ih h

/-- **`hname` from the existing per-kid interface fact**: if every ordinary kid's `RealChildA` result satisfies `ChildIfaceP (ofDecl callee) …`, the result is named `ofDecl callee` -/
theorem hname_of_iface (O : RefLawsAOps MkRefd mref cref) (d : MachineData)
    (hiface : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y →
      ∃ (nArgs : Nat) (outs names : List String), ChildIfaceP (ofDecl (d.shape.insts[k]).1) nArgs outs names y.1 y.2) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y → y.1.name = ofDecl (d.shape.insts[k]).1 := by
  intro k hk y hn hre
  obtain ⟨_, _, _, hI⟩ := hiface k hk y hn hre
  exact hI.name

/-- **`ran_designCorr` over a graph read from a declaration list.**  Replaces the binders `hgraph`, `hname` of `ran_designCorr` by `hfirst : FirstOcc ds c d` and the per-kid `ChildIfaceP` fact `hiface`; `hkids` is unchanged. -/
theorem ran_designCorr_of_graphOf (O : RefLawsAOps MkRefd mref cref) (ds : List (Name × MachineData)) {c : Name}
    (d : MachineData) (hfirst : FirstOcc ds c d) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hiface : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y →
      ∃ (nArgs : Nat) (outs names : List String), ChildIfaceP (ofDecl (d.shape.insts[k]).1) nArgs outs names y.1 y.2)
    (hkids : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none →
      ChildCorr (graphOf ds) O (d.shape.insts[k]).1) :
    ModCorr (graphOf ds) b ∧ ModCorr (graphOf ds) (checkedOptimize b) ∧ DesignCorr (graphOf ds) D.modules :=
  ran_designCorr O (graphOf ds) d ok hbody hC hslots hdomB hins hfne outTy hpost ran
    (callees_graphOf ds c d hfirst) (hname_of_iface O d hiface) hkids

/-! ## Provenance Props (STATED; nothing here is derived) -/

/-- **List completeness** (PREMISE where used): every ordinary (non-memory-origin) callee of a listed declaration is itself listed, i.e. has a first occurrence in `ds`.
Used to obtain the graph entry (`hgraph`) of each callee needed for `hkids`; `graphCovers_callees` is the only consequence proved here. -/
def GraphCovers (ds : List (Name × MachineData)) : Prop :=
  ∀ p ∈ ds, ∀ k ∈ p.2.shape.instTagged, k.2.child? = none → ∃ d' : MachineData, FirstOcc ds k.1 d'

/-- **Shape provenance** (PREMISE where used): the shape fixed by `MachineDefines` for each listed declaration is the shape of its listed machine data.  Used to turn a `MachineDefines` entry for a callee into
the `MachineData`-based `ran` of `ran_designCorr_of_graphOf` (SRM12's instances state `MachineDefines … c X.machineData.shape` directly). -/
def DefsProv (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (ds : List (Name × MachineData)) : Prop :=
  ∀ p ∈ ds, MachineDefines mctx mref cctx cref p.1 p.2.shape

/-- under `GraphCovers`, every ordinary callee of a listed declaration has a graph entry in `graphOf ds` -/
theorem graphCovers_callees {ds : List (Name × MachineData)} (hcov : GraphCovers ds) {p : Name × MachineData}
    (hp : p ∈ ds) {k : Kid} (hk : k ∈ p.2.shape.instTagged) (hn : k.2.child? = none) :
    ∃ d' : MachineData, callees (graphOf ds) k.1 = some d'.shape.instTagged := by
  obtain ⟨d', h⟩ := hcov p hp k hk hn
  exact ⟨d', callees_graphOf ds k.1 d' h⟩

end Tools.ShippingSrm15Graph
