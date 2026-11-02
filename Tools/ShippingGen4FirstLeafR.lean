import Tools.ShippingGen4GateIfaceR
import Tools.ShippingFirstGateChild
-- NOT BUILT. U-GC0 (scripts/gen2/GATE_GC0_FREEZE.md): transfer of kjob/g4gate-g6 to base 15cd9d1f. No sorry / axiom / native_decide.

/-! # U-G3: the FIRST-gate (route 1) combinational leaf at the child interface
No `old`, no `mixedGatePeel`: the module facts come from `first_child_fullFacts` / `first_full_outputs` / `first_child_fnR`
(premises: `EntryDefines` and a run only). Intermediate result: child side of route 1 only; `entry`, `RealChildA` and `Q` are
hypotheses; no run-existence claim; no instance parent, Top, route 2 width 1 or sequential leaf. -/

namespace Tools.ShippingGen2
open Sparkle.IR.Type (HWType)
open Tools.ShippingMachineEntry (kindTy)
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.RegDedup (isAssign)
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingChildInv (Res)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineChild (InRange)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineShipsComb (seedR)
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingChildInvA (RefLawsAOps)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingGateChildComb (ChildFull)
open Tools.ShippingEntrySoundness (FExpr quoteDecl)
open Tools.ShippingUnifiedSource (ofF)
open Tools.ShippingFirstGateChild (firstBs firstFn ChildFnR first_child_fullFacts first_full_outputs first_child_fnR)

variable {ι : Type}
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- Per-declaration data of a FIRST-gate leaf: the premises of `first_child_*` that are not hypotheses of the run. -/
structure FirstLeaf (ι : Type) where
  decl  : Name
  dn    : Name
  names : List Name
  n     : Nat
  fe    : FExpr
  hwf   : fe.WF names.length n
  hn    : 0 < n

/-- The interface record of a first-gate leaf; the output type is `bitVector n`. -/
noncomputable def FirstLeaf.ifaceOf (f : FirstLeaf ι) : ChildIface ι :=
  ⟨f.decl, firstBs f.dn f.names f.n, [GateLeaf.outField (.bitVector f.n)],
   fun _ => gateS (firstBs f.dn f.names f.n) (ofF f.n f.fe) (fun _ => 0) (fun j => j + 1)⟩

theorem firstFn_eq_gateVal (dn : Name) (names : List Name) (n : Nat) (fe : FExpr) :
    firstFn dn names n fe = g4_gateVal (firstBs dn names n) (ofF n fe) (fun _ => 0) (fun j => j + 1) := rfl

/-- T2: the tail of `gate_combChildRunN` against `ChildFnR` (no reset premise). -/
theorem combChildRunN_of_fnR {c : Name} {bs : List (Name × MixedGateBinder)} {y : Res} {F : List Nat → Nat} {ty : HWType}
    (hfull : ChildFull c bs y.1 y.2)
    (hfn : ChildFnR y.1 (fun vs => InRange vs (bs.filter fun b => b.2 != .domain)) F)
    (hout : y.1.outputs = [{ name := "out", ty := ty }]) :
    ∀ (dsn : Design) (n : Nat),
      CombChildRunN (childMap dsn.modules) dsn n y.1 bs [GateLeaf.outField ty] (fun vals => [fun τ => F (vals τ)]) := by
  have hA : y.1.body.all isAssign = true := hfull.comb.assigns
  have halloc := hfull.comb.inputAlloc
  have hnotin : ∀ x, ¬ Sparkle.IR.NameHints.Allocated x → x ∉ y.1.inputs.map (·.name) := by
    intro x hx hm
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hm
    apply hx
    rw [← hpx]
    exact halloc p hp
  have hrst : "rst" ∉ y.1.inputs.map (·.name) := hnotin "rst" Tools.ShippingGateChildIfaceP.not_alloc_rst
  have harg : argPorts y.1 = y.1.inputs := by
    have h0 := Tools.ShippingGateChildIfaceP.inPortsOf_of_alloc halloc
    first
      | exact h0
      | (unfold argPorts; unfold Tools.ShippingInstStmtG.inPortsOf at h0; exact h0)
  obtain ⟨outP, houtP, hF⟩ := hfn
  have hon : outP.name = "out" := by
    rw [hout] at houtP
    injection houtP with h1 h2
    first
      | (rw [← h1]; done)
      | (rw [h1]; done)
      | simp [← h1]
  intro dsn n
  refine ⟨?_, hfull.comb.inputNames, hnotin "clk" Tools.ShippingGateChildIfaceP.not_alloc_clk, hrst,
    ?_, ?_, ?_⟩
  · first
      | (rw [hout]; done)
      | (rw [hout]; rfl)
      | simp [hout, GateLeaf.outField]
  · intro x hx
    rw [hout] at hx
    have hx' : x = "out" := by
      first
        | simpa using hx
        | (simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx; exact hx)
    subst hx'
    exact hnotin "out" Tools.ShippingGateChildIfaceP.not_alloc_out
  · rw [harg]
    have hl := congrArg List.length hfull.tys
    simpa only [List.length_map] using hl
  · intro T ins s vals hrange hports _hreset
    rw [Tools.ShippingMachineDepth.RunOn_instFree (childMap dsn.modules) y.1 (g4_instFree_of_assigns hA)]
    have hstep : ∀ (k : Nat) (st : String → Nat) (mems : MEnv), k < T →
        ∃ env', evalAssigns (Sparkle.IR.RegDedup.declWidth y.1) mems y.1.body (seedR y.1 ins k st) = some env' ∧
          env' "out" = F (vals (T - 1 - k)) := by
      intro k st mems hk
      have hargs : (argPorts y.1).map (fun p => seedR y.1 ins k st p.name) = vals (T - 1 - k) := by
        rw [Tools.ShippingGateDesign.seedR_args]
        exact hports k hk
      have hP : InRange ((argPorts y.1).map fun p => seedR y.1 ins k st p.name)
          (bs.filter fun b => b.2 != .domain) := by
        rw [hargs]
        exact hrange (T - 1 - k) (by omega)
      obtain ⟨cres, hev, hval⟩ := hF mems (seedR y.1 ins k st) hP
      refine ⟨cres, hev, ?_⟩
      have hv' := hval
      rw [hon, hargs] at hv'
      exact hv'
    obtain ⟨envs₁, hr₁, hl₁, hR₁⟩ := Tools.ShippingGateDesign.runModule_assigns_total
      (we := Sparkle.IR.RegDedup.declWidth y.1) (seed := seedR y.1 ins)
      (R := fun k env => env "out" = F (vals (T - 1 - k))) (N := T)
      hA hstep T (Tools.ShippingHierStateG.stOf n s) (Tools.ShippingHierStateG.memsOf n s) (Nat.le_refl T)
    have hagree : ∀ (t : Nat) (st : String → Nat), ∀ x ∈ y.1.inputs.map (·.name),
        seedR y.1 ins t st x = seedIn y.1 ins t st x := by
      intro t st x hx
      have hne : x ≠ "rst" := fun h' => by subst h'; exact hrst hx
      show (if x = "rst" then 0
        else if (y.1.inputs.map (·.name)).contains x then ins t x else st x) =
          (if (y.1.inputs.map (·.name)).contains x then ins t x else st x)
      rw [if_neg hne]
    obtain ⟨envs₂, hr₂, hl₂, hc₂⟩ := Tools.ShippingGen2Comb.runModule_seed_local
      (seed₁ := seedR y.1 ins) (seed₂ := seedIn y.1 ins) hA hfull.comb.closed hagree
      T (Tools.ShippingHierStateG.stOf n s) (Tools.ShippingHierStateG.memsOf n s) envs₁ hr₁
    refine ⟨envs₂, hr₂, hl₂.trans hl₁, ?_⟩
    intro j hj k o' f ho' hf'
    cases k with
    | succ k => simp at ho'
    | zero =>
      have eo : GateLeaf.outField ty = o' := by
        first
          | exact Option.some.inj ho'
          | (simp only [List.getElem?_cons_zero, Option.some.injEq] at ho'; exact ho')
      subst eo
      have ef : (fun τ => F (vals τ)) = f := by
        first
          | exact Option.some.inj hf'
          | (simp only [List.getElem?_cons_zero, Option.some.injEq] at hf'; exact hf')
      subst ef
      have hj₁ : j < envs₁.length := by omega
      show (envs₂[j]'hj) "out" = F (vals j)
      rw [hc₂ j hj₁ hj "out" (List.mem_append.mpr (Or.inr hfull.comb.outDriven))]
      have hRj : (envs₁[j]'hj₁) "out" = F (vals (T - 1 - (T - 1 - j))) :=
        hR₁ j hj₁ (T - 1 - j) (by omega)
      rw [hRj, show T - 1 - (T - 1 - j) = j by omega]

/-- T5 (the S3 port-width conjunct at the record; intermediate). -/
theorem firstLeaf_childPortWidthsI (O : RefLawsAOps MkRefd mref cref) (f : FirstLeaf ι)
    (entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe)) {y : Res} (h : RealChildA O f.decl y) :
    ChildPortWidthsI f.ifaceOf y.1 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    have hfull := first_child_fullFacts hr (Tools.ShippingReflectCtx.EntryDefines.ctx (mctx' := mctx') (cctx' := cctx') entry) f.hwf f.hn
    have harg : Tools.ShippingMachineCompose.argPorts y.1 = y.1.inputs := by
      have h0 := Tools.ShippingGateChildIfaceP.inPortsOf_of_alloc hfull.comb.inputAlloc
      first
        | exact h0
        | (unfold Tools.ShippingMachineCompose.argPorts; unfold Tools.ShippingInstStmtG.inPortsOf at h0; exact h0)
    unfold ChildPortWidthsI
    rw [harg]
    have ht := congrArg (List.map HWType.bitWidth) hfull.tys
    simp only [List.map_map] at ht
    exact ht

/-- T3 (child side). -/
theorem firstLeaf_childShips (O : RefLawsAOps MkRefd mref cref) (f : FirstLeaf ι)
    (entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe)) {y : Res} (h : RealChildA O f.decl y) :
    y.2.modules = [] ∧ y.1.outputs = [{ name := "out", ty := .bitVector f.n }] ∧
      ∀ n, ChildShipsI f.ifaceOf n y.1 y.2 := by
  have hh := h
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    have entry' := Tools.ShippingReflectCtx.EntryDefines.ctx (mctx' := mctx') (cctx' := cctx') entry
    have hfull := first_child_fullFacts hr entry' f.hwf f.hn
    have hout := first_full_outputs hr entry' f.hwf f.hn
    have hfn := first_child_fnR hr entry' f.hwf f.hn
    refine ⟨hfull.design, hout, ?_⟩
    intro n
    refine ⟨firstLeaf_childPortWidthsI O f entry hh, ?_⟩
    intro dsn _ _ i
    exact Or.inr (combChildRunN_of_fnR hfull hfn hout dsn n)

/-- T4. `Q` is an INPUT. -/
theorem firstLeaf_shipsResI (L : Laws mref cref) (f : FirstLeaf ι) (Q : IfaceMap ι) {y : Res}
    (hQ : Q f.decl = some f.ifaceOf) (h : RealChildA L.O f.decl y)
    (hchild : ∀ n, ChildShipsI f.ifaceOf n y.1 y.2) (hinst : InstClosed y) : ShipsResI L Q f.decl y :=
  ⟨h, ⟨f.ifaceOf, 0, hQ, rfl, hchild 0⟩, hinst⟩

theorem firstLeaf_shipsResI_of_real (L : Laws mref cref) (f : FirstLeaf ι) (Q : IfaceMap ι)
    (entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe)) {y : Res}
    (h : RealChildA L.O f.decl y) (hQ : Q f.decl = some f.ifaceOf) : ShipsResI L Q f.decl y :=
  firstLeaf_shipsResI L f Q hQ h (firstLeaf_childShips L.O f entry h).2.2
    (instClosed_of_nil y (firstLeaf_childShips L.O f entry h).1)

end Tools.ShippingGen2
