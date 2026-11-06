import Tools.ShippingFGCircuitApply
import Tools.ShippingSrm11Bounds
set_option autoImplicit false
-- FG circuit pilot S1e, unit 2: `DesignTransport` for a register leaf (core design → printed design). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `DesignTransport` for a register leaf: the printed design is irrelevant

`TopShips p n X b raw D` reads the design `D` only through `childMap D.modules` (the instance oracle) and `ResetNk n raw D kids` (the reset of the instances of `raw`).
For a register leaf the returned module is in the instance-free fragment (`seqStmtOk`: assign / register / memory): `raw.body`, `b.body` and `(checkedOptimize b).body` contain no `Stmt.inst`, so
`runModuleTG_instFree` makes the run independent of the oracle, `ResetNk` is vacuous, and `bodyInstOuts _ b.body = []`. Hence `TopShips p n X b raw D → TopShips p n X b raw D'` for ANY two designs, in particular the
core design `D₀` and the printed design `D' = topMap … D₀` (`PostEntry`).

This does not use `Tools/ShippingGen5DCEntryT.lean` (the oracle-transport lemmas, conditional on `NoRawBelow`, for modules WITH instances): a leaf has none. The facts about `raw` and `b` are read off the machine trace
the run produces (`MachineWired`), exactly as `leaf_topShips_of_LB` reads them. -/
namespace Tools.ShippingFGCircuitTransport
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingFGCircuitBridge
open Tools.ShippingHierStateG (instFree runModuleTG_instFree)
open Sparkle.IR.AST Sparkle.IR.OptCheck Sparkle.IR.RefineCheck

/-- `TopShips` does not depend on the design when `raw`, `b` and the optimized `b` are instance-free. -/
theorem topShips_design_irrel {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (X : Name) {b raw : Sparkle.IR.AST.Module}
    (D D' : Sparkle.IR.AST.Design) (hraw : instFree raw.body) (hb : instFree b.body) (hopt : instFree (checkedOptimize b).body) :
    TopShips p n X b raw D → TopShips p n X b raw D' := by
  rintro ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids h1 h2 h3 h4 h5 h6 h7 h8
  have hreset : Tools.ShippingMachineShipsDepth.ResetNk n raw D kids := fun iname mc ⟨conns, hmem⟩ _ => by
    have := hraw _ hmem
    simp [Sparkle.IR.Machine.isInst] at this
  obtain ⟨envsO, hrun, hlen, hobs⟩ := H i bools bits T ins st0 mems kids h1 h2 h3 h4 h5 hreset h7
    (fun x hx _ => h8 x hx (by rw [Tools.ShippingSrm11Bounds.bodyInstOuts_instFree _ _ hb]; simp))
  refine ⟨envsO, ?_, hlen, hobs⟩
  rw [runModuleTG_instFree _ _ _ _ hopt] at hrun ⊢
  exact hrun

/-- the instance-freeness of `raw` and `b` for a register leaf, read off the machine trace of the core run -/
theorem leaf_instFree_of_run {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D₀ : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D₀) w1)
    (hd : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape)
    (hpost : Tools.ShippingGen5DCEntry.PostT1 b raw) :
    instFree raw.body ∧ instFree b.body ∧ instFree (checkedOptimize b).body := by
  obtain ⟨hok, hco, hSS, houtTy, hnoI, hsl⟩ := hleaf
  subst hdp
  have hran := Tools.ShippingServedRealA.machineRunJQC_of_closesA L.O hstart.1 hr hd
    (machineClosesAtA_of_closes L.O hcl) hstart.2.1 (Or.inl rfl)
  have hL := (Pkg.trace L.O L.T hstart.1 p hran).toLB
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, _, wired, tr⟩ := id hL
  obtain ⟨_, hbok, _⟩ := leaf_b_facts wired rlen hnoI hsl hSS houtTy hpost
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, hevery, _, _, _, _, hokR⟩ := hclean hnoI houtTy
  refine ⟨Tools.ShippingMachineDepthRun.instFree_of_seqOk hokR, Tools.ShippingMachineDepthRun.instFree_of_seqOk hbok,
    Tools.ShippingMachineDepthRun.instFree_of_seqOk (Tools.ShippingChecksDerived.checkedOptimize_seqOk_all hbok)⟩

/-- **`DesignTransport` for a register leaf**, from the core run: no further premise. -/
theorem designTransport_of_leaf {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D₀ D' : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D₀) w1)
    (hd : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape)
    (hpost : Tools.ShippingGen5DCEntry.PostT1 b raw) :
    DesignTransport p p.decl b raw D₀ D' := by
  obtain ⟨h1, h2, h3⟩ := leaf_instFree_of_run L p hdp hleaf hstart hr hd hcl hpost
  exact fun n => topShips_design_irrel p n p.decl D₀ D' h1 h2 h3

end Tools.ShippingFGCircuitTransport

#print axioms Tools.ShippingFGCircuitTransport.topShips_design_irrel
#print axioms Tools.ShippingFGCircuitTransport.designTransport_of_leaf
