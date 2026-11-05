import Tools.ShippingGen2MemData
import Tools.ShippingGen2TopContract
import Tools.ShippingGen2MemBd
import Tools.ShippingGen2MemKids
import Tools.ShippingSrm33Core
import Tools.ShippingSrm32Width
import Tools.ShippingRanABridge
set_option autoImplicit false

/-! # M2-a: `TopShips` of a memory-only machine-route run (MEMPARENT_FREEZE.md rev1 §1, §3, §7.1)

Consumer 1 `machine_ships_hierC_noHstR` at height `n + 1`, with
* `Bnd` = "this very run" (contexts, refs, world, emitted module and design pinned), `C := True`;
* `Bd := kidsMem`, `Inv := memInvN (n+1)`, `hBd` = C2, `hRI` = C3; the antecedent `Bd b D` = C4;
* `soundL` = `genTrace` on `MachineTaken`, `toLB`; `composed` = C8 + `composedNWRegs_of_composedNW` + `hWd_of_wired`
  (its `hierGate` from `RunFacts.gate`); `facts` = `core_runFacts_ranAM` with `hkidP` (`memKidTNC_facts`) and C5;
* data from `MemParentDataOk` (rows and their derivations), `MemOrigin`, the case premises. -/
namespace Tools.ShippingGen2
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain

open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

theorem memParent_topShips (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hmo : MemOrigin p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hcore : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hmd : ∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) (n : Nat) :
    TopShips p (n + 1) p.decl b raw D := by
  obtain ⟨hok, hco, hslots, houtTy, hdomB⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  have hmemO : ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ (cb : Bool) (aw dw : Nat),
      (originAt p.d.shape k).child? = some (memModule cb aw dw) := fun k hk => by
    obtain ⟨cb, aw, dw, ho, -⟩ := hmo k hk
    exact ⟨cb, aw, dw, ho⟩
  have hkidP : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA L.O (originAt p.d.shape k) (p.d.shape.insts[k]).1 y →
      ∀ q ∈ y.1.outputs, (∀ q' ∈ Tools.ShippingInstStmtG.inPortsOf y.1, q'.name ≠ q.name) ∧ q.name ≠ "clk" ∧ q.name ≠ "rst" := by
    intro k hk y hy
    obtain ⟨cb, aw, dw, ho⟩ := hmemO k hk
    exact (Tools.ShippingSrm4Core6.memKidTNC_facts (O := L.O) (c := (p.d.shape.insts[k]).1) ho).outsIn y hy
  have hkidW := hkidW_of_memOrigin L.O p.d p.kD hco hmo
  have factsB : ∀ {b' : Sparkle.IR.AST.Module}, (b' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b' := fun hpb =>
    Tools.ShippingSrm4Core2.core_runFacts_ranAM L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsl hfe houtTy
      hkidP hkidW hpb ranA
  let Bnd : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx' mref' cctx' cref' w' m' D' =>
    mctx' = mctx ∧ mref' = mref ∧ cctx' = cctx ∧ cref' = cref ∧ w' = w ∧ m' = raw ∧ D' = D
  have key := Tools.ShippingSrm33.machine_ships_hierC_noHstR (n := n + 1)
    (fun D' => Tools.ShippingHierStateG.KSn_local _ _) Bnd (fun _ _ _ _ => True)
    (fun b' D' => Tools.ShippingMachineShipsHier.kidsMem (childMap D'.modules) b'.body = true) (memInvN (n + 1))
    (fun b' D' h => memKSn_boundedIn D'.modules b'.body h (n + 1)) (resetNk_memInvN (n + 1))
    p.d (kD := p.kD) (src := p.src) (ext := p.extS) (extB := p.extBS)
    (lsrc := p.lsrc) (srcL := p.src) (extL := p.extS) (extBL := p.extBS)
    (fun {mctx'} {mref'} {cctx'} {cref'} {w'} {w''} {m'} {design'} _ _ _ hB => by
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hB
      exact (Pkg.trace L.O L.T hA p ran).toLB)
    (fun {mctx'} {mref'} {cctx'} {cref'} {w'} {w''} {m'} {design'} {b'} _ hpb _ _ hB _ => by
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hB
      have hNW := pkg_memComposedNW L p hA hfe hkD hdomB hIlen hSL hSlen hLlen hNIn hmd hmo (n + 1) ran
      refine Tools.ShippingSrm28.composedNWRegs_of_composedNW _ hNW ?_
      intro ids cache regs lets _ _ hW
      exact Tools.ShippingSrm32.hWd_of_wired hpb (factsB hpb).gate houtTy hW)
    houtTy (Tools.ShippingC4InitW.hinitW_of_ok p.d hok) hcore hpost entry trivial (fun _ => factsB hpost)
  -- R-G: `key` has the consumer-1 (old) premises; L2 with both memberships from the run (U-TOP-CLKIN)
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id (Pkg.trace L.O L.T hA p ran).toLB
  exact topShips_ofOld_wired p (n + 1) wired hsl hpost (key ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (core_kidsMem_ranAM L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hfe hmemO hpost houtTy ranA))

end Tools.ShippingGen2
