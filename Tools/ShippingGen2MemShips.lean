import Tools.ShippingGen2MemTop
import Tools.ShippingGen2C6
set_option autoImplicit false

/-! # M2-a: `ChildShips` (C6) and the final theorem `memParent_ships : MemParentStmt' L`
(scripts/gen2/MEMPARENT_FREEZE.md rev1 §3, §7.1)

C6: `seqChildRunN_of_composedNW_run` on C8's `ComposedNW n` of this run; `NoInstOf`/`ExtendsAway.2` from the run's
`closeInstsG` (`closeInstsG_acyclic`), `ExtendsAway.1` from `ChildShips`' own hypothesis `Dc ⊆ dsn`. `ChildShips` is
unchanged; no hypothesis beyond the frozen ones is used. -/
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

theorem memParent_childShips (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p) (hmo : MemOrigin p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hmd : ∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) (n : Nat) :
    ChildShips p (n + 1) b D := by
  obtain ⟨hok, hco, hslots, houtTy, hdomB⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := pkg_memComposedNW L p hA hfe hkD hdomB hIlen hSL hSlen hLlen hNIn hmd hmo n ran
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  -- no self-instantiation, from the run's group closing
  have acyc : Tools.ShippingHierMono.NoInstOf raw.name raw.body ∧
      ∀ g ∈ D.modules, Tools.ShippingHierMono.NoInstOf raw.name g.body := by
    obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ranA
    rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, -⟩
    · exact absurd hno hins
    rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩
    · exact absurd hf0 hfe
    obtain ⟨_, h1, h2⟩ := Tools.ShippingChildServe.closeInstsG_acyclic hG
    exact ⟨h1, h2⟩
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  intro dsn hcons _ i
  have hEA : Tools.ShippingHierMono.ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules) := by
    refine ⟨?_, ?_⟩
    · intro x r _ hD
      obtain ⟨g, hg, rfl⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hD
      have hm := Tools.ShippingHierPremisesBase.moduleByName_mem hg
      exact Tools.ShippingMachineDepthRun.childMap_some.mpr ⟨g, by rw [← hm.2]; exact hcons g hm.1, rfl⟩
    · intro x r hD
      obtain ⟨g, hg, rfl⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hD
      exact acyc.2 g (Tools.ShippingHierPremisesBase.moduleByName_mem hg).1
  exact Or.inl <| Tools.ShippingGen2C6.seqChildRunN_of_composedNW_run n houtTy (ok_outNameOk p.d hok) hsl hI0 hkD hIlen hSL
    hSlen hLlen hNIn hext.1 hext.2 i hNW hpost hEA acyc.1

/-- **M2-a: the memory-only parent ships** (`MemParentStmt'`, approved freeze rev1 §3 + A4 §7.1). -/
theorem memParent_ships (L : Laws mref cref) : MemParentStmt' (ι := ι) (dom := dom) L := by
  intro p mctx cctx w w1 raw b D hdata hext hmo hins hfe hsl hA _ hcore hpost entry ran hmd n
  exact ⟨memParent_topShips L p hdata hmo hins hfe hsl hA hcore hpost entry ran hmd n,
    memParent_childShips L p hdata hext hmo hins hfe hsl hA hpost ran hmd n⟩

end Tools.ShippingGen2
