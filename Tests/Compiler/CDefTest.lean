import Tests.Compiler.Srm9ComposedTest
import Tests.Compiler.SharedLeafMemKidEntryTest
-- C-DEF (issue sparkle-gen-c4-cdef): GenPkg / MemSharedLeafParent exactly as scripts/c3/EXPECTED_CDEF.lean.txt (+ members and defeq audits below). Test-only; no production edit.
-- NOT proved here: G-KID, G-HCALLS (unresolved dependencies). C4 and G3 stay OPEN.
namespace Tests.Compiler.CDef
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine
open Tools.ShippingMachineSource Tools.ShippingMachineDenote Tools.ShippingQuadComposed (GenFacts QuadGroupFacts)
open Tools.ShippingCallsChildPorts (argWidths)

structure GenPkg (ι : Type) (dom : ι → DomainConfig) where
  decl : Lean.Name
  d : MachineData
  ρ : ι → Type
  inh : Inhabited (HList (tys d.ss))
  inits : HList (tys d.ss)
  body : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
    Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i)
  obsR : (i : ι) → ρ i → List (Nat → Nat)
  ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)
  gen : @GenFacts d ι dom ρ inh inits body obsR ext extB src

noncomputable def GenPkg.extS {ι} {dom} (p : GenPkg ι dom) := fun i bools bits =>
  p.ext i bools bits (@stateLoop _ _ _ p.inh p.inits (p.body i bools bits))
noncomputable def GenPkg.extBS {ι} {dom} (p : GenPkg ι dom) := fun i bools bits =>
  p.extB i bools bits (@stateLoop _ _ _ p.inh p.inits (p.body i bools bits))
noncomputable def GenPkg.lsrc {ι} {dom} (p : GenPkg ι dom) :=
  @Tools.ShippingMachineCausal.letObsB p.d ι dom p.inh p.ρ p.inits p.body p.ext p.extB

structure MemSharedLeafParent where
  top : GenPkg Unit (fun _ => defaultDomain)
  nDecl : Nat
  cs : List NCal
  pdata : NmParentData top.d cs top.decl nDecl
  outTy : ∀ o ∈ top.d.shape.layout.outs, o.ty.bitWidth = o.width
  noMem : ∀ x ∈ top.d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true
  slotsNe : top.d.shape.layout.slots ≠ []
  outsOf : Nat → List OutField
  insOf : Nat → List Nat
  cw : Tools.ShippingCallWidths.callWidthsOk top.d nDecl outsOf = true
  ca : Tools.ShippingPortsMatchRaw.callArgsOk top.d nDecl insOf = true
  leaf : GenPkg DomainConfig (fun i => i)
  wrappers : List (GenPkg DomainConfig (fun i => i))
  bsC : Lean.Name → List (Name × MixedGateBinder)
  outsC : Lean.Name → List OutField
  srcC : Unit → Lean.Name → (Nat → List Nat) → List (Nat → Nat)
  group : QuadGroupFacts top.d nDecl top.lsrc top.extS top.extBS bsC outsC srcC
  -- AMENDMENT 1 (wrapper / leaf / callee ties; all decidable data except tieSrcC = structural defeq):
  wArity : List Nat                                   -- DATA: declared-input count of each wrapper (M: [4,4]; Q: [3,5])
  wOf : Nat → Nat                                     -- DATA: call index k ↦ index of the wrapper called at k
  wlen : wrappers.length = wArity.length              -- DATA CHECK
  tieCallee : ∀ k, k < top.d.shape.insts.length →
    wOf k < wrappers.length ∧ (top.d.shape.insts.map (·.1))[k]? = (wrappers.map (·.decl))[wOf k]?   -- DATA CHECK (decide)
  tieOuts : ∀ k, k < top.d.shape.insts.length → outsOf k = (wrappers.map (·.d.shape.layout.outs)).getD (wOf k) []   -- DATA CHECK
  tieIns : ∀ k, k < top.d.shape.insts.length →
    insOf k = ((wrappers.zip wArity).map (fun p => argWidths p.1.d p.2)).getD (wOf k) []                  -- DATA CHECK
  tieLeaf : ∀ w ∈ wrappers, leaf.decl ∈ w.d.shape.insts.map (·.1)                                    -- DATA CHECK (leaf is a callee of every wrapper)
  tieBsC : ∀ p ∈ wrappers.zip wArity, bsC p.1.decl = p.1.d.bsIn.take p.2                              -- DATA CHECK
  tieOutsC : ∀ p ∈ wrappers.zip wArity, outsC p.1.decl = p.1.d.shape.layout.outs                      -- DATA CHECK
  tieSrcC : ∀ p ∈ wrappers.zip wArity, srcC () p.1.decl = fun vals => p.1.src defaultDomain
    (Tools.ShippingMachineChild.boolsOf (p.1.d.bsIn.take p.2) vals) (Tools.ShippingMachineChild.bitsOf (p.1.d.bsIn.take p.2) vals)   -- STRUCTURAL (rfl-style)


open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidIfaceTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tests.Compiler.Srm9ComposedTest
variable {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}

/-! ## P_M  (TmGrp is a PREMISE of TmBnd, not a theorem: P_M takes it as a hypothesis = the structural class assumption) -/
noncomputable def P_M (hgrp : TmGrp) : MemSharedLeafParent where
  top := { decl := ``topshareM, d := topshareM.machineData, ρ := _, inh := topshareM_inhab, inits := topshareM.machineInits,
           body := topshareM.machineBody, obsR := topshareM.machineResult, ext := topshareM.machineExt, extB := topshareM.machineExtB,
           src := topshareM.machineSource, gen := topshareM_gen }
  nDecl := 4
  cs := csM
  pdata := topshareM_parentData
  outTy := topshareM_outTy
  noMem := topshareM_nomem
  slotsNe := topshareM_slotsNe
  outsOf := tmOuts
  insOf := tmIns
  cw := topshareM_cw
  ca := topshareM_ca
  leaf := { decl := ``leafM, d := leafM.machineData, ρ := _, inh := leafM_inhab, inits := leafM.machineInits, body := leafM.machineBody,
            obsR := leafM.machineResult, ext := leafM.machineExt, extB := leafM.machineExtB, src := leafM.machineSource, gen := leafM_gen }
  wrappers := [{ decl := ``wrapM, d := wrapM.machineData, ρ := _, inh := wrapM_inhab, inits := wrapM.machineInits, body := wrapM.machineBody,
                 obsR := wrapM.machineResult, ext := wrapM.machineExt, extB := wrapM.machineExtB, src := wrapM.machineSource, gen := wrapM_gen },
               { decl := ``wrapM3, d := wrapM3.machineData, ρ := _, inh := wrapM3_inhab, inits := wrapM3.machineInits, body := wrapM3.machineBody,
                 obsR := wrapM3.machineResult, ext := wrapM3.machineExt, extB := wrapM3.machineExtB, src := wrapM3.machineSource, gen := wrapM3_gen }]
  bsC := tmBsC
  outsC := tmOutsC
  srcC := tmSrcC
  group := hgrp
  wArity := [4, 4]
  wOf := fun k => if k < 2 then 0 else 1
  wlen := rfl
  tieCallee := by first | decide | decide +kernel
  tieOuts := by first | decide | decide +kernel
  tieIns := by first | decide | decide +kernel
  tieLeaf := by first | decide | decide +kernel
  tieBsC := by first | decide | decide +kernel | (intro p hp; simp [List.zip] at hp; rcases hp with rfl | rfl <;> rfl)
  tieOutsC := by first | decide | decide +kernel | (intro p hp; simp [List.zip] at hp; rcases hp with rfl | rfl <;> rfl)
  tieSrcC := by intro p hp; simp [List.zip] at hp; rcases hp with rfl | rfl <;> rfl

/-! ## defeq audits (M): the class projections ARE the terms of TmGrp / topshareM_soundLA / tmOuts / tmIns / tmBsC -/
theorem P_M_group_defeq (hgrp : TmGrp) :
    QuadGroupFacts (P_M hgrp).top.d (P_M hgrp).nDecl (P_M hgrp).top.lsrc (P_M hgrp).top.extS (P_M hgrp).top.extBS (P_M hgrp).bsC (P_M hgrp).outsC (P_M hgrp).srcC = TmGrp := rfl
theorem P_M_ext_defeq (hgrp : TmGrp) : (P_M hgrp).top.extS = tmExt := rfl
theorem P_M_extB_defeq (hgrp : TmGrp) : (P_M hgrp).top.extBS = tmExtB := rfl
theorem P_M_lsrc_defeq (hgrp : TmGrp) :
    (P_M hgrp).top.lsrc = Tools.ShippingMachineCausal.letObsB topshareM.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineInits
        topshareM.machineBody topshareM.machineExt topshareM.machineExtB := rfl
theorem P_M_tables_defeq (hgrp : TmGrp) : (P_M hgrp).outsOf = tmOuts ∧ (P_M hgrp).insOf = tmIns ∧ (P_M hgrp).bsC = tmBsC ∧ (P_M hgrp).outsC = tmOutsC ∧ (P_M hgrp).srcC = tmSrcC :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
/-- the statement of `topshareM_soundLA` re-spelled through the class projections is the same type -/
theorem P_M_soundL_defeq (hgrp : TmGrp) :
    Tools.ShippingMachineAuto.MachineTraceLB (P_M hgrp).top.decl (P_M hgrp).top.d m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) (P_M hgrp).top.src
      (P_M hgrp).top.extS (P_M hgrp).top.extBS (P_M hgrp).top.lsrc =
    Tools.ShippingMachineAuto.MachineTraceLB ``topshareM topshareM.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineSource
      (fun i bools bits => topshareM.machineExt i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (fun i bools bits => topshareM.machineExtB i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshareM.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineInits
        topshareM.machineBody topshareM.machineExt topshareM.machineExtB) := rfl
end Tests.Compiler.CDef
