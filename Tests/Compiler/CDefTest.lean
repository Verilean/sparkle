import Tests.Compiler.Srm9ComposedTest
import Tests.Compiler.SharedLeafMemKidEntryTest
import Tools.ShippingSeqParentGenD2MSD
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

/-! ## leafP generator package (NEW here: no leafP_gen / leafP_inhab existed; built from leafP.machine_* exactly as leafM_gen, Srm4RunTest.lean:23-31) -/
noncomputable instance leafP_inhab : Inhabited (HList (tys leafP.machineData.ss)) :=
  ⟨Tools.ShippingSeqParentGenD2MSD.defaultHList _⟩

theorem leafP_gen : GenFacts leafP.machineData (fun i : DomainConfig => i) leafP.machineInits leafP.machineBody leafP.machineResult
    leafP.machineExt leafP.machineExtB leafP.machineSource :=
  ⟨leafP.machine_ok, leafP.machine_body, leafP.machine_inits, leafP.machine_writes, leafP.machine_result, leafP.machine_source,
   fun i bools bits S S' t h =>
    leafP.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

/-! ## P_Q  (TqGrp is a PREMISE of TqBnd, not a theorem: P_Q takes it as a hypothesis = the structural class assumption) -/
noncomputable def P_Q (hgrp : TqGrp) : MemSharedLeafParent where
  top := { decl := ``topshareQ, d := topshareQ.machineData, ρ := _, inh := topshareQ_inhab, inits := topshareQ.machineInits,
           body := topshareQ.machineBody, obsR := topshareQ.machineResult, ext := topshareQ.machineExt, extB := topshareQ.machineExtB,
           src := topshareQ.machineSource, gen := topshareQ_gen }
  nDecl := 4
  cs := csQ
  pdata := topshareQ_parentData
  outTy := topshareQ_outTy
  noMem := topshareQ_nomem
  slotsNe := topshareQ_slotsNe
  outsOf := tqOuts
  insOf := tqIns
  cw := topshareQ_cw
  ca := topshareQ_ca
  leaf := { decl := ``leafP, d := leafP.machineData, ρ := _, inh := leafP_inhab, inits := leafP.machineInits, body := leafP.machineBody,
            obsR := leafP.machineResult, ext := leafP.machineExt, extB := leafP.machineExtB, src := leafP.machineSource, gen := leafP_gen }
  wrappers := [{ decl := ``wrapP, d := wrapP.machineData, ρ := _, inh := wrapP_inhab, inits := wrapP.machineInits, body := wrapP.machineBody,
                 obsR := wrapP.machineResult, ext := wrapP.machineExt, extB := wrapP.machineExtB, src := wrapP.machineSource, gen := wrapP_gen },
               { decl := ``wrapQ, d := wrapQ.machineData, ρ := _, inh := wrapQ_inhab, inits := wrapQ.machineInits, body := wrapQ.machineBody,
                 obsR := wrapQ.machineResult, ext := wrapQ.machineExt, extB := wrapQ.machineExtB, src := wrapQ.machineSource, gen := wrapQ_gen }]
  bsC := tqBsC
  outsC := tqOutsC
  srcC := tqSrcC
  group := hgrp
  wArity := [3, 5]
  wOf := fun k => if k < 2 then 0 else 1
  wlen := rfl
  tieCallee := by first | decide | decide +kernel
  tieOuts := by first | decide | decide +kernel
  tieIns := by first | decide | decide +kernel
  tieLeaf := by first | decide | decide +kernel
  tieBsC := by first | decide | decide +kernel | (intro p hp; simp [List.zip] at hp; rcases hp with rfl | rfl <;> rfl)
  tieOutsC := by first | decide | decide +kernel | (intro p hp; simp [List.zip] at hp; rcases hp with rfl | rfl <;> rfl)
  tieSrcC := by intro p hp; simp [List.zip] at hp; rcases hp with rfl | rfl <;> rfl

/-! ## defeq audits (Q): the class projections ARE the terms of TqGrp / topshareQ_soundLA / tqOuts / tqIns / tqBsC -/
theorem P_Q_group_defeq (hgrp : TqGrp) :
    QuadGroupFacts (P_Q hgrp).top.d (P_Q hgrp).nDecl (P_Q hgrp).top.lsrc (P_Q hgrp).top.extS (P_Q hgrp).top.extBS (P_Q hgrp).bsC (P_Q hgrp).outsC (P_Q hgrp).srcC = TqGrp := rfl
theorem P_Q_ext_defeq (hgrp : TqGrp) : (P_Q hgrp).top.extS = tqExt := rfl
theorem P_Q_extB_defeq (hgrp : TqGrp) : (P_Q hgrp).top.extBS = tqExtB := rfl
theorem P_Q_lsrc_defeq (hgrp : TqGrp) :
    (P_Q hgrp).top.lsrc = Tools.ShippingMachineCausal.letObsB topshareQ.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineInits
        topshareQ.machineBody topshareQ.machineExt topshareQ.machineExtB := rfl
theorem P_Q_tables_defeq (hgrp : TqGrp) : (P_Q hgrp).outsOf = tqOuts ∧ (P_Q hgrp).insOf = tqIns ∧ (P_Q hgrp).bsC = tqBsC ∧ (P_Q hgrp).outsC = tqOutsC ∧ (P_Q hgrp).srcC = tqSrcC :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
/-- the statement of `topshareQ_soundLA` re-spelled through the class projections is the same type -/
theorem P_Q_soundL_defeq (hgrp : TqGrp) :
    Tools.ShippingMachineAuto.MachineTraceLB (P_Q hgrp).top.decl (P_Q hgrp).top.d m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) (P_Q hgrp).top.src
      (P_Q hgrp).top.extS (P_Q hgrp).top.extBS (P_Q hgrp).top.lsrc =
    Tools.ShippingMachineAuto.MachineTraceLB ``topshareQ topshareQ.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineSource
      (fun i bools bits => topshareQ.machineExt i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (fun i bools bits => topshareQ.machineExtB i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshareQ.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineInits
        topshareQ.machineBody topshareQ.machineExt topshareQ.machineExtB) := rfl

/-! ## expected / binder / closure checks for BOTH members (M and Q); UNBUILT -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- members take exactly ONE explicit binder, the group class assumption (TmGrp / TqGrp), nothing else
  for (n, g) in [(``P_M, ``Tests.Compiler.Srm9ComposedTest.TmGrp), (``P_Q, ``TqGrp)] do
    let t := (← getConstInfo n).type
    forallTelescope t fun xs body => do
      unless xs.size == 1 do throwError "CDEF AUDIT FAILED: {n} has {xs.size} binders, expected 1 (the group assumption)"
      unless ← isDefEq (← inferType xs[0]!) (mkConst g) do throwError "CDEF AUDIT FAILED: {n}'s binder is not {g}"
      unless ← isDefEq body (mkConst ``MemSharedLeafParent) do throwError "CDEF AUDIT FAILED: {n} is not a MemSharedLeafParent"
  -- the defeq audit theorems exist for both members and use only standard axioms
  let audits := [``P_M_group_defeq, ``P_M_ext_defeq, ``P_M_extB_defeq, ``P_M_lsrc_defeq, ``P_M_tables_defeq, ``P_M_soundL_defeq,
                 ``P_Q_group_defeq, ``P_Q_ext_defeq, ``P_Q_extB_defeq, ``P_Q_lsrc_defeq, ``P_Q_tables_defeq, ``P_Q_soundL_defeq, ``leafP_gen,
                 ``P_M, ``P_Q]  -- the constructed members themselves (their stored GenFacts / wrapper / leaf packages)
  -- literal coverage guard: exactly these 15 constants (P_M, P_Q, leafP_gen, 12 projection audits); deleting one fails here
  let expected : List Name := [``P_M, ``P_Q, ``leafP_gen,
    ``P_M_group_defeq, ``P_M_ext_defeq, ``P_M_extB_defeq, ``P_M_lsrc_defeq, ``P_M_tables_defeq, ``P_M_soundL_defeq,
    ``P_Q_group_defeq, ``P_Q_ext_defeq, ``P_Q_extB_defeq, ``P_Q_lsrc_defeq, ``P_Q_tables_defeq, ``P_Q_soundL_defeq]
  unless expected.length == 15 do throwError "CDEF AUDIT FAILED: expected-name list has {expected.length} entries, not 15"
  unless audits.length == 15 do throwError "CDEF AUDIT FAILED: audit list has {audits.length} entries, not 15"
  unless audits.Nodup do throwError "CDEF AUDIT FAILED: duplicate entries in the audit list"
  unless expected.Nodup do throwError "CDEF AUDIT FAILED: duplicate entries in the expected-name list"
  -- exact set equality (both directions), in addition to the length and Nodup guards
  for a in audits do
    unless expected.contains a do throwError "CDEF AUDIT FAILED: {a} in the audit list is not an expected name"
  for e in expected do
    unless audits.contains e do throwError "CDEF AUDIT FAILED: {e} missing from the audit list"
    discard <| getConstInfo e
  for a in audits do
    let axs ← Lean.collectAxioms a
    for x in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "CDEF AUDIT FAILED: non-standard axiom {x} in {a}"
  logInfo m!"CDEF|ok|P_M P_Q: one binder (TmGrp/TqGrp), type MemSharedLeafParent; {audits.length} constants (12 defeq audits, leafP_gen, P_M, P_Q) with standard axioms only"

end Tests.Compiler.CDef
