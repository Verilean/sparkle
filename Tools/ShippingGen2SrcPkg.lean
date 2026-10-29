-- Tools/ShippingGen2SrcPkg.lean: the circuit-do source package, split out of Tools/ShippingGen2Defs.lean (loop-pkg step 2,
-- LOOPPKG_FREEZE.md §6) so that the package sum `Pkg` can sit between it and the generic definitions. Text unchanged.
-- (was: scripts/gen2/GEN2_DEFS.lean.txt — exact text of the gen2 definitions and statements (GENERAL_SPEC.md rev1 §1, §3, §8).
-- Status: elaborated verbatim as Tools/ShippingGen2Defs.lean (cmp-identical; GENERAL_SPEC.md §8.1 lists the builds).
-- Every `…Stmt` is a `def … : Prop` (a statement, no proof, no sorry). Non-semantic corrections (names, opens,
-- annotations) are made in U0 and collected for the result review; semantic changes are listed in GENERAL_SPEC §0.

import Tools.ShippingSrm33Core
import Tools.ShippingMachineDepthRunRA
import Tools.ShippingMachineCallsLinkedTNR
import Tools.ShippingQuadComposed
import Tools.ShippingServedRealA

set_option autoImplicit false

namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
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

/-! ## 1. The source package of one declaration (G3, per declaration; §6 inventory G3-GEN) -/

/-- The generated facts of one declaration as one package: `Tests.Compiler.CDef.GenPkg` (CDefTest.lean:33) moved
to `Tools` unchanged, plus `kD`, the number of declared (non-call-result) binders. -/
structure SrcPkg (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
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
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    List (Nat → Nat)
  gen : @GenFacts d ι dom ρ inh inits body obsR ext extB src

variable {ι : Type} {dom : ι → DomainConfig}

noncomputable def SrcPkg.extS (p : SrcPkg ι dom) := fun i bools bits =>
  p.ext i bools bits (@stateLoop _ _ _ p.inh p.inits (p.body i bools bits))
noncomputable def SrcPkg.extBS (p : SrcPkg ι dom) := fun i bools bits =>
  p.extB i bools bits (@stateLoop _ _ _ p.inh p.inits (p.body i bools bits))
noncomputable def SrcPkg.lsrc (p : SrcPkg ι dom) :=
  @Tools.ShippingMachineCausal.letObsB p.d ι dom p.inh p.ρ p.inits p.body p.ext p.extB
/-- The declared, non-domain ports of `p` (the child interface's binder list). -/
def SrcPkg.ports (p : SrcPkg ι dom) : List (Name × MixedGateBinder) :=
  (p.d.bsIn.take p.kD).filter fun b => b.2 != .domain
/-- The child-interface source function: `p.src` on the boolean/bit-vector signals decoded from port values
(the shape of C4's `tieSrcC`, CDefTest.lean:111). -/
noncomputable def SrcPkg.S (p : SrcPkg ι dom) (i : ι) : (Nat → List Nat) → List (Nat → Nat) :=
  fun vals => p.src i (boolsOf (D := dom i) (p.d.bsIn.take p.kD) vals)
    (bitsOf (D := dom i) (p.d.bsIn.take p.kD) vals)

/-- A package assignment: the package of every declaration a run reaches, or `none`. The G3 premise is that it is
correct where it is `some` (`PkgOk`). -/

end Tools.ShippingGen2
