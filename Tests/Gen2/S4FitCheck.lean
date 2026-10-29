import Tools.ShippingGen2FitChain
set_option autoImplicit false

/-! # S4-BD fit chain: axiom audit and projection checks (scripts/gen2/S4_FIT_FREEZE.md rev2, approved at bbca065d)

UNVERIFIED: written, not built (no lakefile `lean_lib` entry yet).

* Axiom audit of the basics in Tools/ShippingGen2Fit.lean (`KSBoundedRun` is a `def`, so its consumers are audited) and of
  every new declaration of Tools/ShippingGen2FitChain.lean. Expected: no `sorryAx`, no extra axiom (only the standard
  `propext` / `Classical.choice` / `Quot.sound`), no `Lean.ofReduceBool` (no `native_decide`).
* Projection checks (freeze §3.6): the copied statement `machine_linked_ofB_viaV` IS `machine_linked_ofB`'s type (`rfl` on the
  two types), and every `…F` form projects to the accepted stage-A type on the same arguments. -/

-- basics (Tools/ShippingGen2Fit.lean)
#print axioms Tools.ShippingGen2Fit.fitX_of_runR
#print axioms Tools.ShippingGen2Fit.posEnc_lt

-- the chain (Tools/ShippingGen2FitChain.lean)
#print axioms Tools.ShippingGen2Fit.ksBoundedRun_of_In
#print axioms Tools.ShippingGen2Fit.machine_linked_ofBV
#print axioms Tools.ShippingGen2Fit.machine_linked_ofB_viaV
#print axioms Tools.ShippingGen2Fit.ComposedHBF.toHB
#print axioms Tools.ShippingGen2Fit.composedNWn_of_HBF
#print axioms Tools.ShippingGen2Fit.ComposedNWF.toNW
#print axioms Tools.ShippingGen2Fit.composedNWRegsF_of_composedNWF
#print axioms Tools.ShippingGen2Fit.ComposedNWRegsF.toRegs
#print axioms Tools.ShippingGen2Fit.oneOut_lookup_callWire
#print axioms Tools.ShippingGen2Fit.oneOut_ksBoundedRun
#print axioms Tools.ShippingGen2Fit.binders_drop_at
#print axioms Tools.ShippingGen2Fit.composedNWRegsF_of_In
#print axioms Tools.ShippingGen2.machine_linked_callsServed1F
#print axioms Tools.ShippingSrm33.machine_ships_hierC_run

namespace Tests.Gen2.S4FitCheck
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineAuto

/-- CHECK P1: the projection's statement is the accepted `machine_linked_ofB` statement, as a type. -/
example : type_of% @Tools.ShippingGen2Fit.machine_linked_ofB_viaV =
    type_of% @Tools.ShippingMachineCompose.machine_linked_ofB := rfl

/-- CHECK P2: `ComposedHBF → ComposedNWF → ComposedNW` lands on `composedNWn_of_HB`'s conclusion type (ExtB:466-467),
with the same premises `hB`, `hcomb`. -/
example (n : Nat) {R : Nat → Sparkle.IR.AST.Module → Prop} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (hC : Tools.ShippingGen2Fit.ComposedHBF R declName d kD m dsn dom src ext extB)
    (hB : Tools.ShippingMachineDepthH.BoundH R declName d m dsn)
    (hcomb : Tools.ShippingMachineDepthH.kidsComb dsn.modules m.body = true) :
    Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m dsn dom src ext extB :=
  (Tools.ShippingGen2Fit.composedNWn_of_HBF n hC hB hcomb).toNW

/-- CHECK P3: the same chain agrees with stage A's route through `ComposedHB` (`toHB` then `composedNWn_of_HB`), as types. -/
example (n : Nat) {R : Nat → Sparkle.IR.AST.Module → Prop} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (hC : Tools.ShippingGen2Fit.ComposedHBF R declName d kD m dsn dom src ext extB)
    (hB : Tools.ShippingMachineDepthH.BoundH R declName d m dsn)
    (hcomb : Tools.ShippingMachineDepthH.kidsComb dsn.modules m.body = true) :
    Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m dsn dom src ext extB :=
  Tools.ShippingMachineDepthHR.composedNWn_of_HB n hC.toHB hB hcomb

/-- CHECK P4: `ComposedNWRegsF.toRegs` returns `ComposedNWRegs` on the same `P` (from `ComposedNWF` and from the
`KSBoundedIn` side). -/
example (n : Nat) {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (P : List String → Prop)
    (h : Tools.ShippingGen2Fit.ComposedNWF n declName d kD m dsn dom src ext extB)
    (hP : ∀ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs lets : List String),
      regs.Nodup → regs.length = d.ss.length →
      Tools.ShippingMachineEntry.MachineWired declName d.shape ids cache m dsn regs lets → P regs) :
    Tools.ShippingSrm28.ComposedNWRegs n declName d kD m dsn dom src ext extB P :=
  (Tools.ShippingGen2Fit.composedNWRegsF_of_composedNWF P h hP).toRegs

example (n : Nat) {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {P : List String → Prop} (Inv : Sparkle.IR.AST.Module → Tools.ShippingHierStateG.KT n → Prop)
    (h : Tools.ShippingSrm28.ComposedNWRegs n declName d kD m dsn dom src ext extB P)
    (hKSb : Tools.ShippingHierOptRun.KSBoundedIn (Tools.ShippingMachineLinked.childMap dsn.modules)
      (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap dsn.modules) n) m.body Inv)
    (hRI : Tools.ShippingMachineShipsHier.ResetImpliesInv (Tools.ShippingMachineShipsDepth.ResetNk n) Inv)
    (hnd : (Tools.ShippingHierState.instNames m.body).Nodup) :
    Tools.ShippingSrm28.ComposedNWRegs n declName d kD m dsn dom src ext extB P :=
  (Tools.ShippingGen2Fit.composedNWRegsF_of_In Inv h hKSb hRI hnd).toRegs

end Tests.Gen2.S4FitCheck
