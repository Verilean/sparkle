import Tools.ShippingMachineShipsHier

/-! # A composed theorem read under an endpoint's transport (round par/b-17)

A TRANSPORTED endpoint (`Tools/ShippingMachineCommand.lean` 2554–2576, READ):
when the value the endpoint is proved for is not the declaration's own
(sign operations normalised, nested `Signal.loop`s fused into one), the
generator adds two observation constants

    f.machineSource      -- the observations of the REWRITTEN value
    f.machineSourceDecl  -- the observations of the declaration applied

and the kernel-checked equation

    heq : f.machineSourceDecl = f.machineSource

(`funext` of `congrArg` of the rewriting's own equation), and rewrites the
endpoint's statement along it (`Eq.mpr (congrArg motive heq)`). Every
theorem made from the endpoint repeats the rewriting on its own statement
(`Tools/ShippingMachineMemCommand.lean` 93–98, `ShippingMachineSeqCommand`
367–372, `ShippingMachineSeqCommandR` 299–304): a `kabstract` of the source
constant in the statement.

The transport is therefore an EQUATION BETWEEN TWO SOURCE FUNCTIONS — not a
renaming of the module, not a `quantModule`, not another head. The reader's
data (`f.machineData`), the run, the reflection, the closing and the wired
endpoint do not mention the source being rewritten; the source occurs once,
as the `src` argument of the composed statement `ComposedG`.

`composedG_src` is that one step as a lemma, so that a generator can state
the composed theorem for the declaration's source without abstracting a
statement: `ComposedG … src …` and `src' = src` give `ComposedG … src' …`.
Nothing else is in this file.

WRITTEN, NOT BUILT (par/b-17). -/
namespace Tools.ShippingMemTransport
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingMachineShipsHier
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- **A composed statement along an equation of its source**: the composed
theorem of the rewritten source `src` is the composed theorem of any source
`src'` equal to it. (`H` first: its statement fixes every implicit argument;
`heq` is then only checked against them.) -/
theorem composedG_src {σ : Type} {KS : Design → KStep σ}
    {Reset : Sparkle.IR.AST.Module → Design → (String → σ) → Prop}
    {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src src' : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (H : ComposedG KS Reset declName d kD m dsn dom src ext extB) (heq : src' = src) :
    ComposedG KS Reset declName d kD m dsn dom src' ext extB := by
  subst heq
  exact H

end Tools.ShippingMemTransport
