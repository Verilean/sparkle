import Tools.ShippingGen2Loop
set_option autoImplicit false

/-! # `LoopFacts` restricted from `(DomainConfig, id)` to `(Unit, fun _ => D₀)` (the loop analogue of
`genFacts_restrict`, Tools/ShippingGen2CallDec.lean). Every field is a `∀ i` instantiated at `D₀`. -/
namespace Tools.ShippingGen2Loop
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote (tys)
open Sparkle.Core (HList)

theorem loopFacts_restrict (d : MachineData) {α : DomainConfig → Type} [inst : ∀ i, Inhabited (α i)]
    {ρ : DomainConfig → Type}
    {σ : (i : DomainConfig) → α i → HList (tys d.ss)}
    {inits : HList (tys d.ss)}
    {f : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (α i) → Signal i (α i)}
    {res : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (α i) → ρ i}
    {obsR : (i : DomainConfig) → ρ i → List (Nat → Nat)}
    {ext : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (α i) → (j : Nat) → (n : Nat) → Signal i (BitVec n)}
    {extB : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (α i) → Nat → Signal i Bool}
    {src : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      List (Nat → Nat)}
    (D₀ : DomainConfig)
    (h : @LoopFacts d DomainConfig (fun i => i) α inst ρ σ inits f res obsR ext extB src) :
    @LoopFacts d Unit (fun _ => D₀) (fun _ => α D₀) (fun _ => inst D₀) (fun _ => ρ D₀) (fun _ => σ D₀) inits
      (fun _ => f D₀) (fun _ => res D₀) (fun _ => obsR D₀) (fun _ => ext D₀) (fun _ => extB D₀) (fun _ => src D₀) :=
  ⟨h.ok, h.hbody, h.hinit, fun _ => h.h0 D₀, fun _ => h.writes D₀, fun _ => h.hres D₀, fun _ => h.hsrc D₀,
   fun _ => h.hcausal D₀⟩

end Tools.ShippingGen2Loop
