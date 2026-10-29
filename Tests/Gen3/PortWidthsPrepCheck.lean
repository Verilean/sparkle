import Tools.ShippingGen3GroupPortWidths
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built: g3pw-ba9b9c82 (clean snapshot, exit 0, standard axioms).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # U-CHILD-PORTTYS shared-edit preparation checks (scripts/gen3/UCHILD_PORTTYS_TABLE.md rev3 §R3.4)

1. **Move-ready copy = built copy.** Each lemma of Tools/ShippingGen3PortWidthsCore.lean whose statement is unchanged
   (`argPortWidths_of_eq`, N-A `argPorts_noCalls_of_wired`, `argPorts_noCalls_post`, N-B
   `childPortWidths_of_composedNW`) is compared MECHANICALLY with the built one in Tools/ShippingGen3ChildPortWidths.lean
   (g3dsc-1b840215) by `checkExpected` (binder by binder).
2. **Expected types.** The two lemmas whose conclusion became `ChildPortWidths`' body (`childPortWidths_of_tys`,
   `noCalls_childPortWidths`) and `group_childPortWidths` against independent `Expected…` statements.
3. **Mutants (each must be REJECTED):** N-B with `hsl0 : slots = []` (the S5 case it does NOT cover); the core
   `noCalls_childPortWidths` concluding over the unfiltered `bsIn`; `group_childPortWidths` without `hsl` (group
   slotless parents not covered); `group_childPortWidths` concluding the TYPE form.
4. Axioms: `checkAxioms` (standard only) and `#print axioms`. -/

namespace Tests.Gen3.PortWidthsPrepCheck
open Tests.Gen3.ExpectedType

section Expected
-- the opens of Tools/ShippingGen3PortWidthsCore.lean
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingGen2

def ExpectedOfTysCore : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (mc : Module)
    (h : (argPorts mc).map (fun p => p.ty) = q.ports.map (fun b => kindTy b.2)),
    (argPorts mc).map (fun x => x.ty.bitWidth) = q.ports.map (fun b => (kindTy b.2).bitWidth)

def ExpectedNoCallsCore : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)),
    (argPorts b).map (fun x => x.ty.bitWidth) = p.ports.map (fun b => (kindTy b.2).bitWidth)

def ExpectedGroup : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc),
    Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b

/-! ### Mutants (each must be REJECTED) -/

/-- N-B in the S5 case (`slots = []`): NOT what is proved (rev3 §R3.1). -/
def MutNBsl : Prop :=
  ∀ (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl0 : d.shape.layout.slots = []) (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {mc raw : Module} {D : Design}
    (hcomp : Tools.ShippingMachineDepthRun.ComposedNW n c d kD raw D dom src ext extB)
    (hpost : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)),
    (argPorts mc).map (fun p => p.ty.bitWidth) =
      ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).map (fun b => (kindTy b.2).bitWidth)

/-- The core call-free lemma over the UNFILTERED, untruncated binder list. -/
def MutNoCallsBsIn : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)),
    (argPorts b).map (fun x => x.ty.bitWidth) = p.d.bsIn.map (fun b => (kindTy b.2).bitWidth)

/-- The group lemma without `hsl` (group slotless parents NOT covered). -/
def MutGroupNoHsl : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc),
    Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b

/-- The group lemma concluding the TYPE form (candidate T; stronger, not what is proved). -/
def MutGroupTys : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc),
    (argPorts b).map (fun x => x.ty) = p.ports.map (fun b => kindTy b.2)

end Expected

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- 1. the move-ready copies against the built ones
  checkExpected ``Tools.ShippingGen3PortWidthsCore.argPortWidths_of_eq
    ``Tools.ShippingGen3ChildPortWidths.argPortWidths_of_eq
  checkExpected ``Tools.ShippingGen3PortWidthsCore.argPorts_noCalls_of_wired
    ``Tools.ShippingGen3ChildPortWidths.argPorts_noCalls_of_wired
  checkExpected ``Tools.ShippingGen3PortWidthsCore.argPorts_noCalls_post
    ``Tools.ShippingGen3ChildPortWidths.argPorts_noCalls_post
  checkExpected ``Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW
    ``Tools.ShippingGen3ChildPortWidths.childPortWidths_of_composedNW
  -- 2. expected types
  checkExpected ``Tools.ShippingGen3PortWidthsCore.childPortWidths_of_tys ``ExpectedOfTysCore
  checkExpected ``Tools.ShippingGen3PortWidthsCore.noCalls_childPortWidths ``ExpectedNoCallsCore
  checkExpected ``Tools.ShippingGen2.GroupPortWidths.group_childPortWidths ``ExpectedGroup
  -- 3. mutants
  checkMutant ``Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW ``MutNBsl
  checkMutant ``Tools.ShippingGen3PortWidthsCore.noCalls_childPortWidths ``MutNoCallsBsIn
  checkMutant ``Tools.ShippingGen2.GroupPortWidths.group_childPortWidths ``MutGroupNoHsl
  checkMutant ``Tools.ShippingGen2.GroupPortWidths.group_childPortWidths ``MutGroupTys

/-! ## Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingGen3PortWidthsCore.argPortWidths_of_eq,
      ``Tools.ShippingGen3PortWidthsCore.childPortWidths_of_tys,
      ``Tools.ShippingGen3PortWidthsCore.argPorts_noCalls_of_wired,
      ``Tools.ShippingGen3PortWidthsCore.argPorts_noCalls_post,
      ``Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW,
      ``Tools.ShippingGen3PortWidthsCore.noCalls_childPortWidths,
      ``Tools.ShippingGen2.GroupPortWidths.group_childPortWidths] do
    checkAxioms n

#print axioms Tools.ShippingGen3PortWidthsCore.argPortWidths_of_eq
#print axioms Tools.ShippingGen3PortWidthsCore.childPortWidths_of_tys
#print axioms Tools.ShippingGen3PortWidthsCore.argPorts_noCalls_of_wired
#print axioms Tools.ShippingGen3PortWidthsCore.argPorts_noCalls_post
#print axioms Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW
#print axioms Tools.ShippingGen3PortWidthsCore.noCalls_childPortWidths
#print axioms Tools.ShippingGen2.GroupPortWidths.group_childPortWidths

end Tests.Gen3.PortWidthsPrepCheck
