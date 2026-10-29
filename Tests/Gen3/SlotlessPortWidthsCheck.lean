import Tools.ShippingGen3SlotlessPortWidths
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built: g3nc-ce4c32a4 (clean snapshot, exit 0, standard axioms). No `sorry`, no `axiom`, no `native_decide`.

/-! # U-CHILD-PORTTYS N-C checks (scripts/gen3/UCHILD_PORTTYS_TABLE.md rev3 §R3.1)

1. **Expected types.** N-C `childPortWidths_of_composedNW_sl` and its corollaries `oneOutSl_childPortWidths` (B2) /
   `groupSl_childPortWidths` (B3) are compared MECHANICALLY (`Tests.Gen3.ExpectedType.checkExpected`, binder by
   binder) against independent `Expected…` statements transcribed from the §R3.1 text (the corollaries' section
   variables `ι`, `dom`, `mref`, `cref` written first, as in Tests/Gen3/PortWidthsPrepCheck.lean `ExpectedGroup`).
2. **Mutants (each must be REJECTED):**
   * N-C against N-B itself (`Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW`, `hsl : slots ≠ []`):
     N-C is not N-B renamed;
   * N-C concluding over the UNFILTERED `d.bsIn.take kD` (domain binders kept);
   * N-C concluding over all of `d.bsIn` (the call ports included);
   * B2 corollary without `hsl0`; B2 corollary with an extra compat premise `hpw : ChildPortWidths p b`
     (no compat premise on the producers); B2 corollary concluding the TYPE form;
   * B3 corollary without `hsl0`; B3 corollary with `hsimple : instFields = []` in place of `hfe`; B3 corollary with
     the compat premise `hpw`.
   Mutant rejection is signature/defeq rejection (`checkMutant`), not a proof that each mutant is false.
3. Axioms: `checkAxioms` (standard only) and `#print axioms`. -/

namespace Tests.Gen3.SlotlessPortWidthsCheck
open Tests.Gen3.ExpectedType

section Expected
-- the opens of Tools/ShippingGen3ChildPortWidths.lean (Tests/Gen3/ChildPortWidthsCheck.lean)
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingGen2
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (dv)

/-- §R3.1 N-C, transcribed. -/
def ExpectedNC : Prop :=
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

/-- §R3.1 `oneOutSl_childPortWidths`, transcribed. -/
def ExpectedOneOutSl : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld} {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat),
    Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b

/-- §R3.1 `groupSl_childPortWidths`, transcribed. -/
def ExpectedGroupSl : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc),
    Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b

/-! ### Mutants (each must be REJECTED) -/

/-- N-C concluding over the UNFILTERED `d.bsIn.take kD` (domain binders kept). -/
def MutNCunfiltered : Prop :=
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
      (d.bsIn.take kD).map (fun b => (kindTy b.2).bitWidth)

/-- N-C concluding over ALL of `d.bsIn` (the call ports included). -/
def MutNCallIn : Prop :=
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
      (d.bsIn.filter (fun b => b.2 != .domain)).map (fun b => (kindTy b.2).bitWidth)

/-- B2 corollary without `hsl0`. -/
def MutOneOutSlNoHsl0 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld} {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat),
    Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b

/-- B2 corollary with the compat premise `hpw` (NOT taken by the producers). -/
def MutOneOutSlHpw : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld} {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) (hpw : Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b),
    Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b

/-- B2 corollary concluding the TYPE form (candidate T; stronger, not what is proved). -/
def MutOneOutSlTys : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld} {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat),
    (argPorts b).map (fun x => x.ty) = p.ports.map (fun b => kindTy b.2)

/-- B3 corollary without `hsl0`. -/
def MutGroupSlNoHsl0 : Prop :=
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

/-- B3 corollary with `hsimple : instFields = []` in place of `hfe` (the one-output case, not the group case). -/
def MutGroupSlSimple : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc),
    Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b

/-- B3 corollary with the compat premise `hpw` (NOT taken by the producers). -/
def MutGroupSlHpw : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hpw : Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b),
    Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b

end Expected

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- 1. expected types (§R3.1 text)
  checkExpected ``Tools.ShippingGen3SlotlessPortWidths.childPortWidths_of_composedNW_sl ``ExpectedNC
  checkExpected ``Tools.ShippingGen2.SlotlessPortWidths.oneOutSl_childPortWidths ``ExpectedOneOutSl
  checkExpected ``Tools.ShippingGen2.SlotlessPortWidths.groupSl_childPortWidths ``ExpectedGroupSl
  -- 2. mutants
  checkMutant ``Tools.ShippingGen3SlotlessPortWidths.childPortWidths_of_composedNW_sl
    ``Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW
  checkMutant ``Tools.ShippingGen3SlotlessPortWidths.childPortWidths_of_composedNW_sl ``MutNCunfiltered
  checkMutant ``Tools.ShippingGen3SlotlessPortWidths.childPortWidths_of_composedNW_sl ``MutNCallIn
  checkMutant ``Tools.ShippingGen2.SlotlessPortWidths.oneOutSl_childPortWidths ``MutOneOutSlNoHsl0
  checkMutant ``Tools.ShippingGen2.SlotlessPortWidths.oneOutSl_childPortWidths ``MutOneOutSlHpw
  checkMutant ``Tools.ShippingGen2.SlotlessPortWidths.oneOutSl_childPortWidths ``MutOneOutSlTys
  checkMutant ``Tools.ShippingGen2.SlotlessPortWidths.groupSl_childPortWidths ``MutGroupSlNoHsl0
  checkMutant ``Tools.ShippingGen2.SlotlessPortWidths.groupSl_childPortWidths ``MutGroupSlSimple
  checkMutant ``Tools.ShippingGen2.SlotlessPortWidths.groupSl_childPortWidths ``MutGroupSlHpw

/-! ## Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingGen3SlotlessPortWidths.childPortWidths_of_composedNW_sl,
      ``Tools.ShippingGen2.SlotlessPortWidths.oneOutSl_childPortWidths,
      ``Tools.ShippingGen2.SlotlessPortWidths.groupSl_childPortWidths] do
    checkAxioms n

#print axioms Tools.ShippingGen3SlotlessPortWidths.childPortWidths_of_composedNW_sl
#print axioms Tools.ShippingGen2.SlotlessPortWidths.oneOutSl_childPortWidths
#print axioms Tools.ShippingGen2.SlotlessPortWidths.groupSl_childPortWidths

end Tests.Gen3.SlotlessPortWidthsCheck
