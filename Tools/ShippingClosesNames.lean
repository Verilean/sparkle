import Tools.ShippingCallsKidsD
import Tools.ShippingNameDischarge
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # The closing theorems with their name hypotheses stated about DECLARATIONS (round par/b-29)

WRITTEN, NOT BUILT. Not used by any generator in this round.

The three built closing theorems

* `Tools.ShippingCallsGate.machineClosesAt_of_gateKids` (one-output calls),
* `Tools.ShippingCallsSeqKids.machineClosesAt_of_seqKids` (the general
  closing over children without calls),
* `Tools.ShippingCallsKidsD.machineClosesAt_of_kidsD` (children with designs
  of their own)

ask `hsep`, `hparent` (and the last one `hparentD`, `hselfD`, `hdisjD`) about
module-name STRINGS. Here each is restated with

* `hsep` GONE (`ofDecl` is injective: `names_inj`);
* `hparent` as `∀ c ∈ d.shape.insts, c.1 ≠ declName` — no call entry is a
  call of the parent declaration (a statement about the reader's data,
  decidable on `Name`s);
* for the deep closing, the descendants' table as DECLARATIONS
  (`declsK : Nat → List Name`; the theorem is used at
  `namesK k := (declsK k).map ofDecl`, which is what the generators pass),
  and `hparentD` / `hselfD` / `hdisjD` about membership of declarations.

`hfresh` is unchanged in all three: an output port against an instance
name — not a declaration-name condition.

`hdisjD` in its declaration form is still FALSE for a parent whose different
callees share a descendant declaration (`mixDeep`); `machineClosesAt_of_kidsDN`
does not cover it any more than `machineClosesAt_of_kidsD` did.

The proofs are one application each; every other hypothesis is passed on
verbatim. -/
namespace Tools.ShippingClosesNames
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingCallsGate Tools.ShippingCallsRunG Tools.ShippingSeqChildIface
open Tools.ShippingInstStmtG Tools.ShippingCallsStmtsG Tools.ShippingDesignWith
open Tools.ShippingDesignWithG Tools.ShippingCallsSeqKids
open Tools.ShippingCallsKidsD
open Tools.ShippingNameDischarge (names_inj parent_ne parentD_of selfD_of disjD_of)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`machineClosesAt_of_gateKids` without `hsep`, `hparent` about
declarations.** -/
theorem machineClosesAt_of_gateKidsN {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true)
    (nk : Nat → Nat)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y → ChildIface (d.shape.insts[k]).1 (nk k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hparentN : ∀ c ∈ d.shape.insts, c.1 ≠ declName)
    (hfresh : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{k}_{(Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1)}") :
    MachineClosesAt mctx mref cctx cref declName d.shape :=
  machineClosesAt_of_gateKids (nDecl := nDecl) d ok hbody halias hS nk hnomem hkid hargsN
    (names_inj _) (parent_ne _ _ hparentN) hfresh

/-- **`machineClosesAt_of_seqKids` without `hsep`, `hparent` about
declarations.** -/
theorem machineClosesAt_of_seqKidsN {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (nk : Nat → Nat) (outsK : Nat → List String)
    (hnotag : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ChildIfaceG (d.shape.insts[k]).1 (nk k) (outsK k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsK k)
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hparentN : ∀ c ∈ d.shape.insts, c.1 ≠ declName)
    (hfresh : ∀ (gi : Nat), ∀ c ∈ d.shape.insts, ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{(Sparkle.IR.ModuleName.ofDecl c.1)}") :
    MachineClosesAt mctx mref cctx cref declName d.shape :=
  machineClosesAt_of_seqKids (nDecl := nDecl) d ok hbody halias hC hslots hdomB hfne nk outsK
    hnotag hkid hargsN hfieldOut hfieldsNd
    (names_inj _) (parent_ne _ _ hparentN) hfresh

/-- **`machineClosesAt_of_kidsD` with the descendants as declarations**:
`hsep` gone; `hparent`, `hparentD`, `hselfD`, `hdisjD` about `Lean.Name`s. -/
theorem machineClosesAt_of_kidsDN {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (nk : Nat → Nat) (outsK : Nat → List String) (declsK : Nat → List Name)
    (hnotag : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ChildIfaceD (d.shape.insts[k]).1 (nk k) (outsK k)
        ((declsK k).map fun n => Sparkle.IR.ModuleName.ofDecl n) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsK k)
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hparentN : ∀ c ∈ d.shape.insts, c.1 ≠ declName)
    (hfresh : ∀ (gi : Nat), ∀ c ∈ d.shape.insts, ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{(Sparkle.IR.ModuleName.ofDecl c.1)}")
    -- the parent is no descendant of a call entry
    (hparentDN : ∀ (k : Nat), k < d.shape.insts.length → declName ∉ declsK k)
    -- a callee is no descendant of itself
    (hselfDN : ∀ (k : Nat) (hk : k < d.shape.insts.length), (d.shape.insts[k]).1 ∉ declsK k)
    -- two different callees: the first is no descendant of the second, and
    -- they share no descendant (FALSE for `mixDeep`)
    (hdisjDN : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 ≠ (d.shape.insts[k']).1 →
      (d.shape.insts[k]).1 ∉ declsK k' ∧ ∀ a ∈ declsK k, a ∉ declsK k') :
    MachineClosesAt mctx mref cctx cref declName d.shape :=
  machineClosesAt_of_kidsD (nDecl := nDecl) d ok hbody halias hC hslots hdomB hfne nk outsK
    (fun k => (declsK k).map fun n => Sparkle.IR.ModuleName.ofDecl n)
    hnotag hkid hargsN hfieldOut hfieldsNd
    (names_inj _) (parent_ne _ _ hparentN) hfresh
    (parentD_of _ declName declsK hparentDN)
    (selfD_of d.shape.insts declsK hselfDN)
    (disjD_of d.shape.insts declsK hdisjDN)

end Tools.ShippingClosesNames
