import Tools.ShippingGen2OneOut
import Tools.ShippingGen3PortWidthsCore
set_option autoImplicit false
-- Built: g3dsc-1b840215 (clean snapshot, exit 0, standard axioms).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # U-CHILD-PORTTYS (step 1, U-CHILD-PORTW-P): the served child's argument-port widths, as standalone facts
(scripts/gen3/UCHILD_PORTTYS_TABLE.md, approved as a scoped change-site table; issue `sparkle-gen3-uchild-porttys`)

**S3 (applied):** `ChildPortWidths` now lives in Tools/ShippingGen2Defs.lean and is the first conjunct of `ChildShips`; N-A/N-B and
`argPortWidths_of_eq` live in Tools/ShippingGen3PortWidthsCore.lean (the local copies were deleted); P1-P4 below are thin
corollaries of the Core lemmas. The text that follows is the pre-S3 description.

**(pre-S3) No interface change.** `ChildPortWidths` was defined HERE, in an independent file; `ChildShips`, `ChildRunN`,
`SeqChildRunN`, `CombChildRunN`, `ShipsRes`, `T1Hyp`, `DataOkB`, FG, GEN2_DEFS and PkgCompat are unchanged. Nothing here
is a conjunct of `ChildShips` yet (that is U-CHILD-PORTW-DEF, after review).

* `ChildPortWidths q mc` (table §1, variant W): width-only. The right-hand side is `Pkg.portWidths q` (Adapt:80) by
  definition; written inline (no Adapt import).
* `argPortWidths_of_eq`: a producer-local `argPorts m = machPorts c ids cache bs` gives the widths (`machPorts_tys`,
  PortWidthsPure:142-147, projected to widths).
* `childPortWidths_of_tys`: the type form (candidate T) implies W.
* **N-A** `argPorts_noCalls_of_wired`: the argument ports of a call-free machine module are its declaration's
  (LeafSeq:58-67, factored). `argPorts_noCalls_post`: the same after the post-processing `hpost` (LeafSeq:70-74).
* **N-B** `childPortWidths_of_composedNW`: the C6 child module's port widths (C6:29-56 premises; C6:57-85 with
  `machPorts_tys` in place of `machPorts_length`).
* **P1-P4**: each producer's width fact from (a subset of) that producer's existing premises:
  P1 `leaf_childPortWidths` (Leaf:241-266), P2 `slotlessLeaf_childPortWidths` (SlotlessLeaf:283-), both through
  `noCalls_childPortWidths`; P3 `memParent_childPortWidths` (MemShips:39-), P4 `oneOut_childPortWidths`
  (OneOut:288-332), both through N-B. Premises of the producers that the width fact does not use are left out.

**Not claimed.** P1-P4 alone do NOT complete the FG supply (M3/S3/M4 producers, UCHILD table impact rows, UNCHECKED).
`ChildPortWidths` is the sufficient width guarantee used here; its minimality is not proved. The consumer's L6 / source
width equality stays in SRC-ARGW. This is the CHILD side; UARGW supplies the parent side, UARITY the index range; only
with SRC-ARGW's width equality for the same call do they reach `callArgsOkAt`.

**AUDIT.** Expected types: Tests/Gen3/ChildPortWidthsCheck.lean (mechanical, with mutants). Axioms: standard only. -/

namespace Tools.ShippingGen3ChildPortWidths
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

/-! ## P1-P4: each producer's width fact -/

variable {ι : Type} {dom : ι → DomainConfig}

/-- **P1** the register leaf (`leaf_childShips_of_LB`, Leaf:241-266; its premises `hL`, `hnoI`, `hok`, `hSS`,
`houtTy`, `htake`, `hpost`). -/
theorem leaf_childPortWidths (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    ChildPortWidths p b :=
  Tools.ShippingGen3PortWidthsCore.noCalls_childPortWidths p hL hnoI hok hSS houtTy htake hpost

/-- **P2** the slotless leaf (`slotlessLeaf_childShips_of_LB`, SlotlessLeaf:283-; its premises `hL`, `hnoI`, `hsl0`,
`hok`, `hSS`, `houtTy`, `htake`, `hpost`). -/
theorem slotlessLeaf_childPortWidths (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    ChildPortWidths p b :=
  Tools.ShippingGen3PortWidthsCore.noCalls_childPortWidths p hL hnoI hok hSS houtTy htake hpost

/-- **P3** memory parents (`memParent_childShips`, MemShips:39-; C8's `ComposedNW` then N-B). -/
theorem memParent_childPortWidths {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld}
    {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p) (hmo : MemOrigin p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hmd : ∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) (n : Nat) :
    ChildPortWidths p b := by
  obtain ⟨hok, hco, hslots, houtTy, hdomB⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := pkg_memComposedNW L p hA hfe hkD hdomB hIlen hSL hSlen hLlen hNIn hmd hmo n ran
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  exact Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW n houtTy (ok_outNameOk p.d hok) hsl hI0 hkD hIlen hSL hSlen hLlen hNIn
    hNW hpost

/-- **P4** one-output parents (`oneOut_childShips`, OneOut:288-332; `oneOut_composedNW` then N-B). -/
theorem oneOut_childPortWidths {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld} {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) :
    ChildPortWidths p b := by
  obtain ⟨hok, hco, hslots, houtTy, -⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := oneOut_composedNW L P p hdata hins hsimple hA ran hdec h n
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  exact Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW n houtTy (ok_outNameOk p.d hok) hsl hI0 hkD hIlen hSL hSlen hLlen hNIn
    hNW hpost

end Tools.ShippingGen3ChildPortWidths
