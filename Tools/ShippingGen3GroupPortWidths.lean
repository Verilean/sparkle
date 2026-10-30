import Tools.ShippingGen2GroupServed
import Tools.ShippingGen3PortWidthsCore
set_option autoImplicit false
-- Built: g3pw-ba9b9c82 (clean snapshot, exit 0, standard axioms).
-- (after `Tools.ShippingGen3PortWidthsCore`). No `sorry`, no `axiom`, no `native_decide`.

/-! # U-CHILD-PORTTYS: the S3 group producer's width fact (scripts/gen3/UCHILD_PORTTYS_TABLE.md rev3 §R3.4)

`group_childPortWidths`: under the premises of `group_childShips` (GroupServed:294-307) that the width fact uses,
`ChildPortWidths p b`. The proof is GroupServed:308-315 verbatim (the data rows and `hNW` from B4
`group_composedNW`), `hI0` as GroupServed:326-329, then ONE application of N-B
(`Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW`, the move-ready copy).

Premises of `group_childShips` left out (the width fact does not use them): `hext`, `hA`, `ran` (and `mctx`, `cctx`,
`w`). At the shared edit the same N-B term, with the same arguments, is the new first conjunct inside
`group_childShips`' proof (where all of them are already in scope: GroupServed:308-331), importing
`Tools.ShippingGen3PortWidthsCore` from GroupServed; this file then becomes a corollary or is deleted.

Scope: group parents WITH slots (`hsl`). Group slotless parents (S5 B3 `groupSl_childShips`) are NOT covered: N-B
needs `hsl` (rev3 §R3.1). -/

namespace Tools.ShippingGen2.GroupPortWidths
-- a sub-namespace (enclosing `Tools.ShippingGen2` names resolve) so that a later `group_childPortWidths` in
-- GroupServed cannot clash with this one
-- GroupServed:247-266 (the subset used here)
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildBndCore (dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The S3 group parent's port widths** (with slots): N-B on B4's `ComposedNW`. -/
theorem group_childPortWidths (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) :
    ChildPortWidths p b := by
  -- GroupServed:308-315 verbatim
  obtain ⟨hok, hco, hslots, houtTy, -⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := group_composedNW L P p hdata hfe hdec n h
  -- GroupServed:326-329 verbatim
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  -- the ONE N-B application (the term the shared edit puts into `group_childShips`)
  exact Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW n houtTy (ok_outNameOk p.d hok) hsl hI0
    hkD hIlen hSL hSlen hLlen hNIn hNW hpost

end Tools.ShippingGen2.GroupPortWidths
