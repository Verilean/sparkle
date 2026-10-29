import Tools.ShippingGen2DataBridge
import Tests.Compiler.ShippingMachineLinkedTest
set_option autoImplicit false

/-! # Controls for Tools/ShippingGen2DataBridge.lean (P-MEM row, WID strict row)

Built at 5d6ca626 (kjob g2db-5d6ca626: exit 0, standard axioms only). `callerL` is a data-level positive (no parent
package is exhibited); the memory shapes are synthetic.

Parent `callerL` (Tests/Compiler/ShippingMachineLinkedTest.lean:31; one call of `pickByteH`, `instFields = []`), callee
`pickByteH` as the `.comb` package (`pbhC` pattern of Tests/Gen2/SlotlessLeafInstance.lean). NO `callerL` package exists
in the tree (Tests/Gen2/OneOutCallField.lean:11-12 records the same), so the parent-side controls are stated (a) on
`callerL.machineData` directly, and (b) for EVERY parent package `p` with `p.d = callerL.machineData` and `p.kD = 1`
(premises; no such package is exhibited). `p.kD = 1` is the `nDecl` of the existing `callerL_strict`
(Tests/Compiler/OneOutCallerLTest.lean:271-278), re-decided here as `callerL_strict'` (that file is not imported).

Controls:
* positive WID, table form (`callerL_strict` table) and b1 form (`kidOutsP` through a concrete `P`, decided);
* negative WID: a width-mismatched table (width 16 against `pickByteH`'s 8-bit output) fails the row;
* vacuous WID: `P c = none` gives the empty table, which passes; CALL EXISTENCE is not given by the row (it comes from
  `hdec`/the supplier);
* positive/negative P-MEM rows on `callerL` and on synthetic shapes, including the out-of-range case that shows why
  `hord_of_row` takes `hk : k < insts.length`.

These show satisfiability/falsifiability of the rows on this data only; they are not coverage evidence and not a run. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen2.DataBridgeCheck
open Tools.ShippingGen2
open Tools.ShippingGen2DataBridge
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Sparkle.Core.Domain

abbrev U := fun _ : Unit => defaultDomain

/-- `pickByteH`'s comb package (as `Tests.Gen2.SlotlessLeafInstance.pbhC`). -/
noncomputable def pbhC : CombPkg Unit U :=
  { decl := ``pickByteH, d := pickByteH.machineData, kD := pickByteH.machineData.bsIn.length,
    inits := pickByteH.machineInits, src := pickByteH.machineSource,
    facts := ⟨pickByteH.machine_ok, pickByteH.machine_body, pickByteH.machine_inits, pickByteH.machine_next,
      pickByteH.machine_result⟩ }

noncomputable abbrev pbhPkg : Pkg Unit U := .comb pbhC

/-- A concrete assignment: `pickByteH` ↦ its comb package, everything else ↦ none. -/
noncomputable def PL : Pkgs Unit U := fun c => if c == ``pickByteH then some pbhPkg else none

/-- The empty assignment. -/
def PN : Pkgs Unit U := fun _ => none

/-! ## Data facts of `callerL` -/

theorem callerL_noFields' : callerL.machineData.shape.instFields = [] := by
  first | rfl | decide | decide +kernel

theorem callerL_insts_len : callerL.machineData.shape.insts.length = 1 := by
  first | rfl | decide | decide +kernel

set_option maxRecDepth 100000 in
/-- The existing `callerL_strict` (OneOutCallerLTest.lean:271-278), re-decided. -/
theorem callerL_strict' :
    Tools.ShippingCallWidthsStrict.callWidthsStrict callerL.machineData 1
      (fun _ => pickByteH.machineData.shape.layout.outs) = true := by
  first | decide | decide +kernel

/-! ## WID, positive -/

/-- **Positive (table form)**: every parent package with `callerL`'s data gets `OneOutWidth` under `PL`. -/
theorem callerL_oneOutWidth (p : Pkg Unit U) (hp : p.d = callerL.machineData) (hkD : p.kD = 1) :
    ∀ k, OneOutWidth PL p k := by
  apply oneOutWidth_of_strict PL p (fun _ => pickByteH.machineData.shape.layout.outs)
  · rw [hp, hkD]; exact callerL_strict'
  · rw [hp]; exact callerL_noFields'
  · intro k hk q hq
    have hq' : (if ((p.d.shape.insts[k]).1 == ``pickByteH) = true then some pbhPkg else none) = some q := hq
    by_cases hc : ((p.d.shape.insts[k]).1 == ``pickByteH) = true
    · rw [if_pos hc] at hq'
      obtain rfl := Option.some.inj hq'
      rfl
    · rw [if_neg hc] at hq'
      cases hq'

set_option maxRecDepth 100000 in
/-- The b1 row decided through `PL` (the kernel reduces `PL ``pickByteH` to the package). -/
theorem callerL_strictPL :
    Tools.ShippingCallWidthsStrict.callWidthsStrict callerL.machineData 1
      (fun k => ((((callerL.machineData.shape.insts.map (·.1))[k]?).bind PL).map
        (fun q => q.d.shape.layout.outs)).getD []) = true := by
  first | decide | decide +kernel

/-- **Positive (b1 form)**: the same conclusion through `kidOutsP` and `oneOutWidth_of_strictP`. -/
theorem callerL_oneOutWidthP (p : Pkg Unit U) (hp : p.d = callerL.machineData) (hkD : p.kD = 1) :
    ∀ k, OneOutWidth PL p k := by
  apply oneOutWidth_of_strictP PL p
  · have e : kidOutsP PL p = fun k => ((((callerL.machineData.shape.insts.map (·.1))[k]?).bind PL).map
        (fun q => q.d.shape.layout.outs)).getD [] := by
      funext k
      unfold kidOutsP
      rw [hp]
    rw [e, hp, hkD]
    exact callerL_strictPL
  · rw [hp]; exact callerL_noFields'

/-! ## WID, negative: a width-mismatched table -/

/-- A 16-bit output (the call's binder is 8 bits wide). -/
def badOut : Sparkle.IR.Machine.OutField :=
  { name := "out", lo := 0, width := 16, ty := Sparkle.IR.Type.HWType.bitVector 16 }

set_option maxRecDepth 100000 in
/-- **Negative**: the strict row is FALSE for the mismatched table. -/
theorem callerL_strict_bad :
    Tools.ShippingCallWidthsStrict.callWidthsStrict callerL.machineData 1 (fun _ => [badOut]) = false := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
/-- The width the row compares really differs (so the row is not vacuous on this data). -/
theorem callerL_bad_width :
    (callerL.machineData.shape.binders[1 + 0]?).map
      (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) ≠ some badOut.ty.bitWidth := by
  first | decide | decide +kernel

/-! ## WID, vacuous: `P c = none` -/

/-- With no package for any callee the table is empty and the row passes, for EVERY parent package: the row does not
assert that the call is served (existence is `hdec`'s / the supplier's job). -/
theorem empty_table_passes (p : Pkg Unit U) :
    Tools.ShippingCallWidthsStrict.callWidthsStrict p.d p.kD (kidOutsP PN p) = true := by
  rw [kidOutsP_allNone PN p (fun _ => rfl)]
  exact callWidthsStrict_empty p.d p.kD

theorem oneOutWidth_PN (p : Pkg Unit U) (hf : p.d.shape.instFields = []) : ∀ k, OneOutWidth PN p k :=
  oneOutWidth_of_strictP PN p (empty_table_passes p) hf

/-! ## P-MEM rows -/

set_option maxRecDepth 100000 in
theorem callerL_row : noMemRowS callerL.machineData.shape = true := by
  first | decide | decide +kernel

/-- **Positive**: the origin of `callerL`'s entry 0 builds no child, for every package with `callerL`'s data. -/
theorem callerL_hord (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    (p.d.shape.instOrigins.getD 0 Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none := by
  have hrow : OneOutNoMemRow p = true := by
    rw [OneOutNoMemRow_eq, hp]; exact callerL_row
  have hf : p.d.shape.instFields = [] := by rw [hp]; exact callerL_noFields'
  have hk : 0 < p.d.shape.insts.length := by rw [hp, callerL_insts_len]; decide
  exact hord_of_row hrow hf 0 hk

/-- Synthetic shape: one call entry with a MEMORY origin and no field list. -/
def memShape0 : Sparkle.Compiler.Elab.MachineShape :=
  { binders := [], body := .bvar 0,
    layout := { slots := [], outs := [], resetKind := .synchronous },
    insts := [(`m, [], .bits 8)], instOrigins := [.mem false 4 8] }

/-- **Negative**: the row is FALSE on it. -/
theorem memShape0_row : noMemRowS memShape0 = false := by
  first | decide | decide +kernel

/-- Implication form: the same entry WITH a field list (a memory parent) passes. -/
def memShape1 : Sparkle.Compiler.Elab.MachineShape := { memShape0 with instFields := ["out"] }

theorem memShape1_row : noMemRowS memShape1 = true := by
  first | decide | decide +kernel

/-- Out of range: an origin beyond `insts` is not covered by `instTagged`; the row passes but the origin at `0` builds a
child. So `hord_of_row` is stated for `k < insts.length` only. -/
def memShapeX : Sparkle.Compiler.Elab.MachineShape := { memShape0 with insts := [] }

theorem memShapeX_row : noMemRowS memShapeX = true := by
  first | decide | decide +kernel

theorem memShapeX_outOfRange :
    (memShapeX.instOrigins.getD 0 Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child?.isSome = true := by
  first | rfl | decide

#print axioms Tools.ShippingGen2DataBridge.hord_of_rowS
#print axioms Tools.ShippingGen2DataBridge.hord_of_row
#print axioms Tools.ShippingGen2DataBridge.kidOutsP_eq
#print axioms Tools.ShippingGen2DataBridge.kidOutsP_none
#print axioms Tools.ShippingGen2DataBridge.kidOutsP_allNone
#print axioms Tools.ShippingGen2DataBridge.callWidthsStrict_empty
#print axioms Tools.ShippingGen2DataBridge.oneOutWidth_of_strict
#print axioms Tools.ShippingGen2DataBridge.oneOutWidth_of_strictP
#print axioms callerL_strict'
#print axioms callerL_oneOutWidth
#print axioms callerL_strictPL
#print axioms callerL_oneOutWidthP
#print axioms callerL_strict_bad
#print axioms callerL_bad_width
#print axioms empty_table_passes
#print axioms oneOutWidth_PN
#print axioms callerL_row
#print axioms callerL_hord
#print axioms memShape0_row
#print axioms memShape1_row
#print axioms memShapeX_row
#print axioms memShapeX_outOfRange

end Tests.Gen2.DataBridgeCheck
