import Tools.ShippingGen5ReaderTraceDirect2
import Tools.ShippingGen5DataOfDims
import Tools.ShippingGen5SemGen
set_option autoImplicit false
-- NOT BUILT (skeleton with sorry; to be filled by rt46). Freeze: scripts/gen5/RT_CLOSE_PLAN.md §2 C.CV-3 (no new premise).

/-! # RT C.CV-3: `kDOf d = nDeclOfCi ci`

The consumer side counts `nDecl` as `kDOf d = d.nIn - d.shape.insts.length`; the reach side uses `nDeclOfCi ci`.
`dataOfFront` sets `nIn := p.1.length + shape.insts.length` with `p` the `mixedGatePeel` of the packed entry value, so the two agree for a `defnInfo`. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Sem Tools.ShippingGen5DataOf Tools.ShippingMachineAuto

theorem kDOf_eq_nDeclOfCi_of_dataOfFrom (lvl : Lean.Expr → Nat) {dv : Lean.DefinitionVal} {senv : StructEnv}
    {s : MachineShape} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (h : dataOfFrom lvl (Lean.ConstantInfo.defnInfo dv) senv s
      (Sparkle.Compiler.MachTupleIn.packTupleInputs dv.value) fl = some d) :
    kDOf d = nDeclOfCi (Lean.ConstantInfo.defnInfo dv) := by
  sorry

theorem kDOf_eq_nDeclOfCi (lvl : Lean.Expr → Nat) {dv : Lean.DefinitionVal} {senv : StructEnv}
    {s : MachineShape} {d : MachineData}
    (h : dataOfAt lvl (Lean.ConstantInfo.defnInfo dv) senv s = some d) :
    kDOf d = nDeclOfCi (Lean.ConstantInfo.defnInfo dv) := by
  sorry

end Tools.ShippingGen5ReaderTrace
