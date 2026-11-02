import Tools.ShippingGen5ReaderTraceDirect2
import Tools.ShippingGen5DataOfDims
import Tools.ShippingGen5SemGen
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceKDOf, exit 0) on the tree of 55c9331b365c87905bc648b6c5be1cd0d5e727a8 (Lean content identical; this header is comment-only). Clean build is the coder's. No sorry / axiom / native_decide in source. Freeze: scripts/gen5/RT_CLOSE_PLAN.md §2 C.CV-3 (no new premise).

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
  obtain ⟨p, hp, hn⟩ := dataOfFrom_nIn lvl h
  have e : nDeclOfCi (Lean.ConstantInfo.defnInfo dv) = p.1.length := by
    simp only [nDeclOfCi, hp]; rfl
  obtain ⟨hs, -⟩ := dataOfFrom_dims lvl h
  unfold kDOf; rw [hs]; omega

theorem kDOf_eq_nDeclOfCi (lvl : Lean.Expr → Nat) {dv : Lean.DefinitionVal} {senv : StructEnv}
    {s : MachineShape} {d : MachineData}
    (h : dataOfAt lvl (Lean.ConstantInfo.defnInfo dv) senv s = some d) :
    kDOf d = nDeclOfCi (Lean.ConstantInfo.defnInfo dv) := by
  exact kDOf_eq_nDeclOfCi_of_dataOfFrom lvl (by simpa [dataOfAt, Lean.ConstantInfo.value?] using h)

end Tools.ShippingGen5ReaderTrace
