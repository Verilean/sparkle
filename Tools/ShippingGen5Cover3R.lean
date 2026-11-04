import Tools.ShippingGen5Cover3
import Tools.ShippingGen5DataOfDims
import Tools.ShippingMachineShapeTail
set_option autoImplicit false
-- NOT BUILT (written in rt183 from base aab355f2). No sorry / axiom / native_decide.

/-! # C.CV-6: `rowB1_of_inv` without `hcb` (`scripts/gen5/CV6_FREEZE.md`)

`hcb` (the call binder of entry `k` sits at `kDOf d + k` and has the entry's kind) is derived from the facts of the
two functions that built `d`: `machineShape?_callBinder` (for the shape `sp`) and `dataOfAt` (`dataOfFrom_nIn`:
`d.nIn = (peel).length + sp.insts.length`), both applied to the SAME constant `dd` (so the same `packTupleInputs dd.value`
and the same `mixedGatePeel`). The `senv` / `allow` / `sym` / `params` of `machineShape?` and the `senv` / `lvl` of `dataOfAt`
are unrelated here (not needed). Not supplied: that `machineShape?` / `dataOfAt` are `some` on a run, `ShapeAgree`, `FullInv`. -/
namespace Tools.ShippingGen5Cover3R
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Sem Tools.ShippingGen5Cover
open Tools.ShippingMachineShapeUnfold Tools.ShippingGen5DataOf Tools.ShippingUnifiedSource

theorem hcb_of_data {sym : Bool} {params : List (String × Nat)} {dd : DefinitionVal} {senv senv' : StructEnv}
    {allow : Bool} {sp : MachineShape} {lvl : Lean.Expr → Nat} {d : MachineData}
    (hms : machineShape? sym params (.defnInfo dd) senv allow = some sp)
    (hd : dataOfAt lvl (.defnInfo dd) senv' sp = some d) :
    ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2 := by
  obtain ⟨bs, e, hpeel, hb⟩ := machineShape?_callBinder hms
  have hfrom : dataOfFrom lvl (.defnInfo dd) senv' sp
      (Sparkle.Compiler.MachTupleIn.packTupleInputs dd.value) Sparkle.Compiler.MachRawSurface.rootFloat = some d := by
    unfold dataOfAt at hd
    simpa [ConstantInfo.value?] using hd
  obtain ⟨p, hp, hn⟩ := dataOfFrom_nIn lvl hfrom
  obtain ⟨hsh, _⟩ := dataOfFrom_dims lvl hfrom
  rw [hpeel] at hp
  have hbs : bs.length = p.1.length := by
    have := Option.some.inj hp
    rw [← this]
  intro k hk
  have hk' : k < sp.insts.length := by rw [hsh] at hk; exact hk
  have hkd : kDOf d = bs.length := by
    unfold kDOf
    rw [hn, hsh]; omega
  have := hb k hk'
  rw [hkd, hsh]
  simp only [List.getElem?_map] at this ⊢
  rw [List.getElem?_map] at this
  simp only [hsh] at hk
  rw [List.getElem?_eq_getElem hk'] at this
  simpa [List.getElem?_map] using this

theorem rowB1_of_data {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st)
    {sym : Bool} {params : List (String × Nat)} {dd : DefinitionVal} {senv senv' : StructEnv}
    {allow : Bool} {sp : MachineShape} {lvl : Lean.Expr → Nat}
    (hms : machineShape? sym params (.defnInfo dd) senv allow = some sp)
    (hd : dataOfAt lvl (.defnInfo dd) senv' sp = some d) :
    ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain :=
  rowB1_of_inv hag hi (hcb_of_data hms hd)

end Tools.ShippingGen5Cover3R
