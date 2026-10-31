import Tools.ShippingGen5SemGenData
set_option autoImplicit false
-- NOT BUILT HERE (U9, scripts/gen5/DG_SEM_FREEZE_P9.md §2.1; freeze approved at 7f72f5c3. Not elaborated/built when written. Not connected to the real `dataOfAt_sound` / `initOk_of_ok` (they live on another branch, not imported). No sorry/axiom/native_decide.
/-! # DG-SEM U9 (scripts/gen5/DG_SEM_FREEZE_P9.md §2): `DataOfSound` ⇔ (3-conjunct soundness) ∧ (`initOk` from `ok`).

Pure logic over the P8 definition `DataOfSound`. Supplies no real `dataOf`/`initsOf`, no `dataOfAt_sound` connection (unproved here), no `GenWF`,
kit, run, M5 or FG. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Sparkle.Compiler.MachInstOrigin

theorem dataOfSound_of_parts
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss))
    (hf : ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧
      d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : ∀ d : MachineData, d.ok = true → d.initOk (initsOf d) = true) :
    DataOfSound dataOf initsOf :=
  fun E senv s d h =>
    ⟨(hf E senv s d h).1, (hf E senv s d h).2.1, (hf E senv s d h).2.2, hinit d (hf E senv s d h).2.1⟩

theorem dataOfSound_parts
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧
      d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) ∧
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d → d.initOk (initsOf d) = true) :=
  ⟨fun E senv s d h => ⟨(hs E senv s d h).1, (hs E senv s d h).2.1, (hs E senv s d h).2.2.1⟩,
   fun E senv s d h => (hs E senv s d h).2.2.2⟩

end Tools.ShippingGen5Sem
