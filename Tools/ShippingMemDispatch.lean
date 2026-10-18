import Tools.ShippingReaderFuelR1
import Tools.ShippingReaderFuelShape

/-! # Memory placeholder names: the collision, and a GUARDED model of the reader

BUILT on poc 3a1938a3 (run `md1`, exit 0; integrator; reviewer 2026-10-18 item 3).
No `sorry`, no axiom, no `native_decide`. Nothing under `Sparkle/` changed.

## The finding (measured, `Tests/Compiler/MemNameCollisionProbe.lean`, runs `mc2`, `mc4`)

A memory call is read as a call entry named `memChildName combo aw dw`
(`SparkleMem.{combo|sync}.<aw>.<dw>`, two NUMERIC name components). The
general closing `closeInstsGM` (Elab.lean 5213–5217) builds the child of EVERY
entry whose name decodes with `memChild?` as the memory module, without looking
at the environment. Source syntax cannot write a numeric name component, but
`addDecl` can. With `fakeSrc` (memory interface, output `wd + 1`, NOT a memory)
copied under `SparkleMem.sync.4.8` and tagged `@[hardware_module]`:

* `collParent` (a combinational memory AND a call of that declaration, so
  `instFields ≠ []`, closed by `closeInstsGM`): the certified route emits
  instances `[SparkleMem_combo_4_8, SparkleMem_sync_4_8]` — the call of the
  declaration became a SYNCHRONOUS MEMORY. MISCOMPILE. The legacy route
  (`certifiedFrontEnd := false`) instantiates the declaration's own module.
* `collPlain` (only that call, `instFields = []`, closed by `closeInstsM`, which
  synthesises every entry): correct on both routes.
* `MemR1` HOLDS in the miscompiled example (the declaration's result is
  `.bits 8 = .bits dw`), so `MemR1` is NOT the property that guards the
  emitted child: the fault is the name-keyed dispatch (and the name-keyed
  call deduplication of `machInstance`, which can merge a memory call and a
  call of the declaration with the same argument lets into ONE entry).
* `MemR1 (structEnv env)` is FALSE in a real environment: `SparkleMem.sync.4.16`
  declared with result `BitVec 8` (`.bits 8 ≠ .bits 16`), printed by the probe.
  Abstractly: `not_memR1_all`.

## What this file proves (about a MODEL; the compiler is unchanged)

`machineShapeG?` = `machineShape?` followed by the guard `shapeClash`: refuse
a shape closed by the general closing (`instFields ≠ []`) when some entry's
name is a memory placeholder AND has a signature in `senv` (`memSigClash`).
The proposed compiler change (docs/parallel/S-memname-collision.md) puts the
same test inside `machineShape?`, so a refused parent takes the legacy route.

* `gmChoice` — the child choice of `closeInstsGM`, as written there;
* `gmChoice_mem` — a memory-origin entry gets the memory module of its own
  `combo aw dw`;
* `gmChoice_sig` / `machineShapeG_dispatch` — under the guard, an entry whose
  callee has a signature (an ordinary or structure call: `senv.inst c` or
  `senv.instS c` is `some`) gets `synth c`, the declaration's own compile;
* `machineShapeG_some`, `machineShapeG_noClash`;
* `machineShapeFG` — the same guard on the fuel candidate (`machineShapeF`),
  with `machineShapeFG_of` (the guard commutes with the candidate's answer).

NOT proved: that the legacy route accepts every parent the guard refuses (the
probe measures it for `collParent`); that `senv` at reading time is the
environment `closeInstsGM` runs in (the entry reads `structEnv` of the
captured environment, the closing calls the child synthesiser in the same
`MetaM` run — a runtime fact, outside this model). -/
namespace Tools.ShippingMemDispatch
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachMemory (memChild? memChildName memModule)
open Tools.ShippingReaderFuelR1 (MemR1)

/-- The child choice of `closeInstsGM` (Elab.lean 5215–5217) for one entry's
callee `c`, given the child synthesiser. -/
def gmChoice {m : Type → Type} [Monad m] {α : Type}
    (synth : Name → m α) (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α) (c : Name) : m α :=
  match memChild? c with
  | some md => pure (mem md)
  | none => synth c

/-- A memory placeholder decodes to its own memory module. -/
theorem memChild_memChildName (combo : Bool) (aw dw : Nat) :
    memChild? (memChildName combo aw dw) = some (memModule combo aw dw) := by
  cases combo
  · first
      | rfl
      | simp [memChild?, memChildName]
      | decide
  · first
      | rfl
      | simp [memChild?, memChildName]
      | decide

/-- **A memory-origin entry gets its memory module.** -/
theorem gmChoice_mem {m : Type → Type} [Monad m] {α : Type} (synth : Name → m α)
    (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α) (combo : Bool) (aw dw : Nat) :
    gmChoice synth mem (memChildName combo aw dw) = pure (mem (memModule combo aw dw)) := by
  unfold gmChoice
  rw [memChild_memChildName]

/-- A callee name that is a memory placeholder AND has a signature in `senv`. -/
def memSigClash (senv : StructEnv) (c : Name) : Bool :=
  (memChild? c).isSome && ((senv.inst c).isSome || (senv.instS c).isSome)

/-- The guard: a shape closed by the general closing with a clashing entry. -/
def shapeClash (senv : StructEnv) (sp : MachineShape) : Bool :=
  !sp.instFields.isEmpty && sp.insts.any (fun i => memSigClash senv i.1)

/-- **The guarded reader (model of the proposed compiler change).** -/
def machineShapeG? (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo)
    (senv : StructEnv) (allowInsts : Bool := true) : Option MachineShape :=
  (machineShape? symbolicMode parameters ci senv allowInsts).bind fun sp =>
    if shapeClash senv sp then none else some sp

theorem machineShapeG_some {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeG? sym ps ci senv ai = some sp) :
    machineShape? sym ps ci senv ai = some sp ∧ shapeClash senv sp = false := by
  unfold machineShapeG? at h
  cases hm : machineShape? sym ps ci senv ai with
  | none => rw [hm] at h; cases h
  | some sp' =>
    rw [hm] at h
    dsimp only [Option.bind] at h
    cases hc : shapeClash senv sp' with
    | true => rw [hc] at h; cases h
    | false =>
      rw [hc] at h
      cases h
      exact ⟨rfl, hc⟩

/-- No entry of a guarded general-closing shape clashes. -/
theorem machineShapeG_noClash {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeG? sym ps ci senv ai = some sp) (hne : sp.instFields ≠ [])
    {e : Name × List Nat × MixedGateBinder} (he : e ∈ sp.insts) :
    memSigClash senv e.1 = false := by
  have hc := (machineShapeG_some h).2
  unfold shapeClash at hc
  have hne' : sp.instFields.isEmpty = false := by
    cases hf : sp.instFields with
    | nil => exact absurd hf hne
    | cons _ _ => rfl
  rw [hne', Bool.not_false, Bool.true_and] at hc
  cases hx : memSigClash senv e.1 with
  | false => rfl
  | true =>
    have : sp.insts.any (fun i => memSigClash senv i.1) = true :=
      List.any_eq_true.mpr ⟨e, he, hx⟩
    rw [this] at hc
    first | cases hc | simp at hc

/-- **Under the guard, a callee with a signature gets its own compile.** -/
theorem gmChoice_sig {m : Type → Type} [Monad m] {α : Type} (synth : Name → m α)
    (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α) {senv : StructEnv} {c : Name}
    (hsig : (senv.inst c).isSome = true ∨ (senv.instS c).isSome = true)
    (hno : memSigClash senv c = false) :
    gmChoice synth mem c = synth c := by
  unfold gmChoice
  cases hm : memChild? c with
  | none => rfl
  | some md =>
    exfalso
    unfold memSigClash at hno
    rw [hm] at hno
    rcases hsig with h | h
    · rw [h] at hno
      first | cases hno | simp at hno
    · rw [h, Bool.or_true] at hno
      first | cases hno | simp at hno

/-- **Dispatch of a guarded shape**: every entry of a general-closing shape
whose callee has a signature is given the declaration's own compile. -/
theorem machineShapeG_dispatch {m : Type → Type} [Monad m] {α : Type} (synth : Name → m α)
    (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α)
    {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeG? sym ps ci senv ai = some sp) (hne : sp.instFields ≠ [])
    {e : Name × List Nat × MixedGateBinder} (he : e ∈ sp.insts)
    (hsig : (senv.inst e.1).isSome = true ∨ (senv.instS e.1).isSome = true) :
    gmChoice synth mem e.1 = synth e.1 :=
  gmChoice_sig synth mem hsig (machineShapeG_noClash h hne he)

/-- Under the guard, a memory placeholder entry of a general-closing shape has
NO signature (so `R1` holds for it without `MemR1`). -/
theorem machineShapeG_mem_noSig {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeG? sym ps ci senv ai = some sp) (hne : sp.instFields ≠ [])
    {combo : Bool} {aw dw : Nat} {js : List Nat} {r : MixedGateBinder}
    (he : (memChildName combo aw dw, js, r) ∈ sp.insts) :
    senv.inst (memChildName combo aw dw) = none ∧ senv.instS (memChildName combo aw dw) = none := by
  have hc := machineShapeG_noClash h hne he
  unfold memSigClash at hc
  rw [memChild_memChildName] at hc
  dsimp only [Option.isSome] at hc
  cases hi : senv.inst (memChildName combo aw dw) with
  | some _ => rw [hi] at hc; cases hc
  | none =>
    cases hs : senv.instS (memChildName combo aw dw) with
    | some _ => rw [hi, hs] at hc; cases hc
    | none => exact ⟨rfl, rfl⟩

/-- **`MemR1` is not a property of every signature table.** -/
theorem not_memR1_all : ¬ ∀ senv : StructEnv, MemR1 senv := by
  intro h
  have := h { proj := fun _ => none, fields := fun _ => none,
              inst := fun _ => some ([], MixedGateBinder.bool) } false 1 1 [] MixedGateBinder.bool rfl
  cases this

/-! ## The same guard on the fuel candidate -/

/-- The candidate wrapper followed by the guard (OUT stays OUT). -/
def machineShapeFG (n : Nat) (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (senv : StructEnv) (allowInsts : Bool := true) :
    Option (Option MachineShape) :=
  (Tools.ShippingReaderFuel.machineShapeF n symbolicMode parameters ci senv allowInsts).map
    fun r => r.bind fun sp => if shapeClash senv sp then none else some sp

/-- The guard commutes with any answer of the candidate (so every stability /
adequacy / driver theorem of `machineShapeF` transfers by this equation). -/
theorem machineShapeFG_of {n : Nat} {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {r : Option MachineShape}
    (h : Tools.ShippingReaderFuel.machineShapeF n sym ps ci senv ai = some r) :
    machineShapeFG n sym ps ci senv ai =
      some (r.bind fun sp => if shapeClash senv sp then none else some sp) := by
  unfold machineShapeFG
  rw [h]
  rfl

theorem machineShapeFG_out {n : Nat} {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool}
    (h : Tools.ShippingReaderFuel.machineShapeF n sym ps ci senv ai = none) :
    machineShapeFG n sym ps ci senv ai = none := by
  unfold machineShapeFG
  rw [h]
  rfl

end Tools.ShippingMemDispatch
