import Tools.ShippingShapeDecomp
import Tools.ShippingMachineEntry
import Tools.ShippingTextTyped

/-! # Output-port invariants of EVERY machine-reader result (G3b, first data checks)

WRITTEN, NOT BUILT (branch `par/r-1`; record `docs/parallel/R-reader-outs-inv.md`).
No `sorry`, no axiom, no `native_decide`.

Generated endpoints decide, per declaration, on the reflected shape `d.shape`:

    f.noPortsMem_outTy    : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width
    f.noPortsMem_outScalar : ∀ o ∈ d.shape.layout.outs, scalarTy o.ty = true

(`Tools/ShippingNoPortsMemCommand.lean`, `decided c "outTy"` / `"outScalar"`;
the same `outTy` is decided by `ShippingNoPortsMemSeqCommand`,
`ShippingOneOutGenCommand`, `ShippingOneOutAnyGenCommand`, and it is a
hypothesis of ~30 run lemmas under `Tools/ShippingChecks*`, `ShippingCalls*`).

This file proves both for EVERY shape `machineShape?` returns — any
declaration, any structure environment, any flags — with no evaluation:

* `outs_of_reader : machineShape? sym params ci senv allow = some sp →
     ∀ o ∈ sp.layout.outs, o.ty.bitWidth = o.width ∧ scalarTy o.ty = true`;
* `outTy_of_core`, `outScalar_of_core`: the same for the shape of
  `MachineDefines`, from the two hypotheses every generated run theorem
  already has (`hcore`, the run of the real entry; `entry`, the machine
  boundary). No per-declaration computation.

Why it holds for every input although the reader calls `partial`
functions: the output layout is computed by the TOTAL tail of the wrapper
`machineShape?` (a `def`) from `declOuts? senv d.type` alone —
`layout.outs = machOutFields _ outs` (`ShapeDecomp.layoutOuts`, built) — and
`machOutFields` writes `ty := machHWType k`, `width := machWidth k` for EVERY
kind `k`; `machHWType k` has bit width `machWidth k` and is scalar for every
`k` (including `.domain`). No result of a `partial` function enters these
two fields. -/
namespace Tools.ShippingReaderOutsInv
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.IR.Machine (OutField)
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingShapeDecomp

/-! ## The kind table -/

theorem bitWidth_machHWType : ∀ k : MixedGateBinder, (machHWType k).bitWidth = machWidth k
  | .domain => by first | rfl | simp [machHWType, machWidth, Sparkle.IR.Type.HWType.bitWidth]
  | .bool => by first | rfl | simp [machHWType, machWidth, Sparkle.IR.Type.HWType.bitWidth]
  | .bits _ => by first | rfl | simp [machHWType, machWidth, Sparkle.IR.Type.HWType.bitWidth]

theorem scalarTy_machHWType : ∀ k : MixedGateBinder,
    Tools.ShippingTextTyped.scalarTy (machHWType k) = true
  | .domain => by first | rfl | simp [machHWType, Tools.ShippingTextTyped.scalarTy]
  | .bool => by first | rfl | simp [machHWType, Tools.ShippingTextTyped.scalarTy]
  | .bits _ => by first | rfl | simp [machHWType, Tools.ShippingTextTyped.scalarTy]

/-- Every field `machOutFields` writes has a scalar type of its own width. -/
theorem machOutFields_ty (w : Nat) : ∀ (l : List (String × MixedGateBinder)) (o : OutField),
    o ∈ machOutFields w l →
      o.ty.bitWidth = o.width ∧ Tools.ShippingTextTyped.scalarTy o.ty = true
  | [], o, h => by
    first
      | (simp [machOutFields] at h)
      | cases h
      | exact absurd h List.not_mem_nil
  | (nm, k) :: rest, o, h => by
    simp only [machOutFields, List.mem_cons] at h
    rcases h with he | hr
    · subst he
      exact ⟨bitWidth_machHWType k, scalarTy_machHWType k⟩
    · exact machOutFields_ty w rest o hr

/-! ## Every reader result -/

/-- A returned shape was read from a DEFINITION (`machineShape?` is `none`
on every other constant). Same statement as
`Tools.ShippingCallWidthsEntry.machineShape?_defn`, repeated so that this
file does not depend on that one. -/
theorem reader_defn {sym : Bool} {params : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params ci senv allow = some sp) :
    ∃ dE : DefinitionVal, ci = .defnInfo dE := by
  cases ci with
  | defnInfo dE => exact ⟨dE, rfl⟩
  | _ =>
    first
      | cases h
      | (unfold machineShape? at h; cases h)
      | (simp [machineShape?] at h; done)

/-- **The output-port invariant of the machine reader**, for EVERY input on
which it returns a shape. -/
theorem outs_of_reader {sym : Bool} {params : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params ci senv allow = some sp) :
    ∀ o ∈ sp.layout.outs,
      o.ty.bitWidth = o.width ∧ Tools.ShippingTextTyped.scalarTy o.ty = true := by
  obtain ⟨dE, hE⟩ := reader_defn h
  subst hE
  obtain ⟨_, _, _, outs, _, _, _, _, D⟩ := machineShape?_decomp h
  intro o ho
  rw [D.layoutOuts] at ho
  exact machOutFields_ty _ outs o ho

/-- `outTy` (the generated `f.noPortsMem_outTy`) for every reader result. -/
theorem outTy_of_reader {sym : Bool} {params : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params ci senv allow = some sp) :
    ∀ o ∈ sp.layout.outs, o.ty.bitWidth = o.width :=
  fun o ho => (outs_of_reader h o ho).1

/-- `outScalar` (the generated `f.noPortsMem_outScalar`) for every reader result. -/
theorem outScalar_of_reader {sym : Bool} {params : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params ci senv allow = some sp) :
    ∀ o ∈ sp.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true :=
  fun o ho => (outs_of_reader h o ho).2

/-! ## The shape of `MachineDefines`, inside a run of the real entry -/

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- In a run of the real entry, the shape `MachineDefines` names IS a reader
result (on the entry constant, at the run's structure environment). The
two hypotheses are those of every generated run theorem. -/
theorem reader_of_core {c : Name} {shape : MachineShape} {w w1 : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c shape) :
    ∃ (ci : ConstantInfo) (senv : StructEnv), machineShape? false [] ci senv = some shape := by
  obtain ⟨_, _, _, _, _, _, _, _, _, get, henv, -⟩ := synthesizeCombinationalCore_reads hcore
  exact ⟨_, _, (entry _ _ _ _ _ _ _ _ _ get henv henv).2.2⟩

/-- **`outTy` with no per-declaration computation.** -/
theorem outTy_of_core {c : Name} {shape : MachineShape} {w w1 : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c shape) :
    ∀ o ∈ shape.layout.outs, o.ty.bitWidth = o.width := by
  obtain ⟨_, _, h⟩ := reader_of_core hcore entry
  exact outTy_of_reader h

/-- **`outScalar` with no per-declaration computation.** -/
theorem outScalar_of_core {c : Name} {shape : MachineShape} {w w1 : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c shape) :
    ∀ o ∈ shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true := by
  obtain ⟨_, _, h⟩ := reader_of_core hcore entry
  exact outScalar_of_reader h

end Tools.ShippingReaderOutsInv
