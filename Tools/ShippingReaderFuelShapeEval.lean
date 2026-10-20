import Tools.ShippingReaderFuelDriverComplete

/-! # Finite executions of the reader WRAPPER = finished fuel runs (both directions)

BUILT on poc 20304f50 (run `j1`: `cgrun -n j1 -m 3G -j 1 -- lake build Tools.ShippingReaderFuelShapeEval`, exit 0) (worker J, branch `par/r-14`, from poc 20304f50; record
`docs/parallel/R-reader-fuel.md` §"Wrapper compactness (worker J)"). No
`sorry`, no axiom, no `native_decide`. Imports only the BUILT
`Tools/ShippingReaderFuelDriverComplete.lean`. NOT used by the compiler:
production still calls the `partial` reader `machineShape?`; nothing under
`Sparkle/` changed; no existing statement changed.

## What is proved

`Tools/ShippingReaderFuelDriverComplete.lean` proved `shapeRuns_fuel`:
a FINITE derivation of the wrapper (`ShapeRuns … r`) gives some fuel `N`
with `machineShapeF N … = some r`. Here the CONVERSE is proved, which needs
that the wrapper body reads only finitely many table answers:

* `compact_shapeW` — `Compact (shapeW …)`, the wrapper counterpart of
  `compact_step` / `compact_normStep` (`Tools/ShippingReaderFuelEval.lean`),
  from `compact_wNorm` / `compact_wConv` / `compact_wChain` /
  `compact_wLoopRoot` (one table read each), `compact_shapeStart`,
  `compact_shapeRootLet`, `compact_shapeBody` and the generic combinator
  lemmas (`compact_optK`, `compact_bind`, `compact_bindO`, `compact_foldO`,
  `compact_okO`, `compact_failO`, `compact_pure`). The pure fragments
  (`shapePre`, `shapeMid`, `shapePost`, `machReserve`, …) are never
  inspected: each is one discriminant / one returned value.
* `wEval_of_wtab` — a call answered by the fuel table is a finite execution
  (`fuel_evalN` for `machNorm`, `fuel_eval` for a block call).
* `fuel_shapeRuns` — `machineShapeF N … = some r → ShapeRuns … r`;
* `shapeRuns_iff` — `ShapeRuns … r ↔ ∃ N, machineShapeF N … = some r`, and its
  instances `shapeRuns_ok_iff` (success `r = some s`) and `shapeRuns_fail_iff`
  (ordinary refusal `r = none`);
* `shapeRuns_drive_iff` — `ShapeRuns … r ↔ ∃ rounds, (driveShape rounds start …).res
  = some r` (any `start`), with `_ok` / `_fail` instances;
* `shapeRuns_det` (one answer), `shapeRuns_none_iff` (no finite derivation at
  all ⟺ OUT at every fuel) and `shapeRuns_drive_none_iff` (⟺ the driver is OUT
  for every round bound).

`r` ranges over `Option MachineShape`: `some s` is success, `none` an ORDINARY
refusal (the old `none`). Fuel exhaustion (OUT) is not a value of `r`.

## What is NOT proved here (kept apart)

* **O1 (outside the kernel)**: that a RETURNING run of the compiled `partial`
  `machineShape?` produced a finite derivation. Hence nothing here says the
  fuel wrapper / driver answers whenever the old reader answers.
* **The opaque helpers** (`rootFloat`, `zetaAll` in `machReserve`, `rawNode`,
  `machNormNode`, `packTupleInputs`, the `Expr` primitives, …) are
  PARAMETERS: consumed as single values, never inspected, their termination
  and runtime agreement (O3/O4) not claimed.
* **O2**: that the compiled code satisfies its equations. -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab

/-! ## One table read each -/

theorem compact_wNorm {e : Lean.Expr} : Compact (wNorm e) :=
  compact_call (R := WCall.Res) (WCall.norm e)

theorem compact_wConv {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead} :
    Compact (wConv env d e st) :=
  compact_call (R := WCall.Res) (WCall.blk (Call.conv env d e st))

theorem compact_wChain {env : List MachVal} {e : Lean.Expr} {st : MachRead} :
    Compact (wChain env e st) :=
  compact_call (R := WCall.Res) (WCall.blk (Call.chain env e st))

theorem compact_wLoopRoot {env : List MachVal} {e : Lean.Expr} {st : MachRead} :
    Compact (wLoopRoot env e st) :=
  compact_call (R := WCall.Res) (WCall.blk (Call.loopRoot env e st))

/-- One crunch step for the wrapper fragments: a combinator lemma (syntactic,
reducible transparency), an `intro`, a case split, or a beta/zeta/iota
clean-up (as `compact_base` in `…FuelEval`). -/
macro "wcompact_base" : tactic => `(tactic| first
  | with_reducible exact compact_wNorm
  | with_reducible exact compact_wConv
  | with_reducible exact compact_wChain
  | with_reducible exact compact_wLoopRoot
  | with_reducible exact compact_okO _
  | with_reducible exact compact_failO
  | with_reducible exact compact_pure _
  | with_reducible exact compact_call _
  | with_reducible apply compact_bindO
  | with_reducible apply compact_bind
  | with_reducible apply compact_optK
  | with_reducible apply compact_foldO
  | intro _
  | split
  | dsimp only)

/-! ## The reader part of the wrapper -/

theorem compact_shapeStart (senv : StructEnv) (m : ShapeMid) :
    Compact (shapeStart senv m) := by
  unfold shapeStart
  repeat' wcompact_base

theorem compact_shapeRootLet (senv : StructEnv) (s : List MachVal × MachRead)
    (a : Name × Lean.Expr × Lean.Expr) : Compact (shapeRootLet senv s a) := by
  unfold shapeRootLet
  repeat' wcompact_base

theorem compact_shapeBody (m : ShapeMid) (env : List MachVal) (st : MachRead) :
    Compact (shapeBody m env st) := by
  unfold shapeBody
  repeat' wcompact_base

/-- **The wrapper inspects finitely many answers** (`machNorm` and block
calls). -/
theorem compact_shapeW (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo)
    (senv : StructEnv) (ai : Bool) : Compact (shapeW sm ps ci senv ai) := by
  unfold shapeW
  first
    | (refine compact_optK _ (fun p => ?_)
       refine compact_bind compact_wNorm (fun en => ?_)
       refine compact_bindO (compact_shapeStart senv _) (fun st => ?_)
       refine compact_bindO (compact_foldO (compact_shapeRootLet senv) _ _) (fun es => ?_)
       rcases es with ⟨env, st'⟩
       refine compact_bindO (compact_shapeBody _ _ _) (fun sv => ?_)
       rcases sv with ⟨st'', v⟩
       exact compact_pure _)
    | (repeat' (first
        | with_reducible exact compact_shapeStart _ _
        | with_reducible exact compact_shapeBody _ _ _
        | with_reducible exact compact_shapeRootLet _ _ _
        | wcompact_base))

/-! ## Fuel answers are finite executions -/

/-- A call answered by the fuel table has a finite derivation. -/
theorem wEval_of_wtab {senv : StructEnv} {n : Nat} (c : WCall) (r : WCall.Res c)
    (h : wtab senv n c = some r) : WEval senv c r := by
  cases c with
  | norm e =>
    have h' : machNormF n senv e = some r := h
    have h'' : EvalN senv e r := fuel_evalN h'
    exact h''
  | blk c =>
    have h' : readF senv n c = some r := h
    have h'' : Eval senv c r := fuel_eval h'
    exact h''

section Runs
variable {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv}
  {ai : Bool}

/-- **Converse of `shapeRuns_fuel`**: a finished fuel answer of the wrapper
(success or ordinary refusal) is a finite execution of the wrapper. -/
theorem fuel_shapeRuns {N : Nat} {r : Option MachineShape}
    (h : machineShapeF N sm ps ci senv ai = some r) : ShapeRuns sm ps ci senv ai r := by
  have h' : (shapeW sm ps ci senv ai).run (wtab senv N) = some r := h
  obtain ⟨L, e, k⟩ := (compact_shapeW sm ps ci senv ai).ok (wtab senv N) r h'
  unfold ShapeRuns
  exact ⟨L, fun p hp => wEval_of_wtab p.1 p.2 (e p hp), k⟩

/-- **Finite executions of the wrapper = finished fuel runs.** -/
theorem shapeRuns_iff {r : Option MachineShape} :
    ShapeRuns sm ps ci senv ai r ↔ ∃ N, machineShapeF N sm ps ci senv ai = some r := by
  constructor
  · intro h
    exact shapeRuns_fuel h
  · intro h
    obtain ⟨N, hN⟩ := h
    exact fuel_shapeRuns hN

/-- Success. -/
theorem shapeRuns_ok_iff {s : MachineShape} :
    ShapeRuns sm ps ci senv ai (some s) ↔
      ∃ N, machineShapeF N sm ps ci senv ai = some (some s) :=
  shapeRuns_iff

/-- Ordinary refusal (never OUT). -/
theorem shapeRuns_fail_iff :
    ShapeRuns sm ps ci senv ai none ↔ ∃ N, machineShapeF N sm ps ci senv ai = some none :=
  shapeRuns_iff

/-- A finite execution of the wrapper has ONE answer. -/
theorem shapeRuns_det {r r' : Option MachineShape} (h₁ : ShapeRuns sm ps ci senv ai r)
    (h₂ : ShapeRuns sm ps ci senv ai r') : r = r' := by
  obtain ⟨n, hn⟩ := shapeRuns_fuel h₁
  obtain ⟨m, hm⟩ := shapeRuns_fuel h₂
  exact machineShapeF_det hn hm

/-- **With the driver**: a finite execution of the wrapper ⟺ the doubling
driver eventually returns the same answer (any start fuel). -/
theorem shapeRuns_drive_iff (start : Nat) (r : Option MachineShape) :
    ShapeRuns sm ps ci senv ai r ↔
      ∃ rounds, (driveShape rounds start sm ps ci senv ai).res = some r :=
  Iff.trans shapeRuns_iff (driveShape_complete_iff sm ps ci senv ai start r).symm

theorem shapeRuns_drive_ok_iff (start : Nat) (s : MachineShape) :
    ShapeRuns sm ps ci senv ai (some s) ↔
      ∃ rounds, (driveShape rounds start sm ps ci senv ai).res = some (some s) :=
  shapeRuns_drive_iff start (some s)

theorem shapeRuns_drive_fail_iff (start : Nat) :
    ShapeRuns sm ps ci senv ai none ↔
      ∃ rounds, (driveShape rounds start sm ps ci senv ai).res = some none :=
  shapeRuns_drive_iff start none

/-- No finite execution at all ⟺ OUT at every fuel. -/
theorem shapeRuns_none_iff :
    (∀ r, ¬ ShapeRuns sm ps ci senv ai r) ↔ ∀ N, machineShapeF N sm ps ci senv ai = none := by
  constructor
  · intro h N
    cases hN : machineShapeF N sm ps ci senv ai with
    | none => rfl
    | some o => exact absurd (fuel_shapeRuns hN) (h o)
  · intro h r hr
    obtain ⟨N, hN⟩ := shapeRuns_fuel hr
    rw [h N] at hN
    cases hN

/-- No finite execution at all ⟺ the driver is OUT for every round bound. -/
theorem shapeRuns_drive_none_iff (start : Nat) :
    (∀ r, ¬ ShapeRuns sm ps ci senv ai r) ↔
      ∀ rounds, (driveShape rounds start sm ps ci senv ai).res = none :=
  Iff.trans shapeRuns_none_iff (driveShape_out_forever_iff sm ps ci senv ai start).symm

end Runs

end Tools.ShippingReaderFuel
