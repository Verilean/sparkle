import Tools.ShippingReaderOutsInv

/-! # Output-NAME invariants of EVERY machine-reader result (G3b, second data checks)

WRITTEN, NOT BUILT (branch `par/r-2`; record `docs/parallel/R-reader-outs-inv-2.md`).
No `sorry`, no axiom, no `native_decide`. A leaf.

The wrapper `machineShape?` (a `def`, `Sparkle/Compiler/Elab.lean` 5071–5072)
refuses, right after reading the output list `outs` off the declaration's
type,

    if outs.isEmpty || !outs.all (fun o => outNameOk o.1) ||
        !decide (outs.map (·.1)).Nodup then none else …

`ShapeDecomp.machineShape?_decomp` (built) drops that condition
(`ite_none_inv`). This file walks the same prefix as
`Tools.ShippingMachineShapeUnfold.machineShape?_prefix` (built) ONE step
further and keeps it (`ite_none_inv_not`), then transports it to the layout
through `layoutOuts = machOutFields _ outs` (names are copied verbatim):

* `outNames_of_reader : machineShape? … = some sp →
     sp.layout.outs ≠ [] ∧ (∀ o ∈ sp.layout.outs, outNameOk o.name = true) ∧
     (sp.layout.outs.map (·.name)).Nodup`;
* `…_of_core`: the same for the shape of `MachineDefines`, from `hcore` and
  `entry` (`Tools.ShippingReaderOutsInv.reader_of_core`);
* `outsOk_of_core`: the hypothesis `outsOk` of ~20 run lemmas
  (`∀ o ∈ outs, 0 < o.width ∧ outNameOk o.name = true`) from `hcore`, `entry`
  and the WIDTH half alone; `outsNodup_of_core`: the hypothesis `outsNodup`.

Where these facts are decided per declaration today: NOWHERE separately.
They are the name half of conjunct 7 and all of conjunct 8 of
`MachineData.ok` (`Tools/ShippingMachineAuto.lean` 226–227), decided as ONE
Bool by `f.machine_ok`; every consumer reads `outsOk` / `outsNodup` out of
`d.ok`. No generator decides `outNameOk`, the `Nodup` of the names, or
`outs ≠ []` on its own (searched: every `elab "#…"` file under `Tools/`).
The output-name checks the generators DO decide separately —
`noPortsMem_outChars` / `CombKid.outName` (every character `charOk`),
`noPortsMem_outHead` / `hfresh` (no name starts with `i`), `CombKid.one`
(the names are `["out"]`) — are NOT implied by the wrapper's test
(`outNameOk` constrains only a leading `_`, the prefix `next`, `rst`, `clk`).
-/
namespace Tools.ShippingReaderOutNames
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.IR.Machine (OutField outNameOk)
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingShapeDecomp Tools.ShippingMachineShapeUnfold
open Tools.ShippingReaderOutsInv (reader_defn reader_of_core)

/-! ## One more inversion step -/

/-- `if c then none else x` returned: `c` is false. -/
theorem ite_none_inv_not {α : Type} {c : Prop} [Decidable c] {x : Option α} {b : α}
    (h : (if c then none else x) = some b) : ¬ c := by
  intro hc
  rw [if_pos hc] at h
  cases h

theorem bool_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- The wrapper's test on the output list, as a Bool. -/
def outsTest (outs : List (String × MixedGateBinder)) : Bool :=
  outs.isEmpty || !outs.all (fun o => outNameOk o.1) || !decide (outs.map (·.1)).Nodup

/-- **The output test of the wrapper passed**, on the output list
`declOuts?` reads (the prefix walk of `machineShape?_prefix`, one step
further). -/
theorem machineShape?_outsTest {sym : Bool} {params : List (String × Nat)} {d : DefinitionVal}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params (.defnInfo d) senv allow = some sp) :
    ∃ o : Option Name × List (String × MixedGateBinder),
      declOuts? senv d.type = some o ∧ outsTest o.2 = false := by
  unfold machineShape? at h
  dsimp only at h
  -- 1. the outer `if`
  replace h := ite_none_inv h
  -- 2. the binders
  obtain ⟨x, hx, h⟩ := bind_inv h
  -- 3. the output list: a tuple result, or `machOuts?`
  generalize hk : machTupleKinds? d.type = tup at h
  cases tup with
  | none =>
    dsimp only at h
    obtain ⟨o, ho, h⟩ := bind_inv h
    have hd : declOuts? senv d.type = some o := by
      unfold declOuts?
      rw [hk]
      exact ho
    -- 4. the test on the output names, KEPT
    have hc := ite_none_inv_not h
    exact ⟨o, hd, bool_false_of_not_true hc⟩
  | some ks =>
    dsimp only at h
    obtain ⟨o, ho, h⟩ := bind_inv h
    have hd : declOuts? senv d.type = some o := by
      unfold declOuts?
      rw [hk]
      exact ho
    have hc := ite_none_inv_not h
    exact ⟨o, hd, bool_false_of_not_true hc⟩

/-- What the passed test says (pure). -/
theorem outsTest_facts {outs : List (String × MixedGateBinder)} (h : outsTest outs = false) :
    outs ≠ [] ∧ (∀ p ∈ outs, outNameOk p.1 = true) ∧ (outs.map (·.1)).Nodup := by
  unfold outsTest at h
  cases ha : outs.isEmpty <;> cases hb : outs.all (fun o => outNameOk o.1) <;>
    cases hc : decide (outs.map (·.1)).Nodup <;>
    (first | rw [ha, hb, hc] at h | simp only [ha, hb, hc] at h) <;>
    first
      | exact absurd h (by decide)
      | exact ⟨fun he => by subst he; exact absurd ha (by decide),
          fun p hp => List.all_eq_true.mp hb p hp, of_decide_eq_true hc⟩

/-! ## `machOutFields` copies the names -/

theorem machOutFields_names (w : Nat) :
    ∀ l : List (String × MixedGateBinder), (machOutFields w l).map (·.name) = l.map (·.1)
  | [] => rfl
  | (nm, k) :: rest => by
    first
      | exact congrArg (nm :: ·) (machOutFields_names w rest)
      | (simp only [machOutFields, List.map_cons, machOutFields_names w rest])
      | simp [machOutFields, machOutFields_names w rest]

theorem machOutFields_ne_nil (w : Nat) :
    ∀ l : List (String × MixedGateBinder), l ≠ [] → machOutFields w l ≠ []
  | [], h => absurd rfl h
  | (nm, k) :: rest, _ => by
    intro h0
    first
      | cases h0
      | (simp only [machOutFields] at h0; cases h0)
      | simp [machOutFields] at h0

theorem machOutFields_nameOk (w : Nat) : ∀ (l : List (String × MixedGateBinder)),
    (∀ p ∈ l, outNameOk p.1 = true) → ∀ q ∈ machOutFields w l, outNameOk q.name = true
  | [], _, q, hq => by
    first
      | (simp [machOutFields] at hq)
      | cases hq
      | exact absurd hq List.not_mem_nil
  | (nm, k) :: rest, hl, q, hq => by
    simp only [machOutFields, List.mem_cons] at hq
    rcases hq with he | hr
    · subst he
      exact hl (nm, k) (List.Mem.head _)
    · exact machOutFields_nameOk w rest (fun p hp => hl p (List.Mem.tail _ hp)) q hr

/-! ## Every reader result -/

/-- **The output-name invariant of the machine reader**, for EVERY input on
which it returns a shape. -/
theorem outNames_of_reader {sym : Bool} {params : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params ci senv allow = some sp) :
    sp.layout.outs ≠ [] ∧ (∀ o ∈ sp.layout.outs, outNameOk o.name = true) ∧
      (sp.layout.outs.map (·.name)).Nodup := by
  obtain ⟨dE, hE⟩ := reader_defn h
  subst hE
  obtain ⟨o, ho, ht⟩ := machineShape?_outsTest h
  obtain ⟨_, _, ctor?, outs, _, _, _, _, D⟩ := machineShape?_decomp h
  have he : (ctor?, outs) = o := Option.some.inj (D.outsEq.symm.trans ho)
  subst he
  obtain ⟨hne, hok, hnd⟩ := outsTest_facts (outs := outs) ht
  rw [D.layoutOuts]
  refine ⟨machOutFields_ne_nil _ outs hne, machOutFields_nameOk _ outs hok, ?_⟩
  rw [machOutFields_names]
  exact hnd

/-! ## The shape of `MachineDefines`, inside a run of the real entry -/

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The output-name facts with no per-declaration computation.** -/
theorem outNames_of_core {c : Name} {shape : MachineShape} {w w1 : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c shape) :
    shape.layout.outs ≠ [] ∧ (∀ o ∈ shape.layout.outs, outNameOk o.name = true) ∧
      (shape.layout.outs.map (·.name)).Nodup := by
  obtain ⟨_, _, h⟩ := reader_of_core hcore entry
  exact outNames_of_reader h

/-- `outsNodup` (a hypothesis of the closing lemmas) from the run. -/
theorem outsNodup_of_core {c : Name} {shape : MachineShape} {w w1 : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c shape) :
    (shape.layout.outs.map (·.name)).Nodup :=
  (outNames_of_core hcore entry).2.2

/-- `outs ≠ []` (`houtsNe` of `Tools.ShippingCombLeafShape`) from the run. -/
theorem outsNe_of_core {c : Name} {shape : MachineShape} {w w1 : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c shape) :
    shape.layout.outs ≠ [] :=
  (outNames_of_core hcore entry).1

/-- `outsOk` (a hypothesis of ~20 run lemmas) from the run and the WIDTH
half alone: the name half is the reader's. -/
theorem outsOk_of_core {c : Name} {shape : MachineShape} {w w1 : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c shape)
    (hpos : ∀ o ∈ shape.layout.outs, 0 < o.width) :
    ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true :=
  fun o ho => ⟨hpos o ho, (outNames_of_core hcore entry).2.1 o ho⟩

end Tools.ShippingReaderOutNames
