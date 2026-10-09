import Tools.ShippingMachineEntry

/-! # The children of a machine-route compile are runs of the real entry

A machine-route parent ties each `@[hardware_module]` call to an instance of
a child module (`closeInstsM` / `closeInstsGM`): a memory call's child is the
built memory module (`MachMemory.memChild?`), any other call's child is what
the function held in `sparkleChildSynth` returned for the call's declaration.
That function is the memoised child entry `Rec.synthesizeCombinational` — a
`partial def` (logically opaque) reading the per-synthesis cache
`sparkleChildCache` (an `IO.Ref`, its contents opaque in the logic).

`ChildSynthIs` is the ONE boundary this file assumes, for the contexts of the
parent's run: a read of `sparkleChildSynth` returns a function each of whose
runs on a declaration `c` returns what some run of the real entry
`synthesizeCombinational c` returns, in the same contexts (the ref's content,
the partial child entry's equation and the soundness of its cache, together;
none of the three is expressible as a theorem in the logic — the first two
are opaque constants, the third a property of an `IO.Ref` across worlds).

From it and the parent's own run, `machine_children_real` DERIVES, for the
module and design the parent's real entry returned: they are the closing
(`CloseCalls`) of the transition with SOME children, and each call's child is
the built memory module (memory calls of the general closing) or the result of a run of the real
entry on the call's declaration, call by call (`ChildrenReal`). This is the
call-level half of the run boundary (`MachineRun` / `GateRun` /
`MachineRunN`): no recompilation, no trace. -/
namespace Tools.ShippingChildSynth
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab

/-- `r` is what a run of the real entry on `c` returns, in these contexts. -/
def RealChild (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (c : Name)
    (r : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) : Prop :=
  ∃ w w', RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w'

/-- **The child-synthesis boundary.** Every read of `sparkleChildSynth` in
these contexts returns a function whose every run on a declaration returns a
result of the real entry on it. -/
def ChildSynthIs (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ w r w', RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w r w' →
    ∃ synth, r = some synth ∧
      ∀ c w1 y w2, RunsTo (synth c) mctx mref cctx cref w1 y w2 →
        RealChild mctx mref cctx cref c y

/-- The children of a shape's calls, call by call: the built memory module
for a memory call, a real-entry result on the call's declaration otherwise. -/
def ChildrenReal (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (shape : MachineShape) (children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    (Sparkle.Compiler.MachMemory.memChild? (shape.insts[k]).1 = some y ∨
      RealChild mctx mref cctx cref (shape.insts[k]).1 y)

theorem RunsTo_mapM_loop {α β : Type} (f : α → MetaM β) {mctx mref cctx cref} :
    ∀ (l : List α) (acc r : List β) w w', RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        ∀ k (hk : k < l.length), ∃ y w1 w2, RunsTo (f l[k]) mctx mref cctx cref w1 y w2 ∧ ys[k]? = some y
  | [], acc, r, w, w', h => by
    have := RunsTo.pure_eq h
    exact ⟨[], by simp [this], rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | x :: xs, acc, r, w, w', h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨ys, hr, hlen, hget⟩ := RunsTo_mapM_loop f xs (y :: acc) r w1 w' h
    refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk => ?_⟩
    cases k with
    | zero => exact ⟨y, w, w1, hy, rfl⟩
    | succ k =>
      obtain ⟨z, w3, w4, hz, hzk⟩ := hget k (by simpa using hk)
      exact ⟨z, w3, w4, hz, by simpa using hzk⟩

/-- A run of `List.mapM` in `MetaM`, entry by entry, in the same contexts. -/
theorem RunsTo_mapM_get {α β : Type} (f : α → MetaM β) {mctx mref cctx cref} (l : List α)
    (r : List β) {w w'} (h : RunsTo (l.mapM f) mctx mref cctx cref w r w') :
    r.length = l.length ∧
    ∀ k (hk : k < l.length), ∃ y w1 w2, RunsTo (f l[k]) mctx mref cctx cref w1 y w2 ∧ r[k]? = some y := by
  obtain ⟨ys, hr, hlen, hget⟩ := RunsTo_mapM_loop f l [] r w w' h
  simp only [List.reverse_nil, List.nil_append] at hr
  subst hr
  exact ⟨hlen, hget⟩

/-- `closeInstsGM`'s children, call by call. -/
theorem closeInstsGM_runs {shape t m₀ d₀ m d} {mctx mref cctx cref w w'}
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w')
    (hsyn : ChildSynthIs mctx mref cctx cref) :
    ∃ children, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧ MemChildren shape children ∧
      ChildrenReal mctx mref cctx cref shape children := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨synth, rfl, hsynth⟩ := hsyn _ _ _ hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  have heq := RunsTo.pure_eq hr
  obtain ⟨hlen, hk⟩ := RunsTo_mapM_get _ shape.insts children hch
  refine ⟨children, heq.symm, ?_, hlen, fun k hkl => ?_⟩
  · intro k c hc md hmd
    have hkl : k < shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
    obtain ⟨y, _, _, hy, hky⟩ := hk k hkl
    have hck : (shape.insts[k]).1 = c := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hkl] at hc
      simpa using hc
    generalize shape.insts[k] = p at hy hck
    obtain ⟨c', b, k'⟩ := p
    simp only at hck
    subst hck
    simp only [hmd] at hy
    rw [RunsTo.pure_eq hy] at hky
    exact hky
  · obtain ⟨y, w3, w4, hy, hyk⟩ := hk k hkl
    refine ⟨y, hyk, ?_⟩
    generalize hp : shape.insts[k] = p at hy ⊢
    obtain ⟨c, b, k'⟩ := p
    dsimp only at hy ⊢
    cases hmc : Sparkle.Compiler.MachMemory.memChild? c with
    | some md => rw [hmc] at hy; exact Or.inl (by rw [RunsTo.pure_eq hy])
    | none => rw [hmc] at hy; exact Or.inr (hsynth c _ _ _ hy)

/-- `closeInstsM`'s children (one-output combinational calls), call by call:
each a real-entry result on the call's declaration. -/
theorem closeInstsM_runs {shape t m₀ d₀ m d} {mctx mref cctx cref w w'}
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w')
    (hsyn : ChildSynthIs mctx mref cctx cref) :
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      ChildrenReal mctx mref cctx cref shape children := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨synth, rfl, hsynth⟩ := hsyn _ _ _ hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  have heq := RunsTo.pure_eq hr
  obtain ⟨hlen, hk⟩ := RunsTo_mapM_get _ shape.insts children hch
  refine ⟨children, heq.symm, hlen, fun k hkl => ?_⟩
  obtain ⟨y, w3, w4, hy, hyk⟩ := hk k hkl
  exact ⟨y, hyk, Or.inr (hsynth _ _ _ _ hy)⟩

/-- **The machine synthesis, with its children.** A run of the machine
synthesis returning a module: the harness, `closeLets`, `closeMachine`, and —
for a shape with calls — the closing with children that are, call by call,
built memory modules or real-entry results. -/
theorem synthesizeMachineCertified_runs {logProf declName shape m d} {mctx mref cctx cref w w'}
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName shape)
      mctx mref cctx cref w (some (m, d)) w')
    (hsyn : ChildSynthIs mctx mref cctx cref) :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire e hint top named) logProf declName
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
          ChildrenReal mctx mref cctx cref shape children)) := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  dsimp only at hr
  split at hr
  · rename_i t' hcl
    split at hr
    · rename_i hi
      have eq := RunsTo.pure_eq hr
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨hm, hd⟩ := eq
      exact ⟨t, t', d', run.mreturns, hcl, Or.inl ⟨hi, hm, hd⟩⟩
    · rename_i hi
      have hne : shape.insts ≠ [] := by rw [hi]; exact List.cons_ne_nil _ _
      split at hr
      · rename_i hf
        obtain ⟨children, hc, hreal⟩ := closeInstsM_runs hr hsyn
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inl ⟨List.isEmpty_iff.mp hf, hc⟩, hreal⟩⟩
      · rename_i hf
        obtain ⟨children, hc, hmc, hreal⟩ := closeInstsGM_runs hr hsyn
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inr ⟨fun h => hf (List.isEmpty_iff.mpr h), hc, hmc⟩, hreal⟩⟩
  · have eq := RunsTo.pure_eq hr
    cases eq

/-- **The children of a real compile.** One successful run of the real core
entry on a declaration at the machine boundary returns the closing of its
transition with children that are, call by call, built memory modules or
results of the real entry on the call's declaration — in the parent's own
contexts, under the single `ChildSynthIs` boundary. -/
theorem machine_children_real {declName : Name} {shape : MachineShape}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (hsyn : ChildSynthIs mctx mref cctx cref) (hi : shape.insts ≠ []) :
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
      ChildrenReal mctx mref cctx cref shape children := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := synthesizeFromConst_machine old miss run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w9, w10, hrun, hres⟩ := hmach shape hshape
  have hne := closes logProf _ _ _ hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, _, hcl, hmt⟩ := synthesizeMachineCertified_runs hrun hsyn
    rcases hmt with ⟨h0, _, _⟩ | ⟨_, children, hcc, hreal⟩
    · exact absurd h0 hi
    · exact ⟨t, t', d₀, children, hcl, hcc, hreal⟩

end Tools.ShippingChildSynth
