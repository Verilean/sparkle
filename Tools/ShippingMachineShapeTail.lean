import Tools.ShippingMachineShapeUnfold

/-! # P4, second half — `machineShape?` to its final structure literal

`machineShape?_some`: for a returned shape, besides the prefix facts
(`Tools/ShippingMachineShapeUnfold.lean`),

* the shape's binders are the declaration's binders, then ONE binder per
  call entry carrying that entry's kind (`instBinders shape.insts`), then
  the slot binders, then the `let` binders;
* the layout's outputs are `machOutFields` of the output list.

**How the block is inverted.** After the prefix (named steps, as in the
first half) the remaining program has two more `match`es whose
continuation is repeated in the alternatives: the two on the enclosing run
(`run?.bind machRunApp?`, lines 5093 and 5119 — ONE expression, generalised
once and case-split once) and the second one on `machTupleKinds? d.type`
(5154, already decided by the prefix's case split). With those decided the
program is, in each of the four cases, a STRAIGHT LINE of `if … then none
else` and binds ending in `if unifiedGateRoot … then some {…} else none`.

The straight line is inverted by the two one-step lemmas `ite_none_inv` /
`bind_inv`, applied until neither applies. This is a loop, and it is
deliberate: the NUMBER of binds is not known without a build (each inlined
join point may or may not leave a `pure v >>= …`), none of the equations
of that stretch is used by the conclusion, and each step is a lemma
application that either matches the head of the hypothesis or fails — no
`split`, no `simp`, no case split, so it cannot branch or rewrite. What
follows the loop is explicit and fails loudly if the loop stopped early:
`ite_else_none_inv` (the final gate), `Option.some.inj`, `subst`.

Not stated here (reader invariants, `docs/parallel/B-readerinv.md`): what
`shape.insts` is, and that the slot-binder list is as long as the layout's
slot list.

UNVERIFIED: not built. Open risks, in order: (1) `generalize … :
Option.bind _ machRunApp? = run at h` (a pattern with a hole; the run
expression is `(match … with …).bind machRunApp?` in the observed form);
(2) that no other `match` is in control position on the straight line;
(3) the two `rfl`s on the final structure literal. -/
namespace Tools.ShippingMachineShapeUnfold
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderResultKind Tools.ShippingInstSignature

/-- **P4.** What the wrapper code of `machineShape?` determines of a
returned shape. -/
theorem machineShape?_some {sym : Bool} {params : List (String × Nat)} {d : DefinitionVal}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params (.defnInfo d) senv allow = some sp) :
    ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr) (ctor? : Option Name)
      (outs : List (String × MixedGateBinder)) (slotB letB : List (Name × MixedGateBinder))
      (W : Nat),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      declOuts? senv d.type = some (ctor?, outs) ∧
      sp.binders = bs ++ instBinders sp.insts ++ slotB ++ letB ∧
      sp.layout.outs = machOutFields W outs := by
  unfold machineShape? at h
  dsimp only at h
  -- 1. the outer `if`
  replace h := ite_none_inv h
  -- 2. the binders
  obtain ⟨x, hx, h⟩ := bind_inv h
  -- 3. the output list: a tuple result, or `machOuts?` (this also decides
  --    the later `match` on the same expression)
  generalize hk : machTupleKinds? d.type = tup at h
  cases tup <;> dsimp only at h
  all_goals obtain ⟨o, ho, h⟩ := bind_inv h
  all_goals
    have hd : declOuts? senv d.type = some o := by
      unfold declOuts?
      rw [hk]
      exact ho
  -- 4. the test on the output names
  all_goals replace h := ite_none_inv h
  -- 5. the enclosing run: one expression, matched twice
  all_goals generalize hrun : Option.bind _ machRunApp? = run at h
  all_goals rcases run with _ | ⟨dom, αs, initsE, body⟩
  all_goals try dsimp only at h
  -- 6. the straight line (see the header)
  all_goals
    repeat first
      | (replace h := ite_none_inv h)
      | (replace h := bind_inv h; obtain ⟨_, _, h⟩ := h)
      | (replace h := Option.bind_eq_some_iff.mp h; obtain ⟨_, _, h⟩ := h)
  -- 7. the gate, and the structure literal
  all_goals replace h := ite_else_none_inv h
  all_goals have hsp := Option.some.inj h
  all_goals subst hsp
  all_goals exact ⟨x.1, x.2, o.1, o.2, _, _, _, hx, hd, rfl, rfl⟩

/-! ## Consequences -/

/-- **P4, per entry** (R4 of the note): the binder of call entry `k` sits
right after the declaration's binders and has the entry's kind. -/
theorem machineShape?_callBinder {sym : Bool} {params : List (String × Nat)}
    {d : DefinitionVal} {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params (.defnInfo d) senv allow = some sp) :
    ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      ∀ k, k < sp.insts.length →
        (sp.binders.map (·.2))[bs.length + k]? = (sp.insts.map (·.2.2))[k]? := by
  obtain ⟨bs, e, _, _, slotB, letB, _, hpeel, _, hb, _⟩ := machineShape?_some h
  refine ⟨bs, e, hpeel, fun k hk => ?_⟩
  have hlen : k < ((instBinders sp.insts).map (·.2)).length := by
    rw [instBinders_kinds, List.length_map]; exact hk
  have hmid := getElem?_mid (bs.map (·.2)) ((instBinders sp.insts).map (·.2))
    (slotB.map (·.2)) (letB.map (·.2)) k hlen
  simp only [List.length_map, instBinders_kinds] at hmid
  rw [hb]
  simp only [List.map_append, instBinders_kinds]
  exact hmid

/-- **P2 + P4** (the child's half of the result side): a machine-route
declaration whose type has a one-Signal result kind `k` has exactly ONE
layout output, named `out`, of the hardware type of `k`. -/
theorem machineShape?_single_out {sym : Bool} {params : List (String × Nat)}
    {d : DefinitionVal} {senv : StructEnv} {allow : Bool} {sc : MachineShape}
    {k : MixedGateBinder}
    (h : machineShape? sym params (.defnInfo d) senv allow = some sc)
    (hres : machResultKind? d.type = some k) :
    ∃ W, sc.layout.outs =
      [{ name := "out", lo := W, width := machWidth k, ty := machHWType k }] := by
  obtain ⟨_, _, ctor?, outs, _, _, W, _, hout, _, ho⟩ := machineShape?_some h
  have hd : declOuts? senv d.type = some (none, [("out", k)]) :=
    declOuts?_of_resultKind senv hres
  rw [hd] at hout
  cases hout
  exact ⟨W, ho.trans (machOutFields_single W "out" k)⟩

/-- **P1 + P2 + P4** (the result side of the agreement proposition, for a
one-Signal callee whose shape is read from its DECLARED constant): the kind
the parent's reader is handed for callee `c` — `((structEnv env).inst c).2`
— is the hardware type of the child's only layout output.

Not covered: that the parent's call entry carries this kind (R1, inside the
`partial` `machInstance`); a child whose entry constant is its UNFOLDING
(`inlinedConst (userInliner env)`, P5 — `machineShape?_single_out` applies
to it once `machResultKind?` of the unfolded type is known). -/
theorem callee_single_out {env : Environment} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {d : DefinitionVal}
    {sym : Bool} {params : List (String × Nat)} {senvC : StructEnv} {allow : Bool}
    {sc : MachineShape}
    (hinst : (structEnv env).inst c = some (kinds, res))
    (hfind : env.find? c = some (.defnInfo d))
    (hc : machineShape? sym params (.defnInfo d) senvC allow = some sc) :
    ∃ W, sc.layout.outs =
      [{ name := "out", lo := W, width := machWidth res, ty := machHWType res }] := by
  rw [structEnv_inst] at hinst
  obtain ⟨_, ci, hci, _, hr⟩ := instSignature?_some hinst
  rw [hfind] at hci
  cases hci
  exact machineShape?_single_out hc hr

end Tools.ShippingMachineShapeUnfold
