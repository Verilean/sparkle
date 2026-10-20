import Tools.ShippingShapeDecomp

/-! # P4, second half — the consequences of the decomposition (CONSOLIDATED version)

**This is the consolidated version. Apply it only after the queued version
of this file (`f8762e4c`: its own unfold/walk of `machineShape?`) has been
built or has returned its stall head** — that diagnostic is what tells how
to write the straight-line stretch of the walk, and the walk now lives in
ONE place, `machineShape?_decomp` (`Tools/ShippingShapeDecomp.lean`). A
repair found on the queued version goes there, once.

The four statements are unchanged; they are corollaries of
`machineShape?_decomp`:

* `machineShape?_some` — the peel, the output list, `binders = bs ++
  instBinders insts ++ slotB ++ letB` (`slotB` is the decomposition's
  `names.zip kinds`), `layout.outs = machOutFields W outs`
  (`W = (kinds.map machWidth).sum`);
* `machineShape?_callBinder` — `ShapeDecomp.callBinder_bs` (the position
  counted from the declaration binders; the closing's position `nDecl + k`
  is `ShapeDecomp.callBinder`, under R5);
* `machineShape?_single_out` — `ShapeDecomp.single_out`;
* `callee_single_out` — P1 + the previous one.

Import order after the consolidation: `ShippingMachineShapeUnfold` (the
prefix, untouched, its own build) → `ShippingShapeDecomp` → this file.

Not stated here (`docs/parallel/B-readerinv.md` §8): what `shape.insts` is
(R1), and that the slot-binder list is as long as the layout's slot list
(R5).

UNVERIFIED: written, not built; depends on `machineShape?_decomp` (written,
not built). -/
namespace Tools.ShippingMachineShapeUnfold
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderResultKind Tools.ShippingInstSignature
open Tools.ShippingShapeDecomp

/-- **P4.** What the wrapper code of `machineShape?` determines of a
returned shape (the decomposition, with the slot binders and the output
offset existentially quantified). -/
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
  obtain ⟨bs, e, ctor?, outs, names, kinds, inits, letB, D⟩ := machineShape?_decomp h
  exact ⟨bs, e, ctor?, outs, names.zip kinds, letB, (kinds.map machWidth).sum,
    D.peel, D.outsEq, D.binders, D.layoutOuts⟩

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
  obtain ⟨bs, e, ctor?, outs, names, kinds, inits, letB, D⟩ := machineShape?_decomp h
  exact ⟨bs, e, D.peel, fun _ hk => D.callBinder_bs hk⟩

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
  obtain ⟨bs, e, ctor?, outs, names, kinds, inits, letB, D⟩ := machineShape?_decomp h
  exact ⟨(kinds.map machWidth).sum, D.single_out hres⟩

/-- **P1 + P2 + P4** (the result side of the agreement proposition, for a
one-Signal callee whose shape is read from its DECLARED constant): the kind
the parent's reader is handed for callee `c` — `((structEnv env).inst c).2`
— is the hardware type of the child's only layout output.

Not covered: that the parent's call entry carries this kind (R1, inside the
`partial` `machInstance`); a child whose entry constant is its UNFOLDING
(`inlinedConst (userInliner env)`, P5 — the normal case of a machine-route
child under `MachineDefines`; `machineShape?_single_out` applies to it once
`machResultKind?` of the unfolded type is known). -/
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
