import Tools.ShippingMachineShapeUnfold

/-! # The reader's decomposition of a returned shape, ONCE (R5 and the closing's `nDecl`)

`ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB` bundles
everything the WRAPPER text of `machineShape?` (`Sparkle/Compiler/Elab.lean`
5056–5186 at `6a20c9a7`) determines of a returned shape `sp`, so that the
block is unfolded in one place (`machineShape?_decomp`) and every later
fact is derived from the bundle:

| field | wrapper text |
|---|---|
| `peel` | 5062 `mixedGatePeel (packTupleInputs d.value)` |
| `outsEq` | 5063–5067 the output list (`declOuts?`) |
| `binders` | 5165–5168 `bs ++ instBinders ++ (st.names.toList.zip kinds) ++ lets` |
| `slots` | 5173 `machSlotFields ((kinds.map machWidth).zip st.inits.toList)` |
| `layoutOuts` | 5174 `machOutFields (kinds.map machWidth).sum outs` |
| `lets` | 5176 `lets := k`, `k = st.lets.size` |

`names`, `kinds`, `inits` are `st.names`, `st.kinds`, `st.inits` of the
reader state — results of the `partial` readers; the bundle says nothing
about them.

**R5, exactly.** The closing computes (`closeInstsM` 5199, `closeInstsGM`
5218)

    nDecl := shape.binders.length - shape.insts.length - shape.layout.slots.length - shape.layout.lets

From the bundle, PURE: `(instBinders sp.insts).length = sp.insts.length`,
`sp.layout.lets = letB.length`, `sp.layout.slots.length = min kinds.length
inits.length`, and the slot binders are `names.zip kinds`, of length `min
names.length kinds.length`. NOT pure: that these two minima agree. It
holds when `names`, `kinds`, `inits` have one length — a fact about the
`MachRead` the readers return (`machReserve`, a `def`, pushes the three
together; the loop readers are `partial`). So:

* `ShapeDecomp.nDecl` takes `R5 : (names.zip kinds).length =
  sp.layout.slots.length` as an EXPLICIT hypothesis and proves `nDecl =
  bs.length`;
* `ShapeDecomp.r5_of_lengths` gives `R5` from `names.length = kinds.length`
  and `inits.length = kinds.length`;
* `ShapeDecomp.callBinder` is the call-binder fact AT `nDecl + k`.

The walk of `machineShape?_decomp` is the ONLY unfolding of the block's
tail after the consolidation: `Tools/ShippingMachineShapeTail.lean`
(`machineShape?_some`, `_callBinder`, `_single_out`, `callee_single_out`)
imports this file and derives its statements from the bundle. The walk is
the one of the tail's version queued at `f8762e4c`: where that one stalled
(or what made it pass) is the repair to make HERE, once. UNVERIFIED:
written, not built. -/
namespace Tools.ShippingShapeDecomp
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderResultKind Tools.ShippingInstSignature
open Tools.ShippingMachineShapeUnfold

/-- What the wrapper text of `machineShape?` determines of a returned shape. -/
structure ShapeDecomp (d : DefinitionVal) (senv : StructEnv) (sp : MachineShape)
    (bs : List (Name × MixedGateBinder)) (e : Lean.Expr) (ctor? : Option Name)
    (outs : List (String × MixedGateBinder)) (names : List Name)
    (kinds : List MixedGateBinder) (inits : List Nat)
    (letB : List (Name × MixedGateBinder)) : Prop where
  peel : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e)
  outsEq : declOuts? senv d.type = some (ctor?, outs)
  binders : sp.binders = bs ++ instBinders sp.insts ++ names.zip kinds ++ letB
  slots : sp.layout.slots = machSlotFields ((kinds.map machWidth).zip inits)
  layoutOuts : sp.layout.outs = machOutFields (kinds.map machWidth).sum outs
  lets : sp.layout.lets = letB.length

/-- **The decomposition.** -/
theorem machineShape?_decomp {sym : Bool} {params : List (String × Nat)} {d : DefinitionVal}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params (.defnInfo d) senv allow = some sp) :
    ∃ bs e ctor? outs names kinds inits letB,
      ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB := by
  unfold machineShape? at h
  dsimp only at h
  -- 1. the outer `if`
  replace h := ite_none_inv h
  -- 2. the binders
  obtain ⟨x, hx, h⟩ := bind_inv h
  -- 3. the output list (this also decides the later `match` on the same
  --    expression)
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
  -- 6. the straight line: `if … then none else` and binds, by the two
  --    one-step inversions, until the final gate
  all_goals
    repeat first
      | (replace h := ite_none_inv h)
      | (replace h := bind_inv h; obtain ⟨_, _, h⟩ := h)
      | (replace h := Option.bind_eq_some_iff.mp h; obtain ⟨_, _, h⟩ := h)
  -- 7. the gate, and the structure literal
  all_goals replace h := ite_else_none_inv h
  all_goals have hsp := Option.some.inj h
  all_goals subst hsp
  all_goals
    exact ⟨x.1, x.2, o.1, o.2, _, _, _, _,
      ⟨hx, hd, rfl, rfl, rfl, by first | exact (List.length_map ..).symm | simp⟩⟩

/-! ## Pure consequences of the bundle -/

theorem instBinders_length (insts : List (Name × List Nat × MixedGateBinder)) :
    (instBinders insts).length = insts.length := by
  have h := congrArg List.length (instBinders_kinds insts)
  rw [List.length_map, List.length_map] at h
  exact h

theorem machSlotFields_length (l : List (Nat × Nat)) : (machSlotFields l).length = l.length := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    first
      | exact congrArg (· + 1) ih
      | (obtain ⟨w, i⟩ := p; simp only [machSlotFields, List.length_cons, ih])
      | simpa [machSlotFields] using ih

variable {d : DefinitionVal} {senv : StructEnv} {sp : MachineShape}
  {bs : List (Name × MixedGateBinder)} {e : Lean.Expr} {ctor? : Option Name}
  {outs : List (String × MixedGateBinder)} {names : List Name}
  {kinds : List MixedGateBinder} {inits : List Nat} {letB : List (Name × MixedGateBinder)}

/-- The layout has `min kinds.length inits.length` slots (pure). -/
theorem ShapeDecomp.slots_length (D : ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB) :
    sp.layout.slots.length = min kinds.length inits.length := by
  rw [D.slots, machSlotFields_length, List.length_zip, List.length_map]

/-- **R5 from the reader-state lengths**: when the three arrays of the
reader state have one length, the slot binders are as many as the layout's
slots. (The premises are facts about `partial` results.) -/
theorem ShapeDecomp.r5_of_lengths (D : ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB)
    (hn : names.length = kinds.length) (hi : inits.length = kinds.length) :
    (names.zip kinds).length = sp.layout.slots.length := by
  rw [D.slots_length, List.length_zip, hn, hi]

/-- **The closing's `nDecl` is the number of declaration binders**, under
R5. The left side is the expression of `closeInstsM` / `closeInstsGM`. -/
theorem ShapeDecomp.nDecl (D : ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB)
    (R5 : (names.zip kinds).length = sp.layout.slots.length) :
    sp.binders.length - sp.insts.length - sp.layout.slots.length - sp.layout.lets = bs.length := by
  have hi : (instBinders sp.insts).length = sp.insts.length := instBinders_length _
  have hl : sp.layout.lets = letB.length := D.lets
  have hb : sp.binders.length =
      bs.length + (instBinders sp.insts).length + (names.zip kinds).length + letB.length := by
    rw [D.binders, List.length_append, List.length_append, List.length_append]
  omega

/-- The call binder of entry `k` at the position counted from the
declaration binders (pure). -/
theorem ShapeDecomp.callBinder_bs
    (D : ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB)
    {k : Nat} (hk : k < sp.insts.length) :
    (sp.binders.map (·.2))[bs.length + k]? = (sp.insts.map (·.2.2))[k]? := by
  have hlen : k < ((instBinders sp.insts).map (·.2)).length := by
    rw [instBinders_kinds, List.length_map]; exact hk
  have hmid := getElem?_mid (bs.map (·.2)) ((instBinders sp.insts).map (·.2))
    ((names.zip kinds).map (·.2)) (letB.map (·.2)) k hlen
  simp only [List.length_map, instBinders_kinds] at hmid
  rw [D.binders]
  simp only [List.map_append, instBinders_kinds]
  exact hmid

/-- **R4 at the closing's position**: under R5, the binder at `nDecl + k`
(with the closing's `nDecl`) has the kind of call entry `k`. -/
theorem ShapeDecomp.callBinder
    (D : ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB)
    (R5 : (names.zip kinds).length = sp.layout.slots.length)
    {k : Nat} (hk : k < sp.insts.length) :
    (sp.binders.map (·.2))[(sp.binders.length - sp.insts.length - sp.layout.slots.length -
        sp.layout.lets) + k]? = (sp.insts.map (·.2.2))[k]? := by
  rw [D.nDecl R5]
  exact D.callBinder_bs hk

/-- A one-Signal result kind: the layout is ONE output `out` of that kind's
hardware type. -/
theorem ShapeDecomp.single_out
    (D : ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB)
    {k : MixedGateBinder} (hres : machResultKind? d.type = some k) :
    sp.layout.outs = [{ name := "out", lo := (kinds.map machWidth).sum, width := machWidth k,
                        ty := machHWType k }] := by
  have ho := D.outsEq
  rw [declOuts?_of_resultKind senv hres] at ho
  cases ho
  exact D.layoutOuts.trans (machOutFields_single _ "out" k)

end Tools.ShippingShapeDecomp
