import Tools.ShippingReaderResultKind
import Tools.ShippingInstSignature

/-! # P4, first half — the PREFIX of `machineShape?`, inverted one step at a time

`machineShape?` (`Sparkle/Compiler/Elab.lean` 5056) is a plain definition:
an `Option` `do` block. This file inverts its first steps, each by a named
inversion lemma applied to the hypothesis (no generic walk, no `split`):

1. the outer `if symbolicMode || !parameters.isEmpty then none else`
   (`ite_none_inv`);
2. the bind of `mixedGatePeel (packTupleInputs d.value)` (`bind_inv`);
3. the `match machTupleKinds? d.type` (`generalize` + `cases`), and in each
   alternative the bind of the output list (`bind_inv`).

`machineShape?_prefix`: a returned shape has declaration binders
`mixedGatePeel (packTupleInputs d.value) = some x` and an output list
`declOuts? senv d.type = some o`.

The elaborated form these steps are written against was OBSERVED in the
integrator's failed build of the first version (after `unfold` and
`dsimp only`): `if (sym || !params.isEmpty) = true then none else do let __x
← mixedGatePeel …; match machTupleKinds? d.type with | some ks => do let
__x_1 ← some (none, …); if … | none => …` — the pattern matches on pairs are
projections (`__x.snd`), and the continuation of a `match` is repeated in
its alternatives (the join points are inlined by `dsimp only`).

The REST of the block (to the final structure literal) is
`Tools/ShippingMachineShapeTail.lean`; it is a separate file so that a
failure there does not take this half with it.

**The boundary** (where a `partial` function's result enters; lines of
`Sparkle/Compiler/Elab.lean` at `6a20c9a7`). `shape.insts`,
`shape.instFields`, the slot binders (`st.names`, `st.kinds`), the `let`
binders (`st.lets`) and the reset values (`st.inits`) are fields of the
`MachRead` returned by, in order:

| line | call | `partial`? |
|---|---|---|
| 5074 | `machNorm senv e` (the body before it is read) | `partial` (4954) |
| 5098 | `machConv senv … dom st` (the domain) | `partial` (3881) |
| 5099 | `machReserve senv.natOf …` | a `def` (3696) |
| 5106 | `machLoopRoot senv env v st` (a root `Signal.loop`) | `partial` (4190) |
| 5111 | `machConv senv env 0 v st` (a root `let`) | `partial` (3881) |
| 5121 | `machChain senv (.regs 0 :: env) body st` (the body) | `partial` (4121) |
| 5127 | `machConv senv env 0 root st` (a root expression) | `partial` (3881) |

The call entries themselves are pushed by `machInstance` (4042) and
`machInstanceS` (4076), both `partial`, reached only from inside
`machConv` / `machChain`.

Second version (the first one's generic walk did not move). The helper
lemmas `map_snd_instName`, `instBinders_kinds`, `getElem?_mid` are as in
the first version except that `instBinders` is written with projections
(the form `dsimp only` gives the reader's lambda). UNVERIFIED: not built. -/
namespace Tools.ShippingMachineShapeUnfold
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderResultKind Tools.ShippingInstSignature

/-! ## One-step inversions of an `Option` program -/

/-- `if c then none else x` returned: `x` did. -/
theorem ite_none_inv {α : Type} {c : Prop} [Decidable c] {x : Option α} {b : α}
    (h : (if c then none else x) = some b) : x = some b := by
  by_cases hc : c
  · rw [if_pos hc] at h; cases h
  · rw [if_neg hc] at h; exact h

/-- `if c then x else none` returned: `x` did. -/
theorem ite_else_none_inv {α : Type} {c : Prop} [Decidable c] {x : Option α} {b : α}
    (h : (if c then x else none) = some b) : x = some b := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact h
  · rw [if_neg hc] at h; cases h

/-- A bind of the `Option` monad returned: its first action did, and the
continuation on that value did. -/
theorem bind_inv {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b :=
  Option.bind_eq_some_iff.mp h

/-! ## The prefix -/

/-- The output list `machineShape?` reads off a declaration's type (the
same text as its lines 5063–5067). -/
def declOuts? (senv : StructEnv) (ty : Lean.Expr) :
    Option (Option Name × List (String × MixedGateBinder)) :=
  match machTupleKinds? ty with
  | some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)])
  | none => machOuts? senv ty

/-- **P4, prefix.** A returned shape was read from a value whose binders
peel, and from a type whose output list reads. -/
theorem machineShape?_prefix {sym : Bool} {params : List (String × Nat)} {d : DefinitionVal}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params (.defnInfo d) senv allow = some sp) :
    ∃ (x : List (Name × MixedGateBinder) × Lean.Expr)
      (o : Option Name × List (String × MixedGateBinder)),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some x ∧
      declOuts? senv d.type = some o := by
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
    refine ⟨x, o, hx, ?_⟩
    unfold declOuts?
    rw [hk]
    exact ho
  | some ks =>
    dsimp only at h
    obtain ⟨o, ho, h⟩ := bind_inv h
    refine ⟨x, o, hx, ?_⟩
    unfold declOuts?
    rw [hk]
    exact ho

/-- **P2 + the prefix's reader**: a type with a one-Signal result kind has
the output list `[("out", k)]`. -/
theorem declOuts?_of_resultKind (senv : StructEnv) {ty : Lean.Expr} {k : MixedGateBinder}
    (hres : machResultKind? ty = some k) :
    declOuts? senv ty = some (none, [("out", k)]) := by
  obtain ⟨ht, hm⟩ := machOuts?_of_resultKind senv ty k hres
  simp only [declOuts?, ht, hm]

/-! ## The binders of the call entries (pure list facts) -/

/-- The binders of the call entries: one per entry, named `inst{j}`, of the
entry's kind (`machineShape?` 5165–5166, with the pair pattern written as
projections). -/
def instBinders (insts : List (Name × List Nat × MixedGateBinder)) :
    List (Name × MixedGateBinder) :=
  ((List.range insts.length).zip (insts.map (·.2.2))).map
    fun p => (Name.mkSimple s!"inst{p.1}", p.2)

theorem map_snd_instName (l : List (Nat × MixedGateBinder)) :
    (l.map fun p => (Name.mkSimple s!"inst{p.1}", p.2)).map (·.2) = l.map (·.2) := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    first
      | exact congrArg (List.cons p.2) ih
      | simp only [List.map_cons, ih]
      | simpa using ih

/-- The kinds of the call binders are the entries' kinds, in order. -/
theorem instBinders_kinds (insts : List (Name × List Nat × MixedGateBinder)) :
    (instBinders insts).map (·.2) = insts.map (·.2.2) := by
  have h1 := map_snd_instName ((List.range insts.length).zip (insts.map (·.2.2)))
  have h2 : ((List.range insts.length).zip (insts.map (·.2.2))).map (·.2) =
      insts.map (·.2.2) := by
    first
      | exact List.map_snd_zip (by simp)
      | exact List.map_snd_zip _ _ (by simp)
      | simp [List.map_snd_zip]
  exact h1.trans h2

theorem getElem?_mid {α : Type} (A B C D : List α) (k : Nat) (hk : k < B.length) :
    (A ++ B ++ C ++ D)[A.length + k]? = B[k]? := by
  simp only [List.append_assoc]
  first
    | rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        List.getElem?_append_left hk]
    | simp [List.getElem?_append, hk]

end Tools.ShippingMachineShapeUnfold
