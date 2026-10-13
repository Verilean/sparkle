import Tools.ShippingLegacySemTelescopeN
import Tools.ShippingLegacySemBinderListD

/-! # The legacy entry with scalar AND non-hardware (domain) binders

`list_entry_output` (`Tools/ShippingLegacySemEntryList.lean`) restated over
the binder walk with three kinds (`bindInputsLegacy_prepareD`): `bits n`,
`bool`, and `.domain` — a binder on whose type the hardware-type oracle has
no returning run, which the legacy walk skips and for which the certified
`prepare` does nothing. `list_entry_output` is kept.

**Defined here**: `ListScopeD bs leafOf mctx xs inner` — variables `ids`, the
body `leafOf ids`, and `DeclsAtD mctx xs 0 bs ids`.

**Proved here**

* `list_entry_outputD` — as `list_entry_output`, for a binder list `bs` of
  any of the three kinds.
* `telescopeIn_of_lam3` — the hand-over `ListScopeD` for a body with THREE
  binders, from `LamTelescopeN` and the body's shape; each binder's oracle
  facts are asked on its declared type as the telescope computes it
  (`instantiateRevRange` over the variables opened before it — for the
  second and third binder a statement for every earlier variable).

**Premises of `list_entry_outputD`, classified**: `htele` (Meta-library fact
+ the body's shape + the binder-type oracle facts, split by
`telescopeIn_of_lam3`), the result-type oracle `SignalTyped`, the closed
`isLambda = false`; `old` / `mixed` / `hmach` (front end on only). `MemoHit`
stays. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-- What the telescope hands over for a declaration with the binders `bs`
(any of the three kinds) and the result `leafOf ids`. -/
def ListScopeD (bs : List (Name × MixedGateBinder)) (leafOf : List FVarId → Lean.Expr)
    (mctx : Meta.Context) (xs : Array Lean.Expr) (inner : Lean.Expr) : Prop :=
  ∃ ids : List FVarId, inner = leafOf ids ∧ DeclsAtD mctx xs 0 bs ids

/-- **The output of a legacy-route declaration with scalar and non-hardware
binders and a scalar Signal result.** -/
theorem list_entry_outputD {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {cfe : Bool}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (ListScopeD bs leafOf))
    (hleaf : ∀ ids : List FVarId, (leafOf ids).isLambda = false ∧ SignalTyped (leafOf ids))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false cfe (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName)) →
      ∀ v : Value, 0 < v.kind.width →
      LeafDom (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits)
        "out" true (leafOf ids) v →
      Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width bs m initial mems v.toNat := by
  rcases legacy_entry_walk_in old mixed hmach htele hr with hit |
    ⟨body0, mctx, xs, inner, leaves, cache, returned, st, hopen,
      ⟨ids, hinner, hdecls⟩, hsplit, run, hm, legal⟩
  · exact Or.inl hit
  · refine Or.inr ⟨ids, cache, DeclsAtD.length bs ids 0 hdecls, ?_⟩
    rw [hinner] at hsplit
    have hl : leaves.toList = [("out", leafOf ids)] :=
      splitReturnLeaves_scalar (hleaf ids).1 (hleaf ids).2 hsplit
    rw [hl] at run
    intro bools bits initial mems values v pos dom
    have leaf := bindInputsLegacy_prepareD (bools := bools) (bits := bits) bs ids 0
      (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName)) hdecls run
    exact harness_sound_leaf (bs := bs) (ids := ids) hm legal bools bits initial mems
      values leaf v pos (leaf_translate_spec dom) (leaf_translate_order dom)

/-- The array of the first two variables, as the telescope builds it. -/
abbrev fv2p (id1 id2 : FVarId) : Array Lean.Expr := (fv1 id1).push (Lean.Expr.fvar id2)

/-- The array of three variables, as the continuation receives it. -/
abbrev fv3 (id1 id2 id3 : FVarId) : Array Lean.Expr :=
  ([id1, id2, id3].map Lean.Expr.fvar).toArray

/-- **The telescope's hand-over for a three-binder body**, from the
Meta-library fact, the body's shape, and the oracle facts of the three
declared types. -/
theorem telescopeIn_of_lam3 (htel : LamTelescopeN) {body : Lean.Expr} {n1 n2 n3 : Name}
    {T1 T2 T3 b : Lean.Expr} {bi1 bi2 bi3 : BinderInfo} {k1 k2 k3 : MixedGateBinder}
    {leafOf : List FVarId → Lean.Expr}
    (hb : body = Lean.Expr.lam n1 T1 (Lean.Expr.lam n2 T2 (Lean.Expr.lam n3 T3 b bi3) bi2) bi1)
    (hl : b.isLambda = false)
    (hT1 : TypeOk k1 (T1.instantiateRevRange 0 (#[] : Array Lean.Expr).size #[]))
    (hT2 : ∀ id1 : FVarId, TypeOk k2 (T2.instantiateRevRange 0 (fv1 id1).size (fv1 id1)))
    (hT3 : ∀ id1 id2 : FVarId,
      TypeOk k3 (T3.instantiateRevRange 0 (fv2p id1 id2).size (fv2p id1 id2)))
    (hi : ∀ id1 id2 id3 : FVarId,
      b.instantiateRevRange 0 (fv3 id1 id2 id3).size (fv3 id1 id2 id3) =
        leafOf [id1, id2, id3]) :
    TelescopeIn body (ListScopeD [(n1, k1), (n2, k2), (n3, k3)] leafOf) := by
  intro α k r hrun
  rw [hb] at hrun
  obtain ⟨mctx, ids, hdecl, hk⟩ :=
    htel [(n1, T1, bi1), (n2, T2, bi2), (n3, T3, bi3)] b hl α k r hrun
  rcases ids with _ | ⟨id1, _ | ⟨id2, _ | ⟨id3, _ | ⟨id4, ids⟩⟩⟩⟩
  · exact False.elim hdecl
  · obtain ⟨_, h2⟩ := hdecl
    exact False.elim h2
  · obtain ⟨_, _, h3⟩ := hdecl
    exact False.elim h3
  · obtain ⟨⟨d1, hf1, hn1, ht1⟩, ⟨d2, hf2, hn2, ht2⟩, ⟨d3, hf3, hn3, ht3⟩, _⟩ := hdecl
    have hk' : MRunsIn (k (fv3 id1 id2 id3) (leafOf [id1, id2, id3])) mctx r := by
      rw [← hi id1 id2 id3]
      exact hk
    have ho1 : TypeOk k1 d1.type := by
      rw [ht1]
      exact hT1
    have ho2 : TypeOk k2 d2.type := by
      rw [ht2]
      exact hT2 id1
    have ho3 : TypeOk k3 d3.type := by
      rw [ht3]
      exact hT3 id1 id2
    have h0 : 0 < (fv3 id1 id2 id3).size := Nat.zero_lt_succ 2
    have h1 : 0 + 1 < (fv3 id1 id2 id3).size := Nat.succ_lt_succ (Nat.zero_lt_succ 1)
    have h2 : 0 + 1 + 1 < (fv3 id1 id2 id3).size := Nat.lt_succ_self 2
    have hx0 : ((fv3 id1 id2 id3)[0]'h0).fvarId! = id1 := by
      first | rfl | simp [fv3, Lean.Expr.fvarId!]
    have hx1 : ((fv3 id1 id2 id3)[0 + 1]'h1).fvarId! = id2 := by
      first | rfl | simp [fv3, Lean.Expr.fvarId!]
    have hx2 : ((fv3 id1 id2 id3)[0 + 1 + 1]'h2).fvarId! = id3 := by
      first | rfl | simp [fv3, Lean.Expr.fvarId!]
    have hend : (fv3 id1 id2 id3).size ≤ 0 + 1 + 1 + 1 := Nat.le_refl 3
    have hdecls : DeclsAtD mctx (fv3 id1 id2 id3) 0 [(n1, k1), (n2, k2), (n3, k3)]
        [id1, id2, id3] :=
      And.intro
        (Exists.intro h0 (And.intro hx0 (Exists.intro d1
          (And.intro hf1 (And.intro hn1 ho1)))))
        (And.intro
          (Exists.intro h1 (And.intro hx1 (Exists.intro d2
            (And.intro hf2 (And.intro hn2 ho2)))))
          (And.intro
            (Exists.intro h2 (And.intro hx2 (Exists.intro d3
              (And.intro hf3 (And.intro hn3 ho3)))))
            hend))
    have hs : ListScopeD [(n1, k1), (n2, k2), (n3, k3)] leafOf mctx (fv3 id1 id2 id3)
        (leafOf [id1, id2, id3]) := by
      unfold ListScopeD
      exact ⟨[id1, id2, id3], rfl, hdecls⟩
    exact ⟨mctx, fv3 id1 id2 id3, leafOf [id1, id2, id3], hs, hk'⟩
  · obtain ⟨_, _, _, h4⟩ := hdecl
    exact False.elim h4

end Tools.ShippingLegacySem
