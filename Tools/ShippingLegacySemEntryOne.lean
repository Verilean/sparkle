import Tools.ShippingLegacySemEntryIn
import Tools.ShippingLegacySemBinder
import Tools.ShippingLegacySemLeaves
import Tools.ShippingLegacySemLeaf

/-! # The legacy entry on a declaration with ONE `bits n` binder and a scalar result

Composition of the round-14 pieces: the entry's walk in the telescope's
context (`legacy_entry_walk_in`), the binder walk on one binder
(`bindInputsLegacy_one`), the leaves (`splitReturnLeaves_scalar`) and the
harness on a leaf of the entry-flag domain (`leaf_output`). The opaque
`TelescopeSpec … (EntryFacts …)` premise of `leaf_entry_output_walked`
(`BinderWalk` and the leaves as unproved facts) is replaced by named premises.

**Defined here**

* `LamTelescopeOne` — THE META-LIBRARY FACT: `lambdaTelescope` on
  `fun (nm : T) => b`, `b` not a lambda, runs its continuation on
  `#[.fvar id]` and `b.instantiateRevRange 0 1 #[.fvar id]` in a context
  whose local context declares `id` with user name `nm` and type
  `T.instantiateRevRange 0 0 #[]`. This is what `lambdaTelescopeImp.process`
  does (`src/lean/Lean/Meta/Basic.lean`, v4.32.1, lines 1598–1628: one `.lam`
  step — `d.instantiateRevRange 0 fvars.size fvars` with `fvars = #[]`,
  `mkFreshFVarId`, `lctx.mkLocalDecl fvarId n d bi` — then `finish`:
  `e.instantiateRevRange 0 fvars.size fvars`, `withReader (lctx := lctx)`,
  `withNewLocalInstancesImp`, `k fvars e`). It is `private partial`: not
  provable; it mentions no compiler definition. (That the fresh variable is
  FOUND in the extended context is `LocalContext.find?` after `mkLocalDecl`,
  a `PersistentHashMap` fact; part of the premise.)
* `OneBinderScope nm T leafOf mctx xs inner` — what the entry needs of the
  telescope's hand-over.
* `InputSkipped` — the third outcome (see `Tools/ShippingLegacySemBinder.lean`):
  the type oracle threw inside the walk's `try`, no port was bound, and the
  leaf was emitted alone.

**Proved here**

* `telescopeIn_of_lam` — `TelescopeIn body (OneBinderScope nm xTy leafOf)`
  from `LamTelescopeOne` and the SHAPE of `body` (`body = .lam nm T b bi`,
  `b` not a lambda, the two instantiations).
* `one_binder_entry_output` — the output statement of the legacy entry for
  such a declaration: memo hit, OR `RawValueAt` for every admissible
  valuation at which the leaf is in `LeafDom … "out" true`, OR
  `InputSkipped`.

**Premises of `one_binder_entry_output`, classified**

| Premise | Class |
|---|---|
| `old`, `mixed`, `hmach` (front end on only) | reflection of the environment |
| `htele` (`TelescopeIn … (OneBinderScope …)`) | Meta-library fact + the body's shape; split by `telescopeIn_of_lam` |
| `SignalTestFrame T` | provable (`Tools/ShippingLegacySemSignalFrame.lean`) |
| `InfersBits T n` | binder-type oracle (reflection through `inferHWTypeFromSignal`) |
| `(leafOf id).isLambda = false` | closed computation |
| `SignalTyped (leafOf id)` | result-type oracle (reflection through `inferType` / `whnf`) |

Outcomes NOT excluded: `MemoHit` (a heap fact of the caller, see
`Tools/ShippingLegacySemMemo.lean`) and `InputSkipped`. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-- **The Meta-library fact about `lambdaTelescope`, for one binder.** -/
def LamTelescopeOne : Prop :=
  ∀ (nm : Name) (T b : Lean.Expr) (bi : BinderInfo), b.isLambda = false →
  ∀ (α : Type) (k : Array Lean.Expr → Lean.Expr → MetaM α) (r : α),
    MReturns (Lean.Meta.lambdaTelescope (Lean.Expr.lam nm T b bi) k) r →
    ∃ (mctx : Meta.Context) (id : FVarId) (d0 : LocalDecl),
      mctx.lctx.find? id = some d0 ∧ d0.userName = nm ∧
      d0.type = T.instantiateRevRange 0 0 #[] ∧
      MRunsIn (k #[Lean.Expr.fvar id] (b.instantiateRevRange 0 1 #[Lean.Expr.fvar id])) mctx r

/-- What the telescope hands over for a declaration with one binder `nm : T`
and the result `leafOf id`: one variable, declared in the context of the
continuation's run with that name and type, and the instantiated body. -/
def OneBinderScope (nm : Name) (T : Lean.Expr) (leafOf : FVarId → Lean.Expr)
    (mctx : Meta.Context) (xs : Array Lean.Expr) (inner : Lean.Expr) : Prop :=
  ∃ (id : FVarId) (d0 : LocalDecl), xs = #[Lean.Expr.fvar id] ∧ inner = leafOf id ∧
    mctx.lctx.find? id = some d0 ∧ d0.userName = nm ∧ d0.type = T

/-- The telescope's hand-over for a one-binder body, from the Meta-library
fact and the body's shape. -/
theorem telescopeIn_of_lam (htel : LamTelescopeOne) {body : Lean.Expr} {nm : Name}
    {T b xTy : Lean.Expr} {bi : BinderInfo} {leafOf : FVarId → Lean.Expr}
    (hb : body = Lean.Expr.lam nm T b bi) (hl : b.isLambda = false)
    (hT : T.instantiateRevRange 0 0 #[] = xTy)
    (hi : ∀ id : FVarId, b.instantiateRevRange 0 1 #[Lean.Expr.fvar id] = leafOf id) :
    TelescopeIn body (OneBinderScope nm xTy leafOf) := by
  intro α k r hrun
  rw [hb] at hrun
  obtain ⟨mctx, id, d0, hfind, hnm, hty, hk⟩ := htel nm T b bi hl α k r hrun
  rw [hi id] at hk
  have hs : OneBinderScope nm xTy leafOf mctx #[Lean.Expr.fvar id] (leafOf id) := by
    unfold OneBinderScope
    exact ⟨id, d0, rfl, rfl, hfind, hnm, hty.trans hT⟩
  exact ⟨mctx, #[Lean.Expr.fvar id], leafOf id, hs, hk⟩

/-- **The third outcome**: the leaf was emitted with NO input port bound (the
binder was skipped by the legacy walk), and the module finished from that
state. -/
def InputSkipped (logProf : String → IO Unit) (declName : Name)
    (leafOf : FVarId → Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ (id : FVarId) (cache : IO.Ref (ExprStructMap String)) (returned : String)
    (st : CircuitState),
    Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache
        logProf [("out", leafOf id)] none 0)
      (entryCompilerState false cache) (CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)) returned st ∧
    m = (addClockResetIfSequential st.module).finalize

/-- **The output of a legacy-route declaration with one `bits n` binder and a
scalar Signal result.** -/
theorem one_binder_entry_output {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {nm : Name} {n : Nat} {T : Lean.Expr}
    {leafOf : FVarId → Lean.Expr} {m : Sparkle.IR.AST.Module} {d : Design} {cfe : Bool}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (OneBinderScope nm T leafOf))
    (hsig : SignalTestFrame T) (hinf : InfersBits T n)
    (hleaf : ∀ id : FVarId, (leafOf id).isLambda = false ∧ SignalTyped (leafOf id))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false cfe (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    (∃ (id : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
        ([(nm, MixedGateBinder.bits n)].zip [id])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName)) →
      ∀ v : Value, 0 < v.kind.width →
      LeafDom (setupOf declName [(nm, MixedGateBinder.bits n)] [id] cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName [(nm, MixedGateBinder.bits n)] [id] cache bools bits).bools
          (setupOf declName [(nm, MixedGateBinder.bits n)] [id] cache bools bits).bits)
        "out" true (leafOf id) v →
      Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width
        [(nm, MixedGateBinder.bits n)] m initial mems v.toNat) ∨
    InputSkipped logProf declName leafOf m := by
  rcases legacy_entry_walk_in old mixed hmach htele hr with hit |
    ⟨body0, mctx, xs, inner, leaves, cache, returned, st, hopen,
      ⟨id, d0, hxs, hinner, hfind, hnm, hty⟩, hsplit, run, hm, legal⟩
  · exact Or.inl hit
  · refine Or.inr ?_
    -- the leaves: one, `("out", leafOf id)`
    rw [hinner] at hsplit
    have hl : leaves.toList = [("out", leafOf id)] :=
      splitReturnLeaves_scalar (hleaf id).1 (hleaf id).2 hsplit
    rw [hl] at run
    rw [hxs] at run
    -- the binder walk, in the context the telescope installed
    have hsig' : SignalTestFrame d0.type := by
      rw [hty]
      exact hsig
    have hinf' : InfersBits d0.type n := by
      rw [hty]
      exact hinf
    rcases bindInputsLegacy_one hfind hsig' hinf' run with bound | skipped
    · refine Or.inl ⟨id, cache, ?_⟩
      rw [hnm] at bound
      have run' : HarnessRun logProf declName [(nm, MixedGateBinder.bits n)] [id] cache
          (leafOf id) returned st := bound
      intro bools bits initial mems values v pos dom
      exact leaf_output run' hm legal bools bits initial mems values v pos dom
    · have hsk : InputSkipped logProf declName leafOf m := by
        unfold InputSkipped
        exact ⟨id, cache, returned, st, skipped, hm⟩
      exact Or.inr hsk

end Tools.ShippingLegacySem
