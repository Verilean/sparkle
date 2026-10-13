import Tools.ShippingLegacySemHarness
import Tools.ShippingLegacySemOrder

/-! # The legacy arm of the entry, walked — and the output statement it gives

`synthesizeFromConst` (`Sparkle/Compiler/Elab.lean`) tries the certified
shape, the mixed certified shape and the machine shape; when all three
decline it runs the LEGACY arm: the memo read, `openRecordInputs`,
`stripMemoizeWrappers`, `lambdaTelescope`, `splitReturnLeaves`, a fresh
expression cache, `bindInputsLegacy … (emitLeaves …)` from the fresh builder
state, `finishSynth`, the memo write.

**Proved here**

* `legacy_entry_walk` — the arm, step by step, with no parameters, not
  symbolic, the certified front end ON (the shipping configuration; the three
  gates then decline by premise) or OFF (the gates are not asked — the
  configuration in which `useDbl` reaches this arm: with the front end on,
  `entryConst` hands over the unfolded constant and a certified gate takes
  it), for a definition `.defnInfo dv`: a successful run is either a MEMO HIT (`MemoHit`: the
  result was read from `sparkleSubModuleCache`, nothing was compiled) or a
  successful run of `bindInputsLegacy [] false xs 0 (emitLeaves translate
  cache logProf leaves.toList none 0)` from `entryCompilerState false cache`
  and the fresh builder state, finished as the certified entry finishes
  (`finishSynth_returns`: the module equation AND the legal-name fact — the
  legacy arm has the same check), where `xs`, `inner` are what the telescope
  handed over and `leaves` is a result of `splitReturnLeaves inner`.
* `legacy_leaf_output_closed`, `legacy_entry_output_walked` (in place of the
  hypothesis-only `legacy_leaf_output` / `legacy_entry_output` of
  `Tools/ShippingLegacySemEntry.lean`): from the walk, harness soundness
  (`harness_sound_at`, proved), the contract and the order on `LegacyDom`
  (`legacy_translate_contract`, `legacy_translate_order`, proved) — the
  output statement `RawValueAt` for every admissible valuation at which the
  leaf is in the combined domain. No `HarnessSound`, no `ActionOrder`
  hypothesis is left.

**Premises, classified**

*Reflection of the environment* (closed computations on the constant; for a
concrete declaration each is an evaluation):

* `old`, `mixed` — the two certified gates decline the constant (asked only
  when the front end is on);
* `hmach` — `machineShape?` declines it for every structure environment.
  (Stated for every `projs`: the run reads `structEnv (← getEnv)`; a
  declaration-specific version needs the environment of the run.)

*A fact about Lean's `Meta` library* (neither reflection nor a heap fact):

* `TelescopeSpec` — a successful run of `lambdaTelescope body k` is a
  successful run of `k xs inner` for some `xs`, `inner` with the property `P`.
  `lambdaTelescope` is `map2MetaM` over `lambdaTelescopeImp` (control
  operators, `withReader` on the local context); not walked. It is a premise
  for EVERY continuation, so it does not mention the compiler.

*Facts about the run* (oracle results; carried by `EntryFacts`, the property
`P` asked of the telescope):

* `BinderWalk xs bs ids` — the legacy binder walk over the telescope's
  variables is the certified binder walk over `bs.zip ids`. NOT walked, and
  not walkable with `Returns` as it is: `bindInputsLegacy` reads each
  binder's name and type with `fvarId.getDecl`, i.e. from the LOCAL CONTEXT
  the telescope installed, and `Returns` / `MReturns` quantify the `Meta`
  context existentially per run — the link between "the telescope declared
  `x` with this name and type" and "`getDecl` returns it" cannot be stated.
  (needs-definition: a run predicate that exposes the local context, then
  needs-walk: `isSignalBinderType`, `inferHWTypeFromSignal`, the `try`.)
* the leaves — every result of `splitReturnLeaves inner` is the single leaf
  `("out", leafOf ids)` (needs-walk of `splitReturnLeavesStep` for a scalar
  Signal result; an oracle: `whnf` / `inferType` inside).

*The second outcome* (not a premise): `MemoHit`. At the outermost entry the
memo was reset just before (`sparkleSubModuleCache.set {}` at depth 0) — that
is in the caller (`synthesizeCombinationalCoreWith`), outside this function,
and a heap fact: not provable from `MReturns`, which does not model the heap.

**Shapes this proof assumes (NOT observed — written without a build)**: the
`let x ← if …` / `let x ← match …` / `if … then …`-without-`else` items are
taken as join points (`have __do_jp := …`), with the plain-bind form as the
alternative where `first` can choose. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-! ## Two inversions -/

theorem mret_ite_pos {α : Type} {c : Prop} [Decidable c] {a b : MetaM α} {r : α}
    (h : MReturns (if c then a else b) r) (hc : c) : MReturns a r := by
  rw [if_pos hc] at h
  exact h

theorem mret_ite_neg {α : Type} {c : Prop} [Decidable c] {a b : MetaM α} {r : α}
    (h : MReturns (if c then a else b) r) (hc : ¬ c) : MReturns b r := by
  rw [if_neg hc] at h
  exact h

/-! ## The premises -/

/-- The result was read from the per-synthesis memo: nothing was compiled. -/
def MemoHit (declName : Name) (m : Sparkle.IR.AST.Module) (d : Design) : Prop :=
  ∃ memo, MReturns sparkleSubModuleCache.get memo ∧ memo.get? declName = some (m, d)

/-- A successful run of the telescope is a successful run of its continuation
on some variables and body with property `P` (a fact about `Lean.Meta`). -/
def TelescopeSpec (body : Lean.Expr) (P : Array Lean.Expr → Lean.Expr → Prop) : Prop :=
  ∀ (α : Type) (k : Array Lean.Expr → Lean.Expr → MetaM α) (r : α),
    MReturns (Lean.Meta.lambdaTelescope body k) r →
    ∃ xs inner, P xs inner ∧ MReturns (k xs inner) r

/-- The legacy binder walk over the telescope's variables is the certified
binder walk over the binders `bs` and the variables `ids` (a fact about the
run; not walked — see the header). -/
def BinderWalk (xs : Array Lean.Expr) (bs : List (Name × MixedGateBinder))
    (ids : List FVarId) : Prop :=
  ∀ (k : CompilerM String) (ctx : CompilerState) (s t : CircuitState) (r : String),
    Returns (bindInputsLegacy [] false xs 0 k) ctx s r t →
    Returns (bindMixedCertifiedInputs k (bs.zip ids)) ctx s r t

/-- What the telescope's variables and body are, for a declaration with
binders `bs` and one scalar leaf `leafOf ids`. -/
def EntryFacts (bs : List (Name × MixedGateBinder)) (leafOf : List FVarId → Lean.Expr)
    (xs : Array Lean.Expr) (inner : Lean.Expr) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧ BinderWalk xs bs ids ∧
    ∀ leaves, MReturns (splitReturnLeaves inner) leaves → leaves.toList = [("out", leafOf ids)]

/-! ## The walk -/

/-- **The legacy arm of the entry, walked.** -/
theorem legacy_entry_walk {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {P : Array Lean.Expr → Lean.Expr → Prop}
    {m : Sparkle.IR.AST.Module} {d : Design}
    {cfe : Bool}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeSpec (stripMemoizeWrappers body0) P)
    (hr : MReturns (synthesizeFromConst translate logProf declName [] false cfe
      (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    ∃ (body0 : Lean.Expr) (xs : Array Lean.Expr) (inner : Lean.Expr)
      (leaves : Array (String × Lean.Expr)) (cache : IO.Ref (ExprStructMap String))
      (returned : String) (st : CircuitState),
      MReturns (openRecordInputs dv.value) body0 ∧ P xs inner ∧
      MReturns (splitReturnLeaves inner) leaves ∧
      Returns (bindInputsLegacy [] false xs 0
          (emitLeaves translate cache logProf leaves.toList none 0))
        (entryCompilerState false cache) (CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)) returned st ∧
      m = (addClockResetIfSequential st.module).finalize ∧
      Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true := by
  unfold synthesizeFromConst at hr
  cases cfe
  all_goals
    -- the two certified gates decline (front end on), or are not asked (off)
    first
      | simp only [↓reduceIte, old rfl, mixed rfl] at hr
      | simp only [Bool.false_eq_true, ↓reduceIte] at hr
    -- the machine shape declines, or is not asked: `machine? = none`,
    -- `machineResult? = none`. Four shapes: join point / plain bind, front
    -- end on / off
    first
      | (have a1 := mret_ite_pos hr rfl
         obtain ⟨env, _, a2⟩ := MReturns.bind a1
         obtain ⟨y, hy, a3⟩ := MReturns.bind a2
         obtain rfl := MReturns.pure hy
         rw [hmach rfl] at a3
         obtain ⟨y2, hy2, h2⟩ := MReturns.bind a3
         obtain rfl := MReturns.pure hy2)
      | (obtain ⟨mq, hmq, b1⟩ := MReturns.bind hr
         have b2 := mret_ite_pos hmq rfl
         obtain ⟨env, _, b3⟩ := MReturns.bind b2
         have hn := MReturns.pure b3
         rw [hmach rfl] at hn
         subst hn
         obtain ⟨y2, hy2, h2⟩ := MReturns.bind b1
         obtain rfl := MReturns.pure hy2)
      | (have a1 := mret_ite_neg hr (by decide)
         obtain ⟨y, hy, a3⟩ := MReturns.bind a1
         obtain rfl := MReturns.pure hy
         obtain ⟨y2, hy2, h2⟩ := MReturns.bind a3
         obtain rfl := MReturns.pure hy2)
      | (obtain ⟨mq, hmq, b1⟩ := MReturns.bind hr
         have hn := MReturns.pure (mret_ite_neg hmq (by decide))
         subst hn
         obtain ⟨y2, hy2, h2⟩ := MReturns.bind b1
         obtain rfl := MReturns.pure hy2)
      | (obtain ⟨y, hy, a3⟩ := MReturns.bind hr
         obtain rfl := MReturns.pure hy
         obtain ⟨y2, hy2, h2⟩ := MReturns.bind a3
         obtain rfl := MReturns.pure hy2)
    -- the memo read
    have h3 := mret_ite_pos h2 rfl
    obtain ⟨memo, hmemo, h4⟩ := MReturns.bind h3
    cases hget : memo.get? declName with
    | some cached =>
      rw [hget] at h4
      obtain ⟨_, _, h5⟩ := MReturns.bind h4
      have e := MReturns.pure h5
      exact Or.inl ⟨memo, hmemo, by rw [hget, e]⟩
    | none =>
      rw [hget] at h4
      refine Or.inr ?_
      obtain ⟨_, _, h5⟩ := MReturns.bind h4      -- log
      obtain ⟨_, _, h6⟩ := MReturns.bind h5      -- log (the `.defnInfo` alternative)
      obtain ⟨t0, _, h7⟩ := MReturns.bind h6     -- clock
      obtain ⟨_, _, h8⟩ := MReturns.bind h7      -- log
      obtain ⟨body0, hopen, h9⟩ := MReturns.bind h8
      obtain ⟨t1, _, h10⟩ := MReturns.bind h9    -- clock
      obtain ⟨_, _, h11⟩ := MReturns.bind h10    -- log
      obtain ⟨xs, inner, hP, h12⟩ := htele body0 hopen _ _ _ h11
      obtain ⟨_, _, h13⟩ := MReturns.bind h12    -- log
      -- the retained-parameter check is under `if symbolicMode`: a join
      -- point, already reduced by `simp`, or a plain bind
      first
        | (have h14 := mret_ite_neg h13 Bool.false_ne_true
           obtain ⟨leaves, hsplit, h15⟩ := MReturns.bind h14)
        | (obtain ⟨leaves, hsplit, h15⟩ := MReturns.bind h13
           have hsplit : MReturns (splitReturnLeaves inner) leaves := hsplit)
        | (obtain ⟨_, _, h14⟩ := MReturns.bind h13
           obtain ⟨leaves, hsplit, h15⟩ := MReturns.bind h14)
      obtain ⟨t2, _, h16⟩ := MReturns.bind h15   -- clock
      obtain ⟨_, _, h17⟩ := MReturns.bind h16    -- log
      obtain ⟨cache, _, h18⟩ := MReturns.bind h17
      obtain ⟨⟨returned, st⟩, run, h19⟩ := MReturns.bind h18
      obtain ⟨res, hfin, h20⟩ := MReturns.bind h19
      have hres : (m, d) = res := by
        first
          | (have c1 := mret_ite_pos h20 rfl
             obtain ⟨_, _, c2⟩ := MReturns.bind c1
             exact MReturns.pure c2)
          | (obtain ⟨_, _, c2⟩ := MReturns.bind h20
             exact MReturns.pure c2)
      subst hres
      obtain ⟨hm, _, legal⟩ := finishSynth_returns hfin
      exact ⟨body0, xs, inner, leaves, cache, returned, st, hopen, hP, hsplit,
        MReturns.run run, hm, legal⟩

/-! ## The output statement -/

/-- **The output of a legacy-route leaf**, with no hypothesis about the
harness or the order left: a run of the harness and the leaf in the combined
domain. -/
theorem legacy_leaf_output_closed {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {leaf : Lean.Expr} {returned : String}
    {st : CircuitState} {m : Sparkle.IR.AST.Module}
    (run : HarnessRun logProf declName bs ids cache leaf returned st)
    (hm : m = (addClockResetIfSequential st.module).finalize)
    (legal : Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true)
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) (mems : MEnv)
    (values : Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
      (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName)))
    (v : Value) (pos : 0 < v.kind.width)
    (dom : LegacyDom (setupOf declName bs ids cache bools bits).context
      (Tools.ShippingUnifiedMeaning.inputValues (setupOf declName bs ids cache bools bits).bools
        (setupOf declName bs ids cache bools bits).bits) leaf v) :
    Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width bs m initial mems v.toNat :=
  legacy_leaf_output harnessSound run hm legal bools bits initial mems values v pos dom
    (legacy_translate_order dom "out" true)

/-- **The output of a legacy-route declaration.** A successful run of the
shipping entry on a definition that the three certified gates decline is a
memo hit, or it emitted a module whose `out` carries the leaf's value — for
every admissible input valuation at which the leaf is in the combined
domain. -/
theorem legacy_entry_output_walked {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design}
    {cfe : Bool}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeSpec (stripMemoizeWrappers body0) (EntryFacts bs leafOf))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false cfe (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.Nodup ∧ ids.length = bs.length ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName)) →
      ∀ v : Value, 0 < v.kind.width →
      LegacyDom (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits) (leafOf ids) v →
      Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width bs m initial mems v.toNat := by
  rcases legacy_entry_walk old mixed hmach htele hr with hit |
    ⟨body0, xs, inner, leaves, cache, returned, st, hopen, ⟨ids, nd, len, bw, hl⟩, hsplit,
      run, hm, legal⟩
  · exact Or.inl hit
  · refine Or.inr ⟨ids, cache, nd, len, ?_⟩
    intro bools bits initial mems values v pos dom
    rw [hl leaves hsplit] at run
    have run' : HarnessRun logProf declName bs ids cache (leafOf ids) returned st :=
      bw _ _ _ _ _ run
    exact legacy_leaf_output_closed run' hm legal bools bits initial mems values v pos dom

end Tools.ShippingLegacySem
