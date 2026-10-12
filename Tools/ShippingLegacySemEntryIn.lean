import Tools.ShippingLegacySemEntryWalk
import Tools.ShippingLegacySemRunInCalc

/-! # The legacy arm of the entry, walked IN the telescope's context

`legacy_entry_walk` (`Tools/ShippingLegacySemEntryWalk.lean`) takes the
telescope as `TelescopeSpec`: a run of `lambdaTelescope body k` is a run of
`k xs inner` — a run in SOME `Meta` context (`MReturns`). The binder walk
reads the local context (`fvarId.getDecl`), so the facts about the variables
have to be about the context the continuation RUNS in.

**Defined here**: `TelescopeIn body P` — a successful run of
`lambdaTelescope body k` is a successful run of `k xs inner` IN a context
`mctx` with `P mctx xs inner`. (`P` may now say what `mctx.lctx` holds.)

**Proved here**: `legacy_entry_walk_in` — `legacy_entry_walk` with
`TelescopeIn` in place of `TelescopeSpec`, and the binder walk's run handed
over as `RunsIn … mctx …` (same context as `P`). The proof is
`legacy_entry_walk`'s, unchanged up to the telescope; after it the same
steps with `MRunsIn.bind` / `MRunsIn.ite_*` / `MRunsIn.run` (the context is
passed on by every bind). `legacy_entry_walk` itself is untouched.

**Program shape EXPECTED after the telescope** (as in `legacy_entry_walk`,
whose tail was built in this form): `log >>= (symbolic check: join point /
reduced / plain bind) >>= splitReturnLeaves inner >>= clock >>= log >>=
IO.mkRef >>= (compiler.run ctx).run s >>= finishSynth >>= (memo write under
`if !false`) >>= pure`. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-- A successful run of the telescope is a successful run of its continuation
on some variables and body, IN a context `mctx`, with property `P` of the
three (a fact about `Lean.Meta`; for every continuation, so it does not
mention the compiler). -/
def TelescopeIn (body : Lean.Expr) (P : Meta.Context → Array Lean.Expr → Lean.Expr → Prop) :
    Prop :=
  ∀ (α : Type) (k : Array Lean.Expr → Lean.Expr → MetaM α) (r : α),
    MReturns (Lean.Meta.lambdaTelescope body k) r →
    ∃ (mctx : Meta.Context) (xs : Array Lean.Expr) (inner : Lean.Expr),
      P mctx xs inner ∧ MRunsIn (k xs inner) mctx r

/-- **The legacy arm of the entry, walked, with the `Meta` context of the
telescope's continuation exposed.** -/
theorem legacy_entry_walk_in {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {P : Meta.Context → Array Lean.Expr → Lean.Expr → Prop}
    {m : Sparkle.IR.AST.Module} {d : Design}
    {cfe : Bool}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) P)
    (hr : MReturns (synthesizeFromConst translate logProf declName [] false cfe
      (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    ∃ (body0 : Lean.Expr) (mctx : Meta.Context) (xs : Array Lean.Expr) (inner : Lean.Expr)
      (leaves : Array (String × Lean.Expr)) (cache : IO.Ref (ExprStructMap String))
      (returned : String) (st : CircuitState),
      MReturns (openRecordInputs dv.value) body0 ∧ P mctx xs inner ∧
      MReturns (splitReturnLeaves inner) leaves ∧
      RunsIn (bindInputsLegacy [] false xs 0
          (emitLeaves translate cache logProf leaves.toList none 0))
        mctx (entryCompilerState false cache) (CircuitM.init declName.toString) returned st ∧
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
      -- the telescope: from here on the run is in the context `mctx`
      obtain ⟨mctx, xs, inner, hP, h12⟩ := htele body0 hopen _ _ _ h11
      obtain ⟨_, _, h13⟩ := MRunsIn.bind h12    -- log
      -- the retained-parameter check is under `if symbolicMode`: a join
      -- point, already reduced by `simp`, or a plain bind
      first
        | (have h14 := MRunsIn.ite_neg h13 Bool.false_ne_true
           obtain ⟨leaves, hsplit, h15⟩ := MRunsIn.bind h14)
        | (obtain ⟨leaves, hsplit, h15⟩ := MRunsIn.bind h13
           have hsplit : MRunsIn (splitReturnLeaves inner) mctx leaves := hsplit)
        | (obtain ⟨_, _, h14⟩ := MRunsIn.bind h13
           obtain ⟨leaves, hsplit, h15⟩ := MRunsIn.bind h14)
      obtain ⟨t2, _, h16⟩ := MRunsIn.bind h15   -- clock
      obtain ⟨_, _, h17⟩ := MRunsIn.bind h16    -- log
      obtain ⟨cache, _, h18⟩ := MRunsIn.bind h17
      obtain ⟨⟨returned, st⟩, run, h19⟩ := MRunsIn.bind h18
      obtain ⟨res, hfin, h20⟩ := MRunsIn.bind h19
      have hres : (m, d) = res := by
        first
          | (have c1 := MRunsIn.ite_pos h20 rfl
             obtain ⟨_, _, c2⟩ := MRunsIn.bind c1
             exact MRunsIn.pure c2)
          | (obtain ⟨_, _, c2⟩ := MRunsIn.bind h20
             exact MRunsIn.pure c2)
      subst hres
      obtain ⟨hm, _, legal⟩ := finishSynth_returns (MRunsIn.returns hfin)
      exact ⟨body0, mctx, xs, inner, leaves, cache, returned, st, hopen, hP,
        MRunsIn.returns hsplit, MRunsIn.run run, hm, legal⟩

end Tools.ShippingLegacySem
