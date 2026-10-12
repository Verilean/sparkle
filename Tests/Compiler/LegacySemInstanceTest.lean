import Tools.ShippingLegacySemInstance
import Tools.ShippingLegacySemSuffix
import Tools.ShippingLegacySemEntryWalk
import Sparkle

/-! # The legacy inline arm on a real call: which premises can be discharged

`Tools/ShippingLegacySemInstance.lean` (`plain_call_step`) gives the
certified `ActionSpec` for the shipping step on a plain, non-cacheable call,
under a list of premises. Here the list is instantiated at a REAL call — the
leaf `dbl x` of a declaration `fun x => dbl x`, translated with the name flag
set (`emitLeaves` translates a leaf with `isNamed := true`), `x` a bound input
— and each premise is either PROVED for it, or left as a hypothesis of the
final theorem `dbl_call_step`, with the reason.

**Discharged here** (kernel-checked, no hypothesis): the head
(`dbl_head`), `fallbackKind = .other` (`dbl_kind`), `NotCore` (`dbl_notCore`),
the 60-odd tests `name == c` on the head's name (`decide` on `Name`
equality), `isPrimitive`, `signalBinOpOf`, and the call's flags
(`dbl_flags`).

**NOT dischargeable for any real expression — the findings:**

1. `HasMappedFVar ctx e`. The body computes it with `Expr.find?`. Checked in
   the toolchain (`src/lean/Lean/Util/FindExpr.lean`, v4.32.1): line 16–17
   `@[extern "lean_find_expr"] opaque findImpl? (p : @& (Expr → Bool))
   (e : @& Expr) : Option Expr` — declared with the keyword `opaque`, i.e. a
   constant WITHOUT a logical body (not a `def` with an `extern` /
   `implemented_by` attribute, which would be transparent); line 19
   `@[inline] def find? (p : Expr → Bool) (e : Expr) : Option Expr :=
   findImpl? p e` — a real definition, but of the opaque constant. Neither is
   `partial`. The toolchain has no lemma about either (the only occurrences
   of `findImpl?` are those two lines). So the kernel can unfold `find?` to
   `findImpl? p e` and no further: the premise is true at run time and not
   provable, for this expression or any other.
2. (Round 8: no longer a finding.) The eleven suffix tests
   `name.toString.endsWith ".register" = false`, …: `Name.toString` does not
   reduce in the kernel, but the printed name is one of finitely many
   candidate renderings (`Tools.ShippingNameSep.toString_mem`), so each test
   reduces to a closed Boolean over the candidates
   (`Tools.ShippingLegacySem.endsWith_false_of`). `dbl_suffixes` discharges
   them that way IF `String.endsWith` evaluates on literals; `dbl_call_step`
   keeps them as a hypothesis so that it does not depend on that, and
   `dbl_call_step_closed` is the version without it.

**Hypotheses by design or by nature:**

3. `PlainHead ``dbl` — the environment the run reads (reflection).
4. `NoSubModule rec ctx e` — the inline attempt never returns without a
   wire. About the run: the unfolding oracle did return an unfolding, and its
   translation did not throw. Not reflection, not decidable; without it the
   call may have been lowered as a sub-module instance, for which no contract
   is proved.
5. The unfoldings' contracts at the same value (`sub`): reflection of
   unfolding and the recursion hypothesis.
6. `Inv` and `ScalarWidthsAgree`, inside `ActionSpec`.

So the conditional layer has ONE real instance whose remaining premises are
3–6 and the two findings 1–2.

## Round 11: the declaration, end to end (`useDbl_output`)

`useDbl_output` instantiates `legacy_entry_output_walked`
(`Tools/ShippingLegacySemEntryWalk.lean`) at the declaration `useDbl`
compiled with the legacy front end (with the certified front end ON,
`entryConst` unfolds `dbl` and a certified gate takes the declaration: it is
then not a fallback input at all). Conclusion: a successful run of
`synthesizeFromConst` on it is a memo hit, or the emitted module's `out`
carries `x + x` (`RawValueAt 8 … (x + x).toNat`) for every admissible input.

**Hypotheses left — the distance to the acceptance unit:**

* H1 `htele` — the telescope (`TelescopeSpec`: a fact about `Lean.Meta`'s
  `lambdaTelescope`, for every continuation) with the run facts it must hand
  over (`EntryFacts`): the variables are distinct, one per binder; the legacy
  binder walk over them is the certified one over `[(x, bits 8)]`
  (`BinderWalk` — not walked, and not statable through `Returns`: `getDecl`
  reads the local context the telescope installed); `splitReturnLeaves`
  returns the single leaf `("out", dbl x)`.
* H2 `hreach` — `ReachesInline` at the prepared context, for EVERY hint and
  flag. `plain_call_reaches` (walked, round 9) gives the run of the
  translator on an unfolding for the non-cacheable flags (`named ∨ top`)
  from `HasMappedFVar` (kernel-opaque), `PlainHead` (environment) and
  `NoSubModule` (the run). The entry translates the leaf with `named =
  true`, but `Contract` — and so `LegacyDom.inline` — quantifies all flags;
  at the cacheable ones today's shim may return an unvalidated hit. Closing
  this needs the harness lemmas at the flags the entry uses (a
  flag-restricted contract), or the validated hit.
* H3 `hunf` — every unfolding the oracle returns for `dbl x` is in the
  domain at `x + x`, at the prepared inputs (reflection of
  `unfoldDefinition?`, then `LegacyDom.cert` over the input `x`).

NOT hypotheses any more: harness soundness (`harnessSound`), the contract and
the order on the domain (`legacy_translate_contract`,
`legacy_translate_order`), `NotCore` (`dbl_notCore`), the entry arm's own
walk (`legacy_entry_walk`), the legal-name fact (`finishSynth_returns`).

The second outcome, `MemoHit`, is in the conclusion, not excluded. -/

open Lean Meta Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingLegacySem

namespace Sparkle.Tests.Compiler.LegacySemInstanceTest

/-- An untagged helper. -/
def dbl (y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := y + y

/-- A real declaration whose only leaf is the call. -/
def useDbl (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := dbl x

/-- The leaf `dbl x`, `x` the free variable `xid`. -/
abbrev callE (xid : FVarId) : Lean.Expr := .app (.const ``dbl []) (.fvar xid)

/-! ## Discharged -/

/-- A test on a name literal, by evaluation (kernel evaluation if the
elaborator's does not get through; no compiled code). -/
macro "name_ne" : tactic => `(tactic| first | decide | decide +kernel | rfl)

theorem dbl_head (xid : FVarId) : (callE xid).getAppFn = .const ``dbl [] := rfl

set_option maxRecDepth 4096 in
theorem dbl_kind (xid : FVarId) : fallbackKind (callE xid) = .other := by
  first | rfl | decide | decide +kernel

set_option maxRecDepth 4096 in
theorem dbl_binOp : signalBinOpOf ``dbl = none := by
  first
    | rfl
    | decide
    | decide +kernel
    | exact Option.isNone_iff_eq_none.mp (by first | decide | decide +kernel)

set_option maxRecDepth 4096 in
theorem dbl_notPrimitive : isPrimitive ``dbl = false := by
  first | rfl | decide | decide +kernel

set_option maxRecDepth 4096 in
theorem dbl_notCore (xid : FVarId) : NotCore (callE xid) where
  shape := by
    first
      | rfl
      | decide
      | decide +kernel
      | (show ((``dbl == ``Sparkle.Core.Signal.Signal.pure) ||
            (match signalBinOpOf ``dbl,
                canonicalSignalBinKinds ``dbl (callE xid).getAppArgs,
                canonicalSignalBitVecWidth (callE xid).getAppArgs with
             | some _, some (true, true), some _ => true
             | _, _, _ => false)) = false
         rw [show (``dbl == ``Sparkle.Core.Signal.Signal.pure) = false from by name_ne,
           dbl_binOp]
         rfl)
  core := fun rec hint top named => by
    first
      | rfl
      | (show (if (``dbl == ``Sparkle.Core.Signal.Signal.pure) = true then
              translateSignalPureLiteral? (callE xid).getAppArgs hint named
            else
              match signalBinOpOf ``dbl,
                  canonicalSignalBinKinds ``dbl (callE xid).getAppArgs,
                  canonicalSignalBitVecWidth (callE xid).getAppArgs with
              | some op, some (true, true), some _ => do
                let w ← translateCanonicalSignalBinary rec (callE xid) op
                  (callE xid).getAppArgs true true hint named
                pure (some w)
              | _, _, _ => pure none) = pure none
         rw [show (``dbl == ``Sparkle.Core.Signal.Signal.pure) = false from by name_ne,
           dbl_binOp]
         rfl)

theorem dbl_flags (xid : FVarId) (top : Bool) :
    (!true && !(callE xid).isFVar && !top) = false := rfl

theorem dbl_glue : GlueName ``dbl :=
  ⟨by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne⟩

theorem dbl_notBitVecOp : NotBitVecOp ``dbl :=
  ⟨by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne,
    by name_ne, dbl_notPrimitive⟩

/-! ## The suffix tests: hypotheses, with compiled evidence -/

/-- The eleven `Name.toString` suffix tests the handlers and the body run on
the head's name. -/
structure DblSuffixes : Prop where
  register : (``dbl : Name).toString.endsWith ".register" = false
  registerE : (``dbl : Name).toString.endsWith ".registerWithEnable" = false
  lut : (``dbl : Name).toString.endsWith ".lutMuxTree" = false
  mux : (``dbl : Name).toString.endsWith ".mux" = false
  memory : (``dbl : Name).toString.endsWith ".memory" = false
  combo : (``dbl : Name).toString.endsWith ".memoryComboRead" = false
  memoize : (``dbl : Name).toString.endsWith ".memoize" = false
  loop : (``dbl : Name).toString.endsWith ".loop" = false
  ofFin : (``dbl : Name).toString.endsWith ".ofFin" = false
  ofNat : (``dbl : Name).toString.endsWith ".ofNat" = false
  toNat : (``dbl : Name).toString.endsWith ".toNat" = false

/-- A closed Boolean over the candidate renderings, by evaluation. -/
macro "cand_dec" : tactic => `(tactic| first | decide | decide +kernel | rfl)

set_option maxRecDepth 8192 in
/-- **The suffix tests, proved** through the candidate renderings of the
name: no evaluation of `Name.toString`. -/
theorem dbl_suffixes : DblSuffixes :=
  ⟨endsWith_false_of _ _ (by cand_dec), endsWith_false_of _ _ (by cand_dec),
    endsWith_false_of _ _ (by cand_dec), endsWith_false_of _ _ (by cand_dec),
    endsWith_false_of _ _ (by cand_dec), endsWith_false_of _ _ (by cand_dec),
    endsWith_false_of _ _ (by cand_dec), endsWith_false_of _ _ (by cand_dec),
    endsWith_false_of _ _ (by cand_dec), endsWith_false_of _ _ (by cand_dec),
    endsWith_false_of _ _ (by cand_dec)⟩

theorem dbl_plainName (suf : DblSuffixes) : PlainName ``dbl :=
  ⟨by name_ne, by name_ne, by name_ne, by name_ne, by name_ne,
    suf.register, suf.registerE, suf.lut, suf.mux, suf.memory, suf.combo⟩

theorem dbl_plainName2 (suf : DblSuffixes) : PlainName2 ``dbl :=
  ⟨by name_ne, suf.memoize, suf.loop, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne,
    by name_ne, by name_ne, by name_ne, by name_ne⟩

theorem dbl_implName (suf : DblSuffixes) : ImplName ``dbl :=
  ⟨dbl_binOp, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne,
    by name_ne, by name_ne, by name_ne, by name_ne, suf.ofFin, suf.ofNat, suf.toNat,
    by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne,
    by name_ne, by name_ne, by name_ne, by name_ne⟩

/-! ## The instance -/

/-- **The shipping step on the real leaf `dbl x`** (name flag set, any hint
and top flag, any recursive translator): frame and semantic outcome at `v`.
Hypotheses: the two findings (`suf`, `hmap`), the environment (`hplain`), the
run (`hnosub`), and the unfoldings' contracts (`sub`). -/
theorem dbl_call_step [Tools.ShippingLinkCtx.LinkCtx] [Tools.ShippingUnifiedMeaning.ChildSem]
    {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Tools.ShippingUnifiedMeaning.Value}
    {we : Sparkle.IR.Semantics.WEnv} {mems : Sparkle.IR.Semantics.MEnv}
    {initial : Sparkle.IR.Semantics.Env} {xid : FVarId}
    {v : Tools.ShippingUnifiedMeaning.Value} {hint : String} {top : Bool}
    (suf : DblSuffixes) (hmap : HasMappedFVar ctx (callE xid))
    (hplain : PlainHead ``dbl) (hnosub : NoSubModule rec ctx (callE xid))
    (sub : ∀ e' : Lean.Expr, InlineUnfolds (callE xid) e' →
      Tools.ShippingUnifiedRecursion.Contract rec ctx inputs we mems initial e' v) :
    Tools.ShippingUnifiedRecursion.ActionSpec
      (translateStepWith translateFallback rec (callE xid) hint top true)
      ctx inputs we mems initial v :=
  plain_call_step (dbl_head xid) (dbl_notCore xid) (dbl_kind xid) hplain dbl_glue
    (dbl_plainName suf) dbl_notBitVecOp (dbl_plainName2 suf) (dbl_implName suf) hmap
    (dbl_flags xid top) hnosub sub

/-- **The same with the suffix tests discharged**: the ONE kernel-opaque
premise left is `HasMappedFVar` (`Expr.find?` is an opaque constant); the
others are the environment (`PlainHead`), the run (`NoSubModule`) and the
unfoldings' contracts. -/
theorem dbl_call_step_closed [Tools.ShippingLinkCtx.LinkCtx]
    [Tools.ShippingUnifiedMeaning.ChildSem]
    {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Tools.ShippingUnifiedMeaning.Value}
    {we : Sparkle.IR.Semantics.WEnv} {mems : Sparkle.IR.Semantics.MEnv}
    {initial : Sparkle.IR.Semantics.Env} {xid : FVarId}
    {v : Tools.ShippingUnifiedMeaning.Value} {hint : String} {top : Bool}
    (hmap : HasMappedFVar ctx (callE xid))
    (hplain : PlainHead ``dbl) (hnosub : NoSubModule rec ctx (callE xid))
    (sub : ∀ e' : Lean.Expr, InlineUnfolds (callE xid) e' →
      Tools.ShippingUnifiedRecursion.Contract rec ctx inputs we mems initial e' v) :
    Tools.ShippingUnifiedRecursion.ActionSpec
      (translateStepWith translateFallback rec (callE xid) hint top true)
      ctx inputs we mems initial v :=
  dbl_call_step dbl_suffixes hmap hplain hnosub sub

/-! ## The declaration, end to end -/

/-- The binders of `useDbl`. -/
abbrev useDblBinders : List (Name × MixedGateBinder) := [(`x, .bits 8)]

/-- The variable of the one binder. -/
abbrev xOf (ids : List FVarId) : FVarId := ids.headD ⟨.anonymous⟩

/-- **`useDbl`, from the entry to the output wire.** Hypotheses: H1–H3 of the
header. -/
theorem useDbl_output {logProf : String → IO Unit} {dv : DefinitionVal}
    {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (htele : ∀ body0, Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      TelescopeSpec (stripMemoizeWrappers body0)
        (EntryFacts useDblBinders (fun ids => callE (xOf ids))))
    (hreach : ∀ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (rec : TranslateFn),
      ReachesInline rec (setupOf ``useDbl useDblBinders ids cache bools bits).context
        (callE (xOf ids)))
    (hunf : ∀ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (e' : Lean.Expr),
      InlineUnfolds (callE (xOf ids)) e' →
      LegacyDom (setupOf ``useDbl useDblBinders ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf ``useDbl useDblBinders ids cache bools bits).bools
          (setupOf ``useDbl useDblBinders ids cache bools bits).bits)
        e' (.bits 8 (bits (xOf ids) 8 + bits (xOf ids) 8)))
    (hr : Tools.ShippingEntrySoundness.MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf ``useDbl [] false false (.defnInfo dv) isInst) (m, d)) :
    MemoHit ``useDbl m d ∨
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.Nodup ∧ ids.length = 1 ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Sparkle.IR.Semantics.Env) (mems : Sparkle.IR.Semantics.MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (useDblBinders.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (``useDbl : Name).toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt 8 useDblBinders m initial mems
        (bits (xOf ids) 8 + bits (xOf ids) 8).toNat := by
  rcases legacy_entry_output_walked (cfe := false) (bs := useDblBinders)
      (leafOf := fun ids => callE (xOf ids))
      (fun h => absurd h Bool.false_ne_true) (fun h => absurd h Bool.false_ne_true)
      (fun h => absurd h Bool.false_ne_true) htele hr with hit | ⟨ids, cache, nd, len, H⟩
  · exact Or.inl hit
  · refine Or.inr ⟨ids, cache, nd, len, ?_⟩
    intro bools bits initial mems values
    exact H bools bits initial mems values
      (.bits 8 (bits (xOf ids) 8 + bits (xOf ids) 8)) (Nat.succ_pos 7)
      (LegacyDom.inline (dbl_notCore (xOf ids)) (hreach ids cache bools bits)
        (hunf ids cache bools bits))

/-! ## Evidence for the undischarged facts, by compiled code -/

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let n : Name := ``dbl
    let sufs : List String := [".register", ".registerWithEnable", ".lutMuxTree", ".mux",
      ".memory", ".memoryComboRead", ".memoize", ".loop", ".ofFin", ".ofNat", ".toNat"]
    let bad := sufs.filter (fun suffix => n.toString.endsWith suffix)
    -- the body's own test on the leaf, with `x` bound: the same `find?`
    let xid : FVarId := ⟨`x⟩
    let mapped := ((callE xid).find? (fun sub =>
      match sub with
      | .fvar fid => [(xid, "w")].any (fun (vid, _) => vid == fid)
      | _ => false)).isSome
    -- the declaration compiles on the legacy route (legacy front end)
    let compiled ← try
        let _ ← synthesizeCombinationalCoreWith
          (fun e h t n => translateExprToWire e h t n) ``useDbl [] false
          (certifiedFrontEnd := false)
        pure true
      catch _ => pure false
    logInfo m!"LEGACY INLINE ARM, REAL INSTANCE (dbl x): suffix tests true (expected none): {bad}; the mapped-variable test evaluates to {mapped} (expected true; it is `Expr.find?`, opaque in the kernel); useDbl compiles with the legacy front end: {compiled}. dbl_call_step_closed has ONE kernel-opaque premise, HasMappedFVar (Expr.find? = Expr.findImpl?, opaque), beside the environment (PlainHead), the run (NoSubModule) and the unfoldings' contracts; the suffix tests are proved through the candidate renderings of the name."
  catch ex =>
    logInfo m!"LEGACY INLINE ARM, REAL INSTANCE: harness error: {ex.toMessageData}"

end Sparkle.Tests.Compiler.LegacySemInstanceTest
