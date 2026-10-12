import Tools.ShippingLegacySemInstance
import Tools.ShippingLegacySemSuffix
import Tools.ShippingLegacySemLeaf
import Tools.ShippingLegacySemEntryOne
import Tools.ShippingLegacySemSignalFrame
import Tools.ShippingLegacySemEntryBound
import Tools.ShippingLegacySemTelescopeN
import Tools.ShippingLegacySemLeafHandled
import Tools.ShippingLegacySemEntryListD
import Tools.ShippingLegacySemBeta
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

The second outcome, `MemoHit`, is in the conclusion, not excluded.

## Round 12: H2 and H3 reduced (`useDbl_output`)

The round-11 theorem is kept as `useDbl_output_r11` (its `hreach` is now
`ReachesUnfold`, the restated premise of `LegacyDom.inline`). The new
`useDbl_output` asks the leaf in the ENTRY-FLAG domain (`LeafDom … "out"
true`, `Tools/ShippingLegacySemLeaf.lean`), so:

* H2 is replaced by the walked premises of `plain_call_reaches`, at the one
  flag setting the entry uses (`named = true`: the shim's cache is not
  consulted): `hmap` (`HasMappedFVar` at the prepared context —
  kernel-opaque `Expr.find?`), `hplain` (`PlainHead ``dbl`, the environment),
  `hnosub` (`NoSubModule` at the prepared context, the run).
  `dbl_reachesAt` is the reduction.
* H3 is replaced by `hunfE`: every unfolding the oracle returns for `dbl x`
  IS the quoted term `x + x` (`dblTerm`, for some domain expression) — pure
  reflection of `unfoldDefinition?`. Proved from it: the term is in the
  domain at `x + x` (`dbl_unfold_dom`: `LegacyDom.cert` over the input), and
  the prepared setup maps `x` to its value (`useDbl_input`).
  The compiled check below logs whether the oracle's result on `dbl x`
  equals that quoted term in this environment.
* H1 is unchanged.

## Round 13: `hnosub` narrowed

`hnosub` was asked of EVERY recursive translator; it is now asked of the
translators the fuel recursion passes down (`translateFuelFix translateStep
fuel`). The run itself uses one of them (`fuel = translateFuelLimit - 1`).
`hmap` stays quantified over the variable and the cache: they are outputs of
the run (existential in the conclusion), the premise is a closed property of
the leaf and the prepared variable map, and it does not depend on the
valuation in substance (`prepare`'s context ignores `bools` / `bits`; the
quantifier over them is there only because `setupOf` takes them). 
## Round 14: `htele` removed (`useDbl_output`)

The round-13 theorem is kept as `useDbl_output_r13`. The new `useDbl_output`
has no `TelescopeSpec` / `EntryFacts` / `BinderWalk` hypothesis: the entry is
walked in the telescope's own `Meta` context (`legacy_entry_walk_in`), the
binder walk and the leaves are proved (`bindInputsLegacy_one`,
`splitReturnLeaves_scalar`), composed in `one_binder_entry_output`
(`Tools/ShippingLegacySemEntryOne.lean`). In place of `htele`:

* `htel : LamTelescopeOne` — the Meta-library fact about `lambdaTelescope`
  on a one-binder lambda (no compiler definition in it);
* `hbody` — the SHAPE of the body the telescope is run on: for every result
  `body0` of `openRecordInputs dv.value`, `stripMemoizeWrappers body0` is
  `fun (x : T) => b`, `b` not a lambda, `T.instantiateRevRange 0 0 #[] = xTy`
  and `b.instantiateRevRange 0 1 #[.fvar id] = dbl (fvar id)`. Reflection of
  the environment (the constant's value), through one oracle
  (`openRecordInputs`) and two functions without a logical body
  (`stripMemoizeWrappers` is `partial`; `Expr.instantiateRevRange` is an
  `opaque` extern). This part of `htele` was implicit before; it is now a
  stated premise. `xTy` (the binder's type as the walk sees it) is a
  parameter of the theorem;
* (round 15: `hsig : SignalTestFrame xTy` is no longer a premise — it is
  `isSignalBinderType_frame`, `Tools/ShippingLegacySemSignalFrame.lean`);
* `hinf : InfersBits xTy 8` — the binder-type oracle;
* `hres : ∀ id, SignalTyped (dbl (fvar id))` — the result-type oracle.

and a THIRD outcome in the conclusion, `InputSkipped`: the walk's `try`
around the type oracle caught a failure, the binder got no port, the leaf
was emitted alone. Not excluded: a successful run does not show that the
oracle did not throw inside the `try`.

## Round 15

* `hsig` dropped (proved).
* `InputSkipped` is KEPT, and the reason is recorded in
  `Tools/ShippingLegacySemFVarArm.lean` (`impl_fvar`): the body's variable
  arm does not simply throw on an unmapped variable (it consults the
  builder's `sourceBindings`, zeta-reduces through a local-context value,
  and re-translates a changed result of `Lean.Meta.reduce`), and the leaf
  `dbl x` with no mapped variable is first replaced by `whnf` of itself.
* Compiled evidence (logs only) for the reflection premises `hbody`, `hinf`,
  `hres` on the real `useDbl`, and a run of the skipped scenario itself (the
  leaf translated with no port bound): the second `run_cmd` at the end.
  These logs are observations of ONE run in the test's environment; they
  are not proofs of the premises (which speak of every successful run).

## Round 16: `InputSkipped` excluded at its source

The round-15 theorem is kept as `useDbl_output_r15`. The new `useDbl_output`
has one more premise, `hinfT : InfersNoCatch xTy` — the hardware-type oracle
has no CATCHABLE failure on the one declared binder type (every failing run
of `inferHWTypeFromSignal xTy` ends in an interrupt or a runtime exception,
which `try … catch` rethrows) — and its conclusion is `MemoHit ∨ (out
carries x + x)`. The skip is created only by the handler of the walk's
`try` around that oracle (`returns_tryCatch_throws`,
`bindInputsLegacy_one_bound`). Same class as `hinf` (the oracle on one
type): `hinf` speaks of its returning runs, `hinfT` of its failing ones. The
`hinf EVIDENCE` log observes one run that returned.

## Round 17: a second declaration (two inputs) and the axiom audit

* `useDbl2 x y := dbl x` — two `BitVec 8` inputs (the second unused by the
  result), compiled with the legacy front end. `useDbl2_output`: the list
  form of the entry theorem (`list_entry_output`: the binder walk over a LIST
  of scalar binders, `Tools/ShippingLegacySemBinderList.lean`) with the
  n-binder Meta-library fact `LamTelescopeN`
  (`Tools/ShippingLegacySemTelescopeN.lean`); premises of the same classes as
  `useDbl_output`, the binder-type oracle premises once per binder. The leaf
  is the same call `dbl x`, so the leaf lemmas are reused; a leaf that uses
  BOTH inputs through an inline call (`add2 x y`) needs the two-input
  analogue of `dbl_unfold_dom` and of the `dbl_*` name lemmas — not written.
* The last `run_cmd` is the ACCEPTANCE CHECK: it throws unless
  `useDbl_output`, `useDbl2_output`, `one_binder_entry_output_bound`,
  `list_entry_output` and `returns_tryCatch_throws` depend on no axiom
  beyond `propext`, `Classical.choice`, `Quot.sound`.

## Round 18: a leaf that uses both inputs; evidence for the two-binder premises

* `useAdd2 x y := add2 x y`, `add2 a b := a + b` (untagged helper):
  `useAdd2_output` concludes `MemoHit ∨ out carries x + y`. The name facts of
  the callee are one bundle (`PlainCallee ``add2`, `add2_callee`) consumed by
  the generic `plainCallee_leaf` (`Tools/ShippingLegacySemLeafHandled.lean`);
  the unfolding is `LegacyDom.cert` at two vector inputs (`add2_unfold_dom`).
  The per-name tests themselves are closed computations on the name (not
  provable for a variable name): their proofs are `dbl`'s, same text.
* Evidence (logs only): the two-binder `hbody` shape, the binder and result
  oracles for `useDbl2` and `useAdd2`, the unfolding of `add2 x y` against
  the quoted term, and that `useAdd2` compiles with the legacy front end.
* The axiom audit also covers `useAdd2_output`, `plainCallee_leaf`,
  `handlerCase_inline`.

## Round 21: a declaration of the largest RETURNED class (a structure field projection)

The census (`Tests/Compiler/LegacyArmCensusTest.lean`): the shipping entry
returns through the legacy arm for 90 Signal-valued definitions of the
examined IP modules; 45 of them are structure field projection functions,
and every one of the 90 has a domain binder. `SHA256Out_done_output` is the
entry statement for one of them, `Sparkle.IP.Crypto.SHA256.SHA256Out.done`
(named here by a name literal: the module is not imported; the evidence line
for the real constant is in the census test), in the SHIPPING configuration
(certified front end on, the three gates declining):

* binders `dom` (skipped: `InfersNothing`), `hash : bits 256`, `done : bool`
  (`list_entry_outputD`, `telescopeIn_of_lam3`);
* the leaf is a beta-redex whose reducible `whnf` is the variable of the
  field `done` (`WhnfIsVar`, an oracle premise observed by the evidence
  line): a wire-through (`leafDom_betaWire`,
  `Tools/ShippingLegacySemBeta.lean`);
* conclusion: memo hit, or `out` carries the value of the input bound for
  `done`.
-/

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

/-- **`useDbl`, from the entry to the output wire** (round 11 form).
Hypotheses: H1–H3 of the header; `hreach` in the restated form
(`ReachesUnfold`). -/
theorem useDbl_output_r11 {logProf : String → IO Unit} {dv : DefinitionVal}
    {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (htele : ∀ body0, Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      TelescopeSpec (stripMemoizeWrappers body0)
        (EntryFacts useDblBinders (fun ids => callE (xOf ids))))
    (hreach : ∀ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (rec : TranslateFn),
      ReachesUnfold rec (setupOf ``useDbl useDblBinders ids cache bools bits).context
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

/-! ## Round 12: the leaf at the entry flags -/

/-- The dispatch premise at the entry's flags (`named = true`), from the
walked premises. -/
theorem dbl_reachesAt {ctx : CompilerState} {xid : FVarId}
    (hmap : HasMappedFVar ctx (callE xid)) (hplain : PlainHead ``dbl)
    (rec : TranslateFn) (hnosub : NoSubModule rec ctx (callE xid)) (hint : String) :
    ReachesUnfoldAt rec ctx (callE xid) hint false true :=
  fun s t w hr =>
    plain_call_reaches (dbl_head xid) (dbl_kind xid) hplain dbl_glue
      (dbl_plainName dbl_suffixes) dbl_notBitVecOp (dbl_plainName2 dbl_suffixes)
      (dbl_implName dbl_suffixes) hmap (dbl_flags xid false) hnosub s t w hr

/-- The body of `dbl` on one 8-bit input, as a term of the quoted fragment. -/
abbrev dblTerm : Tools.ShippingUnifiedSource.Term (.bits 8) :=
  .binary .add (.bitsInput 8 0) (.bitsInput 8 0)

/-- The quoted unfolding of `dbl x`. -/
abbrev dblUnfoldE (dom : Lean.Expr) (xid : FVarId) : Lean.Expr :=
  Tools.ShippingUnifiedSource.quote dom (fun _ => .fvar xid) (fun _ => .fvar xid) dblTerm

/-- **The quoted unfolding is in the domain at `x + x`**, from the input's
value. -/
theorem dbl_unfold_dom {ctx : CompilerState}
    {inputs : FVarId → Option Tools.ShippingUnifiedMeaning.Value} {dom : Lean.Expr}
    {xid : FVarId} {b : BitVec 8} (hi : inputs xid = some (.bits 8 b)) :
    LegacyDom ctx inputs (dblUnfoldE dom xid) (.bits 8 (b + b)) := by
  have hi' : inputs xid = some (.bits 8 (BitVec.setWidth 8 b)) := by
    rw [BitVec.setWidth_eq]; exact hi
  have hval : Tools.ShippingUnifiedMeaning.pack (.bits 8)
      (Tools.ShippingUnifiedSource.eval (fun _ => false)
        (fun _ w => BitVec.setWidth w b) dblTerm) = .bits 8 (b + b) := by
    show Tools.ShippingUnifiedMeaning.Value.bits 8
      (Tools.ShippingScalarSoundness.Binary.apply .add (BitVec.setWidth 8 b)
        (BitVec.setWidth 8 b)) = _
    rw [BitVec.setWidth_eq] <;> rfl
  have h := LegacyDom.cert (ctx := ctx) (inputs := inputs) (dom := dom) (kb := 0) (kv := 1)
    (vw := fun _ => 8) (bE := fun _ => .fvar xid) (vE := fun _ => .fvar xid)
    (bools := fun _ => false) (bits := fun _ w => BitVec.setWidth w b) dblTerm
    ⟨⟨Nat.zero_lt_one, rfl, Nat.succ_pos 7⟩, ⟨Nat.zero_lt_one, rfl, Nat.succ_pos 7⟩⟩
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun _ _ => Tools.ShippingUnifiedMeaning.Meaning.input rfl hi')
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun _ _ => LegacyDom.input hi')
  first
    | (rw [hval] at h; exact h)
    | exact hval ▸ h

/-- **The prepared setup maps the binder to its value.** -/
theorem useDbl_input (id : FVarId) (cache : IO.Ref (ExprStructMap String))
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    Tools.ShippingUnifiedMeaning.inputValues
      (setupOf ``useDbl useDblBinders [id] cache bools bits).bools
      (setupOf ``useDbl useDblBinders [id] cache bools bits).bits id =
      some (.bits 8 (bits id 8)) := by
  refine Tools.ShippingUnifiedMeaning.inputValues_bits ?_ ?_
  · intro key b h
    exfalso
    revert h
    show (if key = id then (none : Option Bool) else none) = some b → False
    split <;> intro h <;> cases h
  · exact if_pos rfl

/-- **`useDbl`, from the entry to the output wire** (round 13 form, with the
telescope hypothesis). Hypotheses: `htele`
(H1), the walked dispatch premises `hmap` / `hplain` / `hnosub` at the
prepared context, and the reflection of the unfolding oracle `hunfE`. -/
theorem useDbl_output_r13 {logProf : String → IO Unit} {dv : DefinitionVal}
    {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (htele : ∀ body0, Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      TelescopeSpec (stripMemoizeWrappers body0)
        (EntryFacts useDblBinders (fun ids => callE (xOf ids))))
    (hmap : ∀ (id : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
      HasMappedFVar (setupOf ``useDbl useDblBinders [id] cache bools bits).context (callE id))
    (hplain : PlainHead ``dbl)
    (hnosub : ∀ (id : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (fuel : Nat),
      NoSubModule (translateFuelFix translateStep fuel)
        (setupOf ``useDbl useDblBinders [id] cache bools bits).context (callE id))
    (hunfE : ∀ (xid : FVarId) (e' : Lean.Expr), InlineUnfolds (callE xid) e' →
      ∃ dom : Lean.Expr, e' = dblUnfoldE dom xid)
    (hr : Tools.ShippingEntrySoundness.MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf ``useDbl [] false false (.defnInfo dv) isInst) (m, d)) :
    MemoHit ``useDbl m d ∨
    ∃ (id : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Sparkle.IR.Semantics.Env) (mems : Sparkle.IR.Semantics.MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (useDblBinders.zip [id])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (``useDbl : Name).toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt 8 useDblBinders m initial mems
        (bits id 8 + bits id 8).toNat := by
  rcases leaf_entry_output_walked (cfe := false) (bs := useDblBinders)
      (leafOf := fun ids => callE (xOf ids))
      (fun h => absurd h Bool.false_ne_true) (fun h => absurd h Bool.false_ne_true)
      (fun h => absurd h Bool.false_ne_true) htele hr with hit | ⟨ids, cache, nd, len, H⟩
  · exact Or.inl hit
  · have len' : ids.length = 1 := len
    obtain ⟨id, rfl⟩ : ∃ id, ids = [id] := by
      cases ids with
      | nil => first | simp at len' | (simp only [List.length_nil] at len'; omega)
      | cons a tl =>
        cases tl with
        | nil => exact ⟨a, rfl⟩
        | cons a2 tl2 =>
          first | simp at len' | (simp only [List.length_cons] at len'; omega)
    refine Or.inr ⟨id, cache, ?_⟩
    intro bools bits initial mems values
    exact H bools bits initial mems values
      (.bits 8 (bits id 8 + bits id 8)) (Nat.succ_pos 7)
      (LeafDom.inlineAt (dbl_notCore id)
        (fun fuel => dbl_reachesAt (hmap id cache bools bits) hplain
          (translateFuelFix translateStep fuel) (hnosub id cache bools bits fuel) "out")
        (fun e' hU => by
          obtain ⟨dom, rfl⟩ := hunfE id e' hU
          exact LeafDom.dom (dbl_unfold_dom (useDbl_input id cache bools bits))))

/-! ## Round 14: without the telescope hypothesis -/

/-- **`useDbl`, from the entry to the output wire** (round 15 form, three
outcomes). No `TelescopeSpec` /
`BinderWalk` hypothesis: the Meta-library fact about `lambdaTelescope`
(`htel`), the body's shape (`hbody`), the binder-type oracle (`hinf`), the
result-type oracle (`hres`); then, as before, the
dispatch premises `hmap` / `hplain` / `hnosub` and the unfolding oracle
`hunfE`. Three outcomes: memo hit, the output statement, or the binder
skipped (`InputSkipped`). -/
theorem useDbl_output_r15 {logProf : String → IO Unit} {dv : DefinitionVal}
    {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {xTy : Lean.Expr}
    (htel : LamTelescopeOne)
    (hbody : ∀ body0, Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      ∃ (T b : Lean.Expr) (bi : BinderInfo),
        stripMemoizeWrappers body0 = Lean.Expr.lam `x T b bi ∧ b.isLambda = false ∧
        T.instantiateRevRange 0 0 #[] = xTy ∧
        ∀ id : FVarId, b.instantiateRevRange 0 1 #[Lean.Expr.fvar id] = callE id)
    (hinf : InfersBits xTy 8)
    (hres : ∀ id : FVarId, SignalTyped (callE id))
    (hmap : ∀ (id : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
      HasMappedFVar (setupOf ``useDbl useDblBinders [id] cache bools bits).context (callE id))
    (hplain : PlainHead ``dbl)
    (hnosub : ∀ (id : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (fuel : Nat),
      NoSubModule (translateFuelFix translateStep fuel)
        (setupOf ``useDbl useDblBinders [id] cache bools bits).context (callE id))
    (hunfE : ∀ (xid : FVarId) (e' : Lean.Expr), InlineUnfolds (callE xid) e' →
      ∃ dom : Lean.Expr, e' = dblUnfoldE dom xid)
    (hr : Tools.ShippingEntrySoundness.MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf ``useDbl [] false false (.defnInfo dv) isInst) (m, d)) :
    MemoHit ``useDbl m d ∨
    (∃ (id : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Sparkle.IR.Semantics.Env) (mems : Sparkle.IR.Semantics.MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (useDblBinders.zip [id])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (``useDbl : Name).toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt 8 useDblBinders m initial mems
        (bits id 8 + bits id 8).toNat) ∨
    InputSkipped logProf ``useDbl callE m := by
  have htele : ∀ body0,
      Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (OneBinderScope `x xTy callE) := by
    intro body0 hopen
    obtain ⟨T, b, bi, hb, hl, hT, hi⟩ := hbody body0 hopen
    exact telescopeIn_of_lam htel hb hl hT hi
  rcases one_binder_entry_output (cfe := false) (nm := `x) (n := 8) (T := xTy)
      (leafOf := callE)
      (fun h => absurd h Bool.false_ne_true) (fun h => absurd h Bool.false_ne_true)
      (fun h => absurd h Bool.false_ne_true) htele (isSignalBinderType_frame xTy) hinf
      (fun id => ⟨rfl, hres id⟩) hr with hit | ⟨id, cache, H⟩ | skip
  · exact Or.inl hit
  · refine Or.inr (Or.inl ⟨id, cache, ?_⟩)
    intro bools bits initial mems values
    exact H bools bits initial mems values
      (.bits 8 (bits id 8 + bits id 8)) (Nat.succ_pos 7)
      (LeafDom.inlineAt (dbl_notCore id)
        (fun fuel => dbl_reachesAt (hmap id cache bools bits) hplain
          (translateFuelFix translateStep fuel) (hnosub id cache bools bits fuel) "out")
        (fun e' hU => by
          obtain ⟨dom, rfl⟩ := hunfE id e' hU
          exact LeafDom.dom (dbl_unfold_dom (useDbl_input id cache bools bits))))
  · exact Or.inr (Or.inr skip)

/-! ## Round 16: without the skipped outcome -/

/-- **`useDbl`, from the entry to the output wire.** Premises: the
Meta-library fact about `lambdaTelescope` (`htel`), the body's shape
(`hbody`), the binder-type oracle on the one declared type — its returning
runs (`hinf`) and its failing runs (`hinfT`: no catchable failure) —, the
result-type oracle (`hres`), the dispatch premises `hmap` / `hplain` /
`hnosub`, the unfolding oracle `hunfE`. Two outcomes: memo hit, or the
output statement. -/
theorem useDbl_output {logProf : String → IO Unit} {dv : DefinitionVal}
    {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {xTy : Lean.Expr}
    (htel : LamTelescopeOne)
    (hbody : ∀ body0, Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      ∃ (T b : Lean.Expr) (bi : BinderInfo),
        stripMemoizeWrappers body0 = Lean.Expr.lam `x T b bi ∧ b.isLambda = false ∧
        T.instantiateRevRange 0 0 #[] = xTy ∧
        ∀ id : FVarId, b.instantiateRevRange 0 1 #[Lean.Expr.fvar id] = callE id)
    (hinf : InfersBits xTy 8)
    (hinfT : InfersNoCatch xTy)
    (hres : ∀ id : FVarId, SignalTyped (callE id))
    (hmap : ∀ (id : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
      HasMappedFVar (setupOf ``useDbl useDblBinders [id] cache bools bits).context (callE id))
    (hplain : PlainHead ``dbl)
    (hnosub : ∀ (id : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (fuel : Nat),
      NoSubModule (translateFuelFix translateStep fuel)
        (setupOf ``useDbl useDblBinders [id] cache bools bits).context (callE id))
    (hunfE : ∀ (xid : FVarId) (e' : Lean.Expr), InlineUnfolds (callE xid) e' →
      ∃ dom : Lean.Expr, e' = dblUnfoldE dom xid)
    (hr : Tools.ShippingEntrySoundness.MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf ``useDbl [] false false (.defnInfo dv) isInst) (m, d)) :
    MemoHit ``useDbl m d ∨
    ∃ (id : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Sparkle.IR.Semantics.Env) (mems : Sparkle.IR.Semantics.MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (useDblBinders.zip [id])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (``useDbl : Name).toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt 8 useDblBinders m initial mems
        (bits id 8 + bits id 8).toNat := by
  have htele : ∀ body0,
      Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (OneBinderScope `x xTy callE) := by
    intro body0 hopen
    obtain ⟨T, b, bi, hb, hl, hT, hi⟩ := hbody body0 hopen
    exact telescopeIn_of_lam htel hb hl hT hi
  rcases one_binder_entry_output_bound (cfe := false) (nm := `x) (n := 8) (T := xTy)
      (leafOf := callE)
      (fun h => absurd h Bool.false_ne_true) (fun h => absurd h Bool.false_ne_true)
      (fun h => absurd h Bool.false_ne_true) htele (isSignalBinderType_frame xTy) hinf hinfT
      (fun id => ⟨rfl, hres id⟩) hr with hit | ⟨id, cache, H⟩
  · exact Or.inl hit
  · refine Or.inr ⟨id, cache, ?_⟩
    intro bools bits initial mems values
    exact H bools bits initial mems values
      (.bits 8 (bits id 8 + bits id 8)) (Nat.succ_pos 7)
      (LeafDom.inlineAt (dbl_notCore id)
        (fun fuel => dbl_reachesAt (hmap id cache bools bits) hplain
          (translateFuelFix translateStep fuel) (hnosub id cache bools bits fuel) "out")
        (fun e' hU => by
          obtain ⟨dom, rfl⟩ := hunfE id e' hU
          exact LeafDom.dom (dbl_unfold_dom (useDbl_input id cache bools bits))))

/-! ## Round 17: a second declaration, two inputs -/

/-- A second real declaration on the legacy route: two inputs. -/
def useDbl2 (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := dbl x

/-- The binders of `useDbl2`. -/
abbrev useDbl2Binders : List (Name × MixedGateBinder) := [(`x, .bits 8), (`y, .bits 8)]

/-- The binders of `useDbl2` with their declared types. -/
abbrev useDbl2Spec (xTy yTy : Lean.Expr) : List (Name × MixedGateBinder × Lean.Expr) :=
  [(`x, .bits 8, xTy), (`y, .bits 8, yTy)]

/-- **The prepared setup of `useDbl2` maps the first binder to its value.** -/
theorem useDbl2_input (id1 id2 : FVarId) (cache : IO.Ref (ExprStructMap String))
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    Tools.ShippingUnifiedMeaning.inputValues
      (setupOf ``useDbl2 useDbl2Binders [id1, id2] cache bools bits).bools
      (setupOf ``useDbl2 useDbl2Binders [id1, id2] cache bools bits).bits id1 =
      some (.bits 8 (bits id1 8)) := by
  refine Tools.ShippingUnifiedMeaning.inputValues_bits ?_ ?_
  · intro key b h
    exfalso
    revert h
    show (if key = id2 then (none : Option Bool) else if key = id1 then none else none) =
      some b → False
    intro h
    by_cases e2 : key = id2
    · rw [if_pos e2] at h
      cases h
    · rw [if_neg e2] at h
      by_cases e1 : key = id1
      · rw [if_pos e1] at h
        cases h
      · rw [if_neg e1] at h
        cases h
  · by_cases e : id1 = id2
    · subst e
      exact if_pos rfl
    · exact (if_neg e).trans (if_pos rfl)

/-- **`useDbl2`, from the entry to the output wire.** The premises of
`useDbl_output`, for two binders: the n-binder Meta-library fact (`htel`),
the body's shape (`hbody`), the binder-type oracle on each declared type
(returning runs `hinfX` / `hinfY`, failing runs `hinfTX` / `hinfTY`), the
result-type oracle (`hres`), the dispatch premises and the unfolding oracle.
Two outcomes: memo hit, or `out` carries `x + x`. -/
theorem useDbl2_output {logProf : String → IO Unit} {dv : DefinitionVal}
    {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {xTy yTy : Lean.Expr}
    (htel : LamTelescopeN)
    (hbody : ∀ body0, Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      ∃ (T1 T2 b : Lean.Expr) (bi1 bi2 : BinderInfo),
        stripMemoizeWrappers body0 =
          Lean.Expr.lam `x T1 (Lean.Expr.lam `y T2 b bi2) bi1 ∧
        b.isLambda = false ∧
        T1.instantiateRevRange 0 (#[] : Array Lean.Expr).size #[] = xTy ∧
        (∀ id1 : FVarId, T2.instantiateRevRange 0 (fv1 id1).size (fv1 id1) = yTy) ∧
        ∀ id1 id2 : FVarId,
          b.instantiateRevRange 0 (fv2 id1 id2).size (fv2 id1 id2) = callE id1)
    (hinfX : InfersBits xTy 8) (hinfTX : InfersNoCatch xTy)
    (hinfY : InfersBits yTy 8) (hinfTY : InfersNoCatch yTy)
    (hres : ∀ id : FVarId, SignalTyped (callE id))
    (hmap : ∀ (id1 id2 : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
      HasMappedFVar (setupOf ``useDbl2 useDbl2Binders [id1, id2] cache bools bits).context
        (callE id1))
    (hplain : PlainHead ``dbl)
    (hnosub : ∀ (id1 id2 : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (fuel : Nat),
      NoSubModule (translateFuelFix translateStep fuel)
        (setupOf ``useDbl2 useDbl2Binders [id1, id2] cache bools bits).context (callE id1))
    (hunfE : ∀ (xid : FVarId) (e' : Lean.Expr), InlineUnfolds (callE xid) e' →
      ∃ dom : Lean.Expr, e' = dblUnfoldE dom xid)
    (hr : Tools.ShippingEntrySoundness.MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf ``useDbl2 [] false false (.defnInfo dv) isInst) (m, d)) :
    MemoHit ``useDbl2 m d ∨
    ∃ (id1 id2 : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Sparkle.IR.Semantics.Env) (mems : Sparkle.IR.Semantics.MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
        (useDbl2Binders.zip [id1, id2])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (``useDbl2 : Name).toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt 8 useDbl2Binders m initial mems
        (bits id1 8 + bits id1 8).toNat := by
  have htele : ∀ body0,
      Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0)
        (ListScope (useDbl2Spec xTy yTy) (fun ids => callE (xOf ids))) := by
    intro body0 hopen
    obtain ⟨T1, T2, b, bi1, bi2, hb, hl, hT1, hT2, hi⟩ := hbody body0 hopen
    exact telescopeIn_of_lam2 (k1 := .bits 8) (k2 := .bits 8)
      (leafOf := fun ids => callE (xOf ids)) htel hb hl hT1 hT2 hi
  have horacle : ∀ q, q ∈ useDbl2Spec xTy yTy → BinderOracle q := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact And.intro (by intro h; cases h) (And.intro hinfX.hw hinfTX)
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact And.intro (by intro h; cases h) (And.intro hinfY.hw hinfTY)
      · cases hq
  rcases list_entry_output (cfe := false) (B := useDbl2Spec xTy yTy)
      (leafOf := fun ids => callE (xOf ids))
      (fun h => absurd h Bool.false_ne_true) (fun h => absurd h Bool.false_ne_true)
      (fun h => absurd h Bool.false_ne_true) htele horacle
      (fun ids => ⟨rfl, hres (xOf ids)⟩) hr with hit | ⟨ids, cache, hlen, H⟩
  · exact Or.inl hit
  · have len' : ids.length = 2 := hlen
    obtain ⟨id1, id2, rfl⟩ : ∃ id1 id2, ids = [id1, id2] := by
      cases ids with
      | nil => first | simp at len' | (simp only [List.length_nil] at len'; omega)
      | cons a tl =>
        cases tl with
        | nil =>
          first | simp at len' | (simp only [List.length_cons, List.length_nil] at len'; omega)
        | cons b tl2 =>
          cases tl2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons c tl3 =>
            first | simp at len' | (simp only [List.length_cons] at len'; omega)
    refine Or.inr ⟨id1, id2, cache, ?_⟩
    intro bools bits initial mems values
    exact H bools bits initial mems values
      (.bits 8 (bits id1 8 + bits id1 8)) (Nat.succ_pos 7)
      (LeafDom.inlineAt (dbl_notCore id1)
        (fun fuel => dbl_reachesAt (hmap id1 id2 cache bools bits) hplain
          (translateFuelFix translateStep fuel) (hnosub id1 id2 cache bools bits fuel) "out")
        (fun e' hU => by
          obtain ⟨dom, rfl⟩ := hunfE id1 e' hU
          exact LeafDom.dom (dbl_unfold_dom (useDbl2_input id1 id2 cache bools bits))))

/-! ## Round 18: a leaf that uses BOTH inputs (`useAdd2 x y := add2 x y`) -/

/-- An untagged two-argument helper. -/
def add2 (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := a + b

/-- A real declaration whose only leaf is the two-argument call. -/
def useAdd2 (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  add2 x y

/-- The leaf `add2 x y`. -/
abbrev callE2 (xid yid : FVarId) : Lean.Expr :=
  .app (.app (.const ``add2 []) (.fvar xid)) (.fvar yid)

/-- The second variable of a two-binder telescope. -/
abbrev yOf (ids : List FVarId) : FVarId := (ids.drop 1).headD ⟨.anonymous⟩

/-! ### The name facts of `add2` (the proofs of `dbl`'s, same text) -/

theorem add2_head (xid yid : FVarId) : (callE2 xid yid).getAppFn = .const ``add2 [] := rfl

set_option maxRecDepth 4096 in
theorem add2_kind (xid yid : FVarId) : fallbackKind (callE2 xid yid) = .other := by
  first | rfl | decide | decide +kernel

set_option maxRecDepth 4096 in
theorem add2_binOp : signalBinOpOf ``add2 = none := by
  first
    | rfl
    | decide
    | decide +kernel
    | exact Option.isNone_iff_eq_none.mp (by first | decide | decide +kernel)

set_option maxRecDepth 4096 in
theorem add2_notPrimitive : isPrimitive ``add2 = false := by
  first | rfl | decide | decide +kernel

set_option maxRecDepth 4096 in
theorem add2_notCore (xid yid : FVarId) : NotCore (callE2 xid yid) where
  shape := by
    first
      | rfl
      | decide
      | decide +kernel
      | (show ((``add2 == ``Sparkle.Core.Signal.Signal.pure) ||
            (match signalBinOpOf ``add2,
                canonicalSignalBinKinds ``add2 (callE2 xid yid).getAppArgs,
                canonicalSignalBitVecWidth (callE2 xid yid).getAppArgs with
             | some _, some (true, true), some _ => true
             | _, _, _ => false)) = false
         rw [show (``add2 == ``Sparkle.Core.Signal.Signal.pure) = false from by name_ne,
           add2_binOp]
         rfl)
  core := fun rec hint top named => by
    first
      | rfl
      | (show (if (``add2 == ``Sparkle.Core.Signal.Signal.pure) = true then
              translateSignalPureLiteral? (callE2 xid yid).getAppArgs hint named
            else
              match signalBinOpOf ``add2,
                  canonicalSignalBinKinds ``add2 (callE2 xid yid).getAppArgs,
                  canonicalSignalBitVecWidth (callE2 xid yid).getAppArgs with
              | some op, some (true, true), some _ => do
                let w ← translateCanonicalSignalBinary rec (callE2 xid yid) op
                  (callE2 xid yid).getAppArgs true true hint named
                pure (some w)
              | _, _, _ => pure none) = pure none
         rw [show (``add2 == ``Sparkle.Core.Signal.Signal.pure) = false from by name_ne,
           add2_binOp]
         rfl)

theorem add2_flags (xid yid : FVarId) (top : Bool) :
    (!true && !(callE2 xid yid).isFVar && !top) = false := rfl

theorem add2_glue : GlueName ``add2 :=
  ⟨by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne⟩

theorem add2_notBitVecOp : NotBitVecOp ``add2 :=
  ⟨by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne,
    by name_ne, add2_notPrimitive⟩

/-- The eleven `Name.toString` suffix tests the handlers and the body run on
the head's name. -/
structure Add2Suffixes : Prop where
  register : (``add2 : Name).toString.endsWith ".register" = false
  registerE : (``add2 : Name).toString.endsWith ".registerWithEnable" = false
  lut : (``add2 : Name).toString.endsWith ".lutMuxTree" = false
  mux : (``add2 : Name).toString.endsWith ".mux" = false
  memory : (``add2 : Name).toString.endsWith ".memory" = false
  combo : (``add2 : Name).toString.endsWith ".memoryComboRead" = false
  memoize : (``add2 : Name).toString.endsWith ".memoize" = false
  loop : (``add2 : Name).toString.endsWith ".loop" = false
  ofFin : (``add2 : Name).toString.endsWith ".ofFin" = false
  ofNat : (``add2 : Name).toString.endsWith ".ofNat" = false
  toNat : (``add2 : Name).toString.endsWith ".toNat" = false

set_option maxRecDepth 8192 in
/-- **The suffix tests, proved** through the candidate renderings of the
name: no evaluation of `Name.toString`. -/
theorem add2_suffixes : Add2Suffixes :=
  ⟨endsWith_false_of _ _ (by cand_dec), endsWith_false_of _ _ (by cand_dec),
    endsWith_false_of _ _ (by cand_dec), endsWith_false_of _ _ (by cand_dec),
    endsWith_false_of _ _ (by cand_dec), endsWith_false_of _ _ (by cand_dec),
    endsWith_false_of _ _ (by cand_dec), endsWith_false_of _ _ (by cand_dec),
    endsWith_false_of _ _ (by cand_dec), endsWith_false_of _ _ (by cand_dec),
    endsWith_false_of _ _ (by cand_dec)⟩

theorem add2_plainName (suf : Add2Suffixes) : PlainName ``add2 :=
  ⟨by name_ne, by name_ne, by name_ne, by name_ne, by name_ne,
    suf.register, suf.registerE, suf.lut, suf.mux, suf.memory, suf.combo⟩

theorem add2_plainName2 (suf : Add2Suffixes) : PlainName2 ``add2 :=
  ⟨by name_ne, suf.memoize, suf.loop, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne,
    by name_ne, by name_ne, by name_ne, by name_ne⟩

theorem add2_implName (suf : Add2Suffixes) : ImplName ``add2 :=
  ⟨add2_binOp, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne,
    by name_ne, by name_ne, by name_ne, by name_ne, suf.ofFin, suf.ofNat, suf.toNat,
    by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne, by name_ne,
    by name_ne, by name_ne, by name_ne, by name_ne⟩

/-- The name facts of `add2`, bundled. -/
theorem add2_callee : PlainCallee ``add2 :=
  ⟨add2_glue, add2_plainName add2_suffixes, add2_notBitVecOp, add2_plainName2 add2_suffixes,
    add2_implName add2_suffixes⟩

/-! ### The unfolding and the inputs -/

/-- The first of two, or the second. -/
def sel2 {α : Type} (a b : α) : Nat → α
  | 0 => a
  | _ => b

/-- The body of `add2` on two 8-bit inputs, as a term of the quoted fragment. -/
abbrev add2Term : Tools.ShippingUnifiedSource.Term (.bits 8) :=
  .binary .add (.bitsInput 8 0) (.bitsInput 8 1)

/-- The quoted unfolding of `add2 x y`. -/
abbrev add2UnfoldE (dom : Lean.Expr) (xid yid : FVarId) : Lean.Expr :=
  Tools.ShippingUnifiedSource.quote dom (fun _ => .fvar xid)
    (sel2 (Lean.Expr.fvar xid) (Lean.Expr.fvar yid)) add2Term

/-- **The quoted unfolding is in the domain at `x + y`**, from the two
inputs' values (`LegacyDom.cert` with two vector inputs). -/
theorem add2_unfold_dom {ctx : CompilerState}
    {inputs : FVarId → Option Tools.ShippingUnifiedMeaning.Value} {dom : Lean.Expr}
    {xid yid : FVarId} {b1 b2 : BitVec 8}
    (h1 : inputs xid = some (.bits 8 b1)) (h2 : inputs yid = some (.bits 8 b2)) :
    LegacyDom ctx inputs (add2UnfoldE dom xid yid) (.bits 8 (b1 + b2)) := by
  have h1' : inputs xid = some (.bits 8 (BitVec.setWidth 8 b1)) := by
    rw [BitVec.setWidth_eq]; exact h1
  have h2' : inputs yid = some (.bits 8 (BitVec.setWidth 8 b2)) := by
    rw [BitVec.setWidth_eq]; exact h2
  have hval : Tools.ShippingUnifiedMeaning.pack (.bits 8)
      (Tools.ShippingUnifiedSource.eval (fun _ => false)
        (fun j w => BitVec.setWidth w (sel2 b1 b2 j)) add2Term) = .bits 8 (b1 + b2) := by
    show Tools.ShippingUnifiedMeaning.Value.bits 8
      (Tools.ShippingScalarSoundness.Binary.apply .add (BitVec.setWidth 8 b1)
        (BitVec.setWidth 8 b2)) = _
    first
      | (rw [BitVec.setWidth_eq, BitVec.setWidth_eq] <;> rfl)
      | (simp only [BitVec.setWidth_eq]; rfl)
      | simp [BitVec.setWidth_eq]
  have hM : ∀ j, j < 2 → Tools.ShippingUnifiedMeaning.Meaning inputs
      (sel2 (Lean.Expr.fvar xid) (Lean.Expr.fvar yid) j)
      (.bits 8 (BitVec.setWidth 8 (sel2 b1 b2 j))) := by
    intro j hj
    cases j with
    | zero => exact Tools.ShippingUnifiedMeaning.Meaning.input rfl h1'
    | succ j =>
      cases j with
      | zero => exact Tools.ShippingUnifiedMeaning.Meaning.input rfl h2'
      | succ j => exact absurd hj (by omega)
  have hD : ∀ j, j < 2 → LegacyDom ctx inputs
      (sel2 (Lean.Expr.fvar xid) (Lean.Expr.fvar yid) j)
      (.bits 8 (BitVec.setWidth 8 (sel2 b1 b2 j))) := by
    intro j hj
    cases j with
    | zero => exact LegacyDom.input h1'
    | succ j =>
      cases j with
      | zero => exact LegacyDom.input h2'
      | succ j => exact absurd hj (by omega)
  have h := LegacyDom.cert (ctx := ctx) (inputs := inputs) (dom := dom) (kb := 0) (kv := 2)
    (vw := fun _ => 8) (bE := fun _ => .fvar xid)
    (vE := sel2 (Lean.Expr.fvar xid) (Lean.Expr.fvar yid))
    (bools := fun _ => false) (bits := fun j w => BitVec.setWidth w (sel2 b1 b2 j)) add2Term
    ⟨⟨Nat.zero_lt_succ 1, rfl, Nat.succ_pos 7⟩, ⟨Nat.lt_succ_self 1, rfl, Nat.succ_pos 7⟩⟩
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    hM
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    hD
  first
    | (rw [hval] at h; exact h)
    | exact hval ▸ h

/-- **The prepared setup of `useAdd2` maps the first binder to its value.** -/
theorem useAdd2_input1 (id1 id2 : FVarId) (cache : IO.Ref (ExprStructMap String))
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    Tools.ShippingUnifiedMeaning.inputValues
      (setupOf ``useAdd2 useDbl2Binders [id1, id2] cache bools bits).bools
      (setupOf ``useAdd2 useDbl2Binders [id1, id2] cache bools bits).bits id1 =
      some (.bits 8 (bits id1 8)) := by
  refine Tools.ShippingUnifiedMeaning.inputValues_bits ?_ ?_
  · intro key b h
    exfalso
    revert h
    show (if key = id2 then (none : Option Bool) else if key = id1 then none else none) =
      some b → False
    intro h
    by_cases e2 : key = id2
    · rw [if_pos e2] at h
      cases h
    · rw [if_neg e2] at h
      by_cases e1 : key = id1
      · rw [if_pos e1] at h
        cases h
      · rw [if_neg e1] at h
        cases h
  · by_cases e : id1 = id2
    · subst e
      exact if_pos rfl
    · exact (if_neg e).trans (if_pos rfl)

/-- **… and the second binder to its value.** -/
theorem useAdd2_input2 (id1 id2 : FVarId) (cache : IO.Ref (ExprStructMap String))
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    Tools.ShippingUnifiedMeaning.inputValues
      (setupOf ``useAdd2 useDbl2Binders [id1, id2] cache bools bits).bools
      (setupOf ``useAdd2 useDbl2Binders [id1, id2] cache bools bits).bits id2 =
      some (.bits 8 (bits id2 8)) := by
  refine Tools.ShippingUnifiedMeaning.inputValues_bits ?_ ?_
  · intro key b h
    exfalso
    revert h
    show (if key = id2 then (none : Option Bool) else if key = id1 then none else none) =
      some b → False
    intro h
    by_cases e2 : key = id2
    · rw [if_pos e2] at h
      cases h
    · rw [if_neg e2] at h
      by_cases e1 : key = id1
      · rw [if_pos e1] at h
        cases h
      · rw [if_neg e1] at h
        cases h
  · exact if_pos rfl

/-- **`useAdd2`, from the entry to the output wire: `out` carries `x + y`.**
The premise classes of `useDbl2_output`; the leaf is the two-argument call,
in the leaf domain through `plainCallee_leaf` (the name facts of `add2` as
one bundle) and `add2_unfold_dom`. -/
theorem useAdd2_output {logProf : String → IO Unit} {dv : DefinitionVal}
    {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {xTy yTy : Lean.Expr}
    (htel : LamTelescopeN)
    (hbody : ∀ body0, Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      ∃ (T1 T2 b : Lean.Expr) (bi1 bi2 : BinderInfo),
        stripMemoizeWrappers body0 =
          Lean.Expr.lam `x T1 (Lean.Expr.lam `y T2 b bi2) bi1 ∧
        b.isLambda = false ∧
        T1.instantiateRevRange 0 (#[] : Array Lean.Expr).size #[] = xTy ∧
        (∀ id1 : FVarId, T2.instantiateRevRange 0 (fv1 id1).size (fv1 id1) = yTy) ∧
        ∀ id1 id2 : FVarId,
          b.instantiateRevRange 0 (fv2 id1 id2).size (fv2 id1 id2) = callE2 id1 id2)
    (hinfX : InfersBits xTy 8) (hinfTX : InfersNoCatch xTy)
    (hinfY : InfersBits yTy 8) (hinfTY : InfersNoCatch yTy)
    (hres : ∀ id1 id2 : FVarId, SignalTyped (callE2 id1 id2))
    (hmap : ∀ (id1 id2 : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
      HasMappedFVar (setupOf ``useAdd2 useDbl2Binders [id1, id2] cache bools bits).context
        (callE2 id1 id2))
    (hplain : PlainHead ``add2)
    (hnosub : ∀ (id1 id2 : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (fuel : Nat),
      NoSubModule (translateFuelFix translateStep fuel)
        (setupOf ``useAdd2 useDbl2Binders [id1, id2] cache bools bits).context
        (callE2 id1 id2))
    (hunfE : ∀ (xid yid : FVarId) (e' : Lean.Expr), InlineUnfolds (callE2 xid yid) e' →
      ∃ dom : Lean.Expr, e' = add2UnfoldE dom xid yid)
    (hr : Tools.ShippingEntrySoundness.MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf ``useAdd2 [] false false (.defnInfo dv) isInst) (m, d)) :
    MemoHit ``useAdd2 m d ∨
    ∃ (id1 id2 : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Sparkle.IR.Semantics.Env) (mems : Sparkle.IR.Semantics.MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
        (useDbl2Binders.zip [id1, id2])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (``useAdd2 : Name).toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt 8 useDbl2Binders m initial mems
        (bits id1 8 + bits id2 8).toNat := by
  have htele : ∀ body0,
      Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0)
        (ListScope (useDbl2Spec xTy yTy) (fun ids => callE2 (xOf ids) (yOf ids))) := by
    intro body0 hopen
    obtain ⟨T1, T2, b, bi1, bi2, hb, hl, hT1, hT2, hi⟩ := hbody body0 hopen
    exact telescopeIn_of_lam2 (k1 := .bits 8) (k2 := .bits 8)
      (leafOf := fun ids => callE2 (xOf ids) (yOf ids)) htel hb hl hT1 hT2 hi
  have horacle : ∀ q, q ∈ useDbl2Spec xTy yTy → BinderOracle q := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact And.intro (by intro h; cases h) (And.intro hinfX.hw hinfTX)
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact And.intro (by intro h; cases h) (And.intro hinfY.hw hinfTY)
      · cases hq
  rcases list_entry_output (cfe := false) (B := useDbl2Spec xTy yTy)
      (leafOf := fun ids => callE2 (xOf ids) (yOf ids))
      (fun h => absurd h Bool.false_ne_true) (fun h => absurd h Bool.false_ne_true)
      (fun h => absurd h Bool.false_ne_true) htele horacle
      (fun ids => ⟨rfl, hres (xOf ids) (yOf ids)⟩) hr with hit | ⟨ids, cache, hlen, H⟩
  · exact Or.inl hit
  · have len' : ids.length = 2 := hlen
    obtain ⟨id1, id2, rfl⟩ : ∃ id1 id2, ids = [id1, id2] := by
      cases ids with
      | nil => first | simp at len' | (simp only [List.length_nil] at len'; omega)
      | cons a tl =>
        cases tl with
        | nil =>
          first | simp at len' | (simp only [List.length_cons, List.length_nil] at len'; omega)
        | cons b tl2 =>
          cases tl2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons c tl3 =>
            first | simp at len' | (simp only [List.length_cons] at len'; omega)
    refine Or.inr ⟨id1, id2, cache, ?_⟩
    intro bools bits initial mems values
    exact H bools bits initial mems values
      (.bits 8 (bits id1 8 + bits id2 8)) (Nat.succ_pos 7)
      (plainCallee_leaf add2_callee (add2_head id1 id2) (add2_kind id1 id2)
        (add2_notCore id1 id2) hplain (hmap id1 id2 cache bools bits)
        (fun fuel => hnosub id1 id2 cache bools bits fuel)
        (fun e' hU => by
          obtain ⟨dom, rfl⟩ := hunfE id1 id2 e' hU
          exact LeafDom.dom (add2_unfold_dom (useAdd2_input1 id1 id2 cache bools bits)
            (useAdd2_input2 id1 id2 cache bools bits))))

/-! ## Round 21: a structure field projection (`SHA256Out.done`), shipping configuration -/

/-- The declaration's name (the module is not imported here). -/
abbrev sha256DoneName : Name := `Sparkle.IP.Crypto.SHA256.SHA256Out.done

/-- Its binders after `openRecordInputs`: the domain, then the record's two
Signal fields. -/
abbrev sha256OutBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`hash, .bits 256), (`done, .bool)]

/-- **The prepared setup maps the variable of the field `done` to its Bool
value.** -/
theorem sha256Out_done_input (id1 id2 id3 : FVarId) (cache : IO.Ref (ExprStructMap String))
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    Tools.ShippingUnifiedMeaning.inputValues
      (setupOf sha256DoneName sha256OutBinders [id1, id2, id3] cache bools bits).bools
      (setupOf sha256DoneName sha256OutBinders [id1, id2, id3] cache bools bits).bits id3 =
      some (.bool (bools id3)) :=
  Tools.ShippingUnifiedMeaning.inputValues_bool (if_pos rfl)

/-- **`SHA256Out.done`, from the shipping entry to the output wire: `out`
carries the input bound for the field `done`.**

Premises, by class. Environment (reflection): the three gates decline
(`old`, `mixed`, `hmach`); the body's shape after `openRecordInputs` /
`stripMemoizeWrappers` with the instantiated binder types and leaf (`hbody`);
the leaf is an application with a lambda head (`hshape`) of fallback kind
`other` (`hkind`). Meta library: `htel`. Oracles: no hardware type for the
domain binder's type (`hdom`), `bitVector 256` and `bit` for the two fields
(`hhash`, `hdone`), the leaf's reducible `whnf` is the third variable
(`hwhnf`), the leaf's type is Signal-headed (`hres`). The run: `hr`. -/
theorem SHA256Out_done_output {logProf : String → IO Unit} {dv : DefinitionVal}
    {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {leafOf : List FVarId → Lean.Expr} {domTy : Lean.Expr} {hashTy doneTy : FVarId → Lean.Expr}
    (old : certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htel : LamTelescopeN)
    (hbody : ∀ body0, Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      ∃ (T1 T2 T3 b : Lean.Expr) (bi1 bi2 bi3 : BinderInfo),
        stripMemoizeWrappers body0 =
          Lean.Expr.lam `dom T1 (Lean.Expr.lam `hash T2 (Lean.Expr.lam `done T3 b bi3) bi2) bi1 ∧
        b.isLambda = false ∧
        T1.instantiateRevRange 0 (#[] : Array Lean.Expr).size #[] = domTy ∧
        (∀ id1 : FVarId, T2.instantiateRevRange 0 (fv1 id1).size (fv1 id1) = hashTy id1) ∧
        (∀ id1 id2 : FVarId,
          T3.instantiateRevRange 0 (fv2p id1 id2).size (fv2p id1 id2) = doneTy id1) ∧
        ∀ id1 id2 id3 : FVarId,
          b.instantiateRevRange 0 (fv3 id1 id2 id3).size (fv3 id1 id2 id3) =
            leafOf [id1, id2, id3])
    (hdom : InfersNothing domTy)
    (hhash : ∀ id1 : FVarId,
      InfersHW (hashTy id1) (.bitVector 256) ∧ InfersNoCatch (hashTy id1))
    (hdone : ∀ id1 : FVarId, InfersHW (doneTy id1) .bit ∧ InfersNoCatch (doneTy id1))
    (hshape : ∀ ids : List FVarId, ∃ (f a : Lean.Expr) (n : Name) (ty b : Lean.Expr)
      (bi : BinderInfo), leafOf ids = Lean.Expr.app f a ∧
        (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi)
    (hkind : ∀ ids : List FVarId, fallbackKind (leafOf ids) = .other)
    (hwhnf : ∀ id1 id2 id3 : FVarId, WhnfIsVar (leafOf [id1, id2, id3]) id3)
    (hres : ∀ ids : List FVarId, SignalTyped (leafOf ids))
    (hr : Tools.ShippingEntrySoundness.MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf sha256DoneName [] false true (.defnInfo dv) isInst) (m, d)) :
    MemoHit sha256DoneName m d ∨
    ∃ (id1 id2 id3 : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Sparkle.IR.Semantics.Env) (mems : Sparkle.IR.Semantics.MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
        (sha256OutBinders.zip [id1, id2, id3])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          sha256DoneName.toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt
        (Tools.ShippingUnifiedMeaning.Value.bool (bools id3)).kind.width sha256OutBinders m
        initial mems (Tools.ShippingUnifiedMeaning.Value.bool (bools id3)).toNat := by
  have htele : ∀ body0,
      Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (ListScopeD sha256OutBinders leafOf) := by
    intro body0 hopen
    obtain ⟨T1, T2, T3, b, bi1, bi2, bi3, hb, hl, hT1, hT2, hT3, hi⟩ := hbody body0 hopen
    have o1 : TypeOk .domain (T1.instantiateRevRange 0 (#[] : Array Lean.Expr).size #[]) := by
      rw [hT1]
      exact hdom
    have o2 : ∀ id1 : FVarId,
        TypeOk (.bits 256) (T2.instantiateRevRange 0 (fv1 id1).size (fv1 id1)) := by
      intro id1
      rw [hT2 id1]
      exact hhash id1
    have o3 : ∀ id1 id2 : FVarId,
        TypeOk .bool (T3.instantiateRevRange 0 (fv2p id1 id2).size (fv2p id1 id2)) := by
      intro id1 id2
      rw [hT3 id1 id2]
      exact hdone id1
    exact telescopeIn_of_lam3 (k1 := .domain) (k2 := .bits 256) (k3 := .bool)
      (leafOf := leafOf) htel hb hl o1 o2 o3 hi
  have hleaf : ∀ ids : List FVarId,
      (leafOf ids).isLambda = false ∧ SignalTyped (leafOf ids) := by
    intro ids
    obtain ⟨f, a, n, ty, b, bi, he, _⟩ := hshape ids
    refine ⟨?_, hres ids⟩
    rw [he]
    first | done | rfl
  rcases list_entry_outputD (cfe := true) (bs := sha256OutBinders) (leafOf := leafOf)
      (fun _ => old) (fun _ => mixed) (fun _ => hmach) htele hleaf hr with
    hit | ⟨ids, cache, hlen, H⟩
  · exact Or.inl hit
  · have len' : ids.length = 3 := hlen
    obtain ⟨id1, id2, id3, rfl⟩ : ∃ id1 id2 id3, ids = [id1, id2, id3] := by
      cases ids with
      | nil => first | simp at len' | (simp only [List.length_nil] at len'; omega)
      | cons a tl =>
        cases tl with
        | nil =>
          first | simp at len' | (simp only [List.length_cons, List.length_nil] at len'; omega)
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            first
              | simp at len'
              | (simp only [List.length_cons, List.length_nil] at len'; omega)
          | cons c tl3 =>
            cases tl3 with
            | nil => exact ⟨a, b, c, rfl⟩
            | cons e tl4 =>
              first | simp at len' | (simp only [List.length_cons] at len'; omega)
    refine Or.inr ⟨id1, id2, id3, cache, ?_⟩
    intro bools bits initial mems values
    obtain ⟨f, a, n, ty, b, bi, he, hfnL⟩ := hshape [id1, id2, id3]
    have hk := hkind [id1, id2, id3]
    have hw := hwhnf id1 id2 id3
    rw [he] at hk
    rw [he] at hw
    have dom : LeafDom (setupOf sha256DoneName sha256OutBinders [id1, id2, id3] cache bools
        bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf sha256DoneName sha256OutBinders [id1, id2, id3] cache bools bits).bools
          (setupOf sha256DoneName sha256OutBinders [id1, id2, id3] cache bools bits).bits)
        "out" true (leafOf [id1, id2, id3])
        (Tools.ShippingUnifiedMeaning.Value.bool (bools id3)) := by
      rw [he]
      exact leafDom_betaWire hfnL hk hw (sha256Out_done_input id1 id2 id3 cache bools bits)
    exact H bools bits initial mems values
      (Tools.ShippingUnifiedMeaning.Value.bool (bools id3)) Nat.zero_lt_one dom

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
    -- the unfolding oracle on the leaf against the quoted term of `hunfE`
    let unfolded ← Lean.Meta.unfoldDefinition? (callE xid)
    let unfoldMatches : Bool :=
      match unfolded with
      | some u => u == dblUnfoldE (.const ``defaultDomain []) xid
      | none => false
    logInfo m!"LEGACY INLINE ARM, hunfE EVIDENCE: unfoldDefinition? (dbl x) equals the quoted term x + x (domain = the constant defaultDomain): {unfoldMatches}; the oracle returned: {unfolded}"
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

/-! ## Round 15: evidence for the reflection premises of `useDbl_output`

Logs only. One run, in this environment: an observation, not a proof. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let ci ← getConstInfo ``useDbl
    let body0 ← openRecordInputs ci.value!
    let body := stripMemoizeWrappers body0
    let shape : String :=
      match body with
      | .lam nm _ b _ => s!"a lambda, binder name {nm}, its body is a lambda: {b.isLambda}"
      | _ => "NOT a lambda"
    Lean.Meta.lambdaTelescope body fun xs inner => do
      let x := xs[0]!
      let decl ← x.fvarId!.getDecl
      -- hbody: the telescope's own results against the premise's two
      -- instantiations and the leaf
      let leafOk : Bool := xs.size == 1 && inner == callE x.fvarId!
      let rawOk : Bool :=
        match body with
        | .lam _ T b _ =>
          T.instantiateRevRange 0 0 #[] == decl.type &&
            b.instantiateRevRange 0 1 #[x] == callE x.fvarId!
        | _ => false
      let nameOk : Bool := decl.userName == `x
      -- hinf: the binder-type oracle on the declared type
      let cache ← IO.mkRef ({} : ExprStructMap String)
      let st0 := Sparkle.IR.Builder.CircuitM.init "evidence"
      let hw : String ← try
          let (h, _) ←
            ((inferHWTypeFromSignal decl.type).run (entryCompilerState false cache)).run st0
          pure (match h with
            | .bitVector n => s!"bitVector {n}"
            | _ => "another hardware type")
        catch _ => pure "THREW"
      -- hres: the result-type oracle on the leaf
      let ty ← inferType inner
      let tyN ← whnf ty
      let headOk : Bool := tyN.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal
      logInfo m!"LEGACY ENTRY, hbody EVIDENCE: the stripped value of useDbl is {shape}; inside lambdaTelescope: one variable and the body equals `dbl x` (callE): {leafOk}; the premise's two instantiateRevRange results equal the declared type and callE: {rawOk}; the declared user name is x: {nameOk}. hinf EVIDENCE: inferHWTypeFromSignal on the declared binder type returned: {hw} (expected bitVector 8). hres EVIDENCE: the whnf of the leaf's inferred type is headed by Signal: {headOk}"
      -- the third outcome itself: the leaf translated with NO port bound
      let skipped : String ← try
          let _ ←
            ((emitLeaves (fun e h t n => translateExprToWire e h t n) cache (fun _ => pure ())
              [("out", inner)] none 0).run (entryCompilerState false cache)).run st0
          pure "RETURNED: InputSkipped is a real behaviour of the leaf translation"
        catch ex => do
          let msg ← ex.toMessageData.toString
          pure s!"THREW ({msg})"
      logInfo m!"LEGACY ENTRY, SKIPPED-INPUT EVIDENCE: emitLeaves on the leaf `dbl x` with no input port bound (empty varMap, fresh builder state): {skipped}"
  catch ex =>
    logInfo m!"LEGACY ENTRY, ROUND 15 EVIDENCE: harness error: {ex.toMessageData}"

/-! ## Round 17: the second declaration compiles on the legacy route; the axiom audit -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let compiled ← try
      let _ ← synthesizeCombinationalCoreWith
        (fun e h t n => translateExprToWire e h t n) ``useDbl2 [] false
        (certifiedFrontEnd := false)
      pure true
    catch _ => pure false
  logInfo m!"LEGACY ENTRY, SECOND DECLARATION: useDbl2 (two inputs) compiles with the legacy front end: {compiled}"

/-! ## Round 18: evidence for the two-binder `hbody`, the binder and result oracles and the
unfolding of `add2` (logs only; one run in this environment — an observation, not a proof) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let decls : List (Name × (FVarId → FVarId → Lean.Expr)) :=
    [(``useDbl2, fun a _ => callE a), (``useAdd2, fun a b => callE2 a b)]
  for (declName, leafOf) in decls do
    try
      let ci ← getConstInfo declName
      let body0 ← openRecordInputs ci.value!
      let body := stripMemoizeWrappers body0
      let shape : String :=
        match body with
        | .lam n1 _ (.lam n2 _ b _) _ =>
          s!"two nested lambdas, binder names {n1}, {n2}, the inner body is a lambda: {b.isLambda}"
        | _ => "NOT two nested lambdas"
      Lean.Meta.lambdaTelescope body fun xs inner => do
        let x := xs[0]!
        let y := xs[1]!
        let dx ← x.fvarId!.getDecl
        let dy ← y.fvarId!.getDecl
        let leafOk : Bool := xs.size == 2 && inner == leafOf x.fvarId! y.fvarId!
        let rawOk : Bool :=
          match body with
          | .lam _ T1 (.lam _ T2 b _) _ =>
            T1.instantiateRevRange 0 (#[] : Array Lean.Expr).size #[] == dx.type &&
              T2.instantiateRevRange 0 (fv1 x.fvarId!).size (fv1 x.fvarId!) == dy.type &&
              b.instantiateRevRange 0 (fv2 x.fvarId! y.fvarId!).size (fv2 x.fvarId! y.fvarId!) ==
                leafOf x.fvarId! y.fvarId!
          | _ => false
        let namesOk : Bool := dx.userName == `x && dy.userName == `y
        let cache ← IO.mkRef ({} : ExprStructMap String)
        let st0 := Sparkle.IR.Builder.CircuitM.init "evidence"
        let hwX : String ← try
            let (h, _) ←
              ((inferHWTypeFromSignal dx.type).run (entryCompilerState false cache)).run st0
            pure (match h with
              | .bitVector n => s!"bitVector {n}"
              | _ => "another hardware type")
          catch _ => pure "THREW"
        let hwY : String ← try
            let (h, _) ←
              ((inferHWTypeFromSignal dy.type).run (entryCompilerState false cache)).run st0
            pure (match h with
              | .bitVector n => s!"bitVector {n}"
              | _ => "another hardware type")
          catch _ => pure "THREW"
        let ty ← inferType inner
        let tyN ← whnf ty
        let headOk : Bool := tyN.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal
        logInfo m!"LEGACY ENTRY, TWO-BINDER EVIDENCE for {declName}: the stripped value is {shape}; inside lambdaTelescope: two variables and the body equals the stated leaf: {leafOk}; the premise's three instantiateRevRange results equal the two declared types and the leaf: {rawOk}; the declared user names are x, y: {namesOk}. hinfX: {hwX}, hinfY: {hwY} (expected bitVector 8 twice). hres: the whnf of the leaf's inferred type is headed by Signal: {headOk}"
    catch ex =>
      logInfo m!"LEGACY ENTRY, TWO-BINDER EVIDENCE for {declName}: harness error: {ex.toMessageData}"
  try
    let xid : FVarId := ⟨`x⟩
    let yid : FVarId := ⟨`y⟩
    let unfolded ← Lean.Meta.unfoldDefinition? (callE2 xid yid)
    let unfoldMatches : Bool :=
      match unfolded with
      | some u => u == add2UnfoldE (.const ``defaultDomain []) xid yid
      | none => false
    let compiled ← try
        let _ ← synthesizeCombinationalCoreWith
          (fun e h t n => translateExprToWire e h t n) ``useAdd2 [] false
          (certifiedFrontEnd := false)
        pure true
      catch _ => pure false
    logInfo m!"LEGACY ENTRY, THIRD DECLARATION: useAdd2 (leaf add2 x y) compiles with the legacy front end: {compiled}; hunfE EVIDENCE: unfoldDefinition? (add2 x y) equals the quoted term x + y (domain = the constant defaultDomain): {unfoldMatches}; the oracle returned: {unfolded}"
  catch ex =>
    logInfo m!"LEGACY ENTRY, THIRD DECLARATION: harness error: {ex.toMessageData}"

-- The acceptance check: standard axioms only. This one THROWS.
run_cmd Lean.Elab.Command.liftTermElabM do
  let audited : List Name := [``useDbl_output, ``useDbl2_output, ``useAdd2_output,
    ``SHA256Out_done_output, ``Tools.ShippingLegacySem.list_entry_outputD,
    ``Tools.ShippingLegacySem.leafDom_betaWire,
    ``Tools.ShippingLegacySem.plainCallee_leaf, ``Tools.ShippingLegacySem.handlerCase_inline,
    ``Tools.ShippingLegacySem.one_binder_entry_output_bound,
    ``Tools.ShippingLegacySem.list_entry_output,
    ``Tools.ShippingLegacySem.returns_tryCatch_throws]
  for n in audited do
    let axs ← Lean.collectAxioms n
    if axs.any fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound) then
      throwError "{n} depends on a non-standard axiom: {axs}"
  logInfo m!"LEGACY ENTRY, AXIOM AUDIT: {audited} depend on no axiom beyond propext, Classical.choice, Quot.sound"

end Sparkle.Tests.Compiler.LegacySemInstanceTest
