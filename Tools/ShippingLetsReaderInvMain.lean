import Tools.ShippingLetsReaderInvPure
import Tools.ShippingReaderFuelOldEq

/-! # Unit LC3 (main): the joint invariant of the reader twin, its consequences, and what stays OPEN

BUILT: UNBUILT (written, first build pending). No `sorry`, no axiom, no `native_decide`.

## What is PROVED (about the fuel TWIN `readF`, for every fuel)

`machConvF_post` / `machChainF_post` / `machLoopBodyF_post` / `machLoopRootF_post` / `machNestedF_post`:
from a state with `RdOk` (alias-free `let` table, range-closed kept expressions), an environment in range
and an input that mentions no `_machLet` placeholder, every non-OUT, non-FAIL answer has
(i) `NoLetAlias` of the output `let` table, (ii) a table that did not shrink, (iii) the returned expression
in range of the OUTPUT table. `alias_premise_of_conv` turns (iii) into the `Alias` premise of
`machBindLetAlias_noAlias` (`Tools/ShippingLetsAliasInv.lean`) at the `machLoopBody` call site, so the
`machBindLetAlias` step is covered inside the induction (`Tools/ShippingLetsReaderInv.lean`, `loopLet_facts`).

## PREMISES (named hypotheses of the theorems below, none an axiom)

* `OpenFacts senv`: statements about functions this proof cannot unfold — `rootFloat` (`partial def`),
  `Expr.liftLooseBVars` / `Expr.instantiate1` (extern), the signature types of `senv.instS` — and two total
  but matcher-sensitive functions (`bundleIota`, the bare-register view `regView?`; v4.32.1 cannot split their
  `match`, the proof was not done here). Each says "no `_machLet j` out of nothing".
* `LetOk 0 e`: the reader's INPUT mentions no `_machLet` placeholder (true of an environment
  declaration's body; NOT proved from the declaration here).
* `EnvOk 0 env` for the start environment.

## OPEN (stated, not proved)

* TWIN → REAL: `TwinCover senv (realFns senv)` — the real `partial` answer is some fuel's twin answer (O1
  coverage + O2 transcription fidelity, `docs/parallel/R-reader-coverage.md`); `real_machConv_post` is
  CONDITIONAL on it. A twin result is not a proof about the real reader.
* The loose-bvar condition on `let` values (`machClose_bvar` bounds only the root bvar).
* The `Expr` → typed `letFields` / `quote` link (proof-generation side).
* The fields of `OpenFacts`. -/
namespace Tools.ShippingLetsReaderInv
open Lean Sparkle.Compiler.Elab
open Tools.ShippingLetsAliasInv Tools.ShippingReaderFuel

/-- The hypotheses NOT discharged by unfolding (see the header). -/
structure OpenFacts (senv : StructEnv) : Prop where
  rootFloat : ∀ n v, LetOk n v = true →
    LetOk n (Sparkle.Compiler.MachRawSurface.rootFloat v) = true
  lift : ∀ n e k m, LetOk n e = true → LetOk n (e.liftLooseBVars k m) = true
  inst1 : ∀ n b a, LetOk n b = true → LetOk n a = true → LetOk n (b.instantiate1 a) = true
  sigTy : ∀ c kinds ty, senv.instS c = some (kinds, ty) → ∀ n, LetOk n ty = true
  bundleIota : ∀ n e, LetOk n e = true →
    LetOk n (Sparkle.Compiler.MachRawSurface.bundleIota e) = true
  regView : ∀ n fn args d α i x, (∀ a ∈ args, LetOk n a = true) →
    regView? fn args = some (d, α, i, x) → LetOk n d = true ∧ LetOk n x = true

/-- The full record the induction uses, from `OpenFacts` and the lemmas of `…InvPure`. -/
theorem pureFacts_of {senv : StructEnv} (O : OpenFacts senv) : PureFacts senv where
  rootFloat := O.rootFloat
  lift := O.lift
  inst1 := O.inst1
  sigTy := O.sigTy
  bundleIota := O.bundleIota
  projIota := fun n e he => projIota_ok senv.proj n e he
  regView := O.regView
  runApp := fun n e dom αs inits body he h => runApp_ok n e dom αs inits body he h
  instCall := fun n e c kinds res args he h => instCall_ok senv n e c kinds res args he h
  instCallS := fun n e c kinds ty args he h => instCallS_ok senv n e c kinds ty args he h
  memCall := fun n e combo aw dw dom ops he h => memCall_ok _ n e combo aw dw dom ops he h
  loopView := fun n e dom body he h => loopView_ok n e dom body he h
  letTail := fun n e he => letTail_ok n e he
  loopRegs := fun n e regs he h => loopRegs_ok n e regs he h

/-! ## The twin's answers -/

variable {senv : StructEnv}

theorem machConvF_post (O : OpenFacts senv) {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machConvF n senv env d e st = some (some (r, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true := by
  have := readF_good senv (pureFacts_of O) n (Call.conv env d e st) ⟨hst, hE, hl⟩ (r, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem machNestedF_post (O : OpenFacts senv) {n : Nat} {env : List MachVal}
    {dom αs initsE body : Lean.Expr} {st st' : MachRead} {r : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hd : LetOk 0 dom = true) (hb : LetOk 0 body = true)
    (h : machNestedF n senv env dom αs initsE body st = some (some (r, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true := by
  have := readF_good senv (pureFacts_of O) n (Call.nested env dom αs initsE body st)
    ⟨hst, hE, hd, hb⟩ (r, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem machChainF_post (O : OpenFacts senv) {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machChainF n senv env e st = some (some (ws, v, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size v = true := by
  have := readF_good senv (pureFacts_of O) n (Call.chain env e st) ⟨hst, hE, hl⟩ (ws, v, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem machLoopBodyF_post (O : OpenFacts senv) {n : Nat} {base : Nat} {env : List MachVal}
    {e : Lean.Expr} {st st' : MachRead} (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 e = true) (h : machLoopBodyF n senv base env e st = some (some st')) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size :=
  readF_good senv (pureFacts_of O) n (Call.loopBody base env e st) ⟨hst, hE, hl⟩ st' h

theorem machLoopRootF_post (O : OpenFacts senv) {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} {mv : MachVal} (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 e = true) (h : machLoopRootF n senv env e st = some (some (mv, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ MvOk st'.lets.size mv := by
  have := readF_good senv (pureFacts_of O) n (Call.loopRoot env e st) ⟨hst, hE, hl⟩ (mv, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **The `Alias` premise of `machBindLetAlias_noAlias`, at its call site**: the value `machLoopBody`
hands to `machBindLetAlias` is the result of `machConv` on a `let` value; if it is a `_machLet j`
placeholder, `j` is below the size of the table it was read against. -/
theorem alias_premise_of_conv (O : OpenFacts senv) {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st st1 : MachRead} {v' : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machConvF n senv env d e st = some (some (v', st1))) :
    ∀ j, v' = machLet j → j < st1.lets.size :=
  alias_premise rfl (machConvF_post O hst hE hl h).2.2

/-- **Start of a `circuit do` read** (empty state): the output `let` table is alias-free and the returned
placeholder is in range. -/
theorem machConvF_init (O : OpenFacts senv) {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st' : MachRead} {r : Lean.Expr} (hE : EnvOk 0 env) (hl : LetOk 0 e = true)
    (h : machConvF n senv env d e ({} : MachRead) = some (some (r, st'))) :
    NoLetAlias st'.lets ∧ ∀ j, r = machLet j → j < st'.lets.size := by
  have := machConvF_post O rdOk_init (st := ({} : MachRead)) hE hl h
  exact ⟨this.1.1, alias_premise rfl this.2.2⟩

theorem machChainF_init (O : OpenFacts senv) {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hE : EnvOk 0 env)
    (hl : LetOk 0 e = true)
    (h : machChainF n senv env e ({} : MachRead) = some (some (ws, v, st'))) :
    NoLetAlias st'.lets ∧ ∀ j, v = machLet j → j < st'.lets.size := by
  have := machChainF_post O rdOk_init (st := ({} : MachRead)) hE hl h
  exact ⟨this.1.1, alias_premise rfl this.2.2⟩

/-! ## Twin → real: OPEN -/

/-- The real `partial` readers as an `OldFns` tuple. -/
def realFns (senv : StructEnv) : OldFns where
  conv := machConv senv
  nested := machNested senv
  inst := machInstance senv
  instS := machInstanceS senv
  chain := machChain senv
  loopBody := machLoopBody senv
  loopRoot := machLoopRoot senv

/-- **OPEN (O1 coverage + O2 transcription fidelity)**: every answer of the tuple `G` (success or refusal)
is the answer of the twin at some fuel. Nothing in this repository proves it for `realFns senv`: the
`partial def`s are opaque constants (`docs/parallel/R-reader-coverage.md` §5). -/
def TwinCover (senv : StructEnv) (G : OldFns) : Prop :=
  ∀ (c : Call) (r : RB c), G.app c = r → ∃ n, readF senv n c = some r

/-- CONDITIONAL on `TwinCover`: the joint invariant for a tuple whose answers the twin covers (for the real
reader: `G := realFns senv`). Not a theorem about `machConv` unless `TwinCover senv (realFns senv)` is proved. -/
theorem real_conv_post (O : OpenFacts senv) {G : OldFns} (hcov : TwinCover senv G)
    {env : List MachVal} {d : Nat} {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr}
    (hst : RdOk st) (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : G.conv env d e st = some (r, st')) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true := by
  obtain ⟨n, hn⟩ := hcov (Call.conv env d e st) (some (r, st')) h
  exact machConvF_post O hst hE hl hn

end Tools.ShippingLetsReaderInv
