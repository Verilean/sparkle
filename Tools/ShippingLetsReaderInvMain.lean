import Tools.ShippingLetsReaderInvPure
import Tools.ShippingLetsReaderInvPure2
import Tools.ShippingReaderFuelOldEq

/-! # Unit LC3 (main): the joint invariant of the reader twin, its consequences, and what stays OPEN

BUILT: lc3k exit 0 (Tools.ShippingLetsReaderInvMain); audit lc3l exit 0 (ChildVertAuditTest; axioms propext,
Classical.choice, Quot.sound only).
No `sorry`, no axiom, no `native_decide`.

## What is PROVED (about the fuel TWIN `readF`, for every fuel)

`machConvF_post` / `machChainF_post` / `machLoopBodyF_post` / `machLoopRootF_post` / `machNestedF_post`:
from an ENTRY condition — a state with `RdOk` (alias-free `let` table, range-closed kept expressions), an
environment in range of that state's table (`EnvOk`), an input expression mentioning no `_machLet`
placeholder (`LetOk 0`); for the empty initial state `rdOk_init` — every answer of the twin that is a SUCCESS
(`some (some _)`) has (i) `NoLetAlias` of the output `let` table, (ii) a table that did not shrink,
(iii) the returned expression in range of the OUTPUT table. A fuel-EXHAUSTED run (`none`) and a refusal
(`some none`) are not successes and the theorems say nothing about them.
`alias_premise_of_conv` turns (iii) into the `Alias` premise of `machBindLetAlias_noAlias`
(`Tools/ShippingLetsAliasInv.lean`) at the `machLoopBody` call site; the `machBindLetAlias` step is covered
inside the induction (`Tools/ShippingLetsReaderInv.lean`, `loopLet_facts`).

## PREMISES — each named, none an axiom (status / use)

| premise | status | used by |
|---|---|---|
| `RootFloatRange` | NOT PROVED (`rootFloat` is a `partial def`) | the `.letE` arms of `machConv`, `machChain` |
| `LiftRange` | NOT PROVED (`liftLooseBVars` is `extern`) | the same two arms |
| `Inst1Range` | NOT PROVED (`instantiate1` is `extern`) | `machInstanceS` (result type) |
| `SigTyRange senv` | NOT PROVED — ENVIRONMENT INPUT CONDITION (types in `senv.instS` mention no `_machLet`); to be derived from the real `structEnv env` | `machInstanceS` |
| `BundleIotaRange` | NOT PROVED (total function, nested name/array-literal case split not done) | the `.app` arm of `machConv` |
| `LetOk 0 e` | INPUT condition, NOT proved from a declaration body | every call |
| `EnvOk` of the start environment | INPUT condition | every call |

PROVED extractors (`…InvPure.lean`, `…InvPure2.lean`): `regView?`, `machRunApp?`, `machInstCall?`,
`machInstCallS?`, `memCall?`, `loopView?`, `machLetTail`, `machLoopRegs`, `machProjIota`.

## OPEN (stated, not proved)

* TWIN → REAL: `TwinCoverAt senv G S` for `G := realFns senv` — a SUCCESSFUL real answer of a call in `S`
  is some fuel's twin answer (O1 coverage + O2 transcription fidelity, `docs/parallel/R-reader-coverage.md`).
  `real_conv_post` is CONDITIONAL on it. A twin result is not a result about the real `partial` reader.
* The loose-bvar condition on `let` values (`machClose_bvar` bounds only the root bvar; `LetOk` counts a
  loose `bvar` as in range).
* The deep range of the values SAVED in the `let` table (`RdOk` records `NoLetAlias` of the head values only).
* The `Expr` → typed `letFields` / `quote` link (proof-generation side). -/
namespace Tools.ShippingLetsReaderInv
open Lean Sparkle.Compiler.Elab
open Tools.ShippingLetsAliasInv Tools.ShippingReaderFuel

/-- PREMISE (not proved): `rootFloat` (a `partial def`) invents no `_machLet j` placeholder. -/
def RootFloatRange : Prop :=
  ∀ n v, LetOk n v = true → LetOk n (Sparkle.Compiler.MachRawSurface.rootFloat v) = true

/-- PREMISE (not proved): `Expr.liftLooseBVars` (extern) invents no `_machLet j` placeholder. -/
def LiftRange : Prop :=
  ∀ n e k m, LetOk n e = true → LetOk n (e.liftLooseBVars k m) = true

/-- PREMISE (not proved): `Expr.instantiate1` (extern) invents no `_machLet j` placeholder. -/
def Inst1Range : Prop :=
  ∀ n b a, LetOk n b = true → LetOk n a = true → LetOk n (b.instantiate1 a) = true

/-- ENVIRONMENT INPUT CONDITION (not proved, to be derived from the real `structEnv env`): the result types
stored in `senv.instS` mention no `_machLet` placeholder. -/
def SigTyRange (senv : StructEnv) : Prop :=
  ∀ c kinds ty, senv.instS c = some (kinds, ty) → ∀ n, LetOk n ty = true

/-- PREMISE (not proved; a total function, its nested name/array-literal `match` was not case-split):
`bundleIota` invents no `_machLet j` placeholder. -/
def BundleIotaRange : Prop :=
  ∀ n e, LetOk n e = true → LetOk n (Sparkle.Compiler.MachRawSurface.bundleIota e) = true

/-- The record the induction uses (`PureFacts`): the five premises above and the PROVED extractor lemmas.
Used inside the proofs below; the FINAL theorems take the five premises individually. -/
theorem pureFacts_of {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange)
    (hinst1 : Inst1Range) (hsig : SigTyRange senv) (hbundle : BundleIotaRange) :
    PureFacts senv where
  rootFloat := hroot
  lift := hlift
  inst1 := hinst1
  sigTy := hsig
  bundleIota := hbundle
  projIota := fun n e he => projIota_ok senv.proj n e he
  regView := fun n fn args d α i x hall h => regView_ok n fn args d α i x hall h
  runApp := fun n e dom αs inits body he h => runApp_ok n e dom αs inits body he h
  instCall := fun n e c kinds res args he h => instCall_ok senv n e c kinds res args he h
  instCallS := fun n e c kinds ty args he h => instCallS_ok senv n e c kinds ty args he h
  memCall := fun n e combo aw dw dom ops he h => memCall_ok _ n e combo aw dw dom ops he h
  loopView := fun n e dom body he h => loopView_ok n e dom body he h
  letTail := fun n e he => letTail_ok n e he
  loopRegs := fun n e regs he h => loopRegs_ok n e regs he h

/-! ## The twin's answers -/

variable {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range)
  (hsig : SigTyRange senv) (hbundle : BundleIotaRange)
include hroot hlift hinst1 hsig hbundle

theorem machConvF_post {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machConvF n senv env d e st = some (some (r, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true := by
  have := readF_good senv (pureFacts_of hroot hlift hinst1 hsig hbundle) n (Call.conv env d e st) ⟨hst, hE, hl⟩ (r, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem machNestedF_post {n : Nat} {env : List MachVal}
    {dom αs initsE body : Lean.Expr} {st st' : MachRead} {r : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hd : LetOk 0 dom = true) (hb : LetOk 0 body = true)
    (h : machNestedF n senv env dom αs initsE body st = some (some (r, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true := by
  have := readF_good senv (pureFacts_of hroot hlift hinst1 hsig hbundle) n (Call.nested env dom αs initsE body st)
    ⟨hst, hE, hd, hb⟩ (r, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem machChainF_post {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machChainF n senv env e st = some (some (ws, v, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size v = true := by
  have := readF_good senv (pureFacts_of hroot hlift hinst1 hsig hbundle) n (Call.chain env e st) ⟨hst, hE, hl⟩ (ws, v, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem machLoopBodyF_post {n : Nat} {base : Nat} {env : List MachVal}
    {e : Lean.Expr} {st st' : MachRead} (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 e = true) (h : machLoopBodyF n senv base env e st = some (some st')) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size :=
  readF_good senv (pureFacts_of hroot hlift hinst1 hsig hbundle) n (Call.loopBody base env e st) ⟨hst, hE, hl⟩ st' h

theorem machLoopRootF_post {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} {mv : MachVal} (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 e = true) (h : machLoopRootF n senv env e st = some (some (mv, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ MvOk st'.lets.size mv := by
  have := readF_good senv (pureFacts_of hroot hlift hinst1 hsig hbundle) n (Call.loopRoot env e st) ⟨hst, hE, hl⟩ (mv, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **The `Alias` premise of `machBindLetAlias_noAlias`, at its call site**: the value `machLoopBody`
hands to `machBindLetAlias` is the result of `machConv` on a `let` value; if it is a `_machLet j`
placeholder, `j` is below the size of the table it was read against. -/
theorem alias_premise_of_conv {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st st1 : MachRead} {v' : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machConvF n senv env d e st = some (some (v', st1))) :
    ∀ j, v' = machLet j → j < st1.lets.size :=
  alias_premise rfl (machConvF_post hroot hlift hinst1 hsig hbundle hst hE hl h).2.2

/-- **Start of a `circuit do` read** (empty state): the output `let` table is alias-free and the returned
placeholder is in range. -/
theorem machConvF_init {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st' : MachRead} {r : Lean.Expr} (hE : EnvOk 0 env) (hl : LetOk 0 e = true)
    (h : machConvF n senv env d e ({} : MachRead) = some (some (r, st'))) :
    NoLetAlias st'.lets ∧ ∀ j, r = machLet j → j < st'.lets.size := by
  have := machConvF_post hroot hlift hinst1 hsig hbundle rdOk_init (st := ({} : MachRead)) hE hl h
  exact ⟨this.1.1, alias_premise rfl this.2.2⟩

theorem machChainF_init {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hE : EnvOk 0 env)
    (hl : LetOk 0 e = true)
    (h : machChainF n senv env e ({} : MachRead) = some (some (ws, v, st'))) :
    NoLetAlias st'.lets ∧ ∀ j, v = machLet j → j < st'.lets.size := by
  have := machChainF_post hroot hlift hinst1 hsig hbundle rdOk_init (st := ({} : MachRead)) hE hl h
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

/-- **OPEN (O1 coverage + O2 transcription fidelity), for SUCCESSFUL answers of the calls in `S` only**: a
successful answer of the tuple `G` to a call in `S` is the answer of the twin at some fuel. `S` is the set of
calls whose result is used (for one top-level read: that single call); refusals and non-terminating calls are
not covered (and not needed: the invariant speaks about successes only). Nothing in this repository proves it
for `realFns senv`: the `partial def`s are opaque constants (`docs/parallel/R-reader-coverage.md` §5). -/
def TwinCoverAt (senv : StructEnv) (G : OldFns) (S : Call → Prop) : Prop :=
  ∀ c, S c → ∀ v : c.Res, G.app c = some v → ∃ n, readF senv n c = some (some v)

/-- CONDITIONAL on `TwinCoverAt`: the joint invariant for a tuple whose successful answer to this call the
twin covers (for the real reader: `G := realFns senv`). Not a result about `machConv` unless
`TwinCoverAt senv (realFns senv) S` is proved. -/
theorem real_conv_post {G : OldFns} {S : Call → Prop} (hcov : TwinCoverAt senv G S)
    {env : List MachVal} {d : Nat} {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr}
    (hS : S (Call.conv env d e st))
    (hst : RdOk st) (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : G.conv env d e st = some (r, st')) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true := by
  obtain ⟨n, hn⟩ := hcov (Call.conv env d e st) hS (r, st') h
  exact machConvF_post hroot hlift hinst1 hsig hbundle hst hE hl hn

end Tools.ShippingLetsReaderInv
