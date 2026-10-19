import Tools.ShippingCallWidthsStructLink
import Tools.ShippingInstSignature
import Tools.ShippingReaderResultKind

/-! # `StructRes` decomposed: the syntactic parts proved, the rest named

BUILT as written (worker O-RES, from poc ef8ff162; integration run ig4 exit 0; axioms run axo standard).
No `sorry`, no new axiom, no `native_decide`. New file; nothing existing is
changed.

## What this replaces

`Tools.ShippingCallWidthsStructLink.StructResAt` (built) is ONE opaque
premise per structure callee `c`: for every call the parent reads
(`senvP.instS c = some (kinds, ty)`, `instRes ty args = some resTy`,
`machOuts? senvP resTy = some (some ctor, fields)`) and the callee's entry
constant `dE` of every run (`entryConst … ci … = .defnInfo dE`), every field
of `fields` is in `declOuts? (structEnv envR) dE.type`.
Its header named three sufficient facts: (i) type/head preservation from the
declared type to the instantiated call type (`instRes`) and to the entry
constant's type (`userInliner` on the unfolding branch), (ii)
`machTupleKinds? dE.type = none`, (iii) agreement of the two structure tables.

`structResAt_of_parts` derives `StructResAt mref cref (structEnv envP) c`
from the premises below (a conditional decomposition). Everything else is PROVED here from the text of
`machOuts?`, `machTupleKinds?`, `declOuts?`, `instRes`, `instSignatureS?`,
`entryConst`, `inlinedConst`:

* the reader side (`machOuts?`) depends on the structure table only at the
  HEAD constant of the result body (`outs_congr`);
* `instRes` carries the callee's output list and its head constant through
  every substitution step (`instRes_outs`, `instRes_head`), GIVEN the NEW
  premise `InstSubst` about `Expr.instantiate1`;
* (ii) is not needed at all: a tuple result `Signal dom (A × …)` has head
  `Signal`, and a `Signal`-headed instantiated type never yields a structure
  field list once the parent table has no `Signal` entry
  (`outs_signal_head`) — so the tuple branch of `declOuts?` makes StructRes
  hold VACUOUSLY instead of being assumed away;
* the pair case (`Prod a b`, `out_0`/`out_1`) is covered by the same
  forward argument (no separate premise);
* on the NON-unfolding branch of `entryConst`, `dE.type` is the declared
  type `ty` the parent's table holds (`instSignatureS?_some` + `DR`).

## Status: CONDITIONAL DECOMPOSITION, not a discharge (reviewer 2026-10-19)

`structResAt_of_parts` proves `StructResAt` FROM the premises below; it does not establish `StructResAt` for any
real run. Two of the premises (`InstSubst`, `NS`) are NEW semantic premises introduced by this decomposition;
they are NOT in any allowed-premise/trust list and are not claimed established.

### Dependency graph

Before: `callWidthsStrict_of_linksFMS` / `childLinkStruct_real` ← `StructResAt c` (one premise, opaque).

After:

```
childLinkStruct_real_of_parts ← structResAt_of_parts ← InstSubst          (NEW; about Expr.instantiate1, all senv/b/a)
                                                    ← NS                  (NEW; userStructure? envP ``Signal = none)
                                                    ← DeclTypeReadAt envP c   (replaces part of (i))
                                                    ← FieldsAt envP c         (replaces (iii), one head constant)
                                                    ← P5SAt c                 (replaces (i) on the unfolding branch)
```

| premise | status |
|---|---|
| (ii) `machTupleKinds? dE.type = none` | ELIMINATED: proved unnecessary (tuple branch vacuous via `outs_signal_head`, which itself needs `NS`) |
| (i) head preservation through `instRes` | REPLACED by `InstSubst`, a NEW premise: one environment-free, call-free statement about `Expr.instantiate1` (`@[extern "lean_expr_instantiate1"] opaque` in v4.32.1). No equation or bridge for it is established in this repository; it is expected of de Bruijn substitution (case analysis in its docstring) but that expectation is NOT used as evidence. Candidate routes, not done: a proved executable substitution model plus an explicit runtime-agreement boundary, or a restricted case from existing library lemmas |
| (i), non-unfolding branch of `entryConst` | REPLACED by `DeclTypeReadAt envP c` (DR) |
| (i), unfolding branch (`userInliner`) | REPLACED by `P5SAt c` (output lists only; same gap as `P5At`) |
| (iii) structure tables agree | REPLACED by `FieldsAt envP c` (FA), at the head constant only |
| `NS` | NEW premise, decidable on a concrete environment |

DR and FA quantify over EVERY run (`RunsTo (getConstInfo c) …`, `RunsTo getEnv …` from any world) and an arbitrary
`envP`. They are NOT discharged: discharging them needs captured-environment invariants for the ACTUAL parent and
child runs (the environment the parent's reader used and the one the child's run reads), not a global
immutability assumption. Open.

(Built as written; the worker's unsure-spot list is obsolete.)
-/
namespace Tools.ShippingCallWidthsStructRes
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv
open Tools.ShippingCallWidthsStrict Tools.ShippingCallWidthsDeclared Tools.ShippingCallWidthsEntry
open Tools.ShippingCallWidthsChildReal
open Tools.ShippingCallWidthsEntryFM
open Tools.ShippingCallWidthsStructLink
open Tools.ShippingMachineShapeUnfold (declOuts?)
open Tools.ShippingReaderFuelProv (StructOrigin)
open Tools.ShippingReaderFuel (instRes)
open Tools.ShippingReaderResultKind (outsOfKind)
open Tools.ShippingInstSignature (instSignatureS?_some)

/-! ## The result body of a type -/

/-- The body of a `∀` telescope (the type itself when it is not a `∀`). -/
def resBody : Lean.Expr → Lean.Expr
  | .forallE _ _ b _ => resBody b
  | e => e

theorem resBody_not_forall (e : Lean.Expr) :
    ∀ (n : Name) (d b : Lean.Expr) (bi : BinderInfo), resBody e ≠ .forallE n d b bi := by
  induction e with
  | forallE _ _ b _ _ ih => exact ih
  | _ =>
    intro n d b bi h
    first
      | cases h
      | exact Lean.Expr.noConfusion h
      | simp [resBody] at h

theorem machOuts?_forall (senv : StructEnv) (n : Name) (d b : Lean.Expr) (bi : BinderInfo) :
    machOuts? senv (.forallE n d b bi) = machOuts? senv b := by
  first | rfl | simp [machOuts?]

theorem machTupleKinds?_forall (n : Name) (d b : Lean.Expr) (bi : BinderInfo) :
    machTupleKinds? (.forallE n d b bi) = machTupleKinds? b := by
  first | rfl | simp [machTupleKinds?]

/-- `machOuts?` reads the result body. -/
theorem outs_body (senv : StructEnv) (e : Lean.Expr) :
    machOuts? senv e = machOuts? senv (resBody e) := by
  induction e with
  | forallE n d b bi _ ih =>
    rw [machOuts?_forall]
    exact ih
  | _ => rfl

/-- `machTupleKinds?` reads the result body. -/
theorem tuple_body (e : Lean.Expr) : machTupleKinds? e = machTupleKinds? (resBody e) := by
  induction e with
  | forallE n d b bi _ ih =>
    rw [machTupleKinds?_forall]
    exact ih
  | _ => rfl

/-! ## `machOuts?` on a body: the structure table is read at the head only -/

/-- Off the `∀` and `Prod` arms, `machOuts?` is its last alternative. -/
theorem outs_nonprod (senv : StructEnv) {e : Lean.Expr}
    (hnf : ∀ (n : Name) (d b : Lean.Expr) (bi : BinderInfo), e ≠ .forallE n d b bi)
    (hnp : ¬ ∃ (us : List Lean.Level) (a b : Lean.Expr),
      e = .app (.app (.const ``Prod us) a) b) :
    machOuts? senv e = outsOfKind senv e := by
  unfold machOuts?
  split
  · exfalso
    first
      | exact hnf _ _ _ _ rfl
      | exact hnf _ _ _ _ (by assumption)
      | simp_all
  · exfalso
    first
      | exact hnp ⟨_, _, _, rfl⟩
      | exact hnp ⟨_, _, _, by assumption⟩
      | simp_all
  · first
      | rfl
      | (unfold outsOfKind; rfl)
      | simp [outsOfKind]

/-- The last alternative reads the table only at the head constant. -/
theorem outsOfKind_congr {senv senv' : StructEnv} {e : Lean.Expr}
    (hf : ∀ (s : Name) (ls : List Lean.Level), e.getAppFn = .const s ls →
      senv.fields s = senv'.fields s) :
    outsOfKind senv e = outsOfKind senv' e := by
  unfold outsOfKind
  cases hg : e.getAppFn
  case const s ls =>
    first
      | (simp only [hf s ls hg]; done)
      | (simp only []; rw [hf s ls hg])
      | (simp [hf s ls hg]; done)
  all_goals rfl

/-- **The structure table is read at the head of the result body only.** -/
theorem outs_congr {senv senv' : StructEnv} (e : Lean.Expr)
    (hf : ∀ (s : Name) (ls : List Lean.Level), (resBody e).getAppFn = .const s ls →
      senv.fields s = senv'.fields s) :
    machOuts? senv e = machOuts? senv' e := by
  rw [outs_body senv e, outs_body senv' e]
  by_cases hp : ∃ (us : List Lean.Level) (a b : Lean.Expr),
      resBody e = .app (.app (.const ``Prod us) a) b
  · obtain ⟨us, a, b, hp⟩ := hp
    rw [hp]
    first | rfl | simp [machOuts?]
  · rw [outs_nonprod senv (resBody_not_forall e) hp,
      outs_nonprod senv' (resBody_not_forall e) hp]
    exact outsOfKind_congr hf

theorem ne_signal_prod : (``Sparkle.Core.Signal.Signal : Name) ≠ ``Prod := by
  decide

/-- **A `Signal`-headed type never yields a structure field list** once the
table has no `Signal` entry (a Bool / BitVec Signal yields the one port
`out` with no constructor; anything else reads `senv.fields Signal`). -/
theorem outs_signal_head {senv : StructEnv} {e : Lean.Expr} {us : List Lean.Level}
    (NS : senv.fields ``Sparkle.Core.Signal.Signal = none)
    (hh : (resBody e).getAppFn = .const ``Sparkle.Core.Signal.Signal us) :
    ∀ (ctor : Name) (fs : List (String × MixedGateBinder)),
      machOuts? senv e ≠ some (some ctor, fs) := by
  intro ctor fs h
  rw [outs_body _ e] at h
  have hnp : ¬ ∃ (us' : List Lean.Level) (a b : Lean.Expr),
      resBody e = .app (.app (.const ``Prod us') a) b := by
    rintro ⟨us', a, b, hp⟩
    rw [hp] at hh
    have h1 : (Lean.Expr.const ``Prod us' : Lean.Expr) =
        .const ``Sparkle.Core.Signal.Signal us := hh
    injection h1 with h2
    exact ne_signal_prod h2.symm
  rw [outs_nonprod senv (resBody_not_forall e) hnp] at h
  cases hk : mixedGateBinderKind? (resBody e) with
  | none => simp [outsOfKind, hk, hh, NS] at h
  | some k => cases k <;> simp [outsOfKind, hk, hh, NS] at h

/-- A tuple result (`machTupleKinds?`) has head `Signal`. -/
theorem tuple_head {e : Lean.Expr} {ks : List MixedGateBinder}
    (hnf : ∀ (n : Name) (d b : Lean.Expr) (bi : BinderInfo), e ≠ .forallE n d b bi)
    (h : machTupleKinds? e = some ks) :
    ∃ us : List Lean.Level, e.getAppFn = .const ``Sparkle.Core.Signal.Signal us := by
  unfold machTupleKinds? at h
  split at h
  · exfalso
    first
      | exact hnf _ _ _ _ rfl
      | exact hnf _ _ _ _ (by assumption)
      | simp_all
  · first
      | exact ⟨_, rfl⟩
      | (subst_vars; exact ⟨_, rfl⟩)
      | simp_all [Lean.Expr.getAppFn]
  · first
      | cases h
      | simp at h

/-! ## A NEW premise about the extern substitution -/

/-- **The substitution premise** (NEW; environment-free, call-free; not
established). `instRes` substitutes the call's arguments with
`Expr.instantiate1`, an `@[extern "lean_expr_instantiate1"] opaque`; no
equation or bridge for it is established in this repository. Both clauses are
EXPECTED of de Bruijn substitution (which replaces loose `bvar`s only and keeps
every other node, constants and levels included) — an expectation, not
evidence:

* `outs` — a body read by `machOuts?` is a `Prod` of two non-domain hardware
  Signals, a `Signal dom Bool` / `Signal dom (BitVec w)` with `w` a literal
  (`canonicalNatLitValue?` accepts closed forms only), or has a constant
  head `s` with `senv.fields s = some _`; then `s ≠ Signal` by the guard,
  so the substituted body keeps head and arity and cannot become a
  Bool/BitVec Signal. The guard is NEEDED: without it,
  `∀ x, Signal d (BitVec #0)` would change reading under substitution.
* `head` — the `∀` spine and the head constant of the body are kept. -/
structure InstSubst : Prop where
  outs : ∀ (senv : StructEnv), senv.fields ``Sparkle.Core.Signal.Signal = none →
    ∀ (b a : Lean.Expr) (o : Option Name × List (String × MixedGateBinder)),
      machOuts? senv b = some o → machOuts? senv (b.instantiate1 a) = some o
  head : ∀ (b a : Lean.Expr) (s : Name) (ls : List Lean.Level),
    (resBody b).getAppFn = .const s ls → (resBody (b.instantiate1 a)).getAppFn = .const s ls

theorem instRes_nil (e : Lean.Expr) : instRes e [] = some e := by
  first
    | rfl
    | (cases e <;> rfl)
    | simp [instRes]

theorem instRes_cons_forall (n : Name) (d b : Lean.Expr) (bi : BinderInfo)
    (a : Lean.Expr) (as : List Lean.Expr) :
    instRes (.forallE n d b bi) (a :: as) = instRes (b.instantiate1 a) as := by
  first | rfl | simp [instRes]

/-- **`instRes` keeps an output list that reads** (forward). -/
theorem instRes_outs {senv : StructEnv} (IS : InstSubst)
    (NS : senv.fields ``Sparkle.Core.Signal.Signal = none) :
    ∀ (args : List Lean.Expr) (ty resTy : Lean.Expr)
      (o : Option Name × List (String × MixedGateBinder)),
      machOuts? senv ty = some o → instRes ty args = some resTy → machOuts? senv resTy = some o
  | [], ty, resTy, o, hO, hR => by
    rw [instRes_nil] at hR
    cases hR
    exact hO
  | a :: as, ty, resTy, o, hO, hR => by
    cases ty with
    | forallE n d b bi =>
      rw [machOuts?_forall] at hO
      rw [instRes_cons_forall] at hR
      exact instRes_outs IS NS as (b.instantiate1 a) resTy o (IS.outs senv NS b a o hO) hR
    | _ =>
      exfalso
      first
        | exact Option.noConfusion hR
        | (unfold instRes at hR; simp at hR)
        | simp [instRes] at hR

/-- **`instRes` keeps the head constant of the result body.** -/
theorem instRes_head (IS : InstSubst) :
    ∀ (args : List Lean.Expr) (ty resTy : Lean.Expr) (s : Name) (ls : List Lean.Level),
      (resBody ty).getAppFn = .const s ls → instRes ty args = some resTy →
      (resBody resTy).getAppFn = .const s ls
  | [], ty, resTy, s, ls, hh, hR => by
    rw [instRes_nil] at hR
    cases hR
    exact hh
  | a :: as, ty, resTy, s, ls, hh, hR => by
    cases ty with
    | forallE n d b bi =>
      have hh' : (resBody b).getAppFn = .const s ls := hh
      rw [instRes_cons_forall] at hR
      exact instRes_head IS as (b.instantiate1 a) resTy s ls (IS.head b a s ls hh') hR
    | _ =>
      exfalso
      first
        | exact Option.noConfusion hR
        | (unfold instRes at hR; simp at hR)
        | simp [instRes] at hR

/-! ## `StructRes` from the declared type (pure) -/

/-- **`StructRes` from the callee's DECLARED output list.** Premises: the
substitution fact, no `Signal` entry in the parent's table, the two tables
agree at the head of the declared result body, and the entry constant's
output list (when it reads) is the declared type's. No `machTupleKinds?`
premise: the tuple branch is vacuous. -/
theorem structRes_of_declOuts {senvP senvC : StructEnv} {c : Name} {dE : DefinitionVal}
    (IS : InstSubst) (NS : senvP.fields ``Sparkle.Core.Signal.Signal = none)
    (hF : ∀ (kinds : List MixedGateBinder) (ty : Lean.Expr), senvP.instS c = some (kinds, ty) →
      ∀ (s : Name) (ls : List Lean.Level), (resBody ty).getAppFn = .const s ls →
        senvP.fields s = senvC.fields s)
    (hD : ∀ (kinds : List MixedGateBinder) (ty : Lean.Expr), senvP.instS c = some (kinds, ty) →
      ∀ o, declOuts? senvC dE.type = some o → declOuts? senvC ty = some o) :
    StructRes senvP c senvC dE := by
  intro kinds ty args resTy ctor fields hI hR hO ctor? outs hd p hp
  have hd' := hD kinds ty hI _ hd
  unfold declOuts? at hd'
  generalize hk : machTupleKinds? ty = tup at hd'
  cases tup with
  | none =>
    have hC : machOuts? senvC ty = some (ctor?, outs) := hd'
    have hP : machOuts? senvP ty = some (ctor?, outs) :=
      (outs_congr ty (hF kinds ty hI)).trans hC
    have hRes := instRes_outs IS NS args ty resTy _ hP hR
    rw [hRes] at hO
    have h2 : outs = fields := (Prod.mk.inj (Option.some.inj hO)).2
    rw [h2]
    exact hp
  | some ks =>
    exfalso
    rw [tuple_body ty] at hk
    obtain ⟨us, hh⟩ := tuple_head (resBody_not_forall ty) hk
    exact outs_signal_head NS (instRes_head IS args ty resTy _ _ hh hR) ctor fields hO

/-! ## At the callee's real runs -/

section Defs
variable (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)

/-- **Environment-read consistency** (same status as `ResDeclAt`): the type
of what `getConstInfo c` returns is the type of `c` in `env`. -/
def DeclTypeReadAt (env : Environment) (c : Name) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w1 : Void IO.RealWorld) (ci : ConstantInfo)
    (w2 : Void IO.RealWorld),
    RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 →
    ∀ ci' : ConstantInfo, env.find? c = some ci' → ci.type = ci'.type

/-- **(iii), at one name**: the parent's and the callee run's structure
tables agree at the head constant of the callee's declared result body. -/
def FieldsAt (env : Environment) (c : Name) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w5 : Void IO.RealWorld) (envR : Environment)
    (w6 : Void IO.RealWorld),
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    ∀ (kinds : List MixedGateBinder) (ty : Lean.Expr), (structEnv env).instS c = some (kinds, ty) →
      ∀ (s : Name) (ls : List Lean.Level), (resBody ty).getAppFn = .const s ls →
        userStructure? env s = userStructure? envR s

/-- **P5 for output lists, unfolding branch only**: WHEN the entry compiles
the unfolding of `c`, an output list the inlined type reads is the declared
type's. Weaker than `userInliner envR dD.type = dD.type`. -/
def P5SAt (c : Name) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w1 : Void IO.RealWorld) (ci : ConstantInfo)
    (w2 w5 : Void IO.RealWorld) (envR : Environment) (w6 : Void IO.RealWorld)
    (dD : DefinitionVal),
    RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    ci = .defnInfo dD →
    entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ≠ ci →
    ∀ o, declOuts? (structEnv envR) (userInliner envR dD.type) = some o →
      declOuts? (structEnv envR) dD.type = some o

end Defs

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The type of a definition's `ConstantInfo` is the definition's type. -/
theorem defn_type (d : DefinitionVal) : (ConstantInfo.defnInfo d).type = d.type := by
  first
    | rfl
    | (cases d; rfl)
    | simp [ConstantInfo.type, ConstantInfo.toConstantVal]

/-- **`StructResAt` from its parts.** `StructResAt` of the parent's table
`structEnv envP` at callee `c`, from: `InstSubst` (the extern fact), `NS`
(no `Signal` structure), `DR` (environment-read consistency), `FA` (table
agreement at the head constant), `P5S` (unfolding branch only). -/
theorem structResAt_of_parts {envP : Environment} {c : Name}
    (IS : InstSubst) (NS : userStructure? envP ``Sparkle.Core.Signal.Signal = none)
    (DR : DeclTypeReadAt mref cref envP c) (FA : FieldsAt mref cref envP c)
    (P5S : P5SAt mref cref c) :
    StructResAt mref cref (structEnv envP) c := by
  intro mctx' cctx' w1 ci w2 w5 envR w6 dE get henv hE
  refine structRes_of_declOuts (senvP := structEnv envP) (senvC := structEnv envR) (c := c)
    (dE := dE) IS NS ?_ ?_
  · intro kinds ty hI s ls hh
    exact FA mctx' cctx' w5 envR w6 henv kinds ty hI s ls hh
  · intro kinds ty hI o hd
    have hI' : instSignatureS? envP c = some (kinds, ty) := hI
    obtain ⟨_, ci', hfind, _, hty, _⟩ := instSignatureS?_some hI'
    have hct : ci.type = ci'.type := DR mctx' cctx' w1 ci w2 get ci' hfind
    by_cases hne : entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR) = ci
    · rw [hne] at hE
      have hT : ty = dE.type := by
        rw [hty, ← hct, hE, defn_type]
      rw [hT]
      exact hd
    · rcases entryConst_cases ci (instancePredicate envR) (userInliner envR) (structEnv envR)
        with h | h
      · exact absurd h hne
      · rw [h] at hE
        obtain ⟨dD, hciD, hdty⟩ := inlinedConst_defn hE
        rw [hdty] at hd
        have hT : ty = dD.type := by
          rw [hty, ← hct, hciD, defn_type]
        rw [hT]
        exact P5S mctx' cctx' w1 ci w2 w5 envR w6 dD get henv hciD hne o hd

/-- **`ChildLinkStruct` for the child really compiled, from the parts**
(`childLinkStruct_real` with `StructResAt` replaced by its parts). -/
theorem childLinkStruct_real_of_parts {kidOuts : Nat → List OutField} {k : Nat}
    {envP : Environment} {c : Name} {r : MixedGateBinder} {nm : String}
    {sc : MachineShape} {y : Res}
    (entry : MachineDefines mctx mref cctx cref c sc)
    (IS : InstSubst) (NS : userStructure? envP ``Sparkle.Core.Signal.Signal = none)
    (DR : DeclTypeReadAt mref cref envP c) (FA : FieldsAt mref cref envP c)
    (P5S : P5SAt mref cref c) (hy : RealChild mref cref c y)
    (hS : StructOrigin (structEnv envP) c r nm) (hkid : kidOuts k = sc.layout.outs) :
    ChildLinkStruct kidOuts k nm r :=
  childLinkStruct_real entry (structResAt_of_parts IS NS DR FA P5S) hy hS hkid

end Tools.ShippingCallWidthsStructRes
