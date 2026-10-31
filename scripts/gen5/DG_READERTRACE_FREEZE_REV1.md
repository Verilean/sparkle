# DG-READERTRACE freeze rev1 — corrections R1 / R2 and typing of named helpers (Issue sparkle-gen5-dg-readertrace)

**FOR REVIEW.** Committed together with the U-R1 independent-part Lean (`521b3e8a`); that Lean built in the Pod (`rt2v-1fd3e5d9`, exit 0, 722 jobs, at `1fd3e5d9`). Addendum to `scripts/gen5/DG_READERTRACE_FREEZE.md` (rev0, reviewer `changes_requested`). Sections of rev0 not mentioned here are unchanged and are still **not approved** (in particular §3 arms, §5 `machineShapeF_reach`, U-R4 / U-R5 are not re-frozen here).
Base `2b83c234`. No guarantee, law, TRUSTED boundary, FG scope, compiler or shared definition is changed; `GenWF` is not strengthened; no FG premise is added. Conditional results are INTERMEDIATE.
Wording: "not found" = this investigation found no supplier/route, never "impossible". A mutant is a signature/defeq rejection, not a semantic counterexample.

What is already implemented (new file `Tools/ShippingGen5ReaderTrace.lean`, independent of the points below; built SHA is recorded in its header): `phTag, NoPh, BvarLt, NoLoose, EnvPh, DomPh`, `noLoose_zero_le, bvarLt_mono, noPh_letOk`, `inRange_*` helpers,
`reachC_ws / reachC_letv / reachC_slots, envPh_mono, envPh_cons_val`, `bundleSlots_ph`, `convBvar_trace`, `bindLet_reach`. Nothing defined there mentions `CtlPh.groups`, `PhPre.inst` or `PhPre.instS`.

## 0. Change to rev0 §2.1: `DomPh` is a named conjunct

`CtlPh`'s fourth conjunct of rev0 is now the definition `DomPh` (same text), so that `convBvar_trace` depends on `DomPh` only and not on the part of `CtlPh` being revised:

```lean
def DomPh (nDecl : Nat) (st : MachRead) : Prop :=
  ∀ d, st.dom = some d → InRange nDecl st st.lets.size d ∧ NoLoose 0 d
-- CtlPh senv nDecl st := loopWs-clause ∧ bareRegs-clause ∧ nested-clause ∧ DomPh nDecl st ∧ LetsNoLoose st ∧ GroupsPh senv st   (GroupsPh: §2 below, = rev0's last conjunct)
-- convBvar_trace takes (hE : EnvPh nDecl st env) (hD : DomPh nDecl st) in place of (hI : TrInv senv nDecl st):
theorem convBvar_trace {nDecl : Nat} {env : List MachVal} {d j : Nat} {st : MachRead} {r : Lean.Expr × MachRead}
    (hE : EnvPh nDecl st env) (hD : DomPh nDecl st)
    (hb : BvarLt (d + env.length + nDecl) (Lean.Expr.bvar j) = true) (h : convBvar env d j st = some r) :
    r.2 = st ∧ InRange nDecl st st.lets.size r.1 ∧ NoLoose d r.1
```
(`TrInv`-form is recovered by projecting `DomPh` from `CtlPh`.) `NoLoose d v` is **exactly** `∀ b, ¬ LooseOcc d v b`; `LooseOcc` (Cover3) does not descend `letE / mdata / proj`, so `NoLoose` says nothing about loose bvars below those constructors. Outputs of `conv` contain none of them (`mdata`/`proj` are `failO`; `letE` is eliminated by the arm), which is why the weaker predicate suffices for outputs; inputs use `NoPh`/`BvarLt`, which do descend.

## 1. Where the instS / inst origins come from — the caller protocol (R1, R2)

Read: `convStep` arms 5, 6, 7 are the **only** callers of `cInst` / `cInstS` in the seven bodies (`ShippingReaderFuelDefs.lean`; `chainStep`/`loopBodyStep`/`loopRootStep`/`nestedStep` contain no `cInst`/`cInstS` — this investigation grepped `cInst`/`cInstS`, it did not model-check the claim beyond that). Their arguments are:

| arm | call | what the caller has just matched |
|---|---|---|
| 5 | `cInst env c .ord kinds res args st` | `machInstCall? senv (.app f a) = some (c, kinds, res, args)` (`senv.inst c = some (kinds, res)`, `args.length = kinds.length`) |
| 6 | `cInstS env c kinds ty args st` | `machInstCallS? senv (.app f a) = some (c, kinds, ty, args)`, i.e. `senv.instS c = some (kinds, ty)` and `args.length = kinds.length` |
| 7 | `cInst env (memChildName combo aw dw) (.mem combo aw dw) [.domain,.bits aw,.bits dw,.bool,.bits aw] (.bits dw) (dom :: ops) st` | `memCall? … = some (combo, aw, dw, dom, ops)` |

So the origin handed to `instStep` is `.ord` or `.mem …`, **never** `.field _`; and `instSStep` receives exactly the `(kinds, ty)` that `senv.instS c` returns. The rev0 `PhPre` types did not record either fact; the review items are correct.

### 1.1 R2 — `PhPre.inst` input condition (replaces rev0's `.inst` row)

```lean
  | .inst env c org kinds res args st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      (org = InstOrigin.ord ∨
        ∃ cb aw dw, org = InstOrigin.mem cb aw dw ∧
          kinds = [MixedGateBinder.domain, .bits aw, .bits dw, .bool, .bits aw] ∧ res = .bits dw ∧ args.length = 5)
```
(`org = .field _` is excluded by the type.) **Supplier:** `conv_trace` arm 5 (`org := .ord`, left disjunct `rfl`) and arm 7 (`org := .mem combo aw dw`, the `kinds/res` equalities are `rfl` against the literal arguments, `args.length = 5` is `MemCallArity` of rev0 §4). This is a statement about the *call*, proved at the call site from the code of the arm; it is not an FG premise and not a hypothesis of `readF_traceGood`.
**Consequence for `CtlPh.groups`:** an `instStep` miss pushes `org ∈ {ord, mem}`, so the `GroupsPh` hypothesis (which only constrains rows whose origin is `.field 0`) is untouched for the new row (vacuous), and old rows keep their index and values (`insts`/`instOrigins` are append-only; `k + fields.length ≤ insts.size` is monotone). rev0's sentence "new origin is ord/mem" is now a consequence of the input condition above, not of the old `PhPre.inst` type.

### 1.2 R1 — `PhPre.instS` ties `c` to `(kinds, ty)` (replaces rev0's `.instS` row)

```lean
  | .instS env c kinds ty args st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      senv.instS c = some (kinds, ty) ∧ args.length = kinds.length ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      NoPh ty = true ∧ BvarLt (env.length + nDecl) ty = true
```
The group clause (unchanged text from rev0, now named):

```lean
def GroupsPh (senv : StructEnv) (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder),
     st.insts[k]? = some (c, js, r) → st.instOrigins[k]? = some (InstOrigin.field 0) →
     ∃ (kinds : List MixedGateBinder) (ty resTy : Lean.Expr) (args : List Lean.Expr) (ctor : Name)
       (fields : List (String × MixedGateBinder)),
       senv.instS c = some (kinds, ty) ∧ instRes ty args = some resTy ∧
       machOuts? senv resTy = some (some ctor, fields) ∧ k + fields.length ≤ st.insts.size
```
**Supplier of the new row (instSStep miss).** The miss pushes `fields.length` entries at index `k0 := st.insts.size`, origins `field 0 … field (fields.length-1)`. For row `k0` (origin `field 0`, call's `c`) the witness is the **call's own** `kinds, ty, args`, `resTy`, `ctor`, `fields`:
`senv.instS c = some (kinds, ty)` — from the new `PhPre.instS` conjunct (this is the tie that rev0 lacked; `instSStep` itself never reads `senv.instS`, it uses its argument `ty`);
`instRes ty args = some resTy`, `machOuts? senv resTy = some (some ctor, fields)` — from the guards of `instSStep` (`optK`/`match`); `k0 + fields.length ≤ st.insts.size + fields.length` — by the push. Rows `k0+i` (`i ≥ 1`) have origin `field i ≠ field 0`: vacuous.
**Use at the dedup arm (hit at `k0'`, origin `field 0`).** `GroupsPh` gives an earlier `(kinds₀, ty₀, args₀, resTy₀, ctor₀, fields₀)` with `senv.instS c = some (kinds₀, ty₀)`. Since `senv.instS c` is a function value, `PhPre.instS` and `GroupsPh` give `(kinds₀, ty₀) = (kinds, ty)` (by `Option.some.inj` of the two equations); the required `k0' + fields.length ≤ insts.size` then needs `fields.length = fields₀.length`, which is **`InstSFieldsDet`** (rev0 §4, still a *named* condition of `PhFacts`, owner proposed `sparkle-gen5-dg-env`; it is not proved here and is not added to any FG premise). With the tie, `InstSFieldsDet`'s hypotheses are exactly the two available equations (typed in §3).

Supplier lemma for the call-site facts (U-R2, total pure functions, `inlSpine` is not unfolded because the `if` and the result tuple are all that is used; types fixed here):

```lean
theorem machInstCallS?_spec {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} (h : machInstCallS? senv e = some (c, kinds, ty, args)) :
    senv.instS c = some (kinds, ty) ∧ args.length = kinds.length
theorem machInstCall?_spec {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} (h : machInstCall? senv e = some (c, kinds, res, args)) :
    senv.inst c = some (kinds, res) ∧ args.length = kinds.length
```

## 2. Typing of the names that rev0 only named (U-R2 / U-R1)

```lean
theorem bundleSlots_ph {nDecl : Nat} {st : MachRead} {dom : Lean.Expr}
    (hdom : InRange nDecl st st.lets.size dom) (hdn : NoLoose 0 dom) :
    ∀ (is : List Nat) (ts : List Lean.Expr) (e t : Lean.Expr),
      (∀ i ∈ is, i < st.kinds.size) → (∀ y ∈ ts, TyClosed y) →
      bundleSlots dom is ts = some (e, t) →
      InRange nDecl st st.lets.size e ∧ NoLoose 0 e ∧ TyClosed t
-- TyClosed y := (∀ tag i, ¬ MentionsPh tag i y) ∧ NoLoose 0 y     (the slot types BitVec w / Bool built by convBvar are TyClosed)
theorem bvarLt_mono {L L' : Nat} {e : Lean.Expr} (hL : L ≤ L') (h : BvarLt L e = true) : BvarLt L' e = true
theorem noPh_letOk (n : Nat) (e : Lean.Expr) (h : NoPh e = true) : LetOk n e = true
-- remaining helper names of rev0 §6 U-R2/U-R3, each with its type fixed when its unit is frozen (not by this document):
--   bindLetAlias_reach, foldO_js_length, mapM_length_some, RegViewPh, RunAppPh, InstCallPh, InstCallSPh, MemCallPh, LoopViewPh, LetTailPh, LoopRegsPh, GetAppArgsPh, BundleIotaPh, ProjIotaPh
```
**Definition order of rev0 §4 (fixed):** `SigTyPh` and `InstSFieldsDet` are defined **before** `PhFacts`:

```lean
def SigTyPh (senv : StructEnv) : Prop :=
  ∀ c kinds ty, senv.instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 0 ty = true
def InstSFieldsDet (senv : StructEnv) : Prop :=
  ∀ c kinds ty (args args' : List Lean.Expr) (r r' : Lean.Expr) (o o' : Option Name) (fs fs' : List (String × MixedGateBinder)),
    senv.instS c = some (kinds, ty) → instRes ty args = some r → instRes ty args' = some r' →
    machOuts? senv r = some (o, fs) → machOuts? senv r' = some (o', fs') → fs.length = fs'.length
structure PhFacts (senv : StructEnv) : Prop where   -- fields rootFloat, lift, inst1 as in rev0 §4; sigTy : SigTyPh senv; instSFieldsDet : InstSFieldsDet senv
```

## 3. Wording corrections

* The `lift` / `inst1` / `rootFloat` fields of `PhFacts` are properties of the C implementation of `Expr.liftLooseBVars` / `Expr.instantiate1` and of the opaque `partial def rootFloat`. **Their truth is not proved here**; they are named conditions, and any result using them is conditional and INTERMEDIATE.
* "`NoLoose` for the `lift` output" is the `LooseOcc` meaning only (no `letE/mdata/proj` descent), as in §0.
* U-R4 and U-R5 (rev0 §3, §5) are **not** re-frozen by this revision and stay unapproved; nothing in this revision supplies R-trace, R-in, R-nl or R-dom for `readF` calls. The only theorem about the reader proved so far is `convBvar_trace` (the single `_machIn` creation site), under `EnvPh` and `DomPh` hypotheses.

## 4. Checks (as rev0 §7, extended)

`Tests/Gen5/ReaderTraceCheck.lean` compares, with one reducible comparer used for positive and negative controls, `Exp…` declarations written from this document's text (not from the Tools file): the `def`s `phTag/NoPh/BvarLt/NoLoose/EnvPh/DomPh`, and the theorems `noLoose_zero_le, bvarLt_mono, noPh_letOk, reachC_ws, reachC_letv, reachC_slots, envPh_mono, envPh_cons_val, bundleSlots_ph, convBvar_trace, bindLet_reach` (counts are reported with category and counting rule when the Check exists). MUTANT: well-typed single changes only, rejected by signature/defeq (not semantic counterexamples), conclusion-conjunct-dropping mutants included. AXIOMS standard only; CLOSURE with unknown-name `throwError`, root self-check, root / helper value / helper type negatives and clean controls, invalid fixtures inside `withoutModifyingEnv`.
