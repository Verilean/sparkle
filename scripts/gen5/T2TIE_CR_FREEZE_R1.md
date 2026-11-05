# T2-TIE x DG-CLOSINGRUN connection — freeze r1 (docs only; no Lean yet)

Issue `sparkle-gen5-t2-tie`, branch `kjob/g5tt-cr2`, base `ef15da89` (= freeze r0, reviewer changes_requested R1/R2). Supersedes
`T2TIE_CR_FREEZE.md` (r0) §3 last paragraph, §4, §5; §1, §2 and the §3 table are unchanged and remain valid. Reviewer-supported scope kept:
Q1 one-output only (the group parent stays the named premise), Q2 conditional composition with the built `callTie_of_served`.
Nothing here claims T1, FG, M5 or Issue completion. "Not found" means only that this survey did not find a supplier or route in the tree;
it does not say a row is impossible or underivable. The C1-C4 connection is progress on one named hypothesis (`hDG_CLOSINGRUN`, one-output case);
it is NOT a supply of `hDG_GENP`, `hDG_SEM`, `hDG_SEM_range`, range facts, or the general FG. Not elaborated: types were read off built sources.

## 3'. Premise classification (replaces r0 §3 last paragraph; the three groups are not mixed)

(a) **Direct premises of the three new theorems** (this file): `hT : T1HypND …`, `hR`, `hP`, `hsh`/`h`, `h1`, `k`, `hk`, `hnone`; for the composed ones also
`q`, `hDG_GENP`, `hDG_SEM`, `hDG_SEM_range`. `hsh`/`h` (a `ClosingShared`/`ClosingRun0`) is taken as a hypothesis; these theorems do not build it.

(b) **Direct binders of the built `closingRun0_of_run`** (needed only when an upstream user obtains `h : ClosingRun0 …` from a run; NOT binders of the new theorems):
`hord`, `hT`, `hR`, `hP`, `hs : Start L mctx cctx w`, `hd0 : dv w = 0`, `hIH : IHAt L P Reach 1`, `hKI : ChildKeepsInv L P Reach 1`, `hrun`, `Gen`, `hGen`
(plus `L P Reach DataOk mctx cctx X p w w' raw D`). `hrow`/`hrows` is a binder of `closingRun_of_run_ga`, not of `closingRun0_of_run`.

(c) **Indirect supplier candidates — remainder** (candidate routes for supplying (b); they are not binders of `closingRun0_of_run` and nothing here supplies them):
`hrows` (for `hord`), `StepStmt`, `T1Hyp.dec` (as a possible IH-supply route; the new theorems never use it — forbidden root in the Check).

(d) **Verification not performed**: non-vacuity of `ClosingRun0`/`ClosingShared` (that a real run inhabits them) was not checked by this unit.

(e) **Neither field nor premise**: the depth-0 `stop` is not a field of `ClosingRun0` and not a premise of `closingRun0_of_run`; this unit does not mention it as a requirement.

## 4'. Frozen statements (new file `Tools/ShippingGen5T2TieCR.lean`, namespace `Tools.ShippingGen5T2TieCR`)

`import Tools.ShippingGen5ClosingRun2`, `import Tools.ShippingGen5T2Tie`, `import Tools.ShippingChildServe`; `set_option autoImplicit false`.
Header opens are exactly lines 14-23 of `Tools/ShippingGen5ClosingRun2.lean` (`open Lean Meta`, `Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine`, …,
`Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun`), so `Laws Pkgs Pkg T1HypND ShipsRes FieldRowAt CallTie GenExtAtCall CallOutRange Design Environment`
resolve as in `ClosingRun2`. Ambient variable line, verbatim:

```
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
```
Every theorem below lists ALL its binders (no `as above`, no elision). Binder order is the order written; `L P Reach DataOk mctx cctx X p Gen w w' raw D` are implicit,
`hT hR hP hsh/h h1 k hk hnone` (and `q hDG_*`) explicit. In the third theorem `h` occupies exactly the position of `hsh` in the other two (after `hP`'s block, before `h1`).

```
theorem servedCall_of_closingShared_one
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) :
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

theorem callTie_of_closingShared_one
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk) :
    CallTie p q k hk

theorem callTie_of_closingRun0_one
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingGen5ClosingRun2.ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk) :
    CallTie p q k hk
```
Proof plan (unchanged from r0): unpack `hsh` (resp. `h.shared`); the `insts = []` branch contradicts `hk`; the `CloseCalls` right branch contradicts `h1`;
`closeInsts_calls` (at `k`, `insts := shape.insts.map (·.2.1)`, length via `List.length_map`) gives `child` with `children[k]? = some child` and `moduleByName D.modules child.1.name = some mc` and
`st ∈ raw.body` with `CallStmt`; `closeInsts_names.2` gives `moduleByName D.modules child.1.name = some child.1`, so `mc = child.1`; `ChildrenShipsI.2 k hk` gives `y` with `children[k]? = some y`
(so `y = child`), the `child? = some y` disjunct is excluded by `hnone`, and `Reach (insts[k]).1` comes from `hT.closed X hR p hP k hk hnone`; `closeInsts_acyclic.2.2.2` gives C2;
`fieldRow_one_of_callStmt` gives C4; witnesses `r := child`, `dsn := D`. Composed forms: `callTie_of_served L P p q k hk hDG_GENP (servedCall_of_closingShared_one …) hDG_SEM hDG_SEM_range`.

## 5'. Checks (`Tests/Gen5/T2TieCRCheck.lean`, written from this document, not from the implementation's signature)

Expected TYPE for each of the three theorems is written independently from the Lean text in §4' and compared with the same reducible comparator that the positive controls
(built `callTie_of_served`, `closingRun0_of_run`) pass. Mutants are fixed as the following well-typed one-point differences from §4' (each is a type that elaborates; each must be REJECTED
by the comparator; rejection is by signature/defeq only and is NOT a semantic counterexample):

| id | theorem | exact difference |
|---|---|---|
| M1 | 1,2,3 | delete the binder `(h1 : p.d.shape.instFields = [])` |
| M2 | 1,2,3 | `hnone`: `… .child? = none` → `… .child? ≠ none` |
| M3 | 1 | conclusion binder order `∃ (r …) (dsn …)` → `∃ (dsn : Sparkle.IR.AST.Design) (r : Tools.ShippingChildInv.Res)` |
| M4 | 1 | last conjunct `FieldRowAt p k r.1` → `FieldRowAt p (k + 1) r.1` |
| M5 | 1 | first conjunct `ShipsRes L P (p.d.shape.insts[k]'hk).1 r` → `ShipsRes L P X r` |
| M6 | 1 | second conjunct `∀ g ∈ r.2.modules, …` → `∀ g ∈ dsn.modules, …` |
| M7 | 1 | third conjunct `… = some r.1` → `… = none` |
| M8 | 2,3 | `hDG_GENP : P (insts[k]'hk).1 = some q` → `P p.decl = some q` |
| M9 | 2,3 | swap the order of the binders `hDG_SEM` and `hDG_SEM_range` (with their types) |
| M10 | 2,3 | conclusion `CallTie p q k hk` → `CallTie p p k hk` |
| M11 | 3 | `ClosingRun0 … Gen …` → same with `Gen` replaced by `(fun _ _ _ => False)` |
| M12 | 1,2 | move `hsh` after `h1` (binder order) |

Also: closure walker (unknown name = FAIL, with the r6 negative control); forbidden roots (`T1Hyp.dec`, `T1Hyp` projections, `stop_of_run`); AXIOMS standard only; no `sorry`/`axiom`/`native_decide`.
Not claimed: any supply of `hDG_GENP`/`hDG_SEM`/`hDG_SEM_range`, the group field row, or the rows in §3'(b)-(d); the build is run by the coder with a clean exact-head job, not by this freeze.

## 6'. Sync notes (non-blocking, no type change; added at implementation)

1. `closingRun_of_run_ga` takes only `hrow`; `hrows` is not a binder of it. The direct candidate for `hord` is `hrow`; `hrows` (DataRows) belongs to the PostFacts/IH supply route (§3'(c)).
2. The T2Tie names (`FieldRowAt`, `CallTie`, `GenExtAtCall`, `CallOutRange`, `callTie_of_served`) live in namespace `Tools.ShippingGen2`, which the `ClosingRun2` header already opens (`open Tools.ShippingGen2 …`); there is no `Tools.ShippingGen5T2Tie` namespace, so no extra `open` was needed and the types are unchanged.
3. Implementation: `Tools/ShippingGen5T2TieCR.lean` (3 theorems), `Tests/Gen5/T2TieCRCheck.lean` (5 TYPE comparisons incl. 2 positive controls, 20 mutant definitions covering M1-M12, 3 closure audits, 3 axiom checks). Pod build of both targets exit 0; clean exact-head build is the coder's. Scope unchanged: one-output C1-C4 only; not a supply of GENP/SEM/range/group/FG or Issue completion.
