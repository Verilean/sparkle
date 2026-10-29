# SRC-ARGW freeze rev1: the source-side derivation of `callArgsOkAt` (argument widths, DPORT L6w)

**FOR REVIEW — design only, nothing built or proved.** No Lean file, lakefile or shared definition was written or
edited; no Lean was run. Every statement below is TEXT ONLY.

Issue `sparkle-gen3-src-argw`. Base: `par/gen2-spec` at **2b79ba09**. `git diff --stat a5998484 2b79ba09` changes no
file cited here except this one and lakefile.lean (the rest are NEW Tools/Tests files), so rev0's `file:line`s still
hold; lakefile lines are re-read at 2b79ba09. `[T]` = `~/git/.kjob/gen5-t2` worktree (3be26aee). Route:
scripts/gen2/DPORT_ROUTE_REPORT.md rev1 §1 rows L6w/L6', §3 item 4 (:116-120). Reuses UARITY_FREEZE.md (witnesses),
UARGW_PARENT_SURVEY.md (L2), UCHILD_PORTTYS_TABLE.md (L5), scripts/gen2/S4_WID_SUPPLY.md, [T] scripts/gen5/DGEN_FREEZE.md,
[T] scripts/gen5/M5_INDEP_STUDIES.md. Companion: scripts/gen3/SRC_ARGW_AUDIT.md (machConv audit, gen5 overlap,
G-E made concrete, summary for the next review).

## rev1 changes (review of f19fc07d: partial changes_requested)
- **(a)** §1.1 lists the THREE call paths. §2.2 keeps `ArgKindsAt` / `CalleeTeleAt` / `argWidth_of_halves`
  UNCHANGED and says they cover `senv.inst` (one-Signal signatures) only. §2.3 adds `ArgKindsAtS` / `CalleeTeleAtS` /
  `argWidth_of_halvesS` (instS) with full types, and the alternative origin-indexed relation `SigKindsAt`. `hsig` is
  NOT concluded from `hnone` (§2.3, last paragraph).
- **(b)** §2.2 "Strength": SA0's list equation is a sufficient condition STRONGER than `callArgsOkAt` (length and
  `some` at every index); the extra arity comes from `hA`/`hC`. `ArgWidthAt` stays a data Prop (no trace, no run).
- **(c)** §3 (iii-b): full `kidWsP`, transport under `P c = some q`, the vacuous `none ↦ []` case (that `true` is
  NOT supply), and the controls are data controls only.
- **(d)** §3 (i)/(ii): rev0's "fuel proves only the fresh branch" and "typing only as a new premise" are replaced by
  "route not supplied in this survey". Final assumption vs intermediate invariants are separated. Obligations shared
  with gen5 are listed (§3.2).
- **D-ARGW is HELD** (§4). It is not sent to the user. SA0/SA1 are allowed as limited intermediate work only.

## 0. Summary
- The row is DATA-level: it mentions only `p.d.shape` and `q.ports` (Tools/ShippingGen2Adapt.lean:73-80,
  Tools/ShippingGen2Pkg.lean:80-81). A source-side supply needs no trace. It needs the two READER runs (parent and
  callee `machineShape?`) and their environments.
- The parent's argument let kind comes from three `machLetIndex` branches (§1.2). Only the FRESH branch records the
  callee signature kind. The two REUSE branches keep an earlier kind. No reader or run check compares it with the
  callee kind (§1.4).
- The callee side has three more bridges: value-binder kinds vs declared-type kinds (VT), the opaque inliner on binder
  types (P5-arg), and env identity (ENV = [T] DG-ENV) (§1.3).
- Survey finding (not an impossibility claim): a kernel-closed all-source route for the reuse branches and for the
  callee half is **not supplied in this survey**. §3 lists candidate intermediate invariants. G-E is made concrete for
  comparison in SRC_ARGW_AUDIT.md §C. G-ARG-WID stays a named open gap row next to G-ONEOUT-WID.

## 1. Source analysis

### 1.1 The three call paths (all in `machConv`, Sparkle/Compiler/Elab.lean)
| path | recogniser | signature + arity check | arm | origin pushed |
|---|---|---|---|---|
| P-ord | `machInstCall?` :3721-3728 | `senv.inst c = some (kinds, res)`, `args.length == kinds.length` (:3726) | :3945-3947 → `machInstance … .ord` | `.ord` (:4078-4080) |
| P-fld | `machInstCallS?` :3732-3739 | `senv.instS c = some (kinds, ty)`, `args.length == kinds.length` (:3737) | :3949-3951 → `machInstanceS` | `.field i`, one entry per field (:4122-4127) |
| P-mem | `memCall?` :3954-3955 | hard-coded `[.domain, .bits aw, .bits dw, .bool, .bits aw]` (:3958-3959) | :3956-3960 → `machInstance … (.mem …)` | `.mem` |

- The arms :3945-3951 form a separate branch structure. P-ord is tried first. When `senv.inst c = none` OR its arity
  check fails (:3726 returns `none`), control FALLS THROUGH to P-fld (:3949).
- For `structEnv env` the two signatures are disjoint. `instSignature?` needs `machResultKind? ci.type` to succeed
  (:4379); `instSignatureS?` needs it to fail (:4389). For an ARBITRARY `StructEnv` (:3537-3552) both fields may be
  `some`. A `.field` entry may then have been read through `instS` although `inst c = some` with another length.
- `senv = structEnv envR'` (:4394-4397). `kinds = telescopeKinds ci.type` (:4367-4369) on both paths (:4378, :4390).
- `hnone : (instOrigins.getD k .ord).child? = none` excludes exactly `.mem` (`InstOrigin.child?`,
  Sparkle/Compiler/MachInstOrigin.lean:28-30). It leaves `.ord` and `.field i`, i.e. BOTH P-ord and P-fld.

### 1.2 Parent: where the kind of the let at `args[j]` comes from
- `machInstance` (:4049) folds `kinds.zip args` (:4061-4071); `machInstanceS` repeats the fold (:4100-4111). Each arg
  is converted by `machConv` (:4063, :4102). A `.domain` kind contributes no index (:4065-4068, :4104-4107). This
  matches the domain filter of `Pkg.ports` (Pkg.lean:80-81). For other kinds `machLetIndex … kind v'` (:4070, :4109)
  does one of three things (:3743-3750):
  - **F (fresh)** :3750 pushes `(nm, kind, v')`. The let kind is the callee signature kind.
  - **R1 (`_machLet j`)** :3746 returns `j`. `v'` is a let placeholder made by `machBindLet` / `machBindLetNamed` /
    `machBindLetAlias` (:3619-3627, :3640-3647, :3654-3671), for root lets (:5125-5132), body lets (:4007-4010) and
    the chain/loop readers. Its kind is `mixedGateBinderKind? ty` of the let's annotation (:3620, :3641, :3664).
  - **R2 (same value)** :3748-3749 returns the first let whose value is `==` to `v'`. Its kind is that let's kind:
    a user annotation kind, an earlier F push with ANOTHER callee's kind, or a P-mem hard-coded kind (:3958-3959).
- The call dedup (:4075-4080; :4118-4119) reuses an entry only with the same `c`, `js` and origin. It adds no kind source.
- The shape is `binders = bs ++ instBinders ++ slots ++ lets.map (nm, kind)` (:5183-5184). `callArgsOkAt` reads it at
  `nDecl + kI + n + a` (Adapt:76), under R5 (`ShapeDecomp.nDecl`, Tools/ShippingShapeDecomp.lean:37-39) and
  `nDecl = p.kD` (missing small lemma `closingNDecl_eq_kD`, scripts/gen2/S4_CONSUMER_FREEZE.md:510-512).
- Kind reading is syntactic. `mixedGateBinderKind?` (:2337-2343) accepts `Signal _ Bool` and `Signal _ (BitVec w)`
  with a canonical literal `w > 0`. Let annotations are read from the NORMALISED body (:5088-5090). `machNorm` leaves
  binder types "as written" (:4966-4967), but it substitutes `Nat` lets and closed `BitVec` lets (:4988-4992).

### 1.3 Callee: where `q.portWidths` comes from
- `q.ports = (q.d.bsIn.take q.kD).filter nonDom` (Pkg.lean:80-81). `bs` comes from `mixedGatePeel (packTupleInputs
  d.value)` (Elab:5078). `d` is the ENTRY constant `entryConst … (userInliner envR) …` (Elab:5272-5282).
  `packTupleInputs` is `partial` (Sparkle/Compiler/MachTupleIn.lean:79). The callee peel runs BEFORE normalisation
  (:5078 vs :5088).
- So `q.portWidths` are the widths of the VALUE-lambda binders of the (possibly inlined) callee in the callee's run.
  The parent's `kinds` are the DECLARED-type binders of `envR'.find? c` in the parent's run. Three bridges:
  - **VT**: peel kinds of `value` = `telescopeKinds` of `type` (Lean typing of the definition; the binder types are
    defeq, not syntactically equal).
  - **P5-arg**: `inl` keeps the binder kinds, and `packTupleInputs` is the identity on a callable callee.
  - **ENV**: the callee run's `getConstInfo c` agrees with `envR'.find? c` of the parent run ([T] DG-ENV, C0,
    DGEN_FREEZE.md:314-328).

### 1.4 What the run checks (none compares argument widths)
- `instStmt` / `instStmtG` check counts and names only (Sparkle/IR/Machine.lean:272-287;
  Sparkle/IR/MachineInstG.lean:30-52).
- `closeInsts` / `closeInstsG` have no width conjunct (Machine.lean:396-425; MachineInstG.lean:115-140). The only
  existing instance-width check is output-only: `instOutWidthsOk` (Tools/ShippingHierOpen.lean:503-514).
- `unifiedGateRoot` (Elab:5185) types each let VALUE at its own let kind. For R1/R2 that is the REUSED kind.

## 2. The statements (full telescope)

### 2.1 Target row (unchanged)
Same witnesses as U-ARITY (UARITY_FREEZE.md:97-150): `P`, `p`, `k`, `hk`, `hnone`, `q`, `hP`.
```lean
/-- G-ARG-WID at one call (the target row). DATA-level: no trace, no run, no `RunsTo` inside. -/
def ArgWidthAt (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
    ∀ q, P (p.d.shape.insts[k]).1 = some q → callArgsOkAt p.d p.kD k q.portWidths = true
```
`ArgWidthAt` takes the SAME package witnesses as U-ARITY (`callArity_of_trace`, UARITY_FREEZE.md:142-150). Unlike A7,
it contains no trace `MachineTraceLBX` and no run. This is kept: the run enters only through the SUPPLIERS (§2.4).

### 2.2 S0 for P-ord (types UNCHANGED from rev0; scope: `senv.inst`, one-Signal signatures only)
```lean
def ArgKindsAt (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds res, sp.insts[k]? = some (c, js, r) → senv.inst c = some (kinds, res) →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth
def CalleeTeleAt (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  ∀ kinds res, senv.inst c = some (kinds, res) →
    (kinds.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = q.portWidths
/-- Pure. ASSUMES `hsig`; `hsig` is not derived here (§2.3, last paragraph). -/
theorem argWidth_of_halves (senv : StructEnv) (p q : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    {kinds : List MixedGateBinder} {res : MixedGateBinder}
    (hsig : senv.inst (p.d.shape.insts[k]).1 = some (kinds, res))
    (hA : ArgKindsAt senv p.d.shape p.kD k) (hC : CalleeTeleAt senv (p.d.shape.insts[k]).1 q) :
    callArgsOkAt p.d p.kD k q.portWidths = true
```
**Strength (review (b)).**
- `callArgsOkAt d nDecl k ws` checks only `j < ws.length` (Adapt:74), each position `= ws[j]?` (Adapt:75-77). It
  holds when `js` is LONGER than `ws` (the extra arguments are not checked). It holds trivially for `ws = []`.
- `hA` is a list EQUATION. It forces `js.length = (kinds.filter nonDom).length` and a `some` binder at EVERY index of `js`.
- With `hC`, `(kinds.filter nonDom).length = q.portWidths.length = q.ports.length` (Adapt:80).
- So `hA ∧ hC` is a sufficient condition STRICTLY STRONGER than the row. It also gives the arity
  `js.length = q.ports.length`. On the run route that arity is U-ARITY's content (`callArity_of_trace`,
  UARITY_FREEZE.md:140-150). In S0 it comes from `hA`/`hC`, not from a trace.
- A weaker per-index form (`∀ j < q.portWidths.length, …`) would suffice for the row. It is not proposed: the reader
  builds the full list (:4061-4071), and a reader invariant naturally gives the equation.

### 2.3 S0 for P-fld (NEW separate types; the existing types are not widened)
```lean
def ArgKindsAtS (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds ty, sp.insts[k]? = some (c, js, r) → senv.instS c = some (kinds, ty) →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth
def CalleeTeleAtS (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  ∀ kinds ty, senv.instS c = some (kinds, ty) →
    (kinds.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = q.portWidths
theorem argWidth_of_halvesS (senv : StructEnv) (p q : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    {kinds : List MixedGateBinder} {ty : Lean.Expr}
    (hsigS : senv.instS (p.d.shape.insts[k]).1 = some (kinds, ty))
    (hA : ArgKindsAtS senv p.d.shape p.kD k) (hC : CalleeTeleAtS senv (p.d.shape.insts[k]).1 q) :
    callArgsOkAt p.d p.kD k q.portWidths = true
```
The "Strength" remarks of §2.2 apply unchanged. Alternative: one relation, ORIGIN-indexed, so that it follows the
dispatch of §1.1 even for an arbitrary `StructEnv`:
```lean
/-- The kinds list the reader used for entry `k`, chosen by its ORIGIN (`.mem` admits none). -/
def SigKindsAt (senv : StructEnv) (sp : MachineShape) (k : Nat) (c : Name) (kinds : List MixedGateBinder) : Prop :=
  match sp.instOrigins.getD k .ord with
  | .ord     => ∃ res, senv.inst c = some (kinds, res)
  | .field _ => ∃ ty, senv.instS c = some (kinds, ty)
  | .mem ..  => False
def ArgKindsAtG (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds, sp.insts[k]? = some (c, js, r) → SigKindsAt senv sp k c kinds →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth
```
- A plain disjunction `inst c = some (kinds,_) ∨ instS c = some (kinds,_)` would be STRONGER than the reader for an
  arbitrary `StructEnv`: it would constrain a signature the reader did not use. It is not proposed.
- Recommendation: the separate `…S` version (nothing to justify). Use `SigKindsAt` only if one consumer statement for
  both origins is wanted.

**`hsig` / `hsigS` do not follow from `hnone`.**
- `hnone` gives only `origin ∈ {.ord, .field i}` (§1.1).
- That the signature EXISTS is a READER-provenance fact. An `.ord` entry is pushed (:4078-4080) only after
  `machInstCall?` succeeded (:3945-3947). A `.field` entry is pushed (:4122-4127) only after `machInstCallS?` succeeded
  (:3949-3951).
- `instOrigins.getD k .ord` DEFAULTS to `.ord` (also in `instTagged`, Elab:5223-5225). An entry without a recorded
  origin therefore reads as `.ord`. Excluding that needs `instOrigins.length = insts.length`; the reader pushes both
  together (:4078-4080, :4122-4127), but that is a fact about the `partial` reader.
- On the fuel candidate these facts are `InstProv` with its tags `OrdOrigin` / `StructOriginI`
  (Tools/ShippingReaderFuelProv.lean:14-28, :89-90, :95, :167) and `machineShapeF_final_instProv`
  (Tools/ShippingReaderFuelShapeProv.lean:226). On production they are on the O1/O2 side.

### 2.4 S1: source-side supply from the two reader results (scope per origin)
```lean
theorem argWidth_of_shapes (P : Pkgs ι dom) (p : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) {q : Pkg ι dom}
    (hP : P (p.d.shape.insts[k]).1 = some q)
    {Ep Eq : ConstantInfo} {envP envQ : Environment} {kinds : List MixedGateBinder}
    (hp : machineShape? false [] Ep (structEnv envP) = some p.d.shape)
    (hq : machineShape? false [] Eq (structEnv envQ) = some q.d.shape)
    (R5p : …) (KDp : p.kD = <bs length of hp>) (KDq : q.kD = <bs length of hq>)   -- index alignment
    (SIG : SigKindsAt (structEnv envP) p.d.shape k (p.d.shape.insts[k]).1 kinds)   -- §2.3; NOT from hnone
    (SRC : <suppliers of ArgKindsAt/…S and CalleeTeleAt/…S, §3>) :
    callArgsOkAt p.d p.kD k q.portWidths = true
```
The run form wraps it with the `T1Hyp.defines` reads at `p.decl` and at the callee, in ONE `(mctx, mref, cctx, cref)`
([T] `RunReads`, M5_INDEP_STUDIES.md:208-241).

## 3. Routes (for the reuse branches R1/R2 and for the callee half)
**(i) Fuel reader model** (`machineShapeF`, Tools/ShippingReaderFuelShape.lean:256; `instArg` mirrors Elab:4061-4071
at Tools/ShippingReaderFuelDefs.lean:412, `instSArg` at :442).
- Existing: `InstProv` (FuelProv:167), `machineShapeF_final_instProv` (ShapeProv:226), `InstR1` / `machineShapeF_r1At`
  (Tools/ShippingReaderFuelShapeR1.lean:136-178), `machineShapeF_r5` (FuelShapeR5:462), the driver
  (`driveShape_complete`, Tools/ShippingReaderFuelDriverComplete.lean:203).
- Missing: (a) `shapePost` exposing `letB = st.lets.map (nm, kind)`; (b) a let-kind invariant
  `ArgProv senv st : ∀ k c js r kinds, insts[k] = (c,js,r) → SigKindsAt … k c kinds → ∀ j a, js[j]? = some a →
  lets[a].kind = (kinds.filter nonDom)[j] ∨ ReusedAt st k j a`.
- `ArgProv` in this form discharges the F branch only. A discharge of `ReusedAt` (R1/R2) is **not supplied in this
  survey**.
- That `MachineShape` erases the branch does NOT exclude such a discharge. An invariant over the reader STATE can
  carry history: `MachRead.lets` keeps every `(nm, kind, value)` (Elab:3554-3556). A candidate:
  `LetKindOk st : ∀ j nm kd v, st.lets[j]? = some (nm, kd, v) → ValKind st v = some kd`, where `ValKind` is a
  syntactic kind function on placeholder Exprs. It would read slot kinds from `st.kinds`, let kinds, input kinds
  from `bs`, and call result kinds from `insts[k].2.2`.
- Under `LetKindOk`, R1 and R2 both reduce to the SAME per-argument obligation, a typing fact of the call:
  `ValKind st (machConv arg_j) = some kinds_j`. R2 reduces too, because `findIdx?` returns a let whose value is `== v'`
  (:3748).
- Proving `LetKindOk` and that obligation still needs a source-side typing/denotation fact (route (ii)). This survey
  did not find one supplied. The plug-in boundary is O1/O2 (docs/parallel/R-reader-fuel.md:35-48).

**(ii) Typing / source semantics.** Kernel facts about `c args` would give `type(a_j) ≡ binder_j`. Status in this survey:
- no Prop-level typing judgment over `Lean.Expr` was found (grep `HasType`/`WellTyped`/`Typing` in Tools/ and
  Sparkle/: none);
- `Environment` gives no "every constant is well-typed" lemma;
- R1 reads the NORMALISED body (Elab:5088-5090), so a typing fact would have to be carried through `machNorm` /
  `inlFoldNat` / `zeroLit` / `rootFloat`.

Two different things must not be confused:
- **(ii-F) A final assumption** `EnvArgTyped env` added to FG: for every machine-read declaration, the halves hold.
  That is a guarantee change (a user item). It is NOT proposed.
- **(ii-I) Intermediate invariants, to be PROVED:**
  1. `LetKindOk` and the per-argument obligation of (i), stated against a definable Expr denotation. The candidate
     carrier is [T] DC-FORM's `ExprDenotes` (DGEN_FREEZE.md:444-450, :487-493), so no separate typing judgment is
     introduced.
  2. Preservation of that denotation by the normalisers.
  3. Canonical-literal injectivity (`BitVec n` vs `BitVec m`), stated as a fact about `canonicalNatLitValue?`
     (Elab:1389-1390).

  None of these is supplied in this survey. None is shown impossible.

**(iii) Intermediate only** (these do not complete FG; coverage stays open):
- (iii-a) The unsupplied Props of §2 as explicit premises, or a `T1Hyp.argw` field. Either needs an S4_WID_SUPPLY
  §4.1-style revision table before any shared change.
- (iii-b) A per-declaration decided row through a concrete `P` (SA1):
```lean
def kidWsP (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom) (k : Nat) : List Nat :=
  ((((p.d.shape.insts.map (·.1))[k]?).bind P).map Tools.ShippingGen2.Pkg.portWidths).getD []
theorem kidWsP_eq (hk : k < p.d.shape.insts.length) (hq : P (p.d.shape.insts[k]).1 = some q) :
    kidWsP P p k = q.portWidths                              -- as kidOutsP_eq, DataBridge:77-87
theorem kidWsP_none (hk : k < p.d.shape.insts.length) (hn : P (p.d.shape.insts[k]).1 = none) :
    kidWsP P p k = []                                        -- as kidOutsP_none, DataBridge:90-100
theorem callArgsOkAt_nil (d : MachineData) (nDecl k : Nat) : callArgsOkAt d nDecl k [] = true
theorem argWidthAt_iff_rowP (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom) :
    (∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      callArgsOkAt p.d p.kD k (kidWsP P p k) = true) ↔ ∀ k, ArgWidthAt P p k
```
  - Transport: under `P c = some q`, the row at `kidWsP P p k` IS the row at `q.portWidths` (`kidWsP_eq`).
  - The vacuous case: `P c = none` gives `[]`, and `callArgsOkAt … [] = true` (Adapt:74, `List.range 0`). That `true`
    carries no width and is **NOT counted as supply**. It agrees with `ArgWidthAt` only because `ArgWidthAt`
    quantifies over the `q` with `P c = some q`.
  - A decided row is supply only at the concrete `P` it is decided for.
  - Controls (`Tests/Gen3/…`, like DataBridgeCheck): positive `callerL` with `pbhPkg.portWidths = [16, 2]`
    (UARGW_PARENT_SURVEY.md:217-219), a negative mismatched width list, and the vacuous `none` case. These are DATA
    controls on concrete `MachineData`. They are not a parent package from a run, and not run supply.

**(iv) Compiler guard (comparison only; see SRC_ARGW_AUDIT.md §C).**
- **G-T (reader tail):** at the tail of `machineShape?` (before Elab:5185), check the §2.2/§2.3 halves for every
  `.ord`/`.field` entry, and return `none` on failure. It would be kernel-visible through a new `ShapeDecomp` field.
  VT / P5-arg / ENV remain.
- **G-E (emission):** in `instStmt`/`instStmtG`, check `wireWidth m.wires argW == p.ty.bitWidth` per argument port.
  Details, change range and policy obligations are in SRC_ARGW_AUDIT.md §C. Not proposed for application.

### 3.1 Implementation units (future children of `sparkle-gen3-data-supply`)
| unit | statement | inputs | size (estimate) | status |
|---|---|---|---|---|
| SA0 `argWidth_of_halves` + `…S` (+ optional `SigKindsAt`) | §2.2, §2.3 | Adapt:73-80, Pkg:80-81 | 100-160 l + controls (mock `StructEnv`: `inst` only, `instS` only, both) | ALLOWED (limited intermediate) |
| SA1 `kidWsP` row | §3 (iii-b) + positive/negative/vacuous controls | DataBridge:62-145 | 80-120 l | ALLOWED (limited intermediate; not FG) |
| SA2 decision note D-ARGW | — | — | doc | HELD (not to the user) |
| SA3 (only after a later decision) | `argWidth_of_portTie`: L2 + G-E + L5 ⇒ row | AUDIT §C | 150-250 l + compiler edit + re-proofs | not started |
| SA3' (only after a later decision) | halves from VT / P5-arg / ENV | ShapeDecomp, P1 | 200-400 l | not started |
| SA4 (optional) | `ArgProv` / `LetKindOk` on `machineShapeF` | FuelProv skeleton | 300-500 l | not started |

### 3.2 Obligations shared with gen5 ([T] DGEN_FREEZE.md; details in SRC_ARGW_AUDIT.md §B)
| SRC-ARGW obligation | gen5 item | same obligation? |
|---|---|---|
| ENV (§1.3) | DG-ENV, C0 `ReadsAt env₀` (DGEN:314-328, :630) | yes. Route it there; no parallel premise |
| VT (callee peel kinds vs `telescopeKinds ci.type`) | DG-DECLCONNECT, the `args` component of `adapterOf` (DGEN:454-458, :474) | overlapping. `adapterOf` maps the actual binders of `ci.type` to `p.d.bsIn.take p.kD`; VT is its width projection |
| P5-arg (`packTupleInputs` identity); R1 through `rootFloat` | DG-READKINDS: total replacements for `rootFloat`/`zetaAll`/`packTupleInputs` (DGEN:302-308, :622) | same objects. DG-READKINDS replaces them; SRC-ARGW needs a property of them |
| (ii-I) Expr typing/denotation carrier | DC-FORM `ExprDenotes`/`ConstValue` (DGEN:444-450, :487-493) | candidate shared carrier |
| reader provenance (`hsig`, `instOrigins` length), `ArgProv` | DG-COVER on the fuel model (DGEN:635; D2(b) :651-659) | same reader model and the same O1/O2 boundary |

## 4. Stops and decision items
- **D-ARGW is HELD.** It is not sent to the user (review of f19fc07d). Its options are (a) a final typing assumption,
  (b) G-T plus the callee premises, (c) G-E. They are kept only as comparison material (SRC_ARGW_AUDIT.md §D).
  rev0's recommendation "(c) G-E" is withdrawn as a recommendation.
- ENV is not new: route it to DG-ENV and do not add a parallel premise.
- R2 audit: SRC_ARGW_AUDIT.md §A. It is a reading result. It is neither a preservation proof nor a counterexample from a
  type-checked run.
- The `ShapeDecomp` header still says UNVERIFIED (ShapeDecomp:49-50), although `Tools.ShippingShapeDecomp` is a
  lakefile lib (lakefile.lean:2487-2488). Build status not checked here.

## 5. Not claimed
- Nothing was written, elaborated or built. Sizes are estimates.
- No width-mismatched successful run is exhibited, and none is claimed to exist or not to exist. "Not supplied in this
  survey" is a survey finding, not an impossibility claim.
- No claim that G-E/G-T never refuse on the corpus.
- No change to `T1Hyp`, `ChildShips`, `DataOkB`, FG, the compiler or any shared definition.
