# SRC-ARGW freeze rev0: the source-side derivation of `callArgsOkAt` (argument widths, DPORT L6w)

**FOR REVIEW — design only, nothing built or proved.** No Lean file, lakefile or shared definition was written or
edited; no Lean was run. Every statement below is TEXT ONLY.

Issue `sparkle-gen3-src-argw`. Base: `par/gen2-spec` at **a5998484** (all `file:line` at this SHA unless marked
`[T]` = `~/git/.kjob/gen5-t2` worktree). Route: DPORT_ROUTE_REPORT.md rev1 §1 rows L6w/L6' (:61-62), §3 item 4
(:112-118). Reuses UARITY_FREEZE.md (witnesses), UARGW_PARENT_SURVEY.md (L2), UCHILD_PORTTYS_TABLE.md (L5),
S4_WID_SUPPLY.md (result-width analogue), S4_PMEM_FREEZE.md §3 (fuel/O1/O2), [T] scripts/gen5/M5_INDEP_STUDIES.md,
[T] scripts/gen5/DGEN_FREEZE.md.

## 0. Summary
- The row is DATA-level: it mentions only `p.d.shape` and `q.ports` (Adapt:73-77, Pkg.lean:80-81). A source-side
  supply needs no trace; it needs the two READER runs (parent and callee `machineShape?`) and their environments.
- The parent's argument let kind comes from three reader branches (§1.1). Only the FRESH branch carries the callee
  signature kind. The two REUSE branches keep an earlier kind; no reader or run check compares it with the callee
  kind (§1.3). Their agreement is a Lean-typing fact about the (normalised) parent term, and no Prop-level typing
  judgment for `Lean.Expr` exists in the repository (§3 (ii)).
- The callee side has three more gaps: value-binder kinds vs declared-type kinds (typing again), the opaque inliner
  on binder types (P5-arg), and env identity (ENV, which is DGEN's DG-ENV) (§1.2).
- Finding (survey, not an impossibility proof): no kernel-closed all-source route was found without either a new
  source-typing premise (a final-guarantee change) or a compiler guard. Therefore §4 lists **D-ARGW** as a user
  decision, with impact and cost. Until it is decided, G-ARG-WID stays a named open gap row next to G-ONEOUT-WID.

## 1. Source analysis

### 1.1 Parent: where the kind of the let at `args[j]` comes from
- Call recognition: `machInstCall?` (Elab:3721-3728) returns `(c, kinds, res, args)` from `senv.inst c` only when
  `args.length == kinds.length`. `senv = structEnv envR'` (Elab:4394-4397; MachineEntry:2357). `inst =
  instSignature? envR'`, so `kinds = telescopeKinds ci.type` of `envR'.find? c` (Elab:4373-4383, :4366-4368; P1
  `instSignature?_some`, Tools/ShippingInstSignature.lean:18-22). The arms that call it are Elab:3945-3947 (`.ord`),
  and :3949-3951 for structure calls (`instSignatureS?`, Elab:4387-4392, also `telescopeKinds`). The memory arm
  (:3953-3960) hard-codes its kinds and is excluded by `hnone`.
- Arguments: `machInstance` (Elab:4049) folds `kinds.zip args` (:4061-4071). Each arg is converted by `machConv`
  (:4063). A `.domain` kind contributes no index (:4065-4068). So `js[j]` belongs to the j-th NON-domain kind,
  which matches the domain filter of `Pkg.ports` (Pkg.lean:80-81). For other kinds, `machLetIndex … kind v'`
  (:4070) does one of three things (Elab:3743-3750):
  - **F (fresh)** :3750 pushes `(nm, kind, v')`. The let kind is the callee signature kind.
  - **R1 (`_machLet j`)** :3746 returns `j`. `v'` is a let placeholder made by `machBindLet` /
    `machBindLetNamed` / `machBindLetAlias` (:3618-3627, :3640-3647, :3654-3671). These are called for root lets
    (:5124-5132), body lets (:4007-4010), chain lets (:4172-4175) and loop-body lets (:4183-4190). Their kind is
    `mixedGateBinderKind? ty` of the let's annotation (:3620, :3641, :3664).
  - **R2 (same value)** :3748-3749 returns the first let whose value is `==` to `v'`. Its kind is that let's kind:
    either a user annotation kind, or an earlier F push made with ANOTHER callee's signature kind.
- `machInstanceS` repeats the same fold at :4100-4111. The call dedup (:4075-4080, :4118) reuses an entry only with
  the same `js`, so it adds no new kind source.
- The shape: `binders = bs ++ instBinders ++ slots ++ lets.map (nm, kind)` (Elab:5181-5184). The let kind becomes
  `binders[nDecl + kI + n + a]`, which is exactly what `callArgsOkAt` reads (Adapt:76), under R5
  (`ShapeDecomp.nDecl`, Tools/ShippingShapeDecomp.lean:150-158) and `nDecl = p.kD` (S4_CONSUMER_FREEZE.md:510-512).
- Kind reading is syntactic: `mixedGateBinderKind?` (Elab:2337-2343) accepts only `Signal _ Bool` and
  `Signal _ (BitVec w)` with `canonicalNatLitValue? w` (Elab:1389-1394), a literal `> 0`. The let annotations R1
  reads are taken from the NORMALISED body `machNorm`/`inlFoldNat`/`zeroLit`/`rootFloat` (Elab:5087-5090), not from
  the kernel-checked value.

### 1.2 Callee: where `q.portWidths` comes from
- `q.ports = (q.d.bsIn.take q.kD).filter nonDom` (Pkg.lean:80-81). `bsIn = binders.take nIn` (Auto:195).
  `binders = bs ++ …` and `bs` comes from `mixedGatePeel (packTupleInputs d.value)` (ShapeDecomp:63-65), where `d`
  is the ENTRY constant: `entryConst … ci (userInliner envR) …` (MachineEntry:2354-2357; Elab:5272-5282). The
  unfolded form `inlinedConst` rewrites both `value` and `type` with `inl` (Elab:3409-3411); `userInliner` is
  Elab:3387. `packTupleInputs` is `partial` (MachTupleIn.lean:79).
- So `q.portWidths` are the widths of the VALUE-lambda binders of the (possibly inlined) callee read in the callee's
  run. The parent's `kinds` are the DECLARED-type binders of `envR'.find? c` in the parent's run. Three bridges:
  - **VT**: peel kinds of `value` = `telescopeKinds` of `type`. This is Lean typing of the definition (lambda
    binder types are defeq, not syntactically equal, to the pi binder types).
  - **P5-arg**: `inl` keeps the binder kinds. It is opaque, like P5 (ChildReal:143-155; only the candidate
    `userInlinerC`, InlCand:124, is analysed). It also needs `packTupleInputs` to be the identity on a callable
    callee. A tuple binder makes `telescopeKinds` fail, so a callable callee has none. That this is the identity
    is an O2-like fact about a `partial` function.
  - **ENV**: the callee run's `getConstInfo c` value equals `envR'.find? c` of the parent run. This is the same gap
    as S4_WID_SUPPLY.md:45 and [T] DGEN_FREEZE.md:235-241 (DG-ENV, C0).

### 1.3 What the run checks (none compares argument kinds)
- `instStmt`/`instStmtG` check counts and names only (DPORT:21).
- `closeInsts`, `linkedOk`, `kidsCombB`, `hierGate`: no input width (DPORT:22).
- `unifiedGateRoot` (Elab:5185) types each let VALUE at its own let kind. So for R1/R2 it checks the value against
  the REUSED kind, never against the callee kind.
- The callee kind is therefore discarded on R1/R2 and recorded on F only.

## 2. The statement to supply (full telescope)
Same witnesses as U-ARITY (UARITY_FREEZE.md:97-147): `L`, `P`, `p`, `k`, `hk`, `hnone`, `q`, `hP`. The trace is
NOT needed (arity is). The reads are those `T1Hyp.defines` quantifies over (Defs:198-199, MachineEntry:2345-2357),
instantiated at actual runs. The run existence comes from `RealChildA` reads (ChildLinkA:53-56) or [T] RunReads
(M5_INDEP_STUDIES.md:211-236).
```lean
/-- G-ARG-WID at one call (the target row). -/
def ArgWidthAt (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
    ∀ q, P (p.d.shape.insts[k]).1 = some q → callArgsOkAt p.d p.kD k q.portWidths = true

/-- (S0) Pure composition (PROVABLE NOW, no source facts): the two halves + arity give the row. -/
def ArgKindsAt (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds res, sp.insts[k]? = some (c, js, r) → senv.inst c = some (kinds, res) →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth
def CalleeTeleAt (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  ∀ kinds res, senv.inst c = some (kinds, res) →
    (kinds.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = q.portWidths
theorem argWidth_of_halves (senv : StructEnv) (p q : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    {kinds : List MixedGateBinder} {res : MixedGateBinder}
    (hsig : senv.inst (p.d.shape.insts[k]).1 = some (kinds, res))
    (hA : ArgKindsAt senv p.d.shape p.kD k) (hC : CalleeTeleAt senv (p.d.shape.insts[k]).1 q) :
    callArgsOkAt p.d p.kD k q.portWidths = true

/-- (S1) Source-side supply from the two reader results (the run form wraps it with T1Hyp.defines at `p.decl`
and at the callee, in ONE (mctx, mref, cctx, cref)). -/
theorem argWidth_of_shapes (P : Pkgs ι dom) (p : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) {q : Pkg ι dom}
    (hP : P (p.d.shape.insts[k]).1 = some q)
    {Ep Eq : ConstantInfo} {envP envQ : Environment}
    (hp : machineShape? false [] Ep (structEnv envP) = some p.d.shape)
    (hq : machineShape? false [] Eq (structEnv envQ) = some q.d.shape)
    (R5p : …) (KDp : p.kD = <bs length of hp>) (KDq : q.kD = <bs length of hq>)   -- index alignment
    (SRC : <route premises of §3: ArgKindsAt + CalleeTeleAt suppliers>) :
    callArgsOkAt p.d p.kD k q.portWidths = true
```
`hsig` (the callee has a one-Signal or structure signature in `senv`) follows from `hnone` plus provenance
(`OrdOrigin`, FuelProv:89-90; ShapeProv:226 on the fuel candidate). On production it is an O1/O2-side fact,
like R1 (FuelShapeR1:1-30).

## 3. Routes
**(i) Fuel reader model** (`machineShapeF`, FuelShape:256-259; skeleton of `InstProv`/`GoodP`, FuelProv:167-172,
:592-602; `instArg` mirrors Elab:4061-4071 at FuelDefs:412-423, `instSArg` :442-453).
- Existing: `InstProv`, `machineShapeF_final_instProv` (ShapeProv:226), `InstR1`/`machineShapeF_r1At`
  (FuelShapeR1:136-178), `machineShapeF_r5` (FuelShapeR5:462), `machineShapeF_steps` (:391), the driver
  (`driveShape_complete`, DriverComplete:203).
- Missing: (a) `shapePost` exposing `letB = st.lets.map (nm, kind)`; (b) a let-kind invariant
  `ArgProv senv st : ∀ k c js r kinds res, insts[k] = (c,js,r) → senv.inst c = some (kinds,res) → ∀ j a,
  js[j]? = some a → lets[a].kind = (kinds.filter nonDom)[j] ∨ ReusedAt st k j a`.
- Limit: `ReusedAt` (R1/R2) cannot be discharged inside the reader (§1.3), and the shape does not record which
  branch was taken. Even with O1/O2, (i) proves `ArgKindsAt` only on the F branch.
- Plug-in: this is the same model DGEN D2(b) uses for DG-COVER ([T] DGEN_FREEZE.md:456-460); the boundary is the
  O1/O2 one (docs/parallel/R-reader-fuel.md:35-48), stated, not trusted.

**(ii) Typing.** Kernel facts about `c args` would give `type(a_j) ≡ binder_j`. But:
- no typing judgment over `Lean.Expr` is defined (grep `HasType`/`WellTyped`/`Typing` in Tools/ and Sparkle/: none);
- `Environment` gives no "every constant is well-typed" lemma;
- R1 reads the NORMALISED body (Elab:5087-5090), so typing would also have to be preserved by `machNorm` /
  `inlFoldNat` / `rootFloat` (partial or extern pieces);
- the canonical-literal injectivity (`BitVec n ≡ BitVec m` ⇒ `n = m` for literals) is meta-level.
Hence (ii) is available only as a NEW premise, for example `EnvArgTyped env`, which says that for every
machine-read declaration of `env` `ArgKindsAt` holds and VT holds. That is a final-guarantee change (new semantic
premise), so it is not proposed here.

**(iii) Intermediate only** (do not complete FG; coverage stays open):
- (iii-a) the unsupplied Props `ArgKindsAt`/`CalleeTeleAt`, or a `T1Hyp.argw` field `∀ c, Reach c → ∀ p, P c =
  some p → ∀ k, ArgWidthAt P p k`, with an S4_WID_SUPPLY.md §4.1-style revision table before any shared change;
- (iii-b) a per-declaration decided row through a concrete `P`: `kidWsP P p k := ((P.. insts[k].1).map
  Pkg.portWidths).getD []`, the analogue of `kidOutsP` (DataBridge:66-77), and `decide (callArgsOkAt p.d p.kD k
  (kidWsP P p k))` per k. This is the form `UADAPT_RESULT.md:43` already decides.

**(iv) Compiler guard (option for a later user decision; output policy applies).**
- **G-T (reader tail):** at the tail of `machineShape?` (before :5185), check `ArgKindsAt (structEnv envR')` for
  every `.ord`/`.field` entry; on failure return `none`. Kernel-visible through an extended `machineShape?_decomp`
  (a new `ShapeDecomp` field; ShapeDecomp:58-69), so **no O1/O2 is needed for the parent half**. VT / P5-arg / ENV
  remain for the callee half.
- **G-E (emission):** in `instStmt`/`instStmtG` (Machine.lean:272-288; MachineInstG.lean:30-54), require
  `wireWidth m.wires argW == p.ty.bitWidth` per argument port (DPORT:111). With L2 (UARGW §2) and L5
  (`ChildPortWidths`, UCHILD §1) this gives PortTie and hence the row for the actually served child. **No typing,
  VT, P5-arg or ENV** is needed, but it re-proves `CallStmt`/`CallStmtG`/`closeInsts*` (wider). The output analogue
  was declined (S4_WID_SUPPLY.md:74).
- Impact of both: on well-typed sources no refusal is expected (unproved; corpus evidence only). Any refusal falls
  to legacy, which is DG-FALLBACK scope ([T] DGEN:469-470). Each needs a function check, an area/speed
  measurement and a record (compiler output policy).

**Recommendation.**
- Build now: S0 (pure) and (iii-b) as intermediate evidence.
- Do not build (i) for this row alone: it closes only the F branch.
- Bring D-ARGW (§4) to the user: (a) the typing premise, (b) G-T plus the callee-half premises, or (c) G-E. My
  recommendation for that decision is (c) G-E. It is the only option found that needs none of VT/P5-arg/ENV/typing,
  and it reuses U-ARGW-PARENT and U-CHILD-PORTTYS, which are already planned.

### 3.1 Implementation units (future children of `sparkle-gen3-data-supply`)
| unit | statement | inputs | size | deps / overlap |
|---|---|---|---|---|
| SA0 `argWidth_of_halves` | S0 | Adapt:73-83, Pkg:80-81 | 60-100 l + controls (callerL data, a mock `StructEnv`) | none |
| SA1 `kidWsP` row | (iii-b) + positive/negative/vacuous controls as DataBridgeCheck | DataBridge:66-142 | 80-120 l | intermediate; not FG |
| SA2 decision note D-ARGW | §4 options with an impact/cost table, measurement plan | this file | doc | user |
| SA3 (after D-ARGW = c) | `argWidth_of_portTie`: L2 + G-E + L5 ⇒ row | UARGW §2, UCHILD §1, new guard lemma | 150-250 l + compiler edit + re-proofs | U-ARGW-PARENT, U-CHILD-PORTTYS |
| SA3' (after D-ARGW = b) | `ShapeDecomp.argKinds` + `CalleeTeleAt` from VT/P5-arg/ENV | ShapeDecomp:58-110, P1 | 200-400 l + premises | DG-ENV ([T] DGEN:435) |
| SA4 (optional) | `ArgProv` on `machineShapeF` (F branch) | FuelProv skeleton | 300-500 l | gen5 DG-COVER reader model; O1/O2 |

## 4. Stops and decision items
- **D-ARGW (user):** how the reuse branches (R1/R2) and the callee half are closed: (a) a typing premise (FG change);
  (b) the G-T guard plus the VT/P5-arg/ENV premises; (c) the G-E emission guard. No change is applied, and none is
  started without a decision.
- ENV is not new: route it to DG-ENV and do not add a parallel premise.
- R2 audit (open): can two differently-typed source args convert (`machConv`, Elab:3888) to `==`-equal `v'`?
  This was not read. If yes, the typing premise of (a) would itself be insufficient.
- `ShapeDecomp`/`ShapeTail` headers still say UNVERIFIED (ShapeDecomp:30-50) although they are registered in the
  lakefile (:2484-2488) and imported elsewhere. Their build status was not checked here.

## 5. Not claimed
- Nothing written, elaborated or built; sizes are estimates.
- No width-mismatched successful run is exhibited, and none is claimed to exist or not to exist. "No route found" is a
  survey finding, not an impossibility proof.
- No claim that G-E/G-T never refuse on the corpus. The group path (`machInstanceS`) is covered only by the shared
  fold reading (:4100-4111).
- No change to `T1Hyp`, `ChildShips`, `DataOkB`, FG, the compiler or any shared definition.
