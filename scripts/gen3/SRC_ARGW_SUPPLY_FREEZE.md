# SRC-ARGW supply freeze rev1: connecting SA0's premises to ONE run and to the shared gen5 suppliers

**FOR REVIEW — design only, nothing built or proved.** No `.lean` file, lakefile or shared definition was written or
edited; no Lean was run. Every Lean block below is UNELABORATED text. Sizes are estimates.

## rev1 changelog (reviewer changes_requested on rev0 = be4e0b9b)
- **R1 (CR / ReadTyped telescopes).** `argWidthAt_of_closingRun` now binds `HK` and `SK` explicitly and takes
  `EqvSound HK` and `SrcKindingLaws SK` as premises (§1.2). rev0's `ReadTyped` components were prose; §3.3 now gives
  the complete telescopes of `SrcKinding`, `ConvKind` (replaces rev0 `ArgTyped`), `LetSrcKinds`, `MemSrcKinds`
  (replaces `MemArgTyped`), `CallSrcKinds`. rev0's arbitrary `bs`/`st`/`env` are removed: `bs` is the run's own
  `p.bs`; states and environments are restricted by the invariant `ReadInv` / `EnvKindOk`; expressions by `ReadSub`
  (subterms of the run's own normalised body, closed under the reader's let-floating). `TY` is run-indexed (indexed by
  `RunReadsAt`'s witnesses), not `∀ E senv`.
- **R2 (ShapeArgKinds).** rev0's "`inst` AND `instS` form at every index" is replaced by the origin-restricted
  `ArgKindsAtG` (ArgWidthSrc:140-143); LK2 produces `ArgKindsAtG` first. The conversion to the `inst`/`instS` forms is
  per origin, needs no `SigDisj`; the optional conversion to BOTH forms needs `SigDisj (structEnv envR')`
  (`sigDisj_structEnv`, Tools/ShippingReaderFuelR1.lean:87) and is stated for target entries only (§1.1). SC0's
  sufficiency is unchanged.
- **R3 (wording).** The Sort-index paragraph and D1/D3 are rephrased: a kind-indexed carrier is a useful design
  candidate; the current denotation has no supplier for type/kind agreement (not supplied). The extern `Expr.eqv`
  facts are "not supplied in this survey" (§3.5, §5). LK3 gets positive/negative controls for `uniq` on the
  permissive concat branch before the checker mirror (§3.6).
- **Order.** Revised full types of LK1 / LK2 / TY / CR are fixed first (§3.4, §1.2); §1.3 separates them from actual-run
  supply and from FG completion. New §6 "Interface requests to gen5 (R1-R3)". rev0 §6 is now §7.
- **Correction of rev0.** rev0 §3.2 said `shapePost`'s binder list is "missing on the fuel side (FRZ:206)". The fuel
  `shapePost` builds it verbatim (Tools/ShippingReaderFuelShape.lean:186-187); what is missing is a lemma: the existing
  `shapePost_decomp` (Tools/ShippingReaderFuelShapeR5.lean:318-323) exposes it only up to an existential `letB`.
- **Finding (new).** The reader converts CONSTRUCTED terms at the let-floating arms (conv Tools/ShippingReaderFuelDefs.lean:
  361-366, chain :511-515: `.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2)`), so
  "argument is a subterm of the body" is false as stated; `ReadSub` (§3.1) includes that step and `SK` needs a lift law.

Issue `sparkle-gen3-src-argw` (child of `sparkle-gen3-data-supply`). Base `par/gen2-spec` **168e0c95** (SA0/SA1 =
Tools/ShippingGen3ArgWidthSrc.lean, built at g3sb-7813bf32, header :3); rev1 written at be4e0b9b (Elab.lean and
ArgWidthSrc unchanged 168e0c95..be4e0b9b, `git diff --stat` empty). `[T]` = `~/git/.kjob/gen5-t2` at **c398021c**
(par/gen5-t2): `DGEN:` = scripts/gen5/DGEN_FREEZE.md, `M5:` = scripts/gen5/M5_INDEP_STUDIES.md, `T2C:` =
scripts/gen5/T2COVER_FREEZE.md, all at c398021c. `E:` = Sparkle/Compiler/Elab.lean. `FD:` =
Tools/ShippingReaderFuelDefs.lean, `FS:` = Tools/ShippingReaderFuelShape.lean, `FP:` = Tools/ShippingReaderFuelProv.lean.
Prior texts: scripts/gen3/SRC_ARGW_FREEZE.md rev1 (`FRZ:`), SRC_ARGW_AUDIT.md (`AUD:`).

**Rule kept from review:** a per-declaration decided row (`argWidthAt_iff_rowP`, ArgWidthSrc:226-240) is an
INTERMEDIATE check at one concrete `P`; it never counts as supply or completion. Completion = §1's target for every
successful run, with every supplier below proved (or a recorded user decision on a §5 item).

## 1. Target: `∀ k, ArgWidthAt P p k` from ONE run
Same package witnesses as `callArity_of_trace` (Tools/ShippingGen3Arity.lean:172-180: `P p k hk hnone q hP`). The run
witness is [T] `ClosingRun` (DGEN:549-571); `shared` fixes ONE `(b, ci, envR, envR', w5, w6, t, …)` (DGEN:559-571), and
its `RunReadsAt` carries `shapeEq : machineShape? false [] (entryConst true false [] ci (instancePredicate envR)
(userInliner envR) (structEnv envR)) (structEnv envR') = some p.d.shape` (M5:232-233). `P = genP env₀` (DGEN C5, :395-400).
No trace is needed for widths (`ArgWidthAt` is data-level, ArgWidthSrc:175-178); arity comes from `hA ∧ hC` (FRZ:127-134).

### 1.1 Pure core (SC0) — rev1 types
```lean
/-- (C-CORE, pure) Every ordinary call of ONE read shape. rev1: `hARG` is origin-restricted (R2). -/
theorem argWidthAt_of_read (P : Pkgs ι dom) (p : Pkg ι dom) {senv senv₀ : StructEnv}
    (hKD  : p.kD = closingNDecl p.d.shape)                                         -- KD   (§4 row KD)
    (hSIG : ShapeSigProv senv p.d.shape)                                           -- SIG  (§2)
    (hARG : ∀ k, ArgKindsAtG senv p.d.shape (closingNDecl p.d.shape) k)             -- LK2  (§3.4)
    (hENV : ∀ c q, P c = some q → SigEq senv senv₀ c)                              -- ENV  (§4)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senv₀ c q) :                       -- VT ∧ P5 (§4)
    ∀ k, ArgWidthAt P p k
-- proof sketch: `hk`, `hnone` ⇒ origin is `.ord` or `.field _` (`.mem` has `child? = some`, MachInstOrigin.lean:28-30).
-- hSIG gives `SigKindsAt senv sp k c kinds` (ArgWidthSrc:134-138). `.ord`: `ArgKindsAt` at k follows from hARG k
-- because `senv.inst c` is a function value (any `(kinds', res')` with `senv.inst c = some _` equals SIG's), then
-- argWidth_of_halves (ArgWidthSrc:91). `.field`: same with `instS` and argWidth_of_halvesS (:124). NO `SigDisj` used.
-- hC: the matching half of hTEL transported along hENV.
```
Optional conversion (only if a consumer wants BOTH forms, as rev0 stated):
```lean
theorem argKinds_both_of_G {senv : StructEnv} {sp : MachineShape} {nDecl k : Nat}
    (hD : SigDisj senv)                                    -- for senv = structEnv envR': sigDisj_structEnv (R1:87)
    (hk : k < sp.insts.length) (htgt : (sp.instOrigins.getD k .ord).child? = none)
    (hS : ∃ kinds, SigKindsAt senv sp k (sp.insts[k]).1 kinds)
    (hG : ArgKindsAtG senv sp nDecl k) :
    ArgKindsAt senv sp nDecl k ∧ ArgKindsAtS senv sp nDecl k
-- `.ord`: first conjunct as above; second is vacuous since `instS c = some _` contradicts hD with SIG's `inst c = some _`.
-- `.field`: symmetric. `.mem`: excluded by htgt.
```
Grounds for the entries the conversion does NOT cover: memory entries (`.mem`, pushed at E:3956-3958 under the name
`memChildName combo aw dw`) are not targets (`ArgWidthAt` requires `child? = none`, ArgWidthSrc:177; `.mem`'s `child?` is
`some`, MachInstOrigin.lean:28-30) and `ArgKindsAtG` is vacuous there (`SigKindsAt … .mem = False`, ArgWidthSrc:138).
Nothing is claimed about `structEnv.inst (memChildName …)`; rev0's "both forms at every index" would have needed such a
fact and is therefore dropped.

### 1.2 Run form (CR) — rev1 type (R1: HK, SK, EqvSound explicit; TY run-indexed)
```lean
/-- `ReadTyped` at the run's OWN pre-shape and normalised body (fuel side; §3.3). -/
def ReadTypedAt (HK : PhKinding) (SK : SrcKinding) (E : ConstantInfo) (senv : StructEnv) : Prop :=
  ∀ n (p : ShapePre) (en : Lean.Expr), shapePre false [] E senv = some p →        -- FS:105
    machNormF n senv p.e = some en →                                               -- FD:681
    ReadTyped HK SK senv p en

theorem argWidthAt_of_closingRun {HK : PhKinding} {SK : SrcKinding} {mref cref} (L : Laws mref cref)
    (env₀ : Environment) {Reach : Name → Prop} {mctx : Meta.Context} {cctx : Core.Context} {X : Name}
    {p : Pkg ι dom} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (cr   : ClosingRun L (genP env₀) Reach mctx cctx X p w w' raw D)
    (KD   : ∀ X p, genP env₀ X = some p → p.kD = closingNDecl p.d.shape)           -- DG-GENPKG + closingNDecl_eq_kD
    (OSH  : ShapeFuelBridge)                                                     -- §2, = DG-COVER D2(b) boundary (§6 Q5)
    (HKL  : PhKindingLaws HK)                                                    -- §3.1 (LK3)
    (EQ   : EqvSound HK)                                                         -- §3.3, D1
    (SKL  : SrcKindingLaws SK)                                                   -- §3.3 (carrier, §6 Q1)
    (TY   : ∀ b ci envR envR' w5 w6,
              RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
              ReadTypedAt HK SK (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
                (structEnv envR)) (structEnv envR'))                             -- §3.3, AT THIS RUN
    (ENV  : ∀ b ci envR envR' w5 w6, RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
              ∀ c, SigEq (structEnv envR') (structEnv env₀) c)                 -- DG-ENV (C0) at this run (§6 Q3)
    (TEL  : ∀ c q, genP env₀ c = some q → CalleeTeleAll (structEnv env₀) c q) :  -- DG-DECLCONNECT + DG-READKINDS
    ∀ k, ArgWidthAt (genP env₀) p k
-- obtain ⟨b, ci, envR, envR', w5, w6, …, hreads, …⟩ := cr.shared; shapeEq → OSH → ∃ n, machineShapeF n … = some
-- (some p.d.shape); SC1 → SIG; LK2 (with TY at these witnesses, HKL, EQ, SKL) → hARG; argWidthAt_of_read.
```
Shared definitions (src-argw side; types only reuse SA0):
```lean
def ShapeSigProv (senv : StructEnv) (sp : MachineShape) : Prop :=
  sp.instOrigins.length = sp.insts.length ∧
  ∀ k (hk : k < sp.insts.length), (sp.instOrigins.getD k .ord).child? = none →
    ∃ kinds, SigKindsAt senv sp k (sp.insts[k]).1 kinds                     -- ArgWidthSrc:134-138
def SigEq (s s₀ : StructEnv) (c : Name) : Prop := s.inst c = s₀.inst c ∧ s.instS c = s₀.instS c
def CalleeTeleAll (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  CalleeTeleAt senv c q ∧ CalleeTeleAtS senv c q                          -- ArgWidthSrc:71,105
```
`closingNDecl` is Tools/ShippingCallWidthsEntry.lean:62-63 (= E:5216's `nDecl`). rev0's `ShapeArgKinds` is withdrawn.

### 1.3 Three levels (kept distinct)
| level | what is fixed | form | counts as |
|---|---|---|---|
| L-THM (this freeze) | the TYPES of SC0, SC1, LK1, LK2, CR (§1.1, §1.2, §3.4) | conditional theorems; `HK`, `SK`, OSH, TY, ENV, TEL, KD are explicit premises | design; once proved, a conditional theorem only |
| L-RUN (actual-run supply) | TY / ENV / OSH discharged for the witnesses of ONE `ClosingRun` (e.g. one corpus declaration) | `RunReadsAt … → ReadTypedAt HK SK E_run senv_run` proved for that run | INTERMEDIATE evidence (like a decided row); not supply for FG |
| L-FG (completion) | ONE fixed `HK`, `SK`; uniform suppliers over every successful compilation under `genP env₀` | `∀ E senv sp, machineShape? false [] E senv = some sp → ReadTypedAt HK SK E senv` (restricted to successful reads, NOT rev0's unrestricted `∀ E senv`), plus OSH/ENV/TEL/KD from gen5 | the only level that counts toward SRC-ARGW completion |
CR at L-THM is not completion; an L-RUN discharge is not completion; L-FG needs all of §6's requests answered.

## 2. SIG: provenance route
- **Existing (fuel model, kernel-closed):** `machineShapeF_final_instProv` (Tools/ShippingReaderFuelShapeProv.lean:226-233)
  gives `InstProv senv st` with `shapePost … = some sp`; `InstProv` (FP:167-172) has
  `instOrigins.size = insts.size` and, per tag, `OriginT` (:149-153): `.ord` → `OrdOrigin` = `∃ kinds, senv.inst c =
  some (kinds, r)` (:89-90); `.field i` → `StructOriginI`, whose first conjunct is `senv.instS c = some (kinds, ty)`
  (:95-100). Alignment `machineShapeF_instOrigins_length` (ShapeProv:237-242) and `instOrigins_getD_eq` (:246-249).
  `sigDisj_structEnv` (Tools/ShippingReaderFuelR1.lean:87) makes `inst`/`instS` disjoint for `structEnv` (used only by
  the optional `argKinds_both_of_G`, §1.1).
- **Missing (small, src-argw):** `shapeSigProv_of_fuel : machineShapeF n sm ps ci senv ai = some (some sp) →
  ShapeSigProv senv sp` — a projection of the above (est. 60-120 l). The fuel shape's `insts` index = the stored
  `st.insts` index (`shapePost_insts`, Tools/ShippingReaderFuelShapeR1.lean:48).
- **Needs O1/O2: yes.** Production `machineShape?` is not unfolded by proofs (Tools/ShippingLetsCloseRoute.lean:16-19);
  the link is O1/O2 (docs/parallel/R-reader-fuel.md:35-48; O2 = `OldEqV`, Tools/ShippingReaderFuelVerbatim.lean:490).
  The exact Prop consumed:
  ```lean
  def ShapeFuelBridge : Prop :=
    ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
      machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)
  ```
  The driver gives the converse direction only (`driveShape_complete_le/_ge`, Tools/ShippingReaderFuelDriverComplete.lean:184-198).
- **Overlap with DG-COVER: same boundary, same model.** DG-COVER's planned route (b) proves coverage from the fuel model
  and states any O1/O2 boundary as an exact Prop (DGEN:679-683). `ShapeFuelBridge` must be THAT Prop (one statement,
  owned by `sparkle-gen5-package-coverage`, DGEN:723); SRC-ARGW must not state a parallel one (§6 Q5).

## 3. LetKindOk and the per-argument typing
### 3.1 Definitions (full text)
Placeholder conventions: E:3500-3506 (`_machIn`, `_machSlot`, `_machLet`, `_machInst`); de Bruijn closing E:4255-4263
(`_machIn i` ↦ the `i`-th input counted from the LAST of `bs`); a loose bvar past `d + env.length` becomes
`machIn (j - d - env.length)` (`convBvar`, FD:240-255).
```lean
/-- The kind each placeholder denotes in reader state `st` over peeled inputs `bs`. -/
def phKind (bs : List (Name × MixedGateBinder)) (st : MachRead) : Lean.Expr → Option MixedGateBinder
  | .fvar ⟨.num (.str .anonymous "_machIn") i⟩   => (bs.reverse[i]?).map (·.2)
  | .fvar ⟨.num (.str .anonymous "_machSlot") i⟩ => st.kinds[i]?
  | .fvar ⟨.num (.str .anonymous "_machLet") j⟩  => (st.lets[j]?).map (·.2.1)
  | .fvar ⟨.num (.str .anonymous "_machInst") k⟩ => (st.insts[k]?).map (·.2.2)
  | _ => none
/-- A kinding judgment on placeholder-form Exprs (PARAMETER; instantiation is unit LK3). -/
abbrev PhKinding := (Lean.Expr → Option MixedGateBinder) → Lean.Expr → MixedGateBinder → Prop
structure PhKindingLaws (HK : PhKinding) : Prop where
  var  : ∀ Γ e k, (phKind [] {} e).isSome ∨ (∃ x, e = .fvar x) → (HK Γ e k ↔ Γ e = some k)   -- placeholders
  uniq : ∀ Γ e k k', HK Γ e k → HK Γ e k' → k = k'                    -- kind-exact (Bool ≠ .bits 1)
  mono : ∀ Γ Γ' e k, (∀ x kx, Γ x = some kx → Γ' x = some kx) → HK Γ e k → HK Γ' e k
/-- Every stored let value has its stored kind, in the context of the SAME state (history-carrying). -/
def LetKindOk (HK : PhKinding) (bs : List (Name × MixedGateBinder)) (st : MachRead) : Prop :=
  ∀ j nm kd v, st.lets[j]? = some (nm, kd, v) → HK (phKind bs st) v kd
/-- The kinds a STATE's entry `k` was read with, by its stored tag (state version of SigKindsAt, ArgWidthSrc:134). -/
def SigKindsSt (senv : StructEnv) (st : MachRead) (k : Nat) (c : Name) (kinds : List MixedGateBinder) : Prop :=
  match st.instOrigins.toList.getD k .ord with
  | .ord     => ∃ res, senv.inst c = some (kinds, res)
  | .field _ => ∃ ty, senv.instS c = some (kinds, ty)
  | .mem ..  => False
/-- Each call entry's argument lets carry the callee's non-domain kinds, in port order (the §3.2 last column). -/
def InstArgKinds (senv : StructEnv) (st : MachRead) : Prop :=
  ∀ k c js r kinds, st.insts[k]? = some (c, js, r) → SigKindsSt senv st k c kinds →
    js.map (fun a => (st.lets[a]?).map (·.2.1)) = (kinds.filter (· != .domain)).map some
/-- THE state invariant (R1): provenance (FP:167) + let kinds + argument kinds, over the run's OWN inputs `p.bs`. -/
def ReadInv (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (st : MachRead) : Prop :=
  InstProv senv st ∧ LetKindOk HK p.bs st ∧ InstArgKinds senv st
/-- Source binder context of a reader input: one entry per enclosing binder (innermost first), its
`mixedGateBinderKind?` (E:2337-2343); `inCtx p` appends the peeled inputs. -/
abbrev SrcCtx := List (Option MixedGateBinder)
def inCtx (p : ShapePre) : SrcCtx := p.bs.reverse.map fun b => some b.2
/-- The reader's environment agrees with the source context (R1: replaces rev0's arbitrary `env`). Under `d`
lambda binders (`convBvar` returns `.bvar j` for j < d, FD:241); `.domain` entries carry no obligation. -/
def EnvKindOk (HK : PhKinding) (p : ShapePre) (st : MachRead) (Δ : SrcCtx) (env : List MachVal) (d : Nat) : Prop :=
  Δ.length = d + env.length ∧
  ∀ j k x st', d ≤ j → j < d + env.length → Δ[j]? = some (some k) → k ≠ .domain →
    convBvar env d j st = some (x, st') → HK (phKind p.bs st) x k
/-- The run's normalised root expression (the local `e` of `shapeMid`, FS:133-135). -/
def midExpr (en : Lean.Expr) : Lean.Expr :=
  machLoopAsLet (Sparkle.Compiler.MachRawSurface.rootFloat
    (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? (inlFoldNat en)))
/-- Reader inputs of ONE run (R1: replaces "every expression"): subterms of `midExpr en` with their source binder
context, CLOSED under the let-floating the reader performs on constructed terms (FD:363-366, :512-515). -/
inductive ReadSub (r : Lean.Expr) : SrcCtx → Lean.Expr → Prop
  | root : ReadSub r [] r
  | appF  {Δ f a}       : ReadSub r Δ (.app f a) → ReadSub r Δ f
  | appA  {Δ f a}       : ReadSub r Δ (.app f a) → ReadSub r Δ a
  | lamT  {Δ n t b bi}  : ReadSub r Δ (.lam n t b bi) → ReadSub r Δ t
  | lamB  {Δ n t b bi}  : ReadSub r Δ (.lam n t b bi) → ReadSub r (mixedGateBinderKind? t :: Δ) b
  | allT  {Δ n t b bi}  : ReadSub r Δ (.forallE n t b bi) → ReadSub r Δ t
  | allB  {Δ n t b bi}  : ReadSub r Δ (.forallE n t b bi) → ReadSub r (mixedGateBinderKind? t :: Δ) b
  | letV  {Δ n t v b nd} : ReadSub r Δ (.letE n t v b nd) → ReadSub r Δ v
  | letB  {Δ n t v b nd} : ReadSub r Δ (.letE n t v b nd) → ReadSub r (mixedGateBinderKind? t :: Δ) b
  | float {Δ nm ty v b nd n2 t2 v2 w nd2} : ReadSub r Δ (.letE nm ty v b nd) →
      Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2 →
      ReadSub r Δ (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2)
```
`ReadSub`'s closure is an LK1 obligation per reader arm (each arm's recursive inputs must be `ReadSub` of its input):
checked here for `convStep`'s app/lam/forallE/letE arms (FD:301-380; lam :353-356, let :361-380) and `chainStep`'s let arm (FD:511-528); NOT checked
in this survey for `regView?`, `loopView?`, `memCall?`, `machRunApp?`/`machRoot` and the `nestedProbe`/loop arms — any
of them that converts a constructed term must get its own constructor.

### 3.2 Induction over the reader's let construction (on `machineShapeF`, like `InstProv`, ShapeProv:229-233)
Push sites are exactly E:3627, :3647, :3671, :3750 (fuel: FD:378, :527, :544, FS:225-226, `machLetIndex` in
FD:422, :452); lets are never removed or rewritten. All other state growth is by push/append, so `phKind` only
extends (→ `mono`).
| case | site | ReadInv preserved from | at a call: `lets[a].kind = kinds_j` (InstArgKinds) from |
|---|---|---|---|
| F fresh push | E:3750 (fuel FD:422/:452) | `ConvKind` at `arg` with `SK` from `CallSrcKinds` (§3.3) | the push itself (kind := `kinds_j`) |
| R1 `_machLet j` | E:3746 | no push | `ConvKind` at `v' = _machLet j` + `var` ⇒ `lets[j].kind = kinds_j` |
| R2 value dedup | E:3748-3749 | no push | `LetKindOk` at `j` + `ConvKind` at `v'` + `EqvSound` (`lets[j].v == v'`) + `uniq` |
| user let push | E:3627/:3647 (kind `mixedGateBinderKind? ty`, E:3620/:3641); fuel FD:378, :527, FS:225-226 | `ConvKind` with `SK` from `LetSrcKinds`; env grows by `.val x` (EnvKindOk) | — |
| user let dedup | E:3625/:3645 (returns `_machLet j` for annotation kind `k`) | no push; EnvKindOk for `.val (machLet j)` needs `lets[j].kind = k`: `LetKindOk` + `ConvKind` + `EqvSound` + `uniq` | — |
| alias push | E:3654-3671 (stores RESOLVED `val`, kind of `y`) | `ConvKind` at `v'` + `var` along `resolve` + `LetKindOk` of the resolved lets | — |
| memory-op push | E:3956-3958 hard-coded `[.domain, .bits aw, .bits dw, .bool, .bits aw]` | `ConvKind` with `SK` from `MemSrcKinds` | not a target (`SigKindsSt … .mem = False`), but a source of R2 kinds (AUD A6) |
| loop-root state | FD:368-369 / :517-518 (`cLoopRoot`, env grows by `.state b n`) | EnvKindOk at a `.state b 1` entry needs slot kind = annotation kind: NOT in §3.3, listed as LK1-open | — |
| domain arg | E:4065-4068 / :4104-4107 | no push, no index | no obligation (`Pkg.ports` drops `.domain`, Tools/ShippingGen2Pkg.lean:80-81) |
**Provable from existing facts:** the R1 and domain cases, the push/no-push bookkeeping, `mono`-transport, the alias
`resolve` induction, the `InstProv` conjunct (existing, ShapeProv:226-233). **Not:** every case that uses `ConvKind`,
`*SrcKinds` or `EqvSound`; the loop-root row.

### 3.3 What remains (exact Props; R1 full telescopes)
```lean
/-- Source kinding of a pre-conversion Expr in source context Γ (PARAMETER; its instance is the carrier, §6 Q1). -/
abbrev SrcKinding := SrcCtx → Lean.Expr → MixedGateBinder → Prop
structure SrcKindingLaws (SK : SrcKinding) : Prop where
  bvar : ∀ Γ j k, SK Γ (.bvar j) k → Γ[j]? = some (some k)
  uniq : ∀ Γ e k k', SK Γ e k → SK Γ e k' → k = k'
  lift : ∀ Γ e k o, SK Γ e k → SK (o :: Γ) (e.liftLooseBVars 0 1) k      -- needed by ReadSub.float
/-- (TY-1, replaces rev0 ArgTyped) conversion keeps the kind, from a REACHED configuration only. -/
def ConvKind (HK : PhKinding) (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (n : Nat) (Δ : SrcCtx) (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead)
    (k : MixedGateBinder) (v' : Lean.Expr) (st' : MachRead),
    ReadInv HK senv p st → EnvKindOk HK p st Δ env d → ReadSub (midExpr en) Δ e →
    k ≠ .domain → SK (Δ ++ inCtx p) e k →
    readF senv n (.conv env d e st) = some (some (v', st')) → HK (phKind p.bs st') v' k
/-- (TY-2, replaces rev0 LetTyped's source half) annotated lets of the run's body have their annotation kind. -/
def LetSrcKinds (SK : SrcKinding) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (Δ : SrcCtx) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (k : MixedGateBinder),
    ReadSub (midExpr en) Δ (.letE nm ty v b nd) → mixedGateBinderKind? ty = some k → k ≠ .domain →
    SK (Δ ++ inCtx p) v k
/-- (TY-3) at every call node of the run's body, each non-domain argument has the callee's kind (E:3721-3740). -/
def CallSrcKinds (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  (∀ (Δ : SrcCtx) (e : Lean.Expr) (c : Name) (kinds : List MixedGateBinder) (res : MixedGateBinder)
      (args : List Lean.Expr) (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub (midExpr en) Δ e → machInstCall? senv e = some (c, kinds, res, args) →
    (kind, arg) ∈ kinds.zip args → kind ≠ .domain → SK (Δ ++ inCtx p) arg kind) ∧
  (∀ (Δ : SrcCtx) (e : Lean.Expr) (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr)
      (args : List Lean.Expr) (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub (midExpr en) Δ e → machInstCallS? senv e = some (c, kinds, ty, args) →
    (kind, arg) ∈ kinds.zip args → kind ≠ .domain → SK (Δ ++ inCtx p) arg kind)
/-- (TY-4, replaces rev0 MemArgTyped) memory operands have the hard-coded kinds at the `aw`/`dw` the recogniser
returned (E:3953-3958); `natOf`/`kernelNat` correctness is folded into this one obligation. -/
def MemSrcKinds (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (Δ : SrcCtx) (e : Lean.Expr) (combo : Bool) (aw dw : Nat) (dom : Lean.Expr) (ops : List Lean.Expr)
    (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub (midExpr en) Δ e →
    Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) e =
      some (combo, aw, dw, dom, ops) →
    (kind, arg) ∈ [MixedGateBinder.bits aw, .bits dw, .bool, .bits aw].zip ops → SK (Δ ++ inCtx p) arg kind
def ReadTyped (HK : PhKinding) (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ConvKind HK SK senv p en ∧ LetSrcKinds SK p en ∧ CallSrcKinds SK senv p en ∧ MemSrcKinds SK senv p en
/-- §5 D1; a SEPARATE premise of LK1/LK2/CR (R1), not part of ReadTyped. -/
def EqvSound (HK : PhKinding) : Prop :=
  ∀ a b : Lean.Expr, (a == b) = true → ∀ Γ k, HK Γ a k ↔ HK Γ b k
```
- Every obligation is indexed by the run's own `(senv, p, en)` (via `ReadTypedAt`, §1.2), its states by `ReadInv`, its
  environments by `EnvKindOk`, its expressions by `ReadSub (midExpr en)`. LK1 (§3.4) proves that every configuration
  the reader issues from the run's start satisfies these (GoodP pattern, FP:471-479), so the obligations are consumed
  only at reached configurations; a supplier never has to cover an arbitrary `st`/`env`/`bs`.
- `ConvKind` is the ONLY place where the callee kind meets the converted value (rows F/R1/R2); `*SrcKinds` are pure
  source facts about the run's body.
- Through normalisation (`machNorm`/`inlFoldNat`/`zeroLit`/`rootFloat`, E:5088-5090) source kinding must hold of the
  NORMALISED body (`midExpr en`); relating it to `ci.value` is the carrier's job (§6 Q1; FRZ:236 item 2; `natOf`
  literal injectivity FRZ:237-238).

### 3.4 Revised full types of LK1 / LK2 (fixed first, R1/R2)
```lean
/-- The call precondition carried through the table (fuel model): each Call's expression components are reader
inputs of THIS run with a matching environment. -/
def CallPreK (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Call → Prop
  | .conv env d e st          => ∃ Δ, EnvKindOk HK p st Δ env d ∧ ReadSub (midExpr en) Δ e
  | .nested env dom αs is b st => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub (midExpr en) Δ dom ∧
                                   ReadSub (midExpr en) Δ is ∧ ReadSub (midExpr en) (none :: Δ) b
  | .inst env c org ks r args st => CallPreP senv (.inst env c org ks r args st) ∧
                                   ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ∀ a ∈ args, ReadSub (midExpr en) Δ a
  | .instS env c ks ty args st => senv.instS c = some (ks, ty) ∧
                                   ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ∀ a ∈ args, ReadSub (midExpr en) Δ a
  | .chain env e st           => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub (midExpr en) Δ e
  | .loopBody _ env e st      => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub (midExpr en) Δ e
  | .loopRoot env e st        => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub (midExpr en) Δ e
def GoodK (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) (h : Hs) : Prop :=
  ∀ c, CallPreK HK senv p en c → ReadInv HK senv p (Call.inSt c) → ∀ v, h c = some (some v) →
    ReadInv HK senv p (Call.outSt c v)

/-- LK1 (table form). -/
theorem goodK_readF {HK SK} (HKL : PhKindingLaws HK) (SKL : SrcKindingLaws SK) (EQ : EqvSound HK)
    {senv p en} (TY : ReadTyped HK SK senv p en) : ∀ n, GoodK HK senv p en (readF senv n)
/-- LK1 (run form): the FINAL state of a successful fuel read satisfies ReadInv. -/
theorem machineShapeF_final_readInv {HK SK} (HKL : PhKindingLaws HK) (SKL : SrcKindingLaws SK) (EQ : EqvSound HK)
    {n E senv sp} (h : machineShapeF n false [] E senv true = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre false [] E senv = some p ∧ machNormF n senv p.e = some en ∧
      shapePost true p (shapeMid senv p en) st v = some sp ∧
      (ReadTyped HK SK senv p en → ReadInv HK senv p st)
/-- LK2: the origin-restricted argument kinds at the closing index (R2; ArgKindsAtG, ArgWidthSrc:140). -/
theorem argKindsG_of_machineShapeF {HK SK} (HKL : PhKindingLaws HK) (SKL : SrcKindingLaws SK) (EQ : EqvSound HK)
    {n E senv sp} (h : machineShapeF n false [] E senv true = some (some sp))
    (TY : ReadTypedAt HK SK E senv) : ∀ k, ArgKindsAtG senv sp (closingNDecl sp) k
-- from ReadInv's InstArgKinds at the final st, `shapePost_instOrigins` (ShapeR5:343), `shapePost_insts`
-- (ShapeR1:48), and a NEW `shapePost_binders` (letB = st.lets.toList.map (nm, kind), FS:186-187; `shapePost_decomp`,
-- ShapeR5:318-323, leaves letB existential) plus `closingNDecl sp = p.bs.length` and slot-count bookkeeping
-- (`machineShapeF_binderCount`, ShapeR5:497).
```

### 3.5 Carrier and the Bool / width question (R3 rephrased)
- **Relation to DC-FORM `ExprDenotes env e α v` (DGEN:448-450):** `CallSrcKinds`/`LetSrcKinds`/`MemSrcKinds` are
  per-node typing consequences one would want from `ExprDenotes` at the run's body. With a `Sort`-indexed `α`, the
  needed fact `α = Signal d (BitVec n) → α = Signal d (BitVec m) → n = m` (and Bool vs `BitVec 1`) is not delivered by
  the index automatically. This does NOT show that the widths cannot be distinguished; it only says the current
  denotation has no supplier for type/kind agreement (**not supplied**). A KIND-indexed carrier (e.g.
  `ExprDenotesK env Γ e (k : MixedGateBinder) v`, with `SK Γ e k := ∃ v, ExprDenotesK env Γ e k v`) is a useful design
  candidate, because `SrcKindingLaws` would then be read off its rules. Requested for consultation (§6 Q1); not
  formulated here.
- **Bool vs `.bits 1`.** The row compares widths only (`kindTy .bool` and `.bits 1` both width 1, AUD A10), so the row
  is weaker than kind equality. `LetKindOk`/`SK` are stated KIND-exact on purpose: the compiler's gate check separates
  them (`mixedBitKinds` maps `.bool` to `.domain`, E:2355-2359; `unifiedGateBoolBody` vs `…BitsBody`, E:2521/:2560),
  and `uniq` would be false for a width-only `HK`. The final step uses only `(kindTy ·).bitWidth` (ArgWidthSrc:69).
- **Run-side partial source (finding, unchanged).** `unifiedGateRoot` (E:2619, fuel FS:188) checks the packed body,
  i.e. each let field at its kind (`machField`, E:4298-4301). With `HK :=` a placeholder mirror of `unifiedGate*Body`
  (LK3) this could supply `LetKindOk` at the FINAL state, but only where the concat arm checks operands: its
  `none => true` branches skip them (E:2609-2610; Tools/ShippingUnifiedExecutionSoundness.lean:40-49;
  Tools/ShippingLetsCloseRoute.lean:20). It never supplies `ConvKind` (the callee kind is not in the packed body).

### 3.6 LK3 controls BEFORE the checker mirror (R3)
Planned as small Lean tests (like Tests/Gen3/ArityCheck.lean), run before the mirror `HK` is written; none built yet.
- **P1 (positive, permissive branch):** `concatE dom m n a b` (ShippingUnifiedExecutionSoundness.lean:42-49) with
  `sixArgShape? = some (r, none, none)`: `HK Γ e (.bits r)` holds while `a`, `b` are unkinded; check that
  `HK Γ e (.bits r')` (r' ≠ r) and `HK Γ e .bool` are both FALSE, i.e. `uniq` survives the `none => true` branch.
- **P2 (positive, width-1):** an Expr accepted at `.bits 1` (e.g. a 1-bit concat / slice) is not accepted at `.bool`,
  and a Bool gate body is not accepted at `.bits 1`.
- **N1 (negative control of the control):** a deliberately broken mirror whose concat arm returns `true` without the
  `w == r` test; the P1 check must FAIL on it (shows the control detects a non-unique `HK`).
- **N2 (negative):** an operand position under `none => true` holding a `_machLet j` of the wrong kind; record whether
  the mirror accepts it (expected: accepted), documenting that the mirror does NOT supply `LetKindOk` for operands
  under that branch (consistent with §3.5).
Outcome rule: if P1 or P2 fails, `uniq` does not hold for the mirror and LK3 stops with a report (no `HK` adopted).

## 4. VT / P5 / ENV / KD: consumed from gen5, not duplicated
| SRC-ARGW need | exact Prop consumed | gen5 unit (owner issue) | what is still to request |
|---|---|---|---|
| ENV | `∀ c, SigEq (structEnv envR') (structEnv env₀) c` at THIS run's `envR'` (RunReadsAt, DGEN:540-541; read at M5:221) | DG-ENV / C0 `ReadsAt env₀` (DGEN:315-328, row :654) — `sparkle-gen5-reader-bridge` (DGEN:722) | C0 states only `find?` inclusion "plus equal … structEnv" as a comment (DGEN:319); `instSignature?` also reads `isHardwareModule` (E:4375, :4386), so the `structEnv`/`inst`/`instS` equality must be in C0's text, at every world of the run (the second `getEnv`, M5:221) (§6 Q3) |
| VT | `adapterOf ci.type (structEnv env₀) q.d = some _` for each callee (existence conjunct of `DeclConnect`, DGEN:470-476) + a width projection `adapterOf_portWidths` | DG-DECLCONNECT / DC-SUPPLY — `sparkle-gen5-decl-bridge` (DGEN:725) | `SigAdapter` exposes only `toSig` (DGEN:465-466); the `args` map (DGEN:458) must be data or have a lemma (§6 Q2) |
| P5-arg | peel kinds of `packTupleInputs (inl value)` (E:5078, E:3410) = `telescopeKinds ci.type` (E:4367-4369) for a callee with `instSignature? = some` | DG-READKINDS total `packTupleInputs` (DGEN:303-309, row :646) — `sparkle-gen5-reader-bridge` | the property "identity on binders with `mixedGateBinderKind? ≠ none`" and the inliner's type invariance (`inlinedConst` rewrites the type too, E:3410); DG-READKINDS does not state it (AUD B row 3) (§6 Q4) |
| q's shape | `genP env₀ c = some q` ⇒ `q.d.shape` = `machineShape? false [] (entry₀ env₀ c) (structEnv env₀)` | C1/C3/C5 `genS_some_inv`, `genP` (DGEN:330-336, :369-374, :395-400) — `sparkle-gen5-package-coverage` | `Pkg.d (genPkg s _) = s.d` (DG-GENPKG) |
| KD | `p.kD = closingNDecl p.d.shape` for generated packages | DG-GENPKG + missing `closingNDecl_eq_kD` (scripts/gen2/S4_CONSUMER_FREEZE.md:510-512) | — |
| SigDisj (optional) | `SigDisj (structEnv envR')` | existing `sigDisj_structEnv` (R1:87) | — (only for `argKinds_both_of_G`) |
The callee half is STATIC in `env₀`: with `P = genP env₀`, `q` is computed from `env₀` (DGEN:330-336), not from the
callee's own run, so ENV is needed only for the parent's `structEnv envR'`.

## 5. Units, order, STOP/decision items
| unit | statement | inputs | size (est.) | deps | owner |
|---|---|---|---|---|---|
| SC0 | defs §1 + `argWidthAt_of_read` (G form) + optional `argKinds_both_of_G` | SA0 (ArgWidthSrc:91,124,134-143), `sigDisj_structEnv` | 100-180 l | — | src-argw child |
| SC1 | `shapeSigProv_of_fuel` | ShapeProv:226-249, FP:89-172 | 60-120 l | — | src-argw child |
| LK0 | §3.1 defs (`phKind`, laws, `LetKindOk`, `InstArgKinds`, `ReadInv`, `EnvKindOk`, `ReadSub`) + init/extension lemmas | MachRead E:3563-3600, FD:240-255 | 150-250 l | — | src-argw child |
| LK1 | `goodK_readF` + `machineShapeF_final_readInv` (§3.4), incl. `ReadSub` closure per arm | FD:301-607, FP:471-479 pattern | 400-800 l | LK0 | src-argw child |
| LK2 | `shapePost_binders` + `argKindsG_of_machineShapeF` | FS:153-205, ShapeR5:318-363 | 150-300 l | LK1 | src-argw child |
| LK3 | §3.6 controls first; then `HK` instantiation (mirror of `unifiedGate*Body`) + `PhKindingLaws` | E:2521-2633 | 200-400 l | LK0 | src-argw child |
| TY | `ReadTypedAt HK SK` for every successful read (L-FG, §1.3); `SrcKindingLaws SK` | carrier (§6 Q1) | unknown, likely ≥ 1000 l | §6 Q1 | src-argw child; carrier = decl-bridge |
| CR | `argWidthAt_of_closingRun` (§1.2) | `ClosingRun` (DG-CLOSINGRUN), SC0-LK3 | 100-200 l | DG-CLOSINGRUN | src-argw child |
| (consumed) | OSH, ENV, VT, P5, q-shape, KD | §2, §4 | — | — | package-coverage / reader-bridge / decl-bridge |
**Order:** SC0 → SC1 ∥ LK0 → LK3 (controls first) ∥ LK1 → LK2 → CR (CR conditional on consumed Props, explicit as
premises until they land); TY after §6 Q1 is answered. Controls (like Tests/Gen3/ArityCheck.lean): expected-type
comparison and meaning-changing mutants for SC0/SC1/LK2; decided rows on a corpus `P` are intermediate evidence only.

**STOP / decision items (options only; none adopted):**
- **D1 `Expr.eqv` soundness** (`EqvSound`; R2 branch E:3748, user-let dedups E:3625/:3645/:3669). `==` on
  `Lean.Expr` is the extern `Expr.eqv` (`@[extern "lean_expr_eqv"] opaque`, Tools/ShippingReaderMatcherArity.lean:36-40;
  the existing file carries a premise about it, not proved and not assumed, :488-490; same in the fuel model,
  R-reader-fuel.md:55-57). The facts `EqvSound` needs are **not supplied in this survey**. Options seen (not a complete
  list, none adopted): (a) a law on the extern = new TRUSTED boundary (user item); (b) compiler change to a
  kernel-visible comparison in the dedups (output policy: function check, area/speed, record); (c) none → R2/dedup
  rows stay unsupplied. Impact: without a supplier, the R2 and dedup rows of §3.2 do not close.
- **D2 O1/O2** (`ShapeFuelBridge`): not new; shared with DG-COVER D2 (DGEN:679-693). No separate SRC-ARGW decision.
- **D3 kind/type agreement supplier**: if DC-FORM's denotation keeps a `Sort` index and no supplier for type/kind
  agreement is found, `TY` has no carrier; then a report with options (kind-indexed refinement as in §3.5 vs. a typing
  assumption = guarantee change, FRZ:230-231) goes to the user. Not adopted.
- **D4 VT elaboration shape**: the kernel gives only defeq of value-binder and type-binder types; the syntactic
  agreement `mixedGatePeel` (E:2345-2350) vs `telescopeKinds` (E:4367-4369) (count and literal widths) is a fact of
  elaboration. If `adapterOf` (§6 Q2) does not supply it, options: a reader-tail check (G-T, FRZ:268-270; compiler
  change) or a law. Not adopted.
- D-ARGW stays HELD (FRZ:300-302); G-E/G-T remain comparison material (AUD §C/§D).

## 6. Interface requests to gen5 (R1-R3) — REQUESTS FOR CONSULTATION
None of these approves a new TRUSTED boundary, a guarantee change, or a production/compiler change. They ask the
owner issues (DGEN:722-725) whether the stated Prop can be part of their deliverable; the answer may be "no".
- **Q1 → `sparkle-gen5-decl-bridge` (DC-FORM carrier; R1/R3).** Is a kind-indexed carrier (`ExprDenotesK env Γ e k v`,
  or a lemma family from `ExprDenotes`, DGEN:448-450) in DC-FORM's scope, such that `SK Γ e k := ∃ v, ExprDenotesK …`
  satisfies `SrcKindingLaws` (§3.3: `bvar`, `uniq` incl. Bool ≠ `.bits 1`, `lift`) and yields `LetSrcKinds`,
  `CallSrcKinds`, `MemSrcKinds` on the NORMALISED body `midExpr en` of every successful read? If DC-FORM keeps the
  `Sort` index, which agreement supplier (if any) does it plan? (D3.)
- **Q2 → `sparkle-gen5-decl-bridge` (VT).** The exact text of
  `adapterOf_portWidths : adapterOf ci.type senv q.d = some _ → telescopeKinds ci.type = some ks →
   (ks.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = q.portWidths`
  (or `SigAdapter.args` as data, DGEN:458/:465-467), to supply `CalleeTeleAll` (§1.2 TEL) with `senv := structEnv env₀`.
- **Q3 → `sparkle-gen5-reader-bridge` (C0 / DG-ENV).** C0's text (DGEN:318-319) to include, at EVERY world `w` of the
  run (incl. the second `getEnv`, M5:221), `∀ c, SigEq (structEnv (envAt cref w)) (structEnv env₀) c` (i.e. `inst` and
  `instS` equal), not only `find?` inclusion; `instSignature?` also reads `isHardwareModule` (E:4375, :4386).
- **Q4 → `sparkle-gen5-reader-bridge` (DG-READKINDS).** The `packTupleInputs` property "identity on binders with
  `mixedGateBinderKind? ≠ none`" plus the inliner's type invariance (E:3410, E:5078), for P5-arg (§4).
- **Q5 → `sparkle-gen5-package-coverage` (DG-COVER D2(b)).** `ShapeFuelBridge` (§2) as ONE shared Prop, written and
  owned there (DGEN:679-683, :723); SRC-ARGW imports it and states no parallel version.

## 7. Not claimed
- Nothing written in Lean, elaborated or built; all texts are proposals; sizes are estimates.
- No claim that `ShapeFuelBridge`, `ReadTyped` (any component), `SrcKindingLaws`, `EqvSound`, VT or P5 hold, are
  provable, or are unprovable; "not supplied" means only that this survey found no supplier.
- No claim that `HK`'s `uniq` holds for the mirror of `unifiedGate*Body` (§3.6 is the planned check), nor that
  `unifiedGateRoot` supplies `LetKindOk`.
- `ReadSub` closure is checked only for the arms listed in §3.1; the loop-root row of §3.2 is open.
- No width-mismatched successful run is exhibited or excluded. No change to `T1Hyp`, `ChildShips`, `DataOkB`, FG,
  the compiler, or any gen5 freeze; owners/requests above are proposals for review.
