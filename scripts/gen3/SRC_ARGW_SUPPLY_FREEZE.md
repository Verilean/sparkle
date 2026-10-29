# SRC-ARGW supply freeze rev2: connecting SA0's premises to ONE run and to the shared gen5 suppliers

**FOR REVIEW — design only, nothing built or proved.** No `.lean` file, lakefile or shared definition was written or
edited; no Lean was run. Every Lean block below is UNELABORATED text. Sizes are estimates.

## rev3 changelog (batch 2 STOP; written at e134c63a, FOR REVIEW, nothing adopted)
- **New §3.7 (EnvKindOk / CallPreK / GoodK revision proposal).** Batch 2 (Tools/ShippingGen3ArgSupply2.lean, built
  clean in g3se-e134c63a) stopped at every arm that issues a second sub-call at the state `st₁` returned by a first
  one (ArgSupply2:42-53): rev2's `EnvKindOk` is read through `convBvar … st`, whose `.state b n` (n ≠ 1) arm reads
  `st.dom`/`st.kinds` (FD:245-253), so (i) `st.dom = none` → `st₁.dom = some _` creates an obligation and (ii) `dom`
  can be replaced by an `==`-equal but different term (`domGuard` FD:314 then `dom := some dom'` FD:318; also
  FD:572/:585, E:3708-3716 via FD:405). §3.7 gives three options with full types and recommends (b): an
  entry-indexed, `dom`-free `EnvKindOkE` plus an unconditional table invariant `GoodE` (state extension). No new
  premise of CR; no use of `EqvSound` for `dom`; G12/G20 stay the (unchanged) open loop-root row.
- **LK3 control results recorded (§3.7.5).** P1 and P2 PASS, N1 detects non-uniqueness; N2 came out
  `accepted = false` (rev2 §3.6 expected "accepted": that expectation was wrong). rev2's P1 case
  `sixArgShape? = some (r, none, none)` does not exist (E:1538-1548); P1 ran on the three one-`none` arms.
  rev2 §3.6 text is left as written; §3.7.5 supersedes its N2 expectation and P1 case.

## rev2 changelog (reviewer changes_requested on rev1 = d795c916; written at 4c770207, re-checked at f7e42988)
Sources re-read at 4c770207: `git diff --stat 168e0c95..f7e42988 -- Sparkle/Compiler/ Tools/ShippingReaderFuel*.lean
Tools/ShippingGen3ArgWidthSrc.lean` is empty, so every rev1 line citation into those files still holds.
- **V1 (MAIN, CallPreK keeps the call site).** rev1's `.inst`/`.instS` rows of `CallPreK` kept only "each arg is
  `ReadSub`"; since `GoodK` quantifies over ARBITRARY `CallPreK` calls, `instStep`'s let pushes could not be tied back to
  `CallSrcKinds`/`MemSrcKinds` (those are stated at the call EXPRESSION `e` and the recogniser's success). rev2's
  `CallPreK` (§3.4) carries, for `.nested`/`.inst`/`.instS`, an existential call expression `e` with `ReadSub r Δ e`, the
  SAME `Δ`/`env`/`st` as `EnvKindOk`, and the recogniser equation (`machRunApp?`, `machInstCall?`, `memCall?` with the
  hard-coded kinds, `machInstCallS?`), via the new `InstSite`. Argument lengths come from the recogniser
  (E:3727, :3738; `memCall?` returns 4 ops, Sparkle/Compiler/MachMemory.lean:38). The alternative (SK facts directly in
  `CallPreK`) is given as a full type too (§3.4, `CallPreK'`), not chosen.
- **V2 (ReadInv / EnvKindOk are not reachability).** `ConvKind` is a conditional claim over EVERY configuration satisfying
  `ReadInv ∧ EnvKindOk ∧ ReadSub` — a superset of the reached configurations. rev1's "from a REACHED configuration
  only" and "consumed only at reached configurations" are withdrawn (§3.3). A reachability-indexed variant is given
  as an optional candidate (`SubCallK`/`ReachedK`, §3.4), not chosen.
- **V3 (whole GoodK obligation).** New §3.4 table lists every arm of `step` (FD:597-604) with its GoodK obligation and
  status; the loop-root row and the arms not audited by §3.2 (bare register, slot reads, nested/`machReserve`, loop
  root kinds, generic-app rebuild, default arm, `instSParam`, named/alias pushes) are explicitly OPEN there.
- **V4 (ReadSub closure re-checked at every recursive call site).** Finding: in BOTH let arms the non-let branch
  `| v =>` re-binds `v := rootFloat v` (E:3990-3994, :4155-4159; FD:363-367, :512-516), and `rootFloat` is `partial`
  (Sparkle/Compiler/MachRawSurface.lean:198) hence opaque in the fuel model (FD:66-68). rev1's `ReadSub` had no
  constructor for that input. rev2 adds `floatV`, `sparam` (instSStep's params come from the CONSTRUCTED
  `instRes ty args`, FD:266-269, :474) and generalises `SrcKindingLaws.lift` to an arbitrary insertion depth (the float
  lifts `b` at depth 1). Closure table §3.1 covers every call site of FD:301-590 and the start calls FS:207-241
  (checked / open).
- **V5 (L-FG).** The uniform `∀ E senv sp, machineShape? … = some sp → ReadTypedAt …` is now labelled a STRONGER
  candidate sufficient condition (L-FG+), not a requirement. Completion needs TY only at the actual runs FG ranges over
  (CR's `TY` premise, discharged for every `ClosingRun`); `HK`/`SK` may even be chosen per run, since CR's conclusion
  does not mention them (§1.3, §5 TY row, §6 Q1).
- New decision item D5 (`rootFloat` opacity, §5). §6 Q1 wording aligned with V4/V5; no other §6 change.

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
Tools/ShippingGen3ArgWidthSrc.lean, built at g3sb-7813bf32, header :3); rev1 written at be4e0b9b, rev2 at 4c770207 (Elab.lean and
ArgWidthSrc unchanged 168e0c95..4c770207, `git diff --stat` empty). `[T]` = `~/git/.kjob/gen5-t2` at **c398021c**
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

### 1.3 Levels (kept distinct; rev2 V5)
| level | what is fixed | form | counts as |
|---|---|---|---|
| L-THM (this freeze) | the TYPES of SC0, SC1, LK1, LK2, CR (§1.1, §1.2, §3.4) | conditional theorems; `HK`, `SK`, OSH, TY, ENV, TEL, KD are explicit premises | design; once proved, a conditional theorem only |
| L-RUN1 (one concrete run) | TY / ENV / OSH discharged for the witnesses of ONE concrete `ClosingRun` (e.g. one corpus declaration) | `RunReadsAt … → ReadTypedAt HK SK E_run senv_run` proved for that run | INTERMEDIATE evidence (like a decided row); not supply for FG |
| L-FG (completion) | suppliers for EVERY run FG quantifies over: for each `cr : ClosingRun L (genP env₀) …`, some `HK`, `SK` with `PhKindingLaws HK`, `EqvSound HK`, `SrcKindingLaws SK` and CR's `TY` at that run's own `RunReadsAt` witnesses; plus OSH/ENV/TEL/KD from gen5 | a theorem `∀ … (cr : ClosingRun …), ∃ HK SK, (laws) ∧ TY-at-cr` (or one fixed `HK`/`SK`, e.g. LK3's mirror, if that is what the proof gives); the supplier MAY use any fact of the actual run (its `RunReadsAt`, `shapeEq`, the trace) | the level that counts toward SRC-ARGW completion |
| L-FG+ (stronger candidate, optional) | one fixed `HK`, `SK`; uniform over every successful fuel/production read | `∀ E senv sp, machineShape? false [] E senv = some sp → ReadTypedAt HK SK E senv` | a SUFFICIENT condition for L-FG (it implies TY at every run through `shapeEq`), not a required one; a failure to prove L-FG+ does not block completion |
CR at L-THM is not completion; an L-RUN1 discharge is not completion. L-FG does not require L-FG+: the existential
`∃ HK SK` per run is allowed because `argWidthAt_of_closingRun`'s conclusion (`∀ k, ArgWidthAt (genP env₀) p k`) does
not mention `HK`/`SK` (§1.2). Whatever is not answered among §6's requests stays an explicit premise of L-FG.

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
context, CLOSED under the terms the reader CONSTRUCTS and then reads (rev2 V4: `float`, `floatV`, `sparam`).
rev2: indexed by `senv` because `sparam` mentions `machInstCallS? senv`. -/
inductive ReadSub (senv : StructEnv) (r : Lean.Expr) : SrcCtx → Lean.Expr → Prop
  | root : ReadSub senv r [] r
  | appF  {Δ f a}       : ReadSub senv r Δ (.app f a) → ReadSub senv r Δ f
  | appA  {Δ f a}       : ReadSub senv r Δ (.app f a) → ReadSub senv r Δ a
  | lamT  {Δ n t b bi}  : ReadSub senv r Δ (.lam n t b bi) → ReadSub senv r Δ t
  | lamB  {Δ n t b bi}  : ReadSub senv r Δ (.lam n t b bi) → ReadSub senv r (mixedGateBinderKind? t :: Δ) b
  | allT  {Δ n t b bi}  : ReadSub senv r Δ (.forallE n t b bi) → ReadSub senv r Δ t
  | allB  {Δ n t b bi}  : ReadSub senv r Δ (.forallE n t b bi) → ReadSub senv r (mixedGateBinderKind? t :: Δ) b
  | letV  {Δ n t v b nd} : ReadSub senv r Δ (.letE n t v b nd) → ReadSub senv r Δ v
  | letB  {Δ n t v b nd} : ReadSub senv r Δ (.letE n t v b nd) → ReadSub senv r (mixedGateBinderKind? t :: Δ) b
  /-- let arm, `rootFloat v` is a `let` (FD:363-366, :512-515; E:3990-3993, :4155-4158). -/
  | float {Δ nm ty v b nd n2 t2 v2 w nd2} : ReadSub senv r Δ (.letE nm ty v b nd) →
      Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2 →
      ReadSub senv r Δ (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2)
  /-- rev2 V4: let arm, non-let branch: `| v =>` RE-BINDS `v := rootFloat v` (FD:367, :516; E:3994, :4159); the
  loop root, `machTailV`/`machHandleV` tests and `cConv env 0 v` all see `rootFloat v`, not the source value.
  `rootFloat` is `partial` (MachRawSurface.lean:198) = opaque here (FD:66-68), so `rootFloat v = v` for a non-let
  result is NOT derivable (by reading MachRawSurface.lean:199-207 every changing arm returns a `.letE`, but that is
  a meta reading). The constructor is stated for any result shape (over-approximation; it only adds obligations). -/
  | floatV {Δ nm ty v b nd} : ReadSub senv r Δ (.letE nm ty v b nd) →
      ReadSub senv r Δ (Sparkle.Compiler.MachRawSurface.rootFloat v)
  /-- rev2 V4: `instSStep` converts the parameters of the CONSTRUCTED result type `instRes ty args`
  (FD:266-269, :472-474; `ty` from `senv.instS c`, instantiated with the call's arguments). -/
  | sparam {Δ e c ks ty args resTy q} : ReadSub senv r Δ e →
      machInstCallS? senv e = some (c, ks, ty, args) → instRes ty args = some resTy →
      q ∈ resTy.getAppArgs.toList → ReadSub senv r Δ q
```
**Closure table (rev2 V4): every recursive call site of the block (FD:301-590) and every start call of the wrapper
(FS:207-241).** "checked" = the call's input is `ReadSub senv (midExpr en) Δ' _` for the context `Δ'` the call
needs, by the listed constructors and the recogniser text cited (each such step is a small LK1 lemma, e.g.
`inlSpine` arguments are iterated `appF`/`appA` subterms, E:3081-3083). "open" = an obligation outside `ReadSub`
(listed again in §3.4's GoodK table). Context: a new env entry `.regs`/`.handle`/`.unit` makes `convBvar` fail
(FD:254, `some _ => none`), so its `Δ` entry carries no `EnvKindOk` obligation; `.val x` is the user-let row
(§3.2); `.state b 1` is the loop-root row.
| # | site | input converted | derivation | status |
|---|---|---|---|---|
| S1 | `shapeStart` FS:207-211 (conv :210) | `dom` of `m.run?` | `machRoot` peels root lets (`letB`*, E:4416) and optionally one projection with its inner lets (`appA` then `letB`*, E:4419-4427); then `machRunApp?` = `inlSpine` args (E:3675-3679); wrap case: `getAppArgs.back?` = `appA` (FS:146-148) | checked |
| S2 | `shapeRootLet` FS:215-228 (:220, :224) | root-let value `v` (no `rootFloat` here) to `wLoopRoot`/`wConv` | `letV` along S1's `letB` chain | checked |
| S3 | `shapeBody` FS:235 | run body, env `.regs 0 :: env` | `lamB` of `machRunApp?`'s last arg (E:3677) | checked |
| S4 | `shapeBody` FS:240-241 | `m.root` | S1's chain end | checked |
| C1 | `convStep` bare register FD:305-320 (:313, :320) | `dom`, `x` | `regView?` args (FD:259-262) = `appF`*/`appA` | checked (kind of the pushed slot: open, §3.4 G2) |
| C2 | `convStep` → `cNested` FD:326-328 | call `(.app f a)` | `CallPreK` keeps `e` + `machRunApp?` witness (§3.4) | checked |
| C3 | `convStep` → `cInst .ord` FD:330-332 | call `(.app f a)` | witness `machInstCall?` (E:3721-3730) in `InstSite` | checked |
| C4 | `convStep` → `cInstS` FD:334-336 | call `(.app f a)` | witness `machInstCallS?` (E:3732-3741) | checked |
| C5 | `convStep` → `cInst .mem` FD:338-345 | `dom :: ops` | witness `memCall?` (MachMemory.lean:25-39: `a[0]!`, `a[3..6]!` under `isAppOfArity _ 7`) | checked |
| C6 | `convStep` generic app FD:350-352 | `f`, `a` | `appF`, `appA` | checked (rebuilt output `bundleIota (machProjIota …)`: §3.4 G6) |
| C7 | `convStep` lam / forallE FD:354-355, :358-359 | `t` (depth `d`), `b` (depth `d+1`) | `lamT`/`lamB`, `allT`/`allB` | checked |
| C8 | `convStep` let, float FD:363-366 (:365) | constructed let | `float` | checked |
| C9 | `convStep` let, non-let FD:367-377 (:369, :377) | `rootFloat v` to `cLoopRoot` / `cConv env 0` | `floatV` (NEW in rev2) | checked by `floatV`; supply of `SK` at `rootFloat v` is D5 |
| C10 | `convStep` let, body FD:369, :372, :375, :379 | `b` with `mv`/`.regs`/`.handle`/`.val x` | `letB` (context `mixedGateBinderKind? ty`) | checked (`.state b 1` entry: loop-root row, open) |
| N1 | `nestedStep` FD:400 | `dom` | `appA` from C2's witness | checked |
| N2 | `nestedProbe`/`nestedStep` FD:390, :407 | `body`, env `.regs base :: env` | `lamB` from C2's witness | checked |
| N3 | `nestedStep` → `machReserve` FD:405 (and FS:211) | `αs`, `initsE` (NOT converted; `zetaAll`, opaque) | — | no ReadSub needed; slot kinds open (§3.4 G3) |
| I1 | `instArg` FD:412-415, folded at :433 | each `arg ∈ args` of `kinds.zip args` | from `InstSite` (C3/C5) | checked |
| I2 | `instSArg` FD:442-445 | each `arg` | from C4's witness | checked |
| I3 | `instSParam` FD:457-460, :474 | params of `instRes ty args` (constructed) | `sparam` (NEW in rev2) | checked by `sparam`; supply open (§3.4 G7) |
| H1 | `chainStep` `pure'` FD:498-499 | `v` | `appA` | checked |
| H2 | `chainStep` `bind (next h rhs)` FD:500-510 (:504, :508) | `rhs`; `rest` with `.unit :: env` | `appA`…; `lamB` | checked |
| H3 | `chainStep` let FD:511-528 (:514, :518, :521, :524, :526, :528) | as C8-C10 | `float`, `floatV`, `letB` | checked (as C8-C10) |
| B1 | `loopBodyStep` let FD:540-545 (:541, :545) | `v`; `b` with `.val x` | `letV`, `letB` (no `rootFloat` here) | checked |
| B2 | `loopNext` FD:532-536, folded at :548 | `nx` of `machLoopRegs tail` | `appA` under `bundle2`/`register` (E:3783-3795) | checked |
| R1 | `loopRootStep` FD:571 | `dom` of `loopView?` | `inlSpine` arg (FD:280-283) | checked |
| R2 | `loopRootStep`/`loopProbe` FD:556, :590 | loop `body`, env `.state b n :: env` | `lamB` of the 4th arg | checked; `EnvKindOk` at `.state b 1` OPEN (loop-root row) |
| R3 | `loopRootStep` FD:565-569 | `machLoopRegs (machLetTail body)` (not converted) | — | no ReadSub needed; slot kinds open (§3.4 G4) |
A `ReadSub` derivation never needs `rootFloat` to be unfolded: `float`/`floatV` take its result as given. What the
reader reads at C8/C9/H3 is therefore covered; what the SUPPLIERS (`LetSrcKinds`, `CallSrcKinds`, `MemSrcKinds`,
`ConvKind`) must say about `rootFloat`'s output is D5.

### 3.2 Induction over the reader's let construction (on `machineShapeF`, like `InstProv`, ShapeProv:229-233)
Push sites are exactly E:3627, :3647, :3671, :3750 (fuel: FD:378, :527, :544, FS:225-226, `machLetIndex` in
FD:422, :452); lets are never removed or rewritten. All other state growth is by push/append, so `phKind` only
extends (→ `mono`).
| case | site | ReadInv preserved from | at a call: `lets[a].kind = kinds_j` (InstArgKinds) from |
|---|---|---|---|
| F fresh push | E:3750 (fuel FD:422/:452) | `ConvKind` at `arg` with `SK` from `CallSrcKinds`/`MemSrcKinds` (§3.3), reached through the call site kept in `CallPreK` (`instSite_args`, §3.4, rev2 V1) | the push itself (kind := `kinds_j`) |
| R1 `_machLet j` | E:3746 | no push | `ConvKind` at `v' = _machLet j` + `var` ⇒ `lets[j].kind = kinds_j` |
| R2 value dedup | E:3748-3749 | no push | `LetKindOk` at `j` + `ConvKind` at `v'` + `EqvSound` (`lets[j].v == v'`) + `uniq` |
| user let push | E:3627/:3647 (kind `mixedGateBinderKind? ty`, E:3620/:3641); fuel FD:378, :527, FS:225-226 | `ConvKind` with `SK` from `LetSrcKinds`; env grows by `.val x` (EnvKindOk) | — |
| user let dedup | E:3625/:3645 (returns `_machLet j` for annotation kind `k`) | no push; EnvKindOk for `.val (machLet j)` needs `lets[j].kind = k`: `LetKindOk` + `ConvKind` + `EqvSound` + `uniq` | — |
| alias push | E:3654-3671 (stores RESOLVED `val`, kind of `y`) | `ConvKind` at `v'` + `var` along `resolve` + `LetKindOk` of the resolved lets | — |
| memory-op push | E:3956-3958 hard-coded `[.domain, .bits aw, .bits dw, .bool, .bits aw]` | `ConvKind` with `SK` from `MemSrcKinds` | not a target (`SigKindsSt … .mem = False`), but a source of R2 kinds (AUD A6) |
| loop-root state | FD:368-369 / :517-518 (`cLoopRoot`, env grows by `.state b n`) | EnvKindOk at a `.state b 1` entry needs slot kind = annotation kind: NOT in §3.3; LK1-OPEN (§3.4 G12/G20; candidate `LoopSrcKinds`) | — |
| domain arg | E:4065-4068 / :4104-4107 | no push, no index | no obligation (`Pkg.ports` drops `.domain`, Tools/ShippingGen2Pkg.lean:80-81) |
**Provable from existing facts:** the R1 and domain cases, the push/no-push bookkeeping, `mono`-transport, the alias
`resolve` induction, the `InstProv` conjunct (existing, ShapeProv:226-233). **Not:** every case that uses `ConvKind`,
`*SrcKinds` or `EqvSound`; the loop-root row. rev2: the whole per-arm obligation, including arms this table does
not cover, is §3.4's G-table.

### 3.3 What remains (exact Props; R1 full telescopes)
```lean
/-- Source kinding of a pre-conversion Expr in source context Γ (PARAMETER; its instance is the carrier, §6 Q1). -/
abbrev SrcKinding := SrcCtx → Lean.Expr → MixedGateBinder → Prop
structure SrcKindingLaws (SK : SrcKinding) : Prop where
  bvar : ∀ Γ j k, SK Γ (.bvar j) k → Γ[j]? = some (some k)
  uniq : ∀ Γ e k k', SK Γ e k → SK Γ e k' → k = k'
  /-- rev2 V4: insertion at any depth `Γ₁.length` (the float lifts `ty` at 0 and `b` at 1, FD:366). Only a supplier
  that derives `SK` at a floated term from the source term uses it; LK1 itself does not. -/
  lift : ∀ Γ₁ Γ₂ e k o, SK (Γ₁ ++ Γ₂) e k → SK (Γ₁ ++ o :: Γ₂) (e.liftLooseBVars Γ₁.length 1) k
/-- (TY-1, replaces rev0 ArgTyped) conversion keeps the kind. rev2 V2: a CONDITIONAL claim over EVERY configuration
`(Δ, env, d, e, st)` satisfying `ReadInv ∧ EnvKindOk ∧ ReadSub` — an invariant-closed set that contains the
reached configurations but is in general larger; it is NOT restricted to configurations the reader reaches. -/
def ConvKind (HK : PhKinding) (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (n : Nat) (Δ : SrcCtx) (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead)
    (k : MixedGateBinder) (v' : Lean.Expr) (st' : MachRead),
    ReadInv HK senv p st → EnvKindOk HK p st Δ env d → ReadSub senv (midExpr en) Δ e →
    k ≠ .domain → SK (Δ ++ inCtx p) e k →
    readF senv n (.conv env d e st) = some (some (v', st')) → HK (phKind p.bs st') v' k
/-- (TY-2, replaces rev0 LetTyped's source half) annotated lets of the run's body have their annotation kind. -/
def LetSrcKinds (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (Δ : SrcCtx) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (k : MixedGateBinder),
    ReadSub senv (midExpr en) Δ (.letE nm ty v b nd) → mixedGateBinderKind? ty = some k → k ≠ .domain →
    SK (Δ ++ inCtx p) v k
/-- (TY-3) at every call node of the run's body, each non-domain argument has the callee's kind (E:3721-3740). -/
def CallSrcKinds (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  (∀ (Δ : SrcCtx) (e : Lean.Expr) (c : Name) (kinds : List MixedGateBinder) (res : MixedGateBinder)
      (args : List Lean.Expr) (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub senv (midExpr en) Δ e → machInstCall? senv e = some (c, kinds, res, args) →
    (kind, arg) ∈ kinds.zip args → kind ≠ .domain → SK (Δ ++ inCtx p) arg kind) ∧
  (∀ (Δ : SrcCtx) (e : Lean.Expr) (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr)
      (args : List Lean.Expr) (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub senv (midExpr en) Δ e → machInstCallS? senv e = some (c, kinds, ty, args) →
    (kind, arg) ∈ kinds.zip args → kind ≠ .domain → SK (Δ ++ inCtx p) arg kind)
/-- (TY-4, replaces rev0 MemArgTyped) memory operands have the hard-coded kinds at the `aw`/`dw` the recogniser
returned (E:3953-3958); `natOf`/`kernelNat` correctness is folded into this one obligation. -/
def MemSrcKinds (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (Δ : SrcCtx) (e : Lean.Expr) (combo : Bool) (aw dw : Nat) (dom : Lean.Expr) (ops : List Lean.Expr)
    (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub senv (midExpr en) Δ e →
    Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) e =
      some (combo, aw, dw, dom, ops) →
    (kind, arg) ∈ [MixedGateBinder.bits aw, .bits dw, .bool, .bits aw].zip ops → SK (Δ ++ inCtx p) arg kind
def ReadTyped (HK : PhKinding) (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ConvKind HK SK senv p en ∧ LetSrcKinds SK senv p en ∧ CallSrcKinds SK senv p en ∧ MemSrcKinds SK senv p en
/-- §5 D1; a SEPARATE premise of LK1/LK2/CR (R1), not part of ReadTyped. -/
def EqvSound (HK : PhKinding) : Prop :=
  ∀ a b : Lean.Expr, (a == b) = true → ∀ Γ k, HK Γ a k ↔ HK Γ b k
```
- Every obligation is indexed by the run's own `(senv, p, en)` (via `ReadTypedAt`, §1.2), its inputs `bs` are the
  run's own `p.bs`, its expressions range over `ReadSub senv (midExpr en)`. Its states and environments are NOT
  reachability-restricted (rev2 V2): `ReadInv` and `EnvKindOk` are invariants, and `ConvKind` must hold for EVERY
  `st`/`env`/`Δ`/`d` satisfying them, including ones no run reaches. LK1 (§3.4) proves the converse direction only:
  every configuration the reader issues satisfies the invariants (GoodP pattern, FP:470-474). So a supplier of
  `ConvKind` covers the invariant-closed set, which is stronger than covering the reached configurations; it is not
  asked to cover an arbitrary `st`/`env` outside the invariants, nor a `bs` other than `p.bs`.
- If the invariant-closed obligation turns out too strong to supply, the reachability-indexed variant
  (`ReachedK`, §3.4, optional candidate) weakens `ConvKind` to reached configurations at the cost of a per-arm
  "issued calls" lemma; rev2 does not adopt it.
- `ConvKind` is the ONLY place where the callee kind meets the converted value (rows F/R1/R2); `*SrcKinds` are pure
  source facts about the run's body.
- Through normalisation (`machNorm`/`inlFoldNat`/`zeroLit`/`rootFloat`, E:5088-5090) source kinding must hold of the
  NORMALISED body (`midExpr en`); relating it to `ci.value` is the carrier's job (§6 Q1; FRZ:236 item 2; `natOf`
  literal injectivity FRZ:237-238).
- rev2 V4: because `ReadSub` contains `float`/`floatV`/`sparam` terms, `LetSrcKinds`/`CallSrcKinds`/`MemSrcKinds`/
  `ConvKind` are also obligations at `rootFloat v` (opaque, D5) and at the parameters of `instRes ty args`
  (§3.4 G7). These are part of TY's statement as written; the supplier cannot discharge them by unfolding.

### 3.4 Revised full types of LK1 / LK2 (fixed first, R1/R2; rev2 V1-V3)
```lean
/-- The `natOf` of `convStep`'s memory arm (FD:338). -/
def memNatOf (senv : StructEnv) : Lean.Expr → Option Nat := fun e => canonicalNatLitValue? e <|> senv.natOf e
/-- rev2 V1: the recogniser success that dispatched an `.inst` call, per origin (FD:330-345). -/
def InstSite (senv : StructEnv) (e : Lean.Expr) :
    Sparkle.Compiler.MachInstOrigin.InstOrigin → Name → List MixedGateBinder → MixedGateBinder →
      List Lean.Expr → Prop
  | .ord, c, ks, res, args => machInstCall? senv e = some (c, ks, res, args)              -- FD:330-332
  | .mem combo aw dw, c, ks, res, args => ∃ dom ops,                                    -- FD:338-345
      Sparkle.Compiler.MachMemory.memCall? (memNatOf senv) e = some (combo, aw, dw, dom, ops) ∧
      c = Sparkle.Compiler.MachMemory.memChildName combo aw dw ∧
      ks = [.domain, .bits aw, .bits dw, .bool, .bits aw] ∧ res = .bits dw ∧ args = dom :: ops
  | .field _, _, _, _, _ => False              -- `convStep` issues `.inst` only with `.ord`/`.mem` (FD:332, :340-341)
/-- rev2 V1: the call precondition keeps the CALL SITE. For `.nested`/`.inst`/`.instS` it carries the call expression
`e` the dispatching `convStep` arm matched, `ReadSub` of `e` and `EnvKindOk` at the SAME `Δ`, `env`, `st` (the
dispatch is at `d = 0`: every such arm fails on `d != 0`, FD:328, :332, :336, :342), and the recogniser equation. -/
def CallPreK (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Call → Prop
  | .conv env d e st => ∃ Δ, EnvKindOk HK p st Δ env d ∧ ReadSub senv (midExpr en) Δ e
  | .nested env dom αs is body st => ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧
      machRunApp? e = some (dom, αs, is, body)                                            -- E:3675-3679
  | .inst env c org ks res args st => CallPreP senv (.inst env c org ks res args st) ∧    -- FP:432-439
      ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧ InstSite senv e org c ks res args
  | .instS env c ks ty args st => senv.instS c = some (ks, ty) ∧
      ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧
        machInstCallS? senv e = some (c, ks, ty, args)                                    -- E:3732-3741
  | .chain env e st         => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | .loopBody _ env e st    => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | .loopRoot env e st      => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
def GoodK (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) (h : Hs) : Prop :=
  ∀ c, CallPreK HK senv p en c → ReadInv HK senv p (Call.inSt c) → ∀ v, h c = some (some v) →
    ReadInv HK senv p (Call.outSt c v)

/-- rev2 V1, consumption at `instStep`: from the kept call site, every argument is a reader input at the same `Δ`
and every non-domain argument has its callee kind; lengths agree (E:3727 `args.length == kinds.length`;
`.mem`: 5 kinds, `dom :: 4 ops`, MachMemory.lean:38). -/
theorem instSite_args {SK : SrcKinding} {senv p en Δ e org c ks res args}
    (hC : CallSrcKinds SK senv p en) (hM : MemSrcKinds SK senv p en)
    (hR : ReadSub senv (midExpr en) Δ e) (hS : InstSite senv e org c ks res args) :
    ks.length = args.length ∧
    ∀ kind arg, (kind, arg) ∈ ks.zip args →
      ReadSub senv (midExpr en) Δ arg ∧ (kind ≠ .domain → SK (Δ ++ inCtx p) arg kind)
-- `.ord`: hC.1 at (Δ, e) + `inlSpine` args are `appF`*/`appA` subterms. `.mem`: the head pair is `(.domain, dom)`;
-- the tail is `[.bits aw, .bits dw, .bool, .bits aw].zip ops`, exactly hM's list.
/-- rev2 V1, consumption at `instSStep` (args as above with hC.2; params by `sparam`). -/
theorem instSiteS_args {SK : SrcKinding} {senv p en Δ e c ks ty args}
    (hC : CallSrcKinds SK senv p en) (hR : ReadSub senv (midExpr en) Δ e)
    (hS : machInstCallS? senv e = some (c, ks, ty, args)) :
    ks.length = args.length ∧
    (∀ kind arg, (kind, arg) ∈ ks.zip args →
      ReadSub senv (midExpr en) Δ arg ∧ (kind ≠ .domain → SK (Δ ++ inCtx p) arg kind)) ∧
    (∀ resTy q, instRes ty args = some resTy → q ∈ resTy.getAppArgs.toList → ReadSub senv (midExpr en) Δ q)
```
Dispatch side: `convStep`'s arms C2-C5 issue the call with `e := .app f a`, their own `Δ`/`env`/`st` and `d = 0`, so
`CallPreK` of the issued call is `CallPreK (.conv env 0 (.app f a) st)` plus the recogniser equation the arm matched;
`CallPreP` follows from `pre_of_instCallP`/`pre_of_memP` (FP:441, :457). The body context of `.nested` is no longer
rev1's ad-hoc `none :: Δ`: it is `lamB`'s `mixedGateBinderKind? t :: Δ` of the kept `e`.

Alternative (NOT chosen; full type for comparison): SK facts directly in the precondition, supplied at dispatch by
`instSite_args`/`instSiteS_args`. It makes the table invariant depend on `SK`; rev2 keeps `CallPreK` `SK`-free and
consumes `CallSrcKinds`/`MemSrcKinds` only inside the `.inst`/`.instS` arms of LK1.
```lean
def ArgsK (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) (Δ : SrcCtx)
    (ks : List MixedGateBinder) (args : List Lean.Expr) : Prop :=
  ks.length = args.length ∧ ∀ kind arg, (kind, arg) ∈ ks.zip args →
    ReadSub senv (midExpr en) Δ arg ∧ (kind ≠ .domain → SK (Δ ++ inCtx p) arg kind)
def CallPreK' (HK : PhKinding) (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Call → Prop
  | .inst env c org ks res args st => CallPreP senv (.inst env c org ks res args st) ∧
      ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ArgsK SK senv p en Δ ks args
  | .instS env c ks ty args st => senv.instS c = some (ks, ty) ∧
      ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ArgsK SK senv p en Δ ks args ∧
        ∀ resTy q, instRes ty args = some resTy → q ∈ resTy.getAppArgs.toList → ReadSub senv (midExpr en) Δ q
  | .nested env dom αs is body st => ∃ Δ t, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ dom ∧
      ReadSub senv (midExpr en) (mixedGateBinderKind? t :: Δ) body
  | c => CallPreK HK senv p en c                                    -- other arms as in CallPreK
```
Optional reachability-indexed variant (rev2 V2; candidate only, not adopted):
```lean
/-- The calls ONE step of `c` issues against table `h`: one constructor per call-site row of §3.1 (C1-C10, N1-N2,
I1-I3, H1-H3, B1-B2, R1-R2), each stating the issued `Call` from `c`'s data and the answers `h` gave before it. -/
inductive SubCallK (senv : StructEnv) (h : Hs) : Call → Call → Prop
/-- The wrapper's start calls S1-S4 at this run (FS:207-241). -/
inductive StartCallK (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) (h : Hs) : Call → Prop
inductive ReachedK (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) (h : Hs) : Call → Prop
  | start {c} : StartCallK senv p en h c → ReachedK senv p en h c
  | sub {c c'} : ReachedK senv p en h c → SubCallK senv h c c' → ReachedK senv p en h c'
-- ConvKindR n := ConvKind with `ReadInv ∧ EnvKindOk ∧ ReadSub` replaced by `ReachedK senv p en (readF senv n)
-- (.conv env d e st)`. Extra cost: per arm, `(step senv c).run h` reads only `SubCallK`-related calls — `FM` is a
-- run function with monotonicity (FD:86-89), so the queried calls are not observable and need this lemma per arm.
```

**GoodK's whole proof obligation (rev2 V3).** One row per arm of `step` (FD:597-604) and per sub-case. "LK1"
= what `goodK_readF` must prove at that arm given `ReadTyped`, `PhKindingLaws`, `SrcKindingLaws`, `EqvSound`:
`CallPreK` of every issued call (closure table §3.1 + `EnvKindOk` of each new env entry) and `ReadInv` of the output.
"TY supply" = what `ConvKind` (a premise of LK1) asserts at that arm, i.e. what its supplier must establish there.
| # | arm (FD) | LK1 obligation | LK1 status | TY supply (`ConvKind` at this arm's output) |
|---|---|---|---|---|
| G1 | conv `.bvar` (:303, `convBvar` :240-255) | none (state unchanged) | closed | `EnvKindOk` gives it for env entries; `j < d` returns `.bvar j` (needs `HK` on bound `.bvar`): open |
| G2 | conv bare register (:305-320) | issued calls C1; pushes a SLOT kind `machSlotKind? α` (:311-317), no let: `mono` | closed (by `mono`) | NOT AUDITED: result `machSlot base` has kind `machSlotKind? α`; supplier needs `SK e k → k = machSlotKind? α`; the `bareRegs` hit (:309, `·.1 == e`) needs a SOURCE-side `==` law (`SK` respects `Expr.eqv`, cf. D1) |
| G3 | conv slot reads `machLoopRead?` (:323-324), `machReadV` (:347-348) | none | closed | NOT AUDITED: `HK (machSlot i) k` iff `st.kinds[i] = k`; kinds come from `machReserve` (`zetaAll`, opaque, E:3703-3707) or loop regs (`machSlotKind?`, FD:567-569) |
| G4 | conv → nested (:326-328), `nestedStep` (:397-410) | C2/N1/N2 via kept witness; `machReserve` pushes slot kinds (`mono`); shared probe returns the probe's state (:385-393) | closed modulo sub-calls (table IH) | NOT AUDITED: nested result `v` (chain value) kind |
| G5 | conv → inst `.ord`/`.mem` (:330-345), `instStep` (:427-439) | `instSite_args`; pushes F/R1/R2 (§3.2); new entry's `InstArgKinds` | closes modulo `ConvKind` at each arg, `EqvSound`, `uniq` (§3.2) | result `machInstOut k`: kind `res` (`phKind` of `_machInst`): follows from the push (`.ord`/`.mem` both store `res`) |
| G6 | conv → instS (:334-336), `instSStep` (:464-493) | `instSiteS_args`; args as G5; field entries share `js` and `instS c` (§3.2 F row) | closes modulo as G5 | output is a constructor application (not a placeholder): NOT AUDITED |
| G7 | `instSParam` (:457-460, :474) | issued calls I3 by `sparam` | closed (ReadSub); its `ConvKind`/`*SrcKinds` uses are at CONSTRUCTED terms | open: supplier must cover params of `instRes ty args` |
| G8 | conv generic app (:350-352) | C6; no push | closed | NOT AUDITED: rebuilt `bundleIota (machProjIota senv.proj (.app f' a'))` (MachRawSurface `bundleIota`; `machProjIota`) |
| G9 | conv lam / forallE (:353-360) | C7 (`EnvKindOk` at `d+1`: new index `< d+1` is bound, `convBvar` :241) | closed | rebuilt binder: expected vacuous (no `MixedGateBinder` kind for a lam), unchecked |
| G10 | conv let, float (:363-366) | C8 by `float` | closed | — (delegates) |
| G11 | conv let, user value (:376-379, `machBindLet` E:3619-3628) | C9 `floatV`; push / dedup / bare-var rows of §3.2; new entry `.val x`: `EnvKindOk` with Δ entry `mixedGateBinderKind? ty` (same function `machBindLet` keys on, E:3620) | closes modulo `ConvKind` at `rootFloat v`, `LetSrcKinds` at the ORIGINAL `.letE` (its `v` ≠ `rootFloat v`: D5), `EqvSound`, `uniq` | — |
| G12 | conv let, loop (:368-369) and chain let, loop (:517-518) | new entry `mv = .state b n`: `EnvKindOk` at Δ entry `mixedGateBinderKind? ty` | **OPEN (loop-root row)**: `n = 1` needs `st.kinds[b] = k`; `n > 1` vacuous only if `mixedGateBinderKind? ty = none` for the tuple Signal type (E:2337-2343 accepts only `Bool`/`BitVec`) | — |
| G13 | conv/chain let, `.regs`/`.handle` (:371-375, :520-524) | new entry: `convBvar` fails on it (:254) | closed (vacuous) | — |
| G14 | conv default arm (:382, `okO (e, st)`) | none | closed | NOT AUDITED: `HK Γ e k` for an unchanged const/lit/fvar/sort `e` from `SK … e k` |
| G15 | conv `.mdata`/`.proj` (:380-381) | FAIL | closed | — |
| G16 | chain `pure'`/`next` (:498-510) | H1/H2; `.unit` entry vacuous | closed | `next` index check `i < st.kinds.size` (:507): no kind fact |
| G17 | chain let (:511-528) | as G10-G13 | as G10-G13 (loop: OPEN) | — |
| G18 | loopBody let (:540-545; `machBindLetNamed` E:3640-3647, `machBindLetAlias` E:3654-3671) | B1; named/alias/plain push rows of §3.2 (alias: `resolve` induction) | closes modulo as G11 | — |
| G19 | loopBody tail (:546-549) | B2; `ws` append (not in `ReadInv`) | closed | — |
| G20 | loopRoot (:562-594) | R1/R2; pushes slot kinds `machSlotKind?` (:569, :581), no lets (`mono`); issued `loopBody` call's env entry `.state base n` and the probe's `.state b0 n` (:556) | **OPEN (loop-root row)**: `EnvKindOk` at that entry, see G12; the probe (:552-559) compares `n` and `ws`, NOT kinds, so `st.kinds[b0]` for a shared loop needs `ws`-equality ⇒ kind equality (`EqvSound` + `uniq` + `ConvKind` at `nx`) | NOT AUDITED: result `.state` kind |
| G21 | wrapper start S1-S4 (FS:207-241) and root-let pushes (FS:224-226, `machBindLetNamed`/`machBindLet`) | closure rows S1-S4; push rows of §3.2; start state `{}` or `machReserve`'s (no lets: `LetKindOk`/`InstArgKinds` vacuous) | closes modulo as G11 | — |
Candidate source fact for G12/G20 (TY-5, NOT added to `ReadTyped` in rev2; full type for review):
```lean
def LoopSrcKinds (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (Δ : SrcCtx) (e : Lean.Expr) (ls : List Level) (dom a₁ a₂ t body : Lean.Expr) (nm : Name) (bi : BinderInfo)
    (regs : List (Lean.Expr × Lean.Expr × Lean.Expr)) (kinds : List MixedGateBinder) (k : MixedGateBinder),
    ReadSub senv (midExpr en) Δ e →
    inlSpine e [] = (.const ``Sparkle.Core.Signal.Signal.loop ls, [dom, a₁, a₂, .lam nm t body bi]) →  -- FD:280-283
    machLoopRegs (machLetTail body) = some regs → regs.mapM loopRegKind = some kinds →            -- FD:567-569
    mixedGateBinderKind? t = some k → k ≠ .domain → kinds = [k]
```
With it, G12/G20's `n = 1` case closes for a FRESH loop (kinds pushed at `base`); the shared-probe case additionally
needs the `ws`-equality argument above. Whether it is an `SK`-carrier fact or a separate source fact is for §6 Q1.

LK1 / LK2 types (unchanged from rev1 except that `CallPreK` and `ReadTyped` are the rev2 ones):
```lean
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

### 3.7 rev3: EnvKindOk / CallPreK / GoodK revision proposal (for review)
Written at e134c63a. Nothing here is built; Lean blocks are UNELABORATED. `A2:` = Tools/ShippingGen3ArgSupply2.lean
(batch 2, built clean in g3se-e134c63a), `T2:` = Tests/Gen3/ArgSupply2Check.lean.

#### 3.7.1 The problem (batch-2 STOP, A2:42-53)
Every arm that issues a SECOND sub-call at the state `st₁` returned by the first needs `CallPreK` of that call, i.e.
`EnvKindOk HK p st₁ Δ env d` (rev2 §3.4, A2:283-295), but only `EnvKindOk … st …` is known. rev2's `EnvKindOk`
(§3.1, A2:201-206) is stated through `convBvar env d j st` (FD:240-255):
- `.val v` (FD:243): result `v`, obligation `HK (phKind p.bs st) v k` — transports to `st₁` by `mono` + `phKind_ext`
  (A2:600) IF `PhExt st st₁` (A2:587-590) is known; `GoodK` (A2:297-299) gives no relation between input and output
  states, so this "state-extension table invariant" is missing (provable, not written).
- `.state b 1` (FD:244): `machSlot b`; needs `st₁.kinds[b]? = some k`; same missing `PhExt`.
- `.state b n`, `n ≠ 1` (FD:245-253): `let dom ← st.dom`, kinds `b … b+n-1`, `bundleSlots dom …`. (i) `st.dom = none`
  ⇒ `convBvar` fails ⇒ no obligation at `st`, while `st₁.dom = some _` (set at FD:318, :420, :450, :585, E:3716 via
  FD:405) creates one; (ii) at FD:314/:318, FD:572/:585, E:3708-3716 a `some d` is replaced by `some dom'` with only
  `(d == dom') = true` (extern `Expr.eqv`, D1), so the bundle term at `st₁` differs from the one at `st`. Neither
  follows from rev2's types. (`n = 0`: `bundleSlots dom [] []` = none, FD:232-237, so no obligation.)
- `.regs`/`.handle`/`.unit` (FD:254) and `machIn` (FD:255, outside `j < d + env.length`): no obligation.
Blocked arms (§3.4 numbering): G7 (`instSParam` fold, FD:474/:460), G9 (lam/forallE, FD:354-355/:358-359), G16 `next`
(FD:504/:508), G17 user-let (FD:526/:528), G19 (`loopNext` fold, FD:548/:532-536); also the second-call PART of
G2 (FD:313/:320), G4 (FD:400/:407), G5/G6 argument folds (FD:433, :473), G8 (FD:350-351), G11/G18 (FD:377/:379,
:541/:545), G20 (FD:571/:590) — their other open items are unchanged.

#### 3.7.2 Option (a): `EnvKindOk` unchanged, relative to a state-extension relation `StExt`
```lean
/-- Reflexive-transitive closure of the extern `==` (transitivity of `Expr.eqv` itself is not available, D1). -/
def EqvChain : Lean.Expr → Lean.Expr → Prop := Relation.ReflTransGen (fun a b => (a == b) = true)
def DomExt (o o' : Option Lean.Expr) : Prop :=
  o = none ∨ ∃ d d', o = some d ∧ o' = some d' ∧ EqvChain d d'
def StExt (st st' : MachRead) : Prop := PhExt st st' ∧ DomExt st.dom st'.dom          -- PhExt: A2:587-590
/-- Every non-singleton loop entry of `env` already has its domain and slots in `st` (excludes case (i)). -/
def EnvDom (st : MachRead) (env : List MachVal) : Prop :=
  ∀ b n, MachVal.state b n ∈ env → n ≠ 1 → st.dom.isSome ∧ b + n ≤ st.kinds.size
/-- NEW law on the HK parameter (case (ii)): the bundle's kind ignores an `EqvChain`-related domain term. -/
def DomCongr (HK : PhKinding) : Prop :=
  ∀ Γ d d' is tys x x' t t' k, EqvChain d d' →
    bundleSlots d is tys = some (x, t) → bundleSlots d' is tys = some (x', t') → HK Γ x k → HK Γ x' k
def CallPreKa (HK) (senv) (p) (en) (c : Call) : Prop := CallPreK HK senv p en c ∧ EnvDom (Call.inSt c) (Call.env c)
def GoodKa (HK) (senv) (p) (en) (h : Hs) : Prop :=
  ∀ c, CallPreKa HK senv p en c → ReadInv HK senv p (Call.inSt c) → ∀ v, h c = some (some v) →
    ReadInv HK senv p (Call.outSt c v) ∧ StExt (Call.inSt c) (Call.outSt c v)
theorem envKindOk_stExt {HK p st st₁ Δ env d} (HKL : PhKindingLaws HK) (DC : DomCongr HK)
    (h : EnvKindOk HK p st Δ env d) (hD : EnvDom st env) (hx : StExt st st₁) : EnvKindOk HK p st₁ Δ env d
```
(`Call.env` = the env field of each constructor; a 7-line projection, not yet written.) New invariants: `StExt` per
arm (pushes/appends only, §3.2; `dom` transitions FD:318/:420/:450/:585, E:3716); `EnvDom` at every issued call —
from `.state` entries being created only at FD:590 after `dom := some` (FD:585) or at the probe FD:556, which needs a
further invariant `st.loopWs ≠ #[] → st.dom.isSome` (loopWs pushed only at FD:592). **Premise cost:** `DomCongr HK`
is a NEW law premise of LK1/LK2/CR (an extra `PhKindingLaws` field LK3 would have to prove for the mirror; unchecked
whether the mirror's `bundle2` arm reads the domain argument), or, if stated on `Expr.eqv` congruence instead, a
TRUSTED boundary (D1 extension) = **decision item**. Unblocks: all arms of §3.7.1.

#### 3.7.3 Option (b) (RECOMMENDED): entry-indexed, `dom`-free `EnvKindOkE` + unconditional `GoodE`
The obligation is indexed by the ENV ENTRY (the source binder's reader value), not by `convBvar`'s output; for a
loop entry it demands the singleton slot itself, so neither `st.dom` nor a bundle term occurs.
```lean
/-- What a reader value owes the source kind `k` of its binder. -/
def EntryKindOk (HK : PhKinding) (p : ShapePre) (st : MachRead) (k : MixedGateBinder) : MachVal → Prop
  | .val v     => HK (phKind p.bs st) v k
  | .state b n => n = 1 ∧ st.kinds[b]? = some k
  | .regs _    => True                                   -- convBvar fails (FD:254)
  | .handle _  => True
  | .unit      => True
def EnvKindOkE (HK : PhKinding) (p : ShapePre) (st : MachRead) (Δ : SrcCtx) (env : List MachVal) (d : Nat) :
    Prop :=
  Δ.length = d + env.length ∧
  ∀ (j : Nat) (k : MixedGateBinder) (m : MachVal), d ≤ j → Δ[j]? = some (some k) → k ≠ .domain →
    env[j - d]? = some m → EntryKindOk HK p st k m
/-- rev3 CallPreK: rev2's text (§3.4, A2:283-295) with `EnvKindOk` replaced by `EnvKindOkE` in all seven rows. -/
def CallPreKE (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Call → Prop
  | .conv env d e st => ∃ Δ, EnvKindOkE HK p st Δ env d ∧ ReadSub senv (midExpr en) Δ e
  | .nested env dom αs is body st => ∃ Δ e, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧
      machRunApp? e = some (dom, αs, is, body)
  | .inst env c org ks res args st => CallPreP senv (.inst env c org ks res args st) ∧
      ∃ Δ e, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧ InstSite senv e org c ks res args
  | .instS env c ks ty args st => senv.instS c = some (ks, ty) ∧
      ∃ Δ e, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧
        machInstCallS? senv e = some (c, ks, ty, args)
  | .chain env e st      => ∃ Δ, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | .loopBody _ env e st => ∃ Δ, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | .loopRoot env e st   => ∃ Δ, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
/-- GoodK keeps its rev2 shape (A2:297-299) over CallPreKE. -/
def GoodKE (HK) (senv) (p) (en) (h : Hs) : Prop :=
  ∀ c, CallPreKE HK senv p en c → ReadInv HK senv p (Call.inSt c) → ∀ v, h c = some (some v) →
    ReadInv HK senv p (Call.outSt c v)
/-- NEW, UNCONDITIONAL table invariant (no precondition; pattern of `GoodH`, Tools/ShippingReaderFuelR5.lean:71-72). -/
def GoodE (h : Hs) : Prop := ∀ c v, h c = some (some v) → PhExt (Call.inSt c) (Call.outSt c v)
theorem goodE_readF (senv : StructEnv) : ∀ n, GoodE (readF senv n)
theorem envKindOk_of_E {HK p st Δ env d} (HKL : PhKindingLaws HK) :
    EnvKindOkE HK p st Δ env d → EnvKindOk HK p st Δ env d          -- `.state b 1`: HKL.var (fvar) + phKind_slot (A2:574)
theorem envKindOkE_ext {HK p st st₁ Δ env d} (HKL : PhKindingLaws HK) :
    EnvKindOkE HK p st Δ env d → PhExt st st₁ → EnvKindOkE HK p st₁ Δ env d   -- HKL.mono + phKind_ext; PhExt.1
theorem envKindOkE_lift {HK p st Δ env d} (o : Option MixedGateBinder) :
    EnvKindOkE HK p st Δ env d → EnvKindOkE HK p st (o :: Δ) env (d + 1)   -- G9 body at depth d+1
theorem envKindOkE_cons {HK p st Δ env} (o : Option MixedGateBinder) (m : MachVal)
    (hm : ∀ k, o = some k → k ≠ .domain → EntryKindOk HK p st k m) :
    EnvKindOkE HK p st Δ env 0 → EnvKindOkE HK p st (o :: Δ) (m :: env) 0
/-- Hoare combinator for a second call (replaces `satK_bindO`, A2:845, where the continuation needs `st₁`). -/
theorem satK_bindOE [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)} {st : MachRead} (hE : GoodE h)
    (hx : SatK HK senv p h x) (hxE : ∀ b, x.run h = some (some b) → PhExt st (HasSt.st b))
    (hf : ∀ b, StK HK senv p b → PhExt st (HasSt.st b) → SatK HK senv p h (f b)) : SatK HK senv p h (bindO x f)
```
- `ConvKind` (§3.3) keeps its text with `EnvKindOk` replaced by `EnvKindOkE` (a STRONGER hypothesis, so a WEAKER
  obligation for the supplier, by `envKindOk_of_E`); keeping rev2's premise also works via that lemma.
- **New invariant:** only `GoodE`, proved by the fuel induction with no premise: every arm only pushes/appends
  `kinds`/`lets`/`insts` (§3.2: push sites; `machBindLet`/`machLetIndex` push or return the old array, E:3619-3628,
  E:3746-3750; `machReserve` appends, E:3712-3716; probes return a table state or `{ st' with ws := … }`, FD:390-393,
  :556-559). `phExt_refl`/`phExt_trans` exist (A2:592-598). LK1's induction carries `GoodKE ∧ GoodE`.
- **`==`-equal `dom` (case ii):** irrelevant — `EntryKindOk`, `phKind`, `LetKindOk`, `InstArgKinds` and `InstProv`
  (FP:167) do not read `st.dom`; `EqvSound`/`DomCongr` are not used for it; D1 is unchanged.
- **Case (i):** irrelevant — no obligation mentions `dom`.
- **Creation-site obligations** (where LK1 pushes an entry): `.val x` (G11/G17/G18/G21) — unchanged from rev2 (open,
  `ConvKind`/D5/`EqvSound`/`uniq`); `.state b n` at G12 (FD:369, :518), G20 (FD:590) and the probe (FD:556) — now
  `n = 1 ∧ st.kinds[b]? = some k` instead of `HK (phKind …) (convBvar output) k`. This is the SAME open loop-root row:
  for a fresh loop `kinds` are pushed at `base` (FD:581) so `LoopSrcKinds` (§3.4, `kinds = [k]`) gives it for the
  `lamB` entry; the let-annotation entry of G12 needs the let-indexed form below plus a `loopRoot` result fact
  (`.state b n` returned with `kinds[b..b+n) = ` the regs' kinds); the shared probe still needs the `ws`-equality
  argument (G20). For `n ≥ 2` with a Bool/BitVec `k`, rev2 asked `HK` to accept a `bundle2` tuple at a single kind,
  which a kind-exact `HK` is expected to reject (LK3 has NOT checked `bundle2`), so (b) is expected not to lose any
  suppliable case; if the mirror does accept such a term, (b) is strictly stronger there (record as a review point).
```lean
/-- TY-5' candidate (NOT added to ReadTyped; extends §3.4's LoopSrcKinds to the let annotation of G12). -/
def LoopLetSrcKinds (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (Δ : SrcCtx) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (ls : List Level) (dom a₁ a₂ t body : Lean.Expr)
    (nm' : Name) (bi : BinderInfo) (regs : List (Lean.Expr × Lean.Expr × Lean.Expr))
    (kinds : List MixedGateBinder) (k : MixedGateBinder),
    ReadSub senv (midExpr en) Δ (.letE nm ty v b nd) →
    inlSpine (Sparkle.Compiler.MachRawSurface.rootFloat v) [] =
      (.const ``Sparkle.Core.Signal.Signal.loop ls, [dom, a₁, a₂, .lam nm' t body bi]) →         -- FD:280-283
    machLoopRegs (machLetTail body) = some regs → regs.mapM loopRegKind = some kinds →           -- FD:567-569
    mixedGateBinderKind? ty = some k → k ≠ .domain → kinds = [k]
```
- **Premise cost:** NONE added to CR (§1.2): `PhKindingLaws` uses only `var`/`mono`, `EqvSound` unchanged, no new law.
  `LoopSrcKinds`/`LoopLetSrcKinds` are TY components for the ALREADY-OPEN G12/G20 row (rev2 also needed a source
  fact there: "vacuous only if `mixedGateBinderKind? ty = none`", §3.4 G12); whether they enter `ReadTyped` stays the
  existing §6 Q1 item, not a new decision. No semantic premise beyond rev2's.
- **Re-work:** batch-2 lemmas stated with `EnvKindOk` (`envKindOk_cons_vac` A2:735, `callPreK_conv_float`/`_letVac`/
  `chain_*` A2:767-814, arm lemmas A2:879-1143) are restated over `EnvKindOkE`/`CallPreKE` (same proofs; the vacuous
  entries are `True` rows of `EntryKindOk`).

#### 3.7.4 Option (c): carry the obligation at the `dom`-setting site in GoodK's post-condition
```lean
def GoodKc (HK) (senv) (p) (en) (h : Hs) : Prop :=
  ∀ c, CallPreK HK senv p en c → ReadInv HK senv p (Call.inSt c) → ∀ v, h c = some (some v) →
    ReadInv HK senv p (Call.outSt c v) ∧
    ∀ (Δ' : SrcCtx) (env' : List MachVal) (d' : Nat), EnvDom (Call.inSt c) env' →
      EnvKindOk HK p (Call.inSt c) Δ' env' d' → EnvKindOk HK p (Call.outSt c v) Δ' env' d'
```
Each arm must prove preservation for an ARBITRARY caller env `env'`; at FD:318/:420/:450/:585/E:3716 case (i) is
excluded only by `EnvDom` (as in (a)), and case (ii) at FD:318/:585/E:3716 needs `DomCongr` again. Same new law/
decision item as (a), with the burden moved into every arm and a universally quantified outer env. Unblocks the same
arms. Not recommended.
(Variant (b′), "quantify `.state b n` over every future `dom`": `∀ dom x t, bundleSlots dom … = some (x, t) → HK … x k`
is `dom`-independent but makes every creation site prove `HK` of a tuple bundle at a single kind for ALL domain
terms — not suppliable except vacuously; (b)'s `n = 1` states that vacuity directly. Rejected.)

#### 3.7.5 LK3 control results (T2:454-520, build g3se-e134c63a log)
| control | cases (T2 line) | result | note |
|---|---|---|---|
| P1 | literal-high concat :474, literal-low concat :475, slice :476 | PASS (all three) | rev2 §3.6's `sixArgShape? = some (r, none, none)` case does NOT exist: no arm of `sixArgShape?` returns two `none`s (E:1538-1548); P1 was run on the three one-`none` arms (T2:18-20) |
| P2 | `.bits 1` binder :486, Bool binder :487, 1-bit slice :488, `Signal.pure true` :489 | PASS (all four) | Bool ≠ `.bits 1` on the checker |
| N1 | broken checker (no `w == r`), literal-high :497, slice :498 | P1 FAILS on it (both) | the control detects a non-unique checker |
| N2 | wrong-kind binder in the literal position :504 / slice-function position :505 | `accepted = false` (both) | rev2 §3.6 expected "accepted": WRONG — the recognisers (`canonicalConcatLit?`, `canonicalSliceF?`, E:1543-1547) force a literal / the slice lambda in that position, so a binder there is not recognised at all |
Consequence: LK3's stop rule did not fire (`uniq` survives on the permissive arms for these cases); the N2 finding
weakens §3.5's "operands under `none => true` are unchecked" only for these two positions (they cannot hold a
binder); it supplies no `LetKindOk`. No `HK` adopted yet.

#### 3.7.6 Recommendation
Adopt (b): `EntryKindOk`/`EnvKindOkE`/`CallPreKE`/`GoodKE` + unconditional `GoodE` (`goodE_readF`), with
`envKindOk_of_E`, `envKindOkE_ext`/`_lift`/`_cons`, `satK_bindOE`. It closes the STOP for G7, G9, G16 `next`, G19
fully (LK1 side) and the second-call part of G17/G2/G4/G5/G6/G8/G11/G18/G20, adds no premise to CR, does not touch
D1, and leaves G12/G20 as the one open loop-root row (now `n = 1 ∧ kinds[b] = k`). Sizes (est.): defs + LK0 lemmas
80-150 l, `goodE_readF` 150-250 l, restating batch-2 arms 100-200 l.

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
| LK1 | `goodK_readF` + `machineShapeF_final_readInv` (§3.4), incl. `ReadSub` closure (§3.1 table), `instSite_args`/`instSiteS_args`, every G-row of §3.4 (G12/G20 OPEN) | FD:301-604, FP:470-474 pattern | 500-900 l | LK0 | src-argw child |
| LK2 | `shapePost_binders` + `argKindsG_of_machineShapeF` | FS:153-205, ShapeR5:318-363 | 150-300 l | LK1 | src-argw child |
| LK3 | §3.6 controls first; then `HK` instantiation (mirror of `unifiedGate*Body`) + `PhKindingLaws` | E:2521-2633 | 200-400 l | LK0 | src-argw child |
| TY | CR's `TY` at every actual `ClosingRun` (L-FG, §1.3), with laws for the `HK`/`SK` used; the uniform form over every successful read (L-FG+) is an optional stronger route, not required. Includes the D5 and G7 obligations at constructed terms; NOT-AUDITED G-rows are part of `ConvKind` | carrier (§6 Q1) | unknown, likely ≥ 1000 l | §6 Q1 | src-argw child; carrier = decl-bridge |
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
- **D5 `rootFloat` opacity (rev2 V4).** `rootFloat` is `partial` (MachRawSurface.lean:198), opaque to proofs (FD:66-68),
  and the reader converts `rootFloat v` (C9/H3) and floated lets (C8). `ReadSub` covers these without unfolding
  (`float`/`floatV`), but every supplier statement at them (`LetSrcKinds` on a floated `.letE`, `ConvKind`/`*SrcKinds`
  at `rootFloat v`) needs a fact about `rootFloat`'s output that no proof can read off its definition. Options seen
  (none adopted): (a) a total/fuelled `rootFloat` (compiler refactor; output policy applies); (b) a law on it =
  new TRUSTED boundary (user item); (c) leave the obligation in TY for the carrier, which then faces the same
  opacity. Without one of these, L-FG's TY at runs that float a let is unsupplied.
- D-ARGW stays HELD (FRZ:300-302); G-E/G-T remain comparison material (AUD §C/§D).

## 6. Interface requests to gen5 (R1-R3) — REQUESTS FOR CONSULTATION
None of these approves a new TRUSTED boundary, a guarantee change, or a production/compiler change. They ask the
owner issues (DGEN:722-725) whether the stated Prop can be part of their deliverable; the answer may be "no".
- **Q1 → `sparkle-gen5-decl-bridge` (DC-FORM carrier; R1/R3).** Is a kind-indexed carrier (`ExprDenotesK env Γ e k v`,
  or a lemma family from `ExprDenotes`, DGEN:448-450) in DC-FORM's scope, such that `SK Γ e k := ∃ v, ExprDenotesK …`
  satisfies `SrcKindingLaws` (§3.3: `bvar`, `uniq` incl. Bool ≠ `.bits 1`, `lift` at any depth) and yields `LetSrcKinds`,
  `CallSrcKinds`, `MemSrcKinds` on the `ReadSub` terms of the NORMALISED body `midExpr en` (incl. `float`/`floatV`/
  `sparam` terms, D5) of every actual run (L-FG; every successful read would be the stronger L-FG+, not required)?
  Is `LoopSrcKinds` (§3.4, TY-5 candidate) in its scope? If DC-FORM keeps the `Sort` index, which agreement
  supplier (if any) does it plan? (D3.)
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
- `ReadSub` closure: checked for every call site in §3.1's table by reading the code (no lemma proved). GoodK's
  G12/G20 (loop root) are open, and the G-rows marked NOT AUDITED are unchecked `ConvKind` obligations.
- No claim that `ConvKind` (invariant-indexed) is suppliable; `ReachedK` and `CallPreK'` are unadopted alternatives.
- No claim that `rootFloat`'s non-let output equals its input in any kernel-checked sense (D5).
- No width-mismatched successful run is exhibited or excluded. No change to `T1Hyp`, `ChildShips`, `DataOkB`, FG,
  the compiler, or any gen5 freeze; owners/requests above are proposals for review.

## rev3.1 review notes (appended after reviewer approval of §3.7 option (b) at e8a41c70; §3.7 text NOT rewritten)
These notes correct/qualify §3.7's wording; where they conflict with §3.7.3/§3.7.6, these notes win.
- **E ⇒ old is ONE-directional.** `envKindOk_of_E : EnvKindOkE … → EnvKindOk …` only. The converse is false:
  a typed non-domain (`k ≠ .domain`) binder whose env entry is `.state b n` with `n = 0` or `n ≥ 2` satisfies rev2's
  `EnvKindOk` vacuously at a state with `st.dom = none` (and at `n = 0` for every state, `bundleSlots dom [] []` =
  none), but is EXCLUDED by `EnvKindOkE` (`EntryKindOk` demands `n = 1`). Controls: Tests/Gen3/ArgSupply3Check.lean
  `ctl_old_not_E_state0`, `ctl_old_not_E_state2`, `ctl_E_state0_excluded`, `ctl_E_stateN_excluded`.
- **Therefore NOT established:** §3.7.3's "no semantic premise beyond rev2's" and §3.7.3's "(b) is expected not to
  lose any suppliable case". (b) makes the obligation STRONGER at those entries; whether any actual run creates such
  an entry at a typed binder (so that `TY`/LK1 would have to supply it) is not shown either way.
- **CR's surface is unchanged, its content is not.** `argWidthAt_of_closingRun`'s binder list (§1.2) is unchanged,
  but `ReadTyped`/`TY` and `ConvKind` are now read over `EnvKindOkE`/`CallPreKE` (§3.7.3 first bullet), so the
  Props CR consumes change meaning; "no premise added to CR" refers to the binder list only.
- **Explicitly OPEN:** `LoopSrcKinds`, `LoopLetSrcKinds` (§3.4, §3.7.3: candidates, NOT added to `ReadTyped`), and the
  shared loop-probe supply (G20's `ws`-equality argument, the probe's `.state b0 n` entry, FD:556). The loop-root
  row (G12/G20: `n = 1 ∧ kinds[b] = k` at every CREATED `.state` entry) is open.
- **bundle2 mirror check is SEPARATE from actual-run E supply.** Running the compiler checker
  (`unifiedGate*Body`) on a 2-tuple is a record about the mirror only; a mirror rejecting tuples does not prove that
  actual runs never pair a typed binder with a non-singleton `.state` entry (coverage), and a mirror accepting them
  does not make those entries suppliable under (b).
- **(a)'s `DomCongr HK` is an UNINVESTIGATED candidate,** not a necessary TRUSTED boundary: whether it is provable
  for the target `HK` (e.g. LK3's mirror, if its `bundle2` arm ignores the domain argument) has not been examined.
  §3.7.2's "or … a TRUSTED boundary (D1 extension)" describes one way of stating it, not a requirement.
- **The existing dedup `EqvSound` remains** (§3.3, D1: `machBindLet`/`machLetIndex` dedup by `==`). (b) removes only
  the `dom`-replacement use (case ii of §3.7.1); it does not remove `EqvSound` from CR.
- **Arms are closed only by new proofs.** Status after batch 3 (Tools/ShippingGen3ArgSupply3.lean, WRITTEN, NOT
  BUILT at the time of writing): proof written for `goodE_readF` (unconditional), G9 (`satKE_conv_lam`/`_forallE`),
  G16 `next` (`satKE_chain_next`), G7 (`satKE_instSParamFold`), G19 (`satKE_loopBody_tail`), G8
  (`satKE_conv_app_generic`; result-kind item still NOT AUDITED), and the E versions of the batch-2 arms (G1, G10,
  G13, G15, G16-pure, G17 float/regs/handle). Every arm is conditional on `GoodKE` of the table (LK1's induction
  is not written). STILL OPEN: G2, G4, G5, G6, G11, G12, G17 user-let, G18, G20 (and not-audited G3/G14/G21); their
  second-call parts are dischargeable with `envKindOkE_ext`/`_cons` + `goodE_readF` but NO proof is written, so they
  are not counted as closed. Any arm counts as closed only once its file builds.
- **rev3 is not build evidence.** §3.7 and these notes are text; the only build cited in §3.7 (g3se-e134c63a) is
  for batch 2 (Tools/ShippingGen3ArgSupply2.lean, Tests/Gen3/ArgSupply2Check.lean), not for anything in §3.7 or
  batch 3.

## rev3.2 status (review of 88858249, scope-accepted as a local implementation)
- Built: batch 2 in g3se-e134c63a, option (b) in g3sf-88858249 (clean, standard axioms).
- `GoodE` is preservation of three lookups in the FUEL model; it is NOT a supply of `GoodKE(readF)`, of result kinds,
  or of production coverage. In `satK_bindOE` the transport is carried by `hxE` (`hE` unused); `GoodE` alone does not
  extend an arbitrary `x`.
- If an actual entry needs `n ≠ 1`, that is reported as a finding at once; it is not excluded from FG.
- Open: remaining arms and LK1 induction, loop-root (`LoopSrcKinds`/`LoopLetSrcKinds`) and the shared probe on actual
  entries, EqvSound, D5 (`rootFloat`), the gen5 joint suppliers; L-RUN / L-FG not accepted.

## rev3.3 status (review of 5f18f978, batch 4 approved in scope)
- Built: batch 4 in g3sg-5f18f978 (clean, exit 0, 730 jobs; TYPE 11 / MUTANT 8 / AXIOMS 33 standard); the loop-root
  probe in g3lp-5f18f978 (clean, exit 0, 438 jobs).
- Mutants: the 8 rejections (7 distinct mutants + 1 checker re-check) are signature/defeq rejections, not semantic
  refutations or kernel proofs of non-equivalence.
- Probe (unsafe fuel-model measurement, evidence only): 13 declarations, 34 deduplicated lines, 18 typed singletons
  with `kinds[b] = k`, 16 untyped, 0 mismatch, 0 typed non-domain `n ≠ 1` finding. Untyped tuples with n = 2/4/6/8 DO
  occur. (An earlier Issue note "14 typed / 13 untyped" is replaced by these counts.) Not production agreement, not
  coverage, not a `LoopSrcKinds` supply.
- Open: `LK1Open` (8 fields) is unsupplied; G3/G14 only preserve state (TY side unresolved); G21, loop tuples, handles,
  atoms, register kinds and the actual-run connection are OPEN. No Issue or FG is done.
