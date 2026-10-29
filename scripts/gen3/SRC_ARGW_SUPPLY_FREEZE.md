# SRC-ARGW supply freeze rev0: connecting SA0's premises to ONE run and to the shared gen5 suppliers

**FOR REVIEW — design only, nothing built or proved.** No `.lean` file, lakefile or shared definition was written or
edited; no Lean was run. Every Lean block below is UNELABORATED text. Sizes are estimates.

Issue `sparkle-gen3-src-argw` (child of `sparkle-gen3-data-supply`). Base `par/gen2-spec` **168e0c95** (SA0/SA1 =
Tools/ShippingGen3ArgWidthSrc.lean, built at g3sb-7813bf32, header :3). `[T]` = `~/git/.kjob/gen5-t2` at **c398021c**
(par/gen5-t2): `DGEN:` = scripts/gen5/DGEN_FREEZE.md, `M5:` = scripts/gen5/M5_INDEP_STUDIES.md, `T2C:` =
scripts/gen5/T2COVER_FREEZE.md, all at c398021c. `E:` = Sparkle/Compiler/Elab.lean. Prior texts: scripts/gen3/
SRC_ARGW_FREEZE.md rev1 (`FRZ:`), SRC_ARGW_AUDIT.md (`AUD:`).

**Rule kept from review:** a per-declaration decided row (`argWidthAt_iff_rowP`, ArgWidthSrc:226-240) is an
INTERMEDIATE check at one concrete `P`; it never counts as supply or completion. Completion = §1's target for every
successful run, with every supplier below proved (or a recorded user decision on a §5 item).

## 1. Target: `∀ k, ArgWidthAt P p k` from ONE run
Same package witnesses as `callArity_of_trace` (Tools/ShippingGen3Arity.lean:172-180: `P p k hk hnone q hP`). The run
witness is [T] `ClosingRun` (DGEN:549-571); `shared` fixes ONE `(b, ci, envR, envR', w5, w6, t, …)` (DGEN:559-571), and
its `RunReadsAt` carries `shapeEq : machineShape? false [] (entryConst true false [] ci (instancePredicate envR)
(userInliner envR) (structEnv envR)) (structEnv envR') = some p.d.shape` (M5:232-233). `P = genP env₀` (DGEN C5, :395-400).
No trace is needed for widths (`ArgWidthAt` is data-level, ArgWidthSrc:175-178); arity comes from `hA ∧ hC` (FRZ:127-134).
```lean
/-- (C-CORE, pure) Every ordinary call of ONE read shape, from the four named suppliers. -/
theorem argWidthAt_of_read (P : Pkgs ι dom) (p : Pkg ι dom) {senv senv₀ : StructEnv}
    (hKD  : p.kD = closingNDecl p.d.shape)                          -- KD   (§4 row KD)
    (hSIG : ShapeSigProv senv p.d.shape)                            -- SIG  (§2)
    (hARG : ShapeArgKinds senv p.d.shape)                           -- LK   (§3)
    (hENV : ∀ c q, P c = some q → SigEq senv senv₀ c)               -- ENV  (§4)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senv₀ c q) :        -- VT ∧ P5 (§4)
    ∀ k, ArgWidthAt P p k
-- proof sketch: hSIG.2 k gives `SigKindsAt`; by origin (.ord/.field) pick argWidth_of_halves / …S (ArgWidthSrc:91,124);
-- hA from hARG at `closingNDecl` rewritten by hKD; hC from hTEL transported along hENV (inst/instS equal at c).

/-- (C-RUN) The run form. `env₀`-uniform suppliers only; nothing per declaration. -/
theorem argWidthAt_of_closingRun {mref cref} (L : Laws mref cref) (env₀ : Environment) {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {D : Design}
    (cr   : ClosingRun L (genP env₀) Reach mctx cctx X p w w' raw D)
    (KD   : ∀ X p, genP env₀ X = some p → p.kD = closingNDecl p.d.shape)           -- DG-GENPKG + closingNDecl_eq_kD
    (OSH  : ShapeFuelBridge)                                                     -- §2, = DG-COVER D2(b) boundary
    (TY   : ∀ E senv, ReadTyped HK E senv)                                       -- §3.3, typing obligations
    (HKL  : PhKindingLaws HK)                                                    -- §3.1
    (ENV  : ∀ b ci envR envR' w5 w6, RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
              ∀ c, SigEq (structEnv envR') (structEnv env₀) c)                 -- DG-ENV (C0) at this run
    (TEL  : ∀ c q, genP env₀ c = some q → CalleeTeleAll (structEnv env₀) c q) :  -- DG-DECLCONNECT + DG-READKINDS
    ∀ k, ArgWidthAt (genP env₀) p k
-- obtain ⟨b, ci, envR, envR', w5, w6, …, hreads, …⟩ := cr.shared; shapeEq → OSH → fuel shape → SIG (§2) and LK (§3)
-- at senv := structEnv envR'; then argWidthAt_of_read.
```
Shared definitions (new, src-argw side; types only reuse SA0):
```lean
def ShapeSigProv (senv : StructEnv) (sp : MachineShape) : Prop :=
  sp.instOrigins.length = sp.insts.length ∧
  ∀ k (hk : k < sp.insts.length), (sp.instOrigins.getD k .ord).child? = none →
    ∃ kinds, SigKindsAt senv sp k (sp.insts[k]).1 kinds                     -- ArgWidthSrc:134-138
def ShapeArgKinds (senv : StructEnv) (sp : MachineShape) : Prop :=
  ∀ k, ArgKindsAt senv sp (closingNDecl sp) k ∧ ArgKindsAtS senv sp (closingNDecl sp) k   -- ArgWidthSrc:66,100
def SigEq (s s₀ : StructEnv) (c : Name) : Prop := s.inst c = s₀.inst c ∧ s.instS c = s₀.instS c
def CalleeTeleAll (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  CalleeTeleAt senv c q ∧ CalleeTeleAtS senv c q                          -- ArgWidthSrc:71,105
```
`closingNDecl` is Tools/ShippingCallWidthsEntry.lean:62-63 (= E:5216's `nDecl`).

## 2. SIG: provenance route
- **Existing (fuel model, kernel-closed):** `machineShapeF_final_instProv` (Tools/ShippingReaderFuelShapeProv.lean:226-233)
  gives `InstProv senv st` with `shapePost … = some sp`; `InstProv` (Tools/ShippingReaderFuelProv.lean:167-172) has
  `instOrigins.size = insts.size` and, per tag, `OriginT` (:149-153): `.ord` → `OrdOrigin` = `∃ kinds, senv.inst c =
  some (kinds, r)` (:89-90); `.field i` → `StructOriginI`, whose first conjunct is `senv.instS c = some (kinds, ty)`
  (:95-100). Alignment `machineShapeF_instOrigins_length` (ShapeProv:237-242) and `instOrigins_getD_eq` (:246-249).
  `sigDisj_structEnv` (Tools/ShippingReaderFuelR1.lean:87) makes `inst`/`instS` disjoint for `structEnv`.
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
  owned by `sparkle-gen5-package-coverage`, DGEN:723); SRC-ARGW must not state a parallel one. DGEN does not yet write
  its text: request it there (§5 R1).

## 3. LetKindOk and the per-argument typing
### 3.1 Definitions (full text)
Placeholder conventions: E:3500-3506 (`_machIn`, `_machSlot`, `_machLet`, `_machInst`); de Bruijn closing E:4255-4263
(`_machIn i` ↦ the `i`-th input counted from the LAST of `bs`).
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
/-- THE invariant: every stored let value has its stored kind, in the context of the SAME state (history-carrying). -/
def LetKindOk (HK : PhKinding) (bs : List (Name × MixedGateBinder)) (st : MachRead) : Prop :=
  ∀ j nm kd v, st.lets[j]? = some (nm, kd, v) → HK (phKind bs st) v kd
```
### 3.2 Induction over the reader's let construction (on `machineShapeF`, like `InstProv`, ShapeProv:229-233)
Push sites are exactly E:3627, :3647, :3671, :3750; lets are never removed or rewritten (grep `lets :=`/`lets.push`
in E: only these four pushes and their callers :4009-4010, :4070-4071, :4110-4111, :4174-4175, :4187-4190,
:5130-5132). All other state growth is by push/append, so `phKind` only extends (→ `mono`).
| case | site | LetKindOk preserved from | at a call: `lets[a].kind = kinds_j` from |
|---|---|---|---|
| F fresh push | E:3750 (via :4070/:4110) | `ArgTyped` (§3.3) for the pushed `v'` | the push itself (kind := `kinds_j`) |
| R1 `_machLet j` | E:3746 | no push | `ArgTyped` at `v' = _machLet j` + `var` ⇒ `lets[j].kind = kinds_j` |
| R2 value dedup | E:3748-3749 | no push | `LetKindOk` at `j` + `ArgTyped` at `v'` + `EqvSound` (`lets[j].v == v'`) + `uniq` |
| user let push | E:3627/:3647 (`machBindLet(Named)`, kind `mixedGateBinderKind? ty`, E:3620/:3641) | `LetTyped` (§3.3) | — |
| user let dedup | E:3625/:3645 (returns `_machLet j` for annotation kind `k`) | no push; but later uses of `x` carry `lets[j].kind`: `LetTyped` + `EqvSound` + `uniq` give `k = lets[j].kind` | — |
| alias push | E:3654-3671 (stores RESOLVED `val`, kind of `y`) | `LetTyped` at `v'` + `var` along `resolve` + `LetKindOk` of the resolved lets | — |
| memory-op push | E:3956-3959 hard-coded `[.domain, .bits aw, .bits dw, .bool, .bits aw]` | `MemArgTyped` (§3.3); `aw`/`dw` from `natOf` (E:3954) need `kernelNat` correctness | not a target entry (`hnone`), but a source of R2 kinds (AUD A6) |
| domain arg | E:4065-4068 / :4104-4107 | no push, no index | no obligation (`Pkg.ports` drops `.domain`, Tools/ShippingGen2Pkg.lean:80-81) |
Then `LK2`: at the end, `shapePost` must expose `binders = bs ++ instBinders ++ slots ++ st.lets.map (nm, kind)`
(E:5183-5184; missing on the fuel side, FRZ:206) so that `ShapeArgKinds` reads `lets[a].kind` at `closingNDecl + …`.
**Provable from existing facts:** the R1 and domain cases, the push/no-push bookkeeping, `mono`-transport, the alias
`resolve` induction, final placement (given LK2). **Not:** every case marked `ArgTyped`/`LetTyped`/`MemArgTyped`/`EqvSound`.

### 3.3 What remains (exact Props)
```lean
/-- Source typing of the call's j-th argument, then conversion preserves the kind. One Prop per obligation kind. -/
def ArgTyped (HK) (senv) : Prop :=   -- for every machInstance/machInstanceS fold step (instArg/instSArg, FuelDefs:412,442)
  ∀ env bs kind arg st v' st', kind ≠ .domain → SrcKind senv env arg kind →
    machConv senv env 0 arg st = some (v', st') → HK (phKind bs st') v' kind
def ReadTyped (HK) (E : ConstantInfo) (senv : StructEnv) : Prop :=
  ArgTyped HK senv ∧ LetTyped HK senv ∧ MemArgTyped HK senv ∧ CallSrcKinds E senv
-- CallSrcKinds: at every call `c a₁…aₙ` the reader meets in E's NORMALISED body (E:5088-5090),
--   SrcKind senv env aⱼ kindsⱼ with kinds = telescopeKinds (env.find? c).type (E:4367-4369).
-- EqvSound : ∀ a b : Lean.Expr, (a == b) = true → (∀ Γ k, HK Γ a k ↔ HK Γ b k)      -- §5 D1
```
- `SrcKind` is the per-argument typing judgment: "`arg` (pre-conversion, in env `env`) has type `Signal _ Bool` for
  `.bool`, `Signal _ (BitVec n)` for `.bits n`". It is the ONLY place the callee kind enters on R1/R2.
- **Relation to DC-FORM `ExprDenotes env e α v` (DGEN:448-450):** `CallSrcKinds` is the per-node typing consequence of
  `ExprDenotes` at an `app` of `const c`. But a `Sort`-indexed `α` does not separate kinds: `Signal d (BitVec 1)` /
  `Signal d (BitVec 2)` / `Signal d Bool` (Signal is a structure, Sparkle/Core/Signal.lean:92) have no type-disequality
  proof available by cardinality, so `α = α'` cannot yield `n = m`. The carrier needed here is KIND-indexed
  (e.g. `ExprDenotesK env e (k : MixedGateBinder) v`). Request to DC-FORM (§5 R2); not formulated here.
- Through normalisation (`machNorm`/`inlFoldNat`/`zeroLit`/`rootFloat`, E:5088-5090) `SrcKind` must be preserved
  (FRZ:236 item 2); `natOf` literal injectivity (FRZ:237-238).
- **Bool vs `.bits 1`.** The row compares widths only (`kindTy .bool` and `.bits 1` both width 1, AUD A10), so the row
  is weaker than kind equality. `LetKindOk` is stated KIND-exact on purpose: the compiler's gate check separates them
  (`mixedBitKinds` maps `.bool` to `.domain`, E:2355-2359; `unifiedGateBoolBody` vs `…BitsBody`, E:2521/:2560), and
  `uniq` would be false for a width-only `HK`. The final step uses only `(kindTy ·).bitWidth` (ArgWidthSrc:69).
- **Run-side partial source (finding).** `unifiedGateRoot` (E:2619, called E:5185) checks the packed body, i.e. each
  let field at its kind (`machField`, E:4298-4301). With `HK :=` a placeholder mirror of `unifiedGate*Body` (LK3) this
  would supply `LetKindOk` at the FINAL state, but only where the concat arm checks operands: its `none => true`
  branches skip them (Tools/ShippingUnifiedExecutionSoundness.lean:44-49; Tools/ShippingLetsCloseRoute.lean:20). It
  never supplies `ArgTyped` (the callee kind is not in the packed body).

## 4. VT / P5 / ENV / KD: consumed from gen5, not duplicated
| SRC-ARGW need | exact Prop consumed | gen5 unit (owner issue) | what is still to request |
|---|---|---|---|
| ENV | `∀ c, SigEq (structEnv envR') (structEnv env₀) c` at THIS run's `envR'` (RunReadsAt, DGEN:540-541; read at M5:221) | DG-ENV / C0 `ReadsAt env₀` (DGEN:315-328, row :654) — `sparkle-gen5-reader-bridge` (DGEN:722) | C0 states only `find?` inclusion "plus equal … structEnv" as a comment (DGEN:319); `instSignature?` also reads `isHardwareModule` (E:4375, :4386), so the `structEnv`/`inst`/`instS` equality must be in C0's text, at every world of the run (the second `getEnv`, M5:221) |
| VT | `adapterOf ci.type (structEnv env₀) q.d = some _` for each callee (existence conjunct of `DeclConnect`, DGEN:472-476) + a width projection `adapterOf_portWidths` | DG-DECLCONNECT / DC-SUPPLY — `sparkle-gen5-decl-bridge` (DGEN:725) | `SigAdapter` exposes only `toSig` (DGEN:465-466); the `args` map (DGEN:458) must be data or have a lemma `adapterOf … = some _ → telescopeKinds ci.type = some ks → (ks.filter nonDom).map w = q.portWidths` |
| P5-arg | peel kinds of `packTupleInputs (inl value)` (E:5078, E:3410) = `telescopeKinds ci.type` for a callee with `instSignature? = some` | DG-READKINDS total `packTupleInputs` (DGEN:303-309, row :646) — `sparkle-gen5-reader-bridge` | the property "identity on binders with `mixedGateBinderKind? ≠ none`" and the inliner's type invariance (`inlinedConst` rewrites the type too, E:3410); DG-READKINDS does not state it (AUD B row 3) |
| q's shape | `genP env₀ c = some q` ⇒ `q.d.shape` = `machineShape? false [] (entry₀ env₀ c) (structEnv env₀)` | C1/C3/C5 `genS_some_inv`, `genP` (DGEN:330-336, :369-374, :395-400) — `sparkle-gen5-package-coverage` | `Pkg.d (genPkg s _) = s.d` (DG-GENPKG) |
| KD | `p.kD = closingNDecl p.d.shape` for generated packages | DG-GENPKG + missing `closingNDecl_eq_kD` (scripts/gen2/S4_CONSUMER_FREEZE.md:510-512) | — |
The callee half is STATIC in `env₀`: with `P = genP env₀`, `q` is computed from `env₀` (DGEN:330-336), not from the
callee's own run, so ENV is needed only for the parent's `structEnv envR'`.

## 5. Units, order, STOP/decision items
| unit | statement | inputs | size (est.) | deps | owner |
|---|---|---|---|---|---|
| SC0 | defs §1 + `argWidthAt_of_read` | SA0 (ArgWidthSrc:91,124), `sigDisj_structEnv` | 100-180 l | — | src-argw child |
| SC1 | `shapeSigProv_of_fuel` | ShapeProv:226-249, FuelProv:89-172 | 60-120 l | — | src-argw child |
| LK0 | §3.1 defs + init/extension lemmas | MachRead E:3563-3600 | 100-180 l | — | src-argw child |
| LK1 | `LetKindOk` preservation through the §3.2 table on `machineShapeF` (premises §3.3) | FuelDefs:412-452, InstProv pattern | 300-600 l | LK0 | src-argw child |
| LK2 | `shapePost` exposes `letB`; `ShapeArgKinds` from LK1 at `closingNDecl` | FuelShape:153, ShapeR5:318 | 150-300 l | LK1 | src-argw child |
| LK3 | `HK` instantiation (placeholder mirror of `unifiedGate*Body`) + `PhKindingLaws` (`uniq` is new) | E:2521-2633 | 200-400 l | LK0 | src-argw child |
| TY | `ReadTyped` for every successful source: machConv/normaliser kind preservation | DC-FORM kind-indexed carrier | unknown, likely ≥ 1000 l | DC-FORM (R2) | src-argw child; carrier = decl-bridge |
| CR | `argWidthAt_of_closingRun` | `ClosingRun` (DG-CLOSINGRUN), SC0-LK3 | 100-200 l | DG-CLOSINGRUN | src-argw child |
| (consumed) | OSH, ENV, VT, P5, q-shape, KD | §2, §4 | — | — | package-coverage / reader-bridge / decl-bridge |
**Order:** SC0 → SC1 ∥ LK0 → LK3 ∥ LK1 → LK2 → CR (CR conditional on consumed Props, explicit as premises until
they land); TY after DC-FORM answers R2. Controls (like Tests/Gen3/ArityCheck.lean): expected-type comparison and
meaning-changing mutants for SC0/SC1/LK2; decided rows on a corpus `P` are intermediate evidence only.

**Requests (not decisions):** R1 package-coverage: write `ShapeFuelBridge`'s text as DG-COVER's boundary (§2).
R2 decl-bridge: DC-FORM kind-indexed denotation, and `adapterOf_portWidths` (§4). R3 reader-bridge: C0 text with
`structEnv` equality at every world of a run; DG-READKINDS `packTupleInputs` identity property.

**STOP / decision items (options only; none adopted):**
- **D1 `Expr.eqv` soundness** (R2 branch E:3748, user-let dedups E:3625/:3645/:3669). `==` on `Lean.Expr` is the extern
  `Expr.eqv`; nothing about it is provable (Tools/ShippingReaderMatcherArity.lean:36-40, :488-490; same in the fuel model,
  R-reader-fuel.md:55-57). Options: (a) a law on the extern = new TRUSTED boundary (user item); (b) compiler change to a
  kernel-visible comparison in the dedups (output policy: function check, area/speed, record); (c) none → R2 stays
  unsupplied. Impact: without one, the R2 and dedup rows of §3.2 cannot close.
- **D2 O1/O2** (`ShapeFuelBridge`): not new; shared with DG-COVER D2 (DGEN:679-693). No separate SRC-ARGW decision.
- **D3 width-separating carrier**: if DC-FORM keeps only `Sort`-indexed `ExprDenotes`, `TY` has no carrier; then a
  report with options (kind-indexed refinement vs. a typing assumption = guarantee change, FRZ:230-231) goes to the user.
- **D4 VT elaboration shape**: the kernel gives only defeq of value-binder and type-binder types; the syntactic
  agreement `mixedGatePeel` (E:2345-2350) vs `telescopeKinds` (E:4367-4369) (count and literal widths) is a fact of
  elaboration. If `adapterOf` (R2) cannot supply it, options: a reader-tail check (G-T, FRZ:268-270; compiler change)
  or a law. Not adopted.
- D-ARGW stays HELD (FRZ:300-302); G-E/G-T remain comparison material (AUD §C/§D).

## 6. Not claimed
- Nothing written in Lean, elaborated or built; all texts are proposals; sizes are estimates.
- No claim that `ShapeFuelBridge`, `ReadTyped`, `EqvSound`, VT or P5 hold, are provable, or are unprovable.
- No claim that `HK`'s `uniq` holds for the mirror of `unifiedGate*Body`, nor that `unifiedGateRoot` supplies `LetKindOk`.
- No width-mismatched successful run is exhibited or excluded. No change to `T1Hyp`, `ChildShips`, `DataOkB`, FG,
  the compiler, or any gen5 freeze; owners/requests above are proposals for review.
