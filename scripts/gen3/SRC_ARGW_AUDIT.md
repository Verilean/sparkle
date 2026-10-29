# SRC-ARGW audit rev0: machConv kind correspondence, gen5 overlap, G-E made concrete

**Research notes, TEXT ONLY.** Nothing was built, elaborated or run. No `.lean` file, lakefile or shared definition was
edited. Base `par/gen2-spec` 2b79ba09 (Sparkle/ and the cited Tools/ files are unchanged since a5998484).
`[T]` = `~/git/.kjob/gen5-t2` (3be26aee). Companion of scripts/gen3/SRC_ARGW_FREEZE.md rev1 (cited as FREEZE).
"Not found" / "not supplied" below are survey findings, not impossibility claims.

## A. machConv audit: from the pre-normalisation source type to the let kind
The question is not only whether differently typed Exprs can become `==`. It is whether, for each way an argument
let gets its kind, the kind equals the width of the source type before normalisation. Read path by path
(Sparkle/Compiler/Elab.lean):

| # | site | where the kind comes from | what relates it to the source type | status |
|---|---|---|---|---|
| A1 | normalisation, :5088-5090 | the let annotation `ty` after `machNorm` → `inlFoldNat` → `zeroLit` → `rootFloat` | `machNorm` keeps binder types "as written" (:4966-4967). But `Nat` lets and closed `BitVec` lets are SUBSTITUTED (:4988-4992), and `inlFoldNat` (:3290) folds literal sums afterwards (comment :5086-5087). A source annotation `BitVec (W+1)` can therefore become a literal kind only after normalisation | the source type and the read kind agree only up to the defeq that the folding performs. Preservation is not supplied |
| A2 | `machBindLet` :3619-3627 (root lets :5131, body lets :4009) | `mixedGateBinderKind? ty` (:3620) | `.domain`/`none` kinds are SUBSTITUTED, with no let (:3621-3622). A bare variable is substituted (:3624). Dedup is by VALUE only (`l.2.2 == v'`, :3625), ignoring kind and name | a later let with another annotation but a `==` value takes the FIRST let's kind |
| A3 | `machBindLetNamed` :3640-3647 (:5130) | annotation kind (:3641) | dedup by value only (:3645) | as A2 |
| A4 | `machBindLetAlias` :3654-3671 | annotation kind of the ALIAS `y` (:3664) | the stored value is the RESOLVED value of `x` (:3655-3662). Dedup is by (name, resolved value) (:3669). If the resolution ends in a let placeholder it falls back to `machBindLetNamed` (:3663) | the kind is `y`'s annotation, the value is `x`'s definition |
| A5 | `_machLet j` at a call, `machLetIndex` :3746 (R1) | `lets[j]`'s kind (from A2-A4) | none at the call: the callee kind is dropped | R1 |
| A6 | value dedup at a call, :3748-3749 (R2) | the first let with `==` value | the earlier let may be a user let (A2-A4), an F push for ANOTHER callee (:3750), or a P-mem push with hard-coded kinds (:3958-3959; widths from `memCall?`'s `natOf`, :3954) | R2. P-mem as a source of a reused kind is new in this audit |
| A7 | domain removal, :4065-4068 / :4104-4107 | — (no index) | the domain arg is compared with `st.dom` by `!=` on placeholder Exprs. `Pkg.ports` drops `.domain` too (Tools/ShippingGen2Pkg.lean:80-81). Only the ORDER of the non-domain kinds must agree; where the domain binders sit does not matter | no kind obligation |
| A8 | instS argument path, :4100-4111 | the same `machLetIndex` | identical fold. In addition, the result-type parameters are converted (:4113-4116) but bind no let. Dedup is by `(c, js, .field 0)` (:4118-4119) | as A5/A6 |
| A9 | placeholders: `machSlot` (:3894), `machIn` (:3914), `_machLet`, `machInstOut` (:4077-4078, :4129) | the kind of a placeholder lives OUTSIDE the Expr (`st.kinds`, let kinds, `bs`, `insts[k].2.2`) | `machConv` is structural on `.app`/`.lam`/`.forallE` (:3965-3986). Type arguments stay in the Expr. Literals and constants are returned unchanged (:4014). `.mdata`/`.proj` are refused (:4012-4013). `bundleIota`/`machProjIota` (:3969-3970) rewrite projections of bundles | not found: a site where two source terms of different Lean types become one `==` placeholder Expr. That was not shown impossible |
| A10 | `.bool` vs `.bits 1` | — | `kindTy .bool = .bit` and `kindTy (.bits 1) = .bitVector 1` both have `bitWidth = 1` (Tools/ShippingMachineEntry.lean:232-235; Sparkle/IR/Type.lean:137-139) | the row compares widths only, so a Bool/BitVec-1 kind confusion is invisible to `callArgsOkAt` (weaker than kind equality) |

**Probe plan (if one is run). Two kinds of result must be kept apart.**
- **(S) Hand-written Expr / synthetic shape.** Examples: call `machLetIndex` on `lets = #[(n, .bits 8, v)]` with kind
  `.bits 16` and the same `v`; or build a `MachineShape` whose let kind differs from a `kidWsP` entry and `decide` the
  row `false`. These show what the FUNCTIONS do: kind-blind reuse is already visible at :3748. They say nothing about
  whether a type-checked source reaches that state.
- **(R) Type-checked source with a successful run.** A `@[hardware_module]` parent that elaborates (kernel-checked),
  whose `machineShape?` is `some`, and whose closing succeeds, with a call-argument width ≠ the callee port width.
  Candidate attempts: (R-a) A6 through a memory op value reused by an ordinary call; (R-b) A4, an alias whose
  annotation is defeq but not syntactically equal to `x`'s; (R-c) A1, a width that becomes literal only after the
  `Nat`-let substitution. None was exhibited. None is claimed to exist or not to exist.
- Not finding a type-(R) counterexample is NOT a preservation proof. The obligations of FREEZE §3 (ii-I) stay open
  either way.

## B. Connection to the gen5 reader / DG-DECL work
| SRC-ARGW obligation (FREEZE) | gen5 item ([T]) | relation |
|---|---|---|
| ENV: the callee run's `getConstInfo c` = the parent run's `envR'.find? c` (FREEZE §1.3) | DG-ENV / C0 `ReadsAt env₀` (DGEN_FREEZE.md:314-328, :630). `envR' = envR` is not in `Laws` (M5_INDEP_STUDIES.md:255) | **same obligation.** SRC-ARGW needs it at a second name (the callee), which C0's `∀ X` covers |
| VT: the callee's peel kinds of `value` = `telescopeKinds ci.type` | DG-DECLCONNECT: `adapterOf ci.type (structEnv env₀) p.d` with its `args` component "order/kind/width map from the actual binders to `p.d.bsIn.take p.kD`" (DGEN:454-458, :474) | **same content, different direction.** If `adapterOf` is required to succeed on the actual type and to agree with `bsIn`, then VT (width projection) follows. DeclConnect's existence conjunct is a coverage obligation (DGEN:484-486) |
| P5-arg: `packTupleInputs` identity on a callable callee; R1 read through `rootFloat` | DG-READKINDS: total replacements for `rootFloat`/`zetaAll`/`packTupleInputs` (DGEN:307-308, :622; M5:174-182) | **same objects.** A total replacement plus its agreement with production would carry the property SRC-ARGW needs. DG-READKINDS does not state that property |
| per-argument typing / `LetKindOk` (FREEZE §3 (i), (ii-I)) | DC-FORM `ExprDenotes` / `ConstValue` (DGEN:444-450, :487-493); row 2 `dataOf_sound` via `readTerm_sound` / `readN_expr_sound` (DGEN:503-504) | **candidate shared carrier.** `readTerm2`/`readN` (M5:137-138) read `shape.body` (the PACKED Term), not the reader's let kinds, so they supply nothing on argument kinds as they stand |
| reader provenance: `hsig`, `instOrigins.length`, `ArgProv` on `machineShapeF` | DG-COVER (DGEN:635; D2(b) :651-659), the fuel model with the O1/O2 boundary (M5:184-190) | **same model and boundary.** `ArgProv` would be a new invariant beside `InstProv` (Tools/ShippingReaderFuelProv.lean:167) |
| `readTerm2` / `readN` completeness on the lifts (M5:159) | DG-READKINDS | not an SRC-ARGW obligation (body Terms, not argument kinds) |

## C. G-E (compiler input-width guard) made concrete, for comparison only (NOT proposed for application)
**Guard text (comparison).** In `instStmt`, after `argWs`/`inPorts` (Sparkle/IR/Machine.lean:275-277), and in
`instStmtG` after :34-35 (Sparkle/IR/MachineInstG.lean):
```lean
if !(inPorts.zip argWs).all (fun (p, w) => wireWidth m.wires w == p.ty.bitWidth) then none else
```
`wireWidth` is Machine.lean:130-134. `closeLets` already uses the same form on let aliases (Machine.lean:190), and so
did the declined output analogue (scripts/gen2/S4_WID_SUPPLY.md:74).

**Which `m`, and when `wireWidth m.wires w` equals UARGW's `declWidth b w`.**
- `m` is `closeMachine layout t'` (Elab:5262-5263) for `closeInsts`, and `withClockFor children m0` for `closeInstsG`
  (MachineInstG.lean:120). `withClockFor` changes inputs only (:73-78).
- The returned raw module keeps `m.wires`: `{ m' with body }`, where `m'` changes inputs and body only (Machine.lean:407-409,
  :426; MachineInstG.lean:123-125, :144).
- `b` is `dropZeroWidthModule M` or `mergeChecked (dropZeroWidthModule M)` (UARGW_PARENT_SURVEY.md:100). `declWidth`
  (Sparkle/IR/RegDedup.lean:172-176) has the same body as `wireWidth`, on `b.wires`.
- So the two values agree when:
  - (Z) zero-width removal keeps `w`'s entry. `dropZeroWidthModule` filters `bitWidth != 0` (Sparkle/IR/ZeroWidth.lean:118),
    and is the identity when not `allConcrete` (:114). Let kinds have width > 0 (Elab:2342).
  - (M) cleanup/merge keeps `w` (UARGW o2, :40: `dropZW_wires`, `mergeChecked_ports`; `mergeChecked_cases`,
    Sparkle/IR/RefineCheck.lean:280-281).
  - (U) no earlier wire of the same name: both functions take the FIRST `find?` match (Machine.lean:131; RegDedup:173).
    `closeMachine` appends its next-wires AFTER `t.wires` (Machine.lean:111). UARGW o18 `huniq` (:56) and o19
    `declWidth_of_unique` (:57) already carry this.
  - (D) `w` is declared at all. `wireWidth` is 0 for an undeclared name (Machine.lean:129). That every port is a wire is
    the docstring claim at Machine.lean:203-204; it was not re-verified here.
- A proof can also avoid `b`: an L2-style lemma stated on the raw `M` (pre-post-processing), composed directly with the
  guard.

**After a guard failure.**
- `instStmt` → `none` → `closeInsts` → `none` (Machine.lean:400-405), and the same for G (`stmtsG`, MachineInstG.lean:56-68).
  `synthesizeMachineCertified` returns `none` (Elab:5262-5263), and the caller takes the legacy route (doc Elab:5249-5251).
- A legacy SUCCESS is still in FG's scope. It is [T] DG-FALLBACK's producer (DGEN:638; also :659, :665). The guard
  therefore does not remove those runs from FG; it moves them from the machine route to DG-FALLBACK.

**Change range (counts by grep at 2b79ba09; not a proof plan).**
- Compiler: Machine.lean:272-287 (`instStmt`), MachineInstG.lean:30-52 (`instStmtG`).
- Option 1, widen `CallStmt` (Tools/ShippingMachineInst.lean:190-203) / `CallStmtG` (Tools/ShippingMachineInstG.lean:19-37)
  with a width conjunct. Both need a new `m`/`wires` parameter, because neither mentions `m` today. That touches
  every reference: 100 lines in 34 files (`grep -rn 'CallStmtG\?\b'`, incl. Tests/Compiler/OneOutCallerTest.lean:58).
  The positional `obtain ⟨…⟩` destructurings shift.
- Option 2 (smaller): keep `CallStmt`/`CallStmtG` and add separate supply lemmas.
  - `instStmt_argW : instStmt … mc m = some st → ∀ j p w, inPorts[j]? = some p → argWs[j]? = some w →
    wireWidth m.wires w = p.ty.bitWidth`; the same for `instStmtG_argW`;
  - `closeInsts_argW` / `closeInstsG_argW` lift them along `closeInsts_calls` (Tools/ShippingMachineInst.lean:247-252)
    / `closeInstsG_insts`;
  - an L2 bridge `declWidth b w = wireWidth M.wires w` under (Z)(M)(U)(D).
- Either option re-proves the proofs that unfold the definitions (`split at h` chains). There are 31 `unfold`/`simp`
  sites of `instStmt`/`instStmtG`/`closeInsts`/`closeInstsG`/`stmtsG` in: ChildServe:57,141,206,229,252;
  CloseChecksG:48; InstStmt:50; CloseInstsSome:53; MachineInst:152,208,254,283,302,433,457; CallsStmtsG:261;
  MachineInstG:43,238,255,316,327,377,457; CacheCoherentCert:152,171; OneOutClose:44,74; InstStmtG:89;
  TopShareNoParent:45; CacheCoherentClose:86,105 (all `Tools/Shipping*.lean`).
- The existence lemmas gain a width premise: `instStmt_some` (Tools/ShippingInstStmt.lean:20), `instStmtG_some`
  (Tools/ShippingInstStmtG.lean:31), and through them `closeInsts_some_of` (Tools/ShippingCloseInstsSome.lean:40).
- Tests that mention `instStmt*`: Tests/Compiler/ShippingCloseInstsCheckTest.lean, Tests/Gen2/S3GroupCheck.lean.
- Per-declaration generated endpoints that reduce `closeInsts` were not surveyed.

**What it resolves.**
- INPUT widths only. With L2 (UARGW §2), L5 (UCHILD §1) and U-ARITY, it gives `callArgsOkAt` for the actually served
  child, with no VT / P5-arg / ENV / typing.
- Output widths (G-ONEOUT-WID) are NOT resolved. That would need the separate output guard
  `wireWidth m.wires outW == outP.ty.bitWidth` (S4_WID_SUPPLY.md:74, declined), or, for groups, one guard per field.
  `instOutWidthsOk` (Tools/ShippingHierOpen.lean:503-514) is a run-side Bool, not a compiler guard.

**Policy obligations** (compiler output policy: output fixed by default; a deliberate change needs a function check,
an area/speed measurement and a record):
- a function check that every shipping design is unchanged where the guard passes (golden comparison against the
  previous compiler);
- a corpus measurement of refusals (shipping-coverage), area/speed if any output changes, and a record;
- **0 refusals on the corpus is NOT all-success coverage.** Every successful run outside the corpus stays under FG,
  through DG-FALLBACK when the guard refuses.

## D. Summary for the next review
**Props that remain on the derivation (source) route**, per call entry `k` with `hnone` (FREEZE §2):
1. `SIG`: `SigKindsAt (structEnv envR') p.d.shape k c kinds`, plus `instOrigins.length = insts.length` (reader provenance; FREEZE §2.3).
2. `ArgKindsAt` (`.ord`) / `ArgKindsAtS` (`.field`) at `nDecl = p.kD` (F branch: `ArgProv`; R1/R2: `LetKindOk` plus the
   per-argument typing obligation; FREEZE §3 (i), (ii-I)).
3. `CalleeTeleAt` / `CalleeTeleAtS` ⇐ VT ∧ P5-arg ∧ ENV (FREEZE §1.3).
4. Index alignment: R5, `KDp`/`KDq`, `closingNDecl_eq_kD` (missing small lemma, S4_CONSUMER_FREEZE.md:510-512).
5. Run wrapping: `hp`/`hq` at the actual reads (`T1Hyp.defines`; [T] `RunReads`, M5:208-241).

**G-E sites and supply-lemma proposal.** Change sites: Machine.lean:272-287, MachineInstG.lean:30-52 (§C). Option 2
lemmas: `instStmt_argW`, `instStmtG_argW`, `closeInsts_argW`, `closeInstsG_argW`, the L2 bridge
`declWidth b w = wireWidth M.wires w`, then SA3 `argWidth_of_portTie` (L2 + G-E + L5 + U-ARITY ⇒ row).

**Cost comparison (ESTIMATES, unmeasured).**
| route | new proof | shared with gen5 | other cost | closes |
|---|---|---|---|---|
| source | SA0 100-160 l; `ArgProv` + `LetKindOk` on the fuel model 300-500 l + O1/O2 link; typing/denotation carrier + normaliser preservation: unknown, likely ≥ 1000 l; VT/P5-arg 200-400 l | ENV = DG-ENV (200-600, DGEN:630); carrier = DC-FORM; P5-arg via DG-READKINDS (500-1200, DGEN:622) | none on the compiler | input widths, if every item is supplied; no new route |
| guard (G-E, Option 2) | 2 compiler `if`s; 31 unfold sites re-proved (est. 5-40 l each); 3 existence lemmas + premise; 4 supply lemmas + L2 bridge 200-350 l; SA3 150-250 l | none needed for inputs | function check, corpus refusal measurement, area/speed, record; DG-FALLBACK carries every refused success | input widths only; outputs stay open (G-ONEOUT-WID) |

D-ARGW stays HELD (FREEZE §4). This table is comparison material for the reviewer, not a recommendation to the user.
