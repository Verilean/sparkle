# U-CHILD-PORTTYS change-site table rev0: exporting the served child's argument-port widths (DPORT L5)

**FOR REVIEW — design only, nothing built or proved. NO change is applied:** `ChildShips`, `ChildRunN`,
`SeqChildRunN`, `CombChildRunN`, `ShipsRes`, `T1Hyp`, `DataOkB` and FG are unchanged at 10377764. No Lean was run.

Issue `sparkle-gen3-uchild-porttys`. Base: `par/gen2-spec` at **10377764**. All `file:line` citations are at
10377764 unless marked `[M3]` (= `par/gen3-induct` at 96cbd548). Route: DPORT_ROUTE_REPORT.md rev1 §1 L5, §0 rows
"child interface port export" and "producer-local `argPorts` identity", §3 item 3. The format follows
S4_WID_SUPPLY.md §4.1.

## 1. Which variant: widths (recommended) or types
Candidate T (DPORT §2): `ChildPortTys q mc : (argPorts mc).map (·.ty) = q.ports.map (fun b => kindTy b.2)`.

Candidate W:
```lean
/-- G-CHILD-PORTW: the served module's argument ports have the package's declared port widths. -/
def ChildPortWidths (q : Pkg ι dom) (mc : Sparkle.IR.AST.Module) : Prop :=
  (Tools.ShippingMachineCompose.argPorts mc).map (fun p => p.ty.bitWidth) =
    q.ports.map (fun b => (kindTy b.2).bitWidth)
```
The right-hand side is `Pkg.portWidths q` (Adapt:80) by `rfl`. It is written inline because Defs is upstream of
Adapt.

**What the consumers need.** `callArgsOkAt` (Adapt:73-77) compares only `(kindTy bn.2).bitWidth` with `ws[j]?`.
`call_inRange_at` (Adapt:106-163) uses widths only (through `callArgsOkAt_width`, :144, and `sortOf_width`). The
PortTie sketch (DPORT:81-84) compares `declWidth b w : Nat` with `(argPorts mc)[j].ty.bitWidth`. No consumer
compares port TYPES.

**T ⇒ W.** Apply `congrArg (List.map HWType.bitWidth)`, then `List.map_map`. This is a two-line lemma
`childPortWidths_of_tys`. The converse is not claimed.

**Recommendation: W**, the weaker sufficient one. It is robust if an emitted port's type differs from `kindTy` while
the width agrees. For example, `.bit` vs `.bitVector 1`: no such case is known, and none is claimed. W is the sufficient
width guarantee used here for the final-FG obligation (§4); its minimality is not proved. Producers prove T anyway (`machPorts_tys`, PortWidthsPure:142-147) and project to W,
so W costs nothing extra.

**Where to place it (recommendation): as a conjunct of `ChildShips`, OUTSIDE `∀ dsn … ∀ i`.** It is a static fact
about `mc`, independent of the design and of `i`:
```lean
def ChildShips (q : Pkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Design) : Prop :=
  ChildPortWidths q mc ∧
  ∀ (dsn : Design), (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) →
    moduleByName dsn.modules mc.name = some mc →
    ∀ (i : ι), ChildRunN (childMap dsn.modules) dsn n mc (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i)
```
Two alternatives were considered:
- **(alt-R) Put the conjunct inside `SeqChildRunN` and `CombChildRunN`.** Every `SeqChildRunN` producer (about 15
  sites, including generator templates) would then have to prove it (rows marked *alt-R only* in §3). Not
  recommended.
- **(alt-S) Put it in `ShipsRes`/`ShipsAt`.** The ChildShips producers (§3 P1-P4) would still be the ones holding
  the facts, and the IH producers would have to re-thread them. No gain.

Because the fact is outside `∀ i`, it is available even when `ι` is empty. This contrasts with the arity premise
`i : ι` in UARITY_FREEZE.md §4. `ChildPortWidths` also implies arity (`List.length_map`), but U-ARITY does not
depend on it.

## 2. Implication directions (for the recommended placement)
- New `ChildShips` ⇒ old `ChildShips` by projection (`.2`). This lifts to `ShipsRes`/`ShipsAt`/`CacheShips`/`InvAt`
  (positive positions): new ⇒ old.
- Old ⇒ new is **UNPROVED and UNSUPPLIED**. No exported lemma derives `ChildPortWidths q mc` from old `ChildShips`:
  the length conjunct (Defs:67, Depth:71) gives only the count. This is not a claim that it fails. No counterexample
  satisfying old `ChildShips` with mismatched port widths is exhibited.
- Mixed positions keep the classification of PkgCompat:290-294 (no relation claimed either way): `IHAt`
  (`InvAt` premise, `ShipsRes` conclusion), `BodyKeepsInv`/`ChildKeepsInv`/`KeepBodyStmt`/`KeepChildStmt`,
  `ServedShipsStmt` (`ServedP (ShipsRes …)` conclusion, `InvAt` premise), and `StepStmt` (`ServedP (ShipsRes …)`
  premise, `ChildShips` conclusion).
- Statements with `ChildShips` only in the conclusion (`MemParentStmt'`, `MemParentStmt`, `LeafStmt`) become STRONGER
  (new ⇒ old), so their producers must prove the conjunct (§3 P1-P4).

## 3. REVISION TABLE (nothing applied)
| site | kind | file:line | old ↔ new at this site | per-site proof source (where `argPorts = machPorts …` is already proved) | supply unit |
|---|---|---|---|---|---|
| `ChildPortWidths` (new) | definition | Tools/ShippingGen2Defs.lean, before :82 | new | — | U-CHILD-PORTW-DEF |
| `ChildShips` | definition | Defs:87-90 | new ⇒ old (`.2`); old ⇒ new UNPROVED/UNSUPPLIED | — | same |
| GEN2_DEFS copy | text copy | scripts/gen2/GEN2_DEFS.lean.txt:82-90 (cmp-identical to Defs, checked: `cmp` exit 0) | must change in the same commit | — | same |
| `ShipsRes`, `ShipsAt` | text unchanged, meaning strengthened | Defs:135-136, :147-148 | new ⇒ old | — | — |
| `CacheShips`, `InvAt` | text unchanged | Defs:141-143, :151-153 | new ⇒ old | — | — |
| `IHAt`, `BodyKeepsInv`, `ChildKeepsInv`, `KeepBodyStmt`, `KeepChildStmt`, `ServedShipsStmt` | mixed | Defs:158-162, :167-189, :251-260 | no relation claimed | — | re-elaborate only |
| `StepStmt`, `MemParentStmt`, `LeafStmt` | conclusion | Defs:300-313, :319-329, :332-341 | new ⇒ old for the conclusion; StepStmt mixed | — | P1-P4 below |
| `T1Stmt`, `T1Hyp` | unaffected (no `ChildShips`) | Defs:194-212, :347-355 | unchanged | — | — |
| **P1** `leaf_childShips_of_LB` | producer (`mc = b`, register leaf, `insts = []`) | Tools/ShippingGen2Leaf.lean:241-266 | must prove the new conjunct | NOT in this proof; the identity is inside `seqChildRun_of_L`: Tools/ShippingGen2LeafSeq.lean:58-65 (`hbsIn`), :66-67 (`hargs : argPorts raw = machPorts declName ids cache d.bsIn`, from MachineWired:674-676 `hins hnoI`), :68-69 (`hlenIn`), :70-74 (`hbIn`, `hargsB`). Route: re-derive from `wired` (Leaf:256) with **new lemma N-A** + `machPorts_tys` (PortWidthsPure:142-147) + `htake` (Leaf:246) | U-CHILD-PORTW-P |
| **P2** `slotlessLeaf_childShips_of_LB` | producer (comb branch) | Tools/ShippingGen2SlotlessLeaf.lean:283-296- | must prove | IN this proof: `hargs` :325-326, `hargsB` :332-333, `hlenIn` :323-324, `htake` :288. Append `machPorts_tys` (or N-A) | same |
| **P3** `memParent_childShips` | producer (memory parents, also `.loop` via `memParent_ships`: QuantInstance:136) | Tools/ShippingGen2MemShips.lean:39-49- | must prove | via C6 `seqChildRunN_of_composedNW_run` (Tools/ShippingGen2C6.lean:29-56): `calls_ports` (Tools/ShippingMachineDepthChild.lean:41-56, conjunct :56 `argPorts m = machPorts declName ids cache (d.bsIn.take kD)`) at C6:58-59; `hmc` C6:74-78; `hargsMc` C6:79-80; `hlenIn` C6:81-82; C6:85 proves the LENGTH with `machPorts_length`. Route: **new lemma N-B** (C6's premises, `machPorts_tys` in place of `machPorts_length`) | same |
| **P4** `oneOut_childShips` | producer (one-output parents) | Tools/ShippingGen2OneOut.lean:288-332 | must prove | via C6 at OneOut:331 → N-B, premises already in hand (OneOut:301-307, `hNW` :308) | same |
| future producers | StepStmt proof (unbuilt), S3 group parents (another agent: Tools/ShippingGen2GroupComb.lean / GroupServed.lean, not in 10377764) | — | must prove | N-B pattern if they go through C6 or `seqChildRunN_of_composed*` | coordination item |
| **C1** `oneOutWidthAt` | consumer | Tools/ShippingGen2OneOutTop.lean:313 (`hCS D hDc hmod i0`) | must project `.2` | — | U-CHILD-PORTW-C |
| **C2** `oneOutWidthAt` (O copy) | consumer | Tools/ShippingGen2OneOutTopO.lean:306 | `.2` | — | same |
| **C3** `hserve` in OneOut | consumer | OneOut:200-203 (`hcs' D hDc hmod i`) | `.2` | — | same |
| **C4** `hserve` in FitChain | consumer | Tools/ShippingGen2FitChain.lean:949 | `.2` | — | same |
| **C5** `seqFactsRN_of_callDec` | consumer | Tools/ShippingGen2Connect.lean:137-140 (`hcs dsn hcons hmod i`) | `.2` | — | same |
| **C6** PkgCompat `childShips_gen` | Old ⇒ new compat | Tests/Gen2/PkgCompat.lean:300-302 | **BREAKS**: Old.ChildShips (:48-51) has no port conjunct; old ⇒ new is UNPROVED. Either add premise `ChildPortWidths (.gen q) mc` or withdraw, as A-COMB did (:286-294) | — | same |
| C6' dependents | compat | PkgCompat: `shipsRes_lift` :312-315, `shipsAt_lift` :317-320, `cacheShips_lift` :322-325, `invAt_lift` :327-329, `memParentStmt'_gen` :372-389, `memParentStmt_gen` :391-408, `leafStmt_gen` :410-426, `#print axioms` :436-440 | inherit C6's change (conditional or withdrawn); the `.gen` stmt forms can instead be re-derived from the NEW theorems (P1-P4), which is the positive route | — | same |
| instances | re-check only | Tests/Gen2/LeafInstance.lean:67, SlotlessLeafInstance.lean:57, MemParentInstance.lean:55, QuantInstance.lean:136 | text unchanged (they state `ChildShips` through the theorems) | — | rebuild |
| [M3] G-POST | parallel interface change on `ShipsRes` | [M3] Tools/ShippingGen2Defs.lean:135-136 (`… ∧ InstClosed r`), Tools/ShippingGen2KeepChild.lean:4-6, :253-258 | orthogonal (different definition) but the same files: sequence the two edits; obtain patterns `⟨_, q', n', hq', _, hcs'⟩` become `⟨_, ⟨q', n', hq', _, hcs'⟩, _⟩` under G-POST | — | coordination |
| docs | quote `ChildShips` | scripts/gen2/: GENERAL_SPEC.md, STEP_IFACE_FREEZE.md, LEAF_FREEZE.md, LEAF_RESULT.md, MEMPARENT_FREEZE.md, MEMPARENT_RESULT.md, LOOPPKG_FREEZE.md, LOOPPKG_RESULT.md, T1_CONNECT_FREEZE.md, CALLFIELD_FREEZE.md, S3_GROUP_FREEZE.md, S4_*.md, G3GEN_CALL_PLAN.md, LEAD_UNITS_PLAN.md, ROUTE_CENSUS.md, STEP_S2_VACUITY_REPORT.md, STEP_S6_RESULT.md (grep list) | add a note; history entries stay | — | doc |
| *alt-R only*: `SeqChildRunN` producers | unaffected under the recommended placement | Tools/ShippingMachineDepthRun.lean:160 (source `calls_ports` :165, `hargsMc` :185, length :191); DepthRunR:145 (:150, :170, :176); SeqChildDeepRunA:61 (:66, :86, :92; used by Srm4Run:112 (doc :94-96), Srm4Mixed:276 (doc :244), Srm4Callee:87/:194-198, QuadComposed:351-355); C6:55 (:59, :79, :85); QuadCalls:323; MachineDepth:86 (`seqChildRunN_of_flat`), :113; generator templates SeqParentGenD2.lean:585, SeqParentGenD2M.lean:340 (emitted per parent: every generated endpoint re-checks); MachineChild.lean:196/217, MachineSeqChild.lean:128/319, GateChild.lean:142/167, FirstGateChild.lean:603/628 (DPORT §0 grep list) | under alt-R each must prove the new conjunct; the source is the listed `hargs` line + `machPorts_tys` | — | not proposed |
| *alt-R only*: `CombChildRunN` / `ChildRunN` users | unaffected | Tools/ShippingGen2AComb.lean:18-29 (`childRunN_of_seq` is `Or.inl`; the exclusion/iff lemmas project conjuncts by position: `.2.2.1`), OneOut:77-82, CallField:195-200, CombKid:177/208, CallsLinkedTN:38, CallsLinkedTNR:34 | under alt-R, positional projections `.2.2.2.2.2.1` (Connect:143) shift if the conjunct is not appended LAST | — | not proposed |

**Additional impact rows (UNCHECKED: listed, not audited line by line):**
| site | kind | where | note |
|---|---|---|---|
| [M3] `childShips_congr` | lemma on `ChildShips` | `par/gen3-induct` | must ALSO transport the new static conjunct (`ChildPortWidths` of the transported `q`/`mc`) |
| [M3] old projections of `ChildShips` | consumers | `par/gen3-induct` | positional projections shift (`.2`) |
| [M3] skeleton | StepStmt/IH skeleton | `par/gen3-induct` | must carry the conjunct through the induction |
| in-progress S3 `group_childShips` | producer | Tools/ShippingGen2GroupServed.lean (another agent, uncommitted) | must prove the conjunct (N-B pattern if it goes through C6) |
| M4 gate / future-route producers | producers | not built | must prove the conjunct; UNCHECKED |

P1-P4 alone do NOT complete the FG supply: the M3/S3/M4 producers above must also prove the conjunct. Mixed sites are
NOT guaranteed to need only re-elaboration (the "re-elaborate only" entry above is an expectation, to be checked at
build). PkgCompat old→new (C6/C6') is limited to a version with a `ChildPortWidths` premise, or withdrawn. The
consumer's L6/source width equality is not part of this unit; it stays in SRC-ARGW.

**New small lemmas (text; new file `Tools/ShippingGen3ChildPortWidths.lean`, no shared edit):**
```lean
/-- N-A: the argument ports of a call-free machine module are its declaration's ports (LeafSeq:58-67, factored). -/
theorem argPorts_noCalls_of_wired {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Sparkle.IR.AST.Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (hnoI : d.shape.insts = []) (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets) :
    Tools.ShippingMachineCompose.argPorts m = machPorts declName ids cache d.bsIn

/-- N-B: the port widths of the C6 child module (C6:29-56 premises; C6:57-85 with `machPorts_tys`). -/
theorem childPortWidths_of_composedNW (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl : d.shape.layout.slots ≠ []) (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {mc raw : Sparkle.IR.AST.Module} {D : Design}
    (hcomp : ComposedNW n c d kD raw D dom src ext extB)
    (hpost : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    (Tools.ShippingMachineCompose.argPorts mc).map (fun p => p.ty.bitWidth) =
      ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).map (fun b => (kindTy b.2).bitWidth)
```
N-B's binders are C6:29-46 in C6's order (checked against the text), plus `hcomp`/`hpost` (C6:50-52). It drops
what only the run part uses (`hextB`, `hext` :47-48, `i` :49, `dsn`, `hEA` :53, `hNI` :54). `hI0` is kept because
C6:63-77 uses it to collapse `mergeChecked` (`mc = dropZW raw`). Ambient opens are C6:11-19 (`ComposedNW` resolves
through them). Bridging `nonDom` (PortWidthsPure:46) and the lambda `fun b => b.2 != .domain` is `rfl`. Sizes: N-A about 20 lines, N-B about 40 lines, `childPortWidths_of_tys` about
5 lines.

## Result dependencies (shared by UARITY_FREEZE.md, UARGW_PARENT_SURVEY.md, UCHILD_PORTTYS_TABLE.md)
| unit | supplies | side | alone reaches `callArgsOkAt`? |
|---|---|---|---|
| U-ARGW-PARENT (`core_inputWidth_A`, `core_callArgPorts_oneA`/`_ranA`) | `declWidth b argWs[j] = (kindTy binders[nDecl+(kI+(n+a))].2).bitWidth` | PARENT (let wire) | no |
| U-CHILD-PORTTYS (`ChildPortWidths`, N-A/N-B, P1-P4) | `(argPorts mc).map (·.ty.bitWidth) = q.ports.map (kindTy ·.2).bitWidth` | CHILD (served module) | no |
| U-ARITY (`callArity_of_trace`) | `(insts[k]).2.1.length = q.ports.length` | the matching INDEX RANGE | no |
| SRC-ARGW (scripts/gen3/SRC_ARGW_FREEZE.md, separate unit) | the width equality L6/L6w for the same call | source | — |

The three results above reach `callArgsOkAt p.d p.kD k q.portWidths` only when composed with SRC-ARGW's width equality
for the SAME call (same `k`, statement, `mc`, `q`, and one `MachineTraceLBX` witness). None of them, nor any pair of
them, supplies the row alone.

## 4. Final-FG obligation
- The new conjunct lives in `ChildShips`, i.e. in the IH, the cache invariant and the `StepStmt` conclusion. It is
  **not** a new FG premise: `T1Hyp`/`T1Stmt` are unchanged, and FG's conclusion (`TopShips`) does not mention it.
- The obligation is that **every producer of `ChildShips` proves it from its own run**: P1-P4 now, plus the unbuilt
  `StepStmt` proof and the S3 group producers. Per-site sources exist for P1-P4 (§3). No producer is known to lack
  one, but N-A/N-B are unbuilt, so this is a plan, not a supply.
- Unlike `T1Hyp.wid` (S4_WID_SUPPLY.md §4.1), nothing has to be discharged and then REMOVED later. The export is
  supplied run-locally. The remaining width gap for `callArgsOkAt` is L6 (emitted tie, G-ARG-WID), which this
  change does not touch and which stays **UNSUPPLIED; no derivation route found** (DPORT §1 L6).
- PkgCompat's Old ⇒ new A-COMB lifts (C6/C6') lose their unconditional form. That is a compat-test change, not an FG
  change; record it as such in the result.

## 5. Order and size
1. U-CHILD-PORTW-P (new file, no shared edit): N-A, N-B, `childPortWidths_of_tys`, and per-producer corollaries
   `leaf_childPortWidths`, `slotlessLeaf_childPortWidths`, `memParent_childPortWidths`, `oneOut_childPortWidths`. Each
   states `ChildPortWidths p b` under its producer's premises. About 150 lines plus controls (P2 `pbhPkg` decided at
   the data level; N: a toy module with one 8-bit port against a 16-bit package port, row false). This proves the
   facts BEFORE any interface change.
2. Only after review of 1: U-CHILD-PORTW-DEF + C (the shared edit). Defs + GEN2_DEFS copy + P1-P4 `refine ⟨_, ?_⟩`
   (about 4 lines each) + C1-C5 `.2` (1 line each) + PkgCompat C6/C6'. About 40 changed lines plus the PkgCompat
   reclassification. Sequence it with [M3] G-POST.

## Shared-edit plan (rev2)
**Design only; nothing applied, built or merged.** Read-only survey on 2026-10-29. Branches: `par/gen2-spec` at
**8ee219c3** (the standalone part is accepted at 1b840215), `par/gen3-induct` at **96cbd548** ([M3]), and
`par/gen4-gate` at b3a72c91 ([M4]). Merge-base of 8ee219c3 and 96cbd548 is **1fdbc18d** (S6 A-COMB). `par/gen4-gate`
and `par/gen5-t2` also fork at 1fdbc18d, with Defs unchanged since. A trial `git merge-tree --write-tree 8ee219c3
par/gen3-induct` gave tree 09b6bea8. No ref or worktree was changed.

### a. Defs diff and conflict analysis
`git diff 8ee219c3 par/gen3-induct -- Tools/ShippingGen2Defs.lean scripts/gen2/GEN2_DEFS.lean.txt` shows two
independent hunks, each one-sided since 1fdbc18d:
| change | branch, commit | Defs lines | GEN2_DEFS copy |
|---|---|---|---|
| CallField: `def CallField` (8ee219c3 Defs:91-97); `CallDec` uses `CallField p q k o` (:109) instead of `o.name = instFields.getD k ""` | gen2-spec b213b3b4 | :91-109 | updated (cmp-identical at 8ee219c3) |
| G-POST: `def InstClosed` ([M3] Defs:127-131); `ShipsRes := RealChildA ∧ (∃ q n, … ChildShips …) ∧ InstClosed r` ([M3] Defs:135-136) | gen3-induct 28476add | :127-136 | **NOT updated** on gen3-induct (cmp differs at line 127) |
| ChildShips + `ChildPortWidths` (this unit) | not applied | 8ee219c3 Defs:82-90 | — |

- **Textual:** Defs, PkgCompat (A-COMB section: CallField `t1Hyp_iff` vs G-POST `hic` lifts) and GEN2_DEFS auto-merge.
  The only textual conflict is `lakefile.lean`: both branches append `lean_lib` blocks after :4549 (09b6bea8:4551-4677).
  Resolve it as the union.
- **Copy:** at the merged SHA, `GEN2_DEFS.lean.txt` lacks `InstClosed`. Sync it to Defs (`cmp` exit 0) in the
  integration commit.
- **Semantic conflicts at integration (they break the build; git does not report them).** Five sites exist only on
  gen2-spec and destructure `ShipsRes` with the 2-conjunct pattern `⟨_, q', n', hq', _, hcs'⟩`. Each must become
  `⟨_, ⟨q', n', hq', _, hcs'⟩, _⟩`:
  - Tools/ShippingGen2FitChain.lean:946;
  - Tools/ShippingGen2OneOut.lean:200;
  - Tools/ShippingGen2OneOutTop.lean:310;
  - Tools/ShippingGen2OneOutTopO.lean:303;
  - Tools/ShippingGen3Arity.lean:83 (`argLen_of_shipsRes`).

  `ShipsAt` (8ee219c3 Defs:147-148) has no `InstClosed`, so Connect:137 and GroupServed:80/:94 are unaffected.
  GPOST_STAGE1_RESULT.md lists `leaf_ships`, `slotlessLeaf_ships` and `Pkg.comb` as "must be re-verified on integration".
- **InstClosed vs ChildShips.** InstClosed touches `ShipsRes`'s top-level shape, i.e. how `ShipsRes` is consumed.
  ChildShips touches the body of `ChildShips`, i.e. how ChildShips is produced and how its run part is applied
  (`hcs dsn …` becomes `hcs.2 dsn …`). The two edits touch different definitions and are orthogonal, but they share 4
  consumer sites: FitChain:946, OneOut:200, OneOutTop:310 and Arity:83 are touched by both. OneOutTopO:303 is also
  touched by both.

### b. Order, host, owner, re-verification
**Recommended: InstClosed first, ChildShips on top, in ONE combined branch.**
1. Create `par/gen3-combined` from 8ee219c3 and merge 96cbd548 into it:
   - lakefile union;
   - GEN2_DEFS sync;
   - the 5 `ShipsRes` pattern fixes above, and nothing else.

   Build and record this as the integration SHA S1.
2. On top of S1, make the ChildShips edit (§3 rows and c. below) as one commit, S2.

Reasons:
- InstClosed is already built (g3pf-28476add, exit 0). Its consumers on gen3-induct (`childShips_congr` T1:142-145,
  PostFacts `ShipsResOld`/`shipsRes_old` :68-99, `ihAt_stepPF` :194, KeepChild, PkgCompat `hic` lifts) only become
  visible to the ChildShips edit in a tree that contains them.
- The reverse order would have gen3-induct re-patch `childShips_congr` and the same 5 sites after its own merge. That
  means two interface migrations of the same lines on two branches.
- S1 alone separates "integration regressions" from "ChildShips regressions".

**Host:** `par/gen3-combined`, a new branch. It becomes the base for gen2-spec, gen3-induct, S3 and S5 follow-ups.
gen2-spec and gen3-induct stop editing Defs, PkgCompat and the 5 sites until S2 is accepted.

**Single owner:** the coder of `sparkle-gen3-uchild-porttys` owns S1 and S2. This is one worker, serial. The other
agents are frozen on the listed files:
- the SRC-ARGW agent does not touch Defs;
- the gen3-post (M3) agent continues only after S2.

The S1 merge needs a recorded go-ahead from the gen3-post (M3) issue owner (managerctl note), because it moves M3's
branch base.

**Re-verification.** Use `kjob run --issue sparkle-gen3-uchild-porttys` with `kjob lake build`, serially, at S1 and
then at S2. Do not reuse 28476add or 1b840215 results.
- Tools:
  - `Tools.ShippingGen2{Defs,Connect,FitChain,OneOut,OneOutTop,OneOutTopO,Leaf,SlotlessLeaf,MemParent,MemShips,GroupComb,GroupServed,C6,AComb,CallField,PostFacts,T1,KeepChild,InstKeep,KidsInst}`;
  - `Tools.ShippingGen3{Arity,ChildPortWidths,ArgWidthSrc}` (ArgWidthSrc only if committed by then).
- Tests:
  - `Tests.Gen2.{PkgCompat,LeafInstance,SlotlessLeafInstance,MemParentInstance,QuantInstance,QuantEndpoint,S3GroupCheck,S4StageACheck,SlotlessCheck,CallDecInstance,AdaptInstance}`;
  - `Tests.Gen3.{T1Check,InstKeepCheck,ArityCheck,ChildPortWidthsCheck}`.
- Each step also needs:
  - a `#print axioms` audit (roots ⊆ propext/Classical.choice/Quot.sound, no sorryAx);
  - GEN2_DEFS `cmp`.

Finally, run `Tests.AllTests` at S2 before any poc integration request. The focused list is a plan; derive the exact
closure from `lake` at S1 (UNCHECKED that it is complete).

### c. ChildShips producers and consumers after the change (both branches + [M4])
Producers (conclusion `ChildShips`; each must prove `ChildPortWidths q mc` as the new first conjunct):
| producer | file:line @ branch | width source | status |
|---|---|---|---|
| `leaf_childShips_of_LB` | Leaf.lean:241-266 @ both (from mb) | P1 `leaf_childPortWidths` (Gen3ChildPortWidths:198) — same premises (`hL hnoI hsl hok hSS houtTy htake hpost`) | covered by P1 |
| `slotlessLeaf_childShips_of_LB` | SlotlessLeaf.lean:283-296- @ gen2-spec | P2 (:211), same premises | covered by P2 |
| `memParent_childShips` | MemShips.lean:39-49- @ both | P3 (:223); `hNW` already in the proof → N-B directly | covered by P3 |
| `oneOut_childShips` | OneOut.lean:288-332 @ gen2-spec | P4 (:251); `hNW` in hand → N-B | covered by P4 |
| `group_childShips` (S3 B5) | GroupServed.lean:294-352 @ gen2-spec | NOT covered by P1-P4. **New lemma `group_childPortWidths`**: under `group_childShips`' binders, `ChildPortWidths p b`, proof = `childPortWidths_of_composedNW n houtTy (ok_outNameOk p.d hok) hsl hI0 hkD hIlen hSL hSlen hLlen hNIn (group_composedNW L P p hdata hfe hdec n h) hpost` (all terms already built at GroupServed:308-331) | needs new lemma (N-B instance) |
| `leaf_ships`, `slotlessLeaf_ships`, `memParent_ships` (+ `.loop`: QuantInstance:136) | Leaf:271, SlotlessLeaf:438, MemShips:87 | via the row-level producers above | follow from P1-P3 |
| `childShips_congr` [M3] | T1.lean:142-145 @ gen3-induct | `intro dsn hg hmc i` breaks; becomes `⟨hc.1, fun dsn hg hmc i => hc.2 dsn (h ▸ hg) hmc i⟩` (width conjunct independent of `Dc`) | needs edit, no new lemma |
| `ihAt_stepPF` [M3] | T1.lean:194 | takes `ChildShips` from `hStep` via `childShips_congr` | unchanged text |
| `StepStmt` proof (M2-b) | unbuilt | must prove the conjunct; route: dispatch to P1-P4/group by parent kind | UNCHECKED (no proof exists) |
| S5 slotless parents | design only (fd55bcfc) @ gen2-spec | N-B if via C6/ComposedNW, else N-A | UNCHECKED |
| `PostFacts` `ShipsResOld`/`StepStmtOld` [M3] | PostFacts:68-95 | they reference CURRENT `ChildShips`, so "verbatim old" now means old-InstClosed only; `shipsRes_old` `⟨h.1, h.2.1⟩` unchanged | re-elaborate; doc note |
| KeepChild / InstKeep / KidsInst [M3] | KeepChild:77-152, :257-347 | generic in `ShipsRes`/`InvAt` (no `ChildShips` destructuring found) | re-elaborate only (UNCHECKED until S2 build) |
| [M4] gate route | par/gen4-gate b3a72c91: GateLeaf.lean:34-35 states `ChildShips`/`ShipsRes` for gate names NOT covered | none exists | no producer; UNCHECKED for future |
| PkgCompat `childShips_gen` | PkgCompat:300-302 @ both | Old ⇒ new unproved | see d. |

Import constraint: producers (Leaf, SlotlessLeaf, MemShips, OneOut, GroupServed) are UPSTREAM of
`Tools/ShippingGen3ChildPortWidths.lean` (imports OneOut). They cannot call P1-P4. Plan: in S2, move
`ChildPortWidths` into Defs (argPorts is reachable from Defs: Arity uses it importing only Defs), and split the
lemmas (`argPortWidths_of_eq`, `childPortWidths_of_tys`, N-A, N-B, `noCalls_childPortWidths`) into a new file
`Tools/ShippingGen3PortWidthsCore.lean` importing only C6 + PortWidthsPure + MemData. MemShips/Leaf/SlotlessLeaf/
OneOut/GroupServed then import it. P1-P4 remain as thin corollaries. ChildPortWidthsCheck's expected type follows
the moved name. The absence of an import cycle is to be confirmed at the S2 build.

Consumers that destructure or apply `ChildShips` (shift: `hcs …` → `hcs.2 …`, or pattern `⟨-, hcs⟩`):
- 8ee219c3 @ gen2-spec:
  - Connect:140 (`hcs dsn hcons hmod i`);
  - GroupServed:80, :94 (obtain over `ShipsAt`, then applied);
  - FitChain:949;
  - OneOut:203;
  - OneOutTop:313;
  - OneOutTopO:306;
  - Arity:86 (`childRunN_argLen (hCS D hDc hmod i)`).
- [M3]: `childShips_congr` T1:144-145.
- PkgCompat: `shipsRes_lift`/`shipsAt_lift` :312-320 and `memParentStmt'_gen`/`memParentStmt_gen`/`leafStmt_gen`
  :386-426 (`childShips_gen … this.2`).

No other `ChildShips`/`ShipsRes` destructuring was found by grep for these patterns in `Tools/ShippingGen2*`,
`Tools/ShippingGen3*`, `Tests/Gen2`, `Tests/Gen3` on either branch. Grep is not a proof, so the S2 build is the check.

### d. Interface claims
- **No new T1/FG premise.** `T1Hyp`/`T1Stmt` and FG's conclusion are unchanged. `PostFactsStmt` [M3] is unchanged.
  The conjunct is supplied run-locally by the producers in c.
- New ⇒ old by projection: `ChildShips` `.2`, lifted to `ShipsRes`/`ShipsAt`/`CacheShips`/`InvAt`, and composing
  with M3's `shipsRes_old` (`⟨h.1, h.2.1⟩`, which then carries the new `ChildShips`). Old ⇒ new: UNPROVED/UNSUPPLIED
  (§2).
- **PkgCompat.** `childShips_gen` (Old ⇒ new) is either WITHDRAWN or takes an explicit `ChildPortWidths (.gen q) mc`
  premise. Recommended: width-premised, mirroring G-POST's explicit `hic`. Its dependents `shipsRes_lift`,
  `shipsAt_lift`, `cacheShips_lift`, `invAt_lift` and the `.gen` stmt forms (:372-426) then take the premise, or are
  re-derived from the NEW producers. This is a compat-test change, not an FG change.

**Note (review of a966486b):** for slotless parents with calls (`slots = []`, `insts ≠ []`), neither existing N-A nor
N-B applies directly; an independent `ChildPortWidths` supplier for that case remains to be provided (S5 producers).
