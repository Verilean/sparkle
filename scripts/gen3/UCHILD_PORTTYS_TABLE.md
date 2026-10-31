# U-CHILD-PORTTYS change-site table rev0: exporting the served child's argument-port widths (DPORT L5)

> **rev3 (2026-10-29, at the end of this file) supersedes conflicting text above.** Corrected in place and marked
> `[rev3]`: the S5 slotless-parent producers (no supplier yet: §R3.1), the PkgCompat width premises (§R3.2), the
> order InstClosed → R-G → ChildPortWidths, base SHAs and owner (§R3.3). The ChildShips edit is called **S3** in rev3
> (it was S2 in rev2).

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
| future producers | StepStmt proof (unbuilt), S3 group parents (another agent: Tools/ShippingGen2GroupComb.lean / GroupServed.lean, not in 10377764) | — | must prove | N-B pattern if they go through C6 or `seqChildRunN_of_composed*`. [rev3] Group parents WITH slots: `group_childPortWidths` (§R3.4). S5 slotless parents with calls: NOT N-A/N-B; OPEN (§R3.1) | coordination item |
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
| in-progress S3 `group_childShips` | producer | Tools/ShippingGen2GroupServed.lean (another agent, uncommitted) | must prove the conjunct (N-B pattern if it goes through C6). [rev3] committed (2676204d); supplier `group_childPortWidths` written (§R3.4) |
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
  `StepStmt` proof and the S3 group producers. Per-site sources exist for P1-P4 (§3). [rev3: the following sentence is WITHDRAWN. The S5 slotless parents with
  calls (`oneOutSl_childShips`, `groupSl_childShips`) and the [M4] gate route lack a supplier (§R3.1).] No producer is known to lack
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
   reclassification. Sequence it with [M3] G-POST. [rev3: the order is InstClosed → R-G → ChildPortWidths (§R3.3).]

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
**Recommended: InstClosed first, ChildShips on top, in ONE combined branch.** [rev3: SUPERSEDED by §R3.3. R-G
(TOP_CONTRACT_REVISION.md rev1.1) now sits between them; the ChildShips edit is S3, not S2.]
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

**Single owner:** [rev3: superseded by §R3.3, which records the owner and the fixed bases.] the coder of `sparkle-gen3-uchild-porttys` owns S1 and S2. This is one worker, serial. The other
agents are frozen on the listed files:
- the SRC-ARGW agent does not touch Defs;
- the gen3-post (M3) agent continues only after S2.

[rev3: superseded by §R3.3. The same coder owns M3, and the merge itself is a user operation.] The S1 merge needs a recorded go-ahead from the gen3-post (M3) issue owner (managerctl note), because it moves M3's
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
| S5 slotless parents | design only (fd55bcfc) @ gen2-spec | ~~N-B if via C6/ComposedNW, else N-A~~ [rev3: WRONG. Neither applies: N-A needs `hnoI`, N-B needs `hsl`. The producers are now committed, unbuilt (f7e42988: SlotlessParentRun:291, :340). Supplier N-C is OPEN (§R3.1)] | UNCHECKED; OPEN |
| `PostFacts` `ShipsResOld`/`StepStmtOld` [M3] | PostFacts:68-95 | they reference CURRENT `ChildShips`, so "verbatim old" now means old-InstClosed only; `shipsRes_old` `⟨h.1, h.2.1⟩` unchanged. [rev3: they are pre-InstClosed copies, NOT pre-ChildPortWidths copies. After S3 they carry the width conjunct. No old/new ChildPortWidths relation is claimed through them (§R3.2c)] | re-elaborate; doc note |
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
  premise. Recommended: width-premised, mirroring G-POST's explicit `hic` [rev3: the exact types are in §R3.2]. Its dependents `shipsRes_lift`,
  `shipsAt_lift`, `cacheShips_lift`, `invAt_lift` and the `.gen` stmt forms (:372-426) then take the premise, or are
  re-derived from the NEW producers. This is a compat-test change, not an FG change.

**Note (review of a966486b; [rev3] resolved as OPEN with a fixed type in §R3.1):** for slotless parents with calls (`slots = []`, `insts ≠ []`), neither existing N-A nor
N-B applies directly; an independent `ChildPortWidths` supplier for that case remains to be provided (S5 producers).

## rev3 — review of 878bf5f3 (changes_requested): S5 supplier, PkgCompat width types, order and owner, verification plan

**Design only for the shared change: nothing is applied to Defs, GEN2_DEFS, PkgCompat or any existing `.lean` file.**
Three new files are written but NOT built (§R3.4). Bases: `par/gen2-spec` at **e8a41c70** and `par/gen3-induct` at
**96cbd548** ([M3]). Every `file:line` in rev3 is at these SHAs. `git diff --stat 8ee219c3 e8a41c70 --
Tools/ShippingGen2Defs.lean scripts/gen2/GEN2_DEFS.lean.txt Tests/Gen2/PkgCompat.lean` is empty, so rev2's Defs and
PkgCompat citations still hold.

### Changelog
- **rev3** (this section):
  - §R3.1: the S5 slotless parents with calls have NO supplier among N-A/N-B. A supplier type (N-C) is fixed, with its
    source and owner; its status is **OPEN**.
  - §R3.2: complete Lean types of the width premise added to each PkgCompat lift and `.gen` statement form. PostFacts'
    `*Old` copies are pre-InstClosed copies; no old/new claim at mixed positions.
  - §R3.3: order InstClosed → R-G (NC suppliers first) → ChildPortWidths (TOP_CONTRACT_REVISION.md rev1.1). Fixed bases,
    owner, and the merge as a user operation.
  - §R3.4: new files (core split, `group_childPortWidths`, check file). §R3.5: verification plan for after the shared
    change.
  - Earlier text corrected in place (marked `[rev3]`): the header note, §3 "future producers"/"in-progress S3" rows,
    §4 (the "no producer is known to lack one" sentence is withdrawn), §5 item 2, rev2 b (order, owner, go-ahead),
    rev2 c (S5 row, PostFacts row), rev2 d (PkgCompat), and the closing note.
- rev2 (878bf5f3): shared-edit plan (InstClosed first on `par/gen3-combined`, then ChildShips).
- rev1 / rev0: change-site table, N-A/N-B text, P1-P4 (built in 1b840215).

### R3.1 Slotless parents with calls (`slots = []`, `insts ≠ []`): supplier OPEN
**Neither N-A nor N-B applies:**
- N-A (`argPorts_noCalls_of_wired`) needs `hnoI : insts = []`, which is false here.
- N-B (`childPortWidths_of_composedNW`) needs `hsl : slots ≠ []`, which is false here. In N-B's proof, `hsl` is used
  only as the argument of `calls_ports` (MachineDepthChild:41-56). The other steps (`hInst` from `calls1`/`gCalls`,
  `hmc`, `hargsMc`, `hlenIn`) do not mention `hsl` (read, not built).

**Producers that need a supplier** (built clean in g2s5-f7e42988):
- `oneOutSl_childShips` (Tools/ShippingGen2SlotlessParentRun.lean:291-337, S5 B2);
- `groupSl_childShips` (:340-389, S5 B3).

Both end with `intro dsn hcons _ i` against `ChildShips`. At S3 that line breaks, and each must prove the width conjunct.

**Supplier N-C (type fixed here; NOT written, NOT built):**
```lean
/-- N-C: the port widths of a slotless parent with calls (N-B with A1 `calls_ports_sl` in place of `calls_ports`). -/
theorem childPortWidths_of_composedNW_sl (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl0 : d.shape.layout.slots = []) (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {mc raw : Module} {D : Design}
    (hcomp : Tools.ShippingMachineDepthRun.ComposedNW n c d kD raw D dom src ext extB)
    (hpost : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    (argPorts mc).map (fun p => p.ty.bitWidth) =
      ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).map (fun b => (kindTy b.2).bitWidth)
```
Its per-producer corollaries (binders = those of B2/B3 that the fact uses, as P3/P4 do; conclusion
`ChildPortWidths p b`, i.e. Defs' definition after S3):
```lean
theorem oneOutSl_childPortWidths (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) :
    ChildPortWidths p b

theorem groupSl_childPortWidths (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) :
    ChildPortWidths p b
```
- **Source (S5 run facts):**
  - A1 `calls_ports_sl` (Tools/ShippingGen2SlotlessParent.lean:68-85, statement). Its fourth conjunct
    `argPorts m = machPorts declName ids cache (d.bsIn.take kD)` holds in BOTH case S (clk/rst inputs) and case C
    (neither). Design: scripts/gen2/S5_SLOTLESS_FREEZE.md rev1 §3 A1, accepted.
  - The proof is N-B's text with `(calls_ports_sl wired len hsl0 houtOk kD hkD hIlen hSL hSlen hLlen hNIn).2.2.2.1`
    for `hargs`.
  - The corollaries take `hNW` as B2/B3 do: `oneOut_composedNW L P p hdata hins hsimple hA ran hdec h n` (B2,
    SlotlessParentRun:311) and `group_composedNW L P p hdata hfe hdec n h` (B3, :361). They take `hI0` from `hins`.
- **Placement:** a new file `Tools/ShippingGen3SlotlessPortWidthsCore.lean` importing `Tools.ShippingGen2SlotlessParent`
  and `Tools.ShippingGen3PortWidthsCore`. At S3, SlotlessParentRun imports it (no cycle expected: SlotlessParent
  imports only C6 + Defs; to be confirmed at build).
- **Owner:** the S5 stage-B owner (issue `sparkle-gen2-step`), as a sub-item of S5 stage B. It is not part of
  `sparkle-gen3-uchild-porttys`.
- **Status: OPEN.** Not written, not built. Its prerequisite S5 stage A/B (SlotlessParent, SlotlessParentRun) is
  built clean (g2s5-f7e42988).
- **S3 gate (required, review of ba9b9c82):** N-C must be supplied for the existing producers B2/B3 BEFORE S3. The
  alternative of starting S3 with B2/B3 broken is withdrawn.

**Producer coverage of `ChildPortWidths` after rev3:**

| class | producer | supplier | status |
|---|---|---|---|
| register leaf | `leaf_childShips_of_LB` | P1 (N-A) | built 1b840215 |
| slotless leaf | `slotlessLeaf_childShips_of_LB` | P2 (N-A) | built 1b840215 |
| memory parent (and `.loop`) | `memParent_childShips` | P3 (N-B) | built 1b840215 |
| one-output parent with slots | `oneOut_childShips` | P4 (N-B) | built 1b840215 |
| group parent with slots | `group_childShips` | `group_childPortWidths` (N-B) | built g3pw-ba9b9c82 (§R3.4) |
| one-output slotless parent | `oneOutSl_childShips` (B2) | `oneOutSl_childPortWidths` (N-C) | **OPEN** |
| group slotless parent | `groupSl_childShips` (B3) | `groupSl_childPortWidths` (N-C) | **OPEN** |
| `childShips_congr` [M3] | transport | `hc.1` (no new lemma) | text plan (rev2 c) |
| `StepStmt` proof (M2-b) | dispatch | the rows above, by parent kind | UNBUILT; UNCHECKED |
| [M4] gate route | none exists | none | UNCHECKED |

**Not all producers are supplied.** The two slotless-parent rows are OPEN, the gate route has no producer, and the
`StepStmt` dispatch is unbuilt.

### R3.2 PkgCompat (Tests/Gen2/PkgCompat.lean) at S3: the width premises, complete types
**Context.**
- `Old.ChildShips` (PkgCompat:48-51) has no width conjunct, and no lemma derives `ChildPortWidths (.gen q) mc` from it
  (§2: old ⇒ new UNPROVED/UNSUPPLIED).
- So every Old ⇒ new lift whose conclusion contains the new `ChildShips` takes the width as an EXPLICIT premise `hpw`.
  This mirrors G-POST's `hic` (already on [M3], PkgCompat [M3]:284-310).
- The lifts' text below is the post-S1 text (with `hic`). `ChildPortWidths` is Defs' definition after S3,
  `Tools.ShippingGen2.ChildPortWidths (q : Pkg ι dom) (mc : Module) : Prop`.
- This is a compat-test change, not an FG change.

**a. Lifts (positive positions).** `P c = some q` determines `q`. So the `∀ q` form below is no weaker than its `∃`
reading, and it avoids naming the witness hidden inside `Old.ShipsRes`.
```lean
theorem childShips_gen (q : SrcPkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design)
    (hpw : ChildPortWidths (.gen q) mc) :
    Old.ChildShips q n mc Dc → ChildShips (.gen q) n mc Dc :=
  fun h => ⟨hpw, fun dsn h1 h2 i => Or.inl (h dsn h1 h2 i)⟩

theorem shipsRes_lift (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (c : Lean.Name)
    (r : Tools.ShippingChildInv.Res) (hic : InstClosed r)
    (hpw : ∀ q, P c = some q → ChildPortWidths (.gen q) r.1) :
    Old.ShipsRes L P c r → ShipsRes L (Pkgs.lift P) c r
  -- rintro ⟨h1, q, n, hq, hd, hc⟩
  -- exact ⟨h1, ⟨.gen q, n, lift_some.mpr ⟨q, hq, rfl⟩, hd, childShips_gen q n _ _ (hpw q hq) hc⟩, hic⟩

theorem shipsAt_lift (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (n : Nat) (c : Lean.Name)
    (r : Tools.ShippingChildInv.Res)
    (hpw : ∀ q, P c = some q → ChildPortWidths (.gen q) r.1) :
    Old.ShipsAt L P n c r → ShipsAt L (Pkgs.lift P) n c r

theorem cacheShips_lift (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop)
    (m : Std.HashMap Lean.Name Tools.ShippingChildInv.Res)
    (hic : ∀ c r, Reach c → m.get? c = some r → InstClosed r)
    (hpw : ∀ c r, Reach c → m.get? c = some r → ∀ q, P c = some q → ChildPortWidths (.gen q) r.1) :
    Old.CacheShips L P Reach m → CacheShips L (Pkgs.lift P) Reach m

theorem invAt_lift (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop)
    (D : Nat) (w : Void IO.RealWorld)
    (hic : ∀ c r, Reach c → (Tools.ShippingChildBndCore.cv w).get? c = some r → InstClosed r)
    (hpw : ∀ c r, Reach c → (Tools.ShippingChildBndCore.cv w).get? c = some r →
      ∀ q, P c = some q → ChildPortWidths (.gen q) r.1) :
    Old.InvAt L P Reach D w → InvAt L (Pkgs.lift P) Reach D w
```
**b. `.gen` statement forms** (`ChildShips` only in the conclusion). Each gains ONE premise,
`ChildPortWidths (.gen q) b →`, placed immediately before `∀ n`. Everything else is the current text (PkgCompat:372-426).
The `TopShips` conjunct is as U-TOP-COMPAT leaves it at S2 (TOP_CONTRACT_REVISION.md §4, compat row: L2 plus
memberships, or re-derived). That change is separate and precedes this one.
```lean
theorem memParentStmt'_gen (L : Laws mref cref) : Old.MemParentStmt' (ι := ι) (dom := dom) L →
    ∀ (q : SrcPkg ι dom) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
      (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      MemParentDataOk (.gen q) → ExtInS (.gen q) → MemOrigin (.gen q) →
      q.d.shape.insts ≠ [] → q.d.shape.instFields ≠ [] → q.d.shape.layout.slots ≠ [] →
      Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
      Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w →
      Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore q.decl [] false)
        mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref q.decl q.d.shape →
      MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) q.decl q.d.shape raw D →
      (∀ k (hk : k < q.d.shape.insts.length), MemDec (.gen q) k (q.d.shape.insts[k]).1) →
      ChildPortWidths (.gen q) b →                                                          -- NEW (S3)
      ∀ n, TopShips (.gen q) (n + 1) q.decl b raw D ∧ ChildShips (.gen q) (n + 1) b D

theorem memParentStmt_gen (L : Laws mref cref) (DataOk : SrcPkg ι dom → Prop) :
    Old.MemParentStmt L DataOk →
    ∀ (q : SrcPkg ι dom) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
      (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      DataOkLiftCompat DataOk (.gen q) → q.d.shape.layout.slots ≠ [] →
      Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
      Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w →
      Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore q.decl [] false)
        mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref q.decl q.d.shape →
      MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) q.decl q.d.shape raw D →
      (∀ k (hk : k < q.d.shape.insts.length), MemDec (.gen q) k (q.d.shape.insts[k]).1) →
      ChildPortWidths (.gen q) b →                                                          -- NEW (S3)
      ∀ n, TopShips (.gen q) (n + 1) q.decl b raw D ∧ ChildShips (.gen q) (n + 1) b D

theorem leafStmt_gen (L : Laws mref cref) (DataOk : SrcPkg ι dom → Prop) :
    Old.LeafStmt L DataOk →
    ∀ (q : SrcPkg ι dom) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
      (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      DataOkLiftCompat DataOk (.gen q) → q.d.shape.insts = [] →
      Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
      Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w →
      Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore q.decl [] false)
        mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref q.decl q.d.shape →
      MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) q.decl q.d.shape raw D →
      ChildPortWidths (.gen q) b →                                                          -- NEW (S3)
      ∀ n, TopShips (.gen q) n q.decl b raw D ∧ ChildShips (.gen q) n b D
```
- Proof change in each stmt form: `intro … h13 hpw n` (or `… h8 hpw n`), then
  `⟨this.1, childShips_gen q _ _ _ hpw this.2⟩`.
- The positive alternative (re-derive the `.gen` forms from the new producers P1/P3, without `hpw`) needs the
  producers' run premises, which `Old.*Stmt` does not supply. It is not proposed.
- **Why these are not Lean statements yet.** They mention the post-S3 `ChildShips` (with the conjunct) and the post-S1
  `ShipsRes` (with `InstClosed`). Neither exists at e8a41c70, and a stand-in definition would state facts about a
  copy, not about Defs. So no `Tests/Gen3/PkgCompatWidthTypes.lean` is written. The types are fixed here and are to be
  pinned by `checkExpected` in PkgCompat at S3.

**c. PostFacts [M3] and mixed positions (correction of rev2 c/d).**
- `ShipsResOld`, `CacheShipsOld`, `InvAtOld` and `StepStmtOld` (PostFacts [M3]:68-95) are the **pre-InstClosed**
  copies. They refer to the CURRENT `ChildShips`, so after S3 they carry the width conjunct.
- They are **not** pre-ChildPortWidths copies, and none is introduced. `shipsRes_old`/`cacheShips_old`/`invAt_old`/
  `servedP_old`/`stepStmt_of_old` (PostFacts [M3]:96-123) remain statements about dropping `InstClosed` only.
- **No old/new `ChildPortWidths` relation is claimed at mixed positions, in either direction.** This covers `IHAt`,
  `BodyKeepsInv`/`ChildKeepsInv`, `KeepBodyStmt`/`KeepChildStmt`, `ServedShipsStmt`, `StepStmt` (and `StepStmtOld`,
  whose `ServedP (ShipsResOld …)` premise also strengthens). The earlier §2 classification stands; "re-elaborate
  only" there is an expectation, checked at build.

### R3.3 Order, fixed bases, owner (synced with TOP_CONTRACT_REVISION.md rev1.1)
**Fixed bases (recorded 2026-10-29):**
- `par/gen2-spec` = **e8a41c70a82ec7f978c19ecf12b49921a2d10e60**;
- `par/gen3-induct` = **96cbd54887425b37d6d6ac5f7c3d4ee4dc0a2260**;
- merge-base 1fdbc18d.

A trial `git merge-tree --write-tree e8a41c70 96cbd548` gives tree e99716b9. Defs and PkgCompat auto-merge, and the
only textual conflict is `lakefile.lean` (union). No ref or worktree was changed. If either branch moves before S1,
the bases are re-recorded and the trial is repeated.

**Owner:** one coder owns `sparkle-gen3-uchild-porttys` AND the gen3-post (M3) issue.
- The M3 go-ahead required by rev2 b is therefore recorded by that same owner, as a managerctl note on both issues
  with the two base SHAs above.
- The R-G steps belong to `sparkle-gen2-top-contract`, under the same serial single-owner rule (TOP rev1.1 item 4).
- **The merge itself is a user operation.** Creating `par/gen3-combined` and merging 96cbd548 into it, and any later
  integration into poc, are done by the user or on the user's explicit instruction. Approval of this plan is not
  approval of the merge.
  - 2026-10-30: the user gave that explicit instruction for S1 (local only). The coder created `par/gen3-combined`
    from d0ddc50b and merged 26f5d72a (merge 31a3fdfa; scripts/gen3/S1_MERGE_REQUEST.md status, Issue
    `sparkle-gen3-s1-combined`). Integration into poc/main and any push remain user operations.

**Sequence (serial; each numbered step is one buildable SHA or a series of them):**
0. **Now, no shared edit (new files only).**
   - This rev's files (§R3.4).
   - R-G's NC suppliers and L1-L4 in new files (TOP rev1.1 item 2: U-TOP-S2 for the slotless leaf, S5 C5a).
   - N-C (§R3.1), after the S5 stage-A build.
1. **S1 = InstClosed integration.** `par/gen3-combined` from e8a41c70, merge 96cbd548 (user operation), lakefile
   union, GEN2_DEFS sync (`cmp` exit 0), the 5 `ShipsRes` pattern sites (rev2 a; re-grepped at e8a41c70: the new S5 and
   SRC-ARGW files add none).
2. **S2 = R-G** (TOP rev1.1 item 2, each at a buildable point): U-TOP-DEF → U-TOP-CLKIN/U-TOP-PROD → U-TOP-COMPAT →
   U-TOP-CTRL.
3. **Before S3:** update this table at the final S2 SHA.
   - Re-cite `file:line`; S2 touches Leaf, MemTop, OneOutTop(O) and the PkgCompat statement forms.
   - Re-grep producers and consumers.
   - Record the fixed base (S2 SHA) and the owner in the issue note.
4. **S3 = ChildPortWidths (one commit):**
   - `ChildPortWidths` into Defs, and the GEN2_DEFS copy;
   - switch Tools/ShippingGen3ChildPortWidths.lean to import `Tools.ShippingGen3PortWidthsCore` and delete its N-A/N-B
     copies;
   - producers `refine ⟨<width term>, ?_⟩`: P1-P4, `group_childShips` (the §R3.4 term), and B2/B3 (N-C, §R3.1 gate);
   - `childShips_congr` [M3];
   - consumers `.2` (rev2 c list);
   - PkgCompat §R3.2.

### R3.4 Code prepared now (new files; NOT built; no existing `.lean` edited)
- **Tools/ShippingGen3PortWidthsCore.lean** — the move-ready core split.
  - `argPortWidths_of_eq`, `childPortWidths_of_tys`, N-A (`argPorts_noCalls_of_wired`, `argPorts_noCalls_post`), N-B
    (`childPortWidths_of_composedNW`) and `noCalls_childPortWidths`, in namespace `Tools.ShippingGen3PortWidthsCore`.
  - The proofs are verbatim. The two lemmas that concluded `ChildPortWidths` conclude its body (the definition moves to
    Defs at S3).
  - Imports: C6, MemData, PortWidthsPure. Their import closure (script over the source tree) contains none of Leaf,
    SlotlessLeaf, MemShips, OneOut or GroupServed.
  - Tools/ShippingGen3ChildPortWidths.lean is UNCHANGED.
- **Tools/ShippingGen3GroupPortWidths.lean** — `Tools.ShippingGen2.GroupPortWidths.group_childPortWidths`.
  - The data rows and `hNW` are GroupServed:308-315 verbatim, `hI0` is :326-329, then ONE N-B application (Core).
    Conclusion `Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b`.
  - At S3 the same term goes into `group_childShips`.
- **Tests/Gen3/PortWidthsPrepCheck.lean**:
  - `checkExpected` of the four unchanged Core statements against the BUILT ChildPortWidths.lean ones;
  - expected types of `childPortWidths_of_tys` (Core), `noCalls_childPortWidths` (Core) and `group_childPortWidths`;
  - mutants (each rejected): N-B with `hsl0`, Core no-calls over unfiltered `bsIn`, group without `hsl`, group TYPE
    form;
  - `checkAxioms` + `#print axioms`.
- **lakefile entries:** added at ba9b9c82 for `Tools.ShippingGen3PortWidthsCore`,
  `Tools.ShippingGen3GroupPortWidths` and `Tests.Gen3.PortWidthsPrepCheck`; built clean in g3pw-ba9b9c82.
- **Not written:** `Tests/Gen3/PkgCompatWidthTypes.lean` (§R3.2 b, it needs the shared change) and N-C (§R3.1, OPEN).

### R3.5 Verification plan (after the shared change; nothing here is run now)
1. **Per-SHA focused builds.** Run `kjob run --issue sparkle-gen3-uchild-porttys` with `kjob lake build`, serially, at
   S1, at each S2 SHA, and at S3. Do not reuse results of another SHA (28476add, 1b840215, or this rev's prep build).
   - At S1 and S2: rev2 b's target list.
   - At S3, add:
     - `Tools.ShippingGen3{PortWidthsCore,GroupPortWidths,SlotlessPortWidthsCore}`;
     - `Tools.ShippingGen2{SlotlessParent,SlotlessParentRun,GroupServed}`;
     - `Tests.Gen2.S5Check`;
     - `Tests.Gen3.{PortWidthsPrepCheck,ChildPortWidthsCheck}`.
2. **Final importers.** At S3, compute the reverse import closure of `Tools.ShippingGen2Defs` from `lake` (not grep) and
   build every member that is a lakefile target. Then run `Tests.AllTests` at S3, before any poc integration request.
3. **GEN2_DEFS sync.** `cmp Tools/ShippingGen2Defs.lean scripts/gen2/GEN2_DEFS.lean.txt` exits 0 at S1, at every S2 SHA
   and at S3.
4. **Audit.** Run `#print axioms` / `checkAxioms` (roots ⊆ propext/Classical.choice/Quot.sound, no sorryAx) on every
   changed producer, the PkgCompat lifts and the prep checks. Record the result with its SHA in the issue.

### R3.6 Not claimed (rev3)
- That every `ChildShips` producer is supplied (§R3.1: two OPEN, gate none, `StepStmt` unbuilt).
- That N-C holds (type only; route read, not built).
- Old ⇒ new for `ChildShips`, or any relation at mixed positions.
- That the three new files build. Nothing in rev3 is built.
- That the import-cycle freedom of the core split holds beyond the script check.

**Review note (ba9b9c82, binding):** at the final S2 SHA (after R-G) the full PkgCompat text is re-checked against the
§R3.2 types; `hpw` is a compat-lemma premise only and must NOT be reused as an added premise of production producers.

## rev4 — change-site table re-taken at fa84af5d (S3 `ChildPortWidths`, before any shared edit)

**Design only. Nothing is applied, built or proved by this revision; no `.lean` file and no Defs/GEN2_DEFS text is
edited.** rev4 supersedes the `file:line` citations of rev0-rev3 (they were taken at 10377764 / e8a41c70). The
plan itself (rev3 §1 Candidate W, §R3.1-R3.3) is unchanged: the only shared-definition change is the new
`ChildPortWidths` and one new FIRST conjunct of `ChildShips`. No change to `T1Hyp`, FG, `GenWF`, any law or any TRUSTED
boundary.

**Base.** `kjob/g3pt-s3` = `kjob/g2tc-s2` = **fa84af5d48edc11e75c3ed31dbb49f0a1e817b74** (S1 InstClosed merged, S2 R-G
Defs switched; S2 CTRL freeze at fa84af5d is docs only). `cmp Tools/ShippingGen2Defs.lean scripts/gen2/GEN2_DEFS.lean.txt`
exits 0 at fa84af5d (checked). All `file:line` below are at fa84af5d. Method: `grep` over `Tools/` and `Tests/` for
`ChildShips`, `ChildPortWidths`, `childPortWidths`, the run-part applications (`hcs …`, `hCS …`) and the 3-conjunct
`ShipsRes` patterns. Grep is not a proof; the S3 build is the check (§R4.8).

### R4.1 The shared edit (Tools/ShippingGen2Defs.lean, one commit, with the GEN2_DEFS copy)
Defs:87-90 (`ChildShips`) currently starts with `∀ (dsn : Design), …`. `argPorts` is already used in Defs (:67), so
`ChildPortWidths` needs no new import. Insert before Defs:82 (the `ChildShips` doc comment):
```lean
/-- G-CHILD-PORTW: the served module's argument ports have the package's declared port widths. -/
def ChildPortWidths (q : Pkg ι dom) (mc : Sparkle.IR.AST.Module) : Prop :=
  (Tools.ShippingMachineCompose.argPorts mc).map (fun p => p.ty.bitWidth) =
    q.ports.map (fun b => (kindTy b.2).bitWidth)
```
and change `ChildShips` to
```lean
def ChildShips (q : Pkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Design) : Prop :=
  ChildPortWidths q mc ∧
  ∀ (dsn : Design), (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) →
    moduleByName dsn.modules mc.name = some mc →
    ∀ (i : ι), ChildRunN (childMap dsn.modules) dsn n mc (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i)
```
This is the Candidate W text of rev3 §1 verbatim (the right-hand side is `Pkg.portWidths q` by `rfl`; written inline because Defs is
upstream of Adapt). Existing `ChildShips` uses in Defs need no text edit: ShipsRes :143, ShipsAt :155, StepStmt :323,
MemParentStmt' :339, MemParentStmt/LeafStmt :351 (grep list at fa84af5d: Defs:87, 143, 155, 323, 339, 351). Their MEANING
changes: positive positions (`ShipsRes`, `ShipsAt`, `CacheShips`, `InvAt`) strengthen, conclusions of
`MemParentStmt'`/`LeafStmt`/(`StepStmt` conclusion) strengthen, and `StepStmt`'s `ServedP (ShipsRes …)` premise
strengthens (mixed). The ordering of the conjunct (FIRST) is chosen so that the existing run part keeps its
position `.2`; positional projections *into* the run (`h.2.2.2.2.2.1`, Connect/GroupServed) are on `ChildRunN`, not on
`ChildShips`, and are unaffected.

### R4.2 Producers of `ChildShips` (each must prove the new conjunct from its own premises)
"Supplier" = the lemma already built that gives the width fact; it is applied as `refine ⟨<term>, ?_⟩` placed
immediately before the `intro dsn …` line (the run part is untouched). **No producer gets a new premise.**
Core = `Tools.ShippingGen3PortWidthsCore` (built clean, g3pw-ba9b9c82), imports C6 + MemData + PortWidthsPure only.

| # | producer | file:line (fa84af5d) | `intro dsn` line | supplier (built) | term inserted | producer-local `argPorts` identity (where it lives) | S3 import change |
|---|---|---|---|---|---|---|---|
| P1 | `leaf_childShips_of_LB` | Tools/ShippingGen2Leaf.lean:243-263 | :263 | Core `noCalls_childPortWidths` (N-A) | `noCalls_childPortWidths p hL hnoI hok hSS houtTy htake hpost` | not in this proof; inside Core N-A from `wired` of `hL` (LeafSeq `hargs`, MachineWired) | Leaf imports Core (Leaf→MemShips→C6; Core→C6: no cycle expected) |
| P2 | `slotlessLeaf_childShips_of_LB` | Tools/ShippingGen2SlotlessLeaf.lean:283-296 (comb branch) | :345 | Core `noCalls_childPortWidths` | same term (its `hL hnoI hok hSS houtTy htake hpost` are binders of the producer) | Core N-A (the producer's own `hargs` is :325-ish in rev2 text; not reused) | SlotlessLeaf imports Core |
| P3 | `memParent_childShips` | Tools/ShippingGen2MemShips.lean:39-73 | :73 | Core N-B `childPortWidths_of_composedNW` | `Core.childPortWidths_of_composedNW n houtTy (ok_outNameOk p.d hok) hsl hI0 hkD hIlen hSL hSlen hLlen hNIn hNW hpost` (`hNW` :54, `hI0` in scope as in P3) | `calls_ports` conjunct `argPorts m = machPorts … (d.bsIn.take kD)` inside N-B (MachineDepthChild) | MemShips imports Core |
| P4 | `oneOut_childShips` | Tools/ShippingGen2OneOut.lean:288-321 | :321 | Core N-B | same shape; `hNW := oneOut_composedNW L P p hdata hins hsimple hA ran hdec h n` (already :308) | as P3 | OneOut gets Core transitively (MemShips) |
| P5 | `group_childShips` | Tools/ShippingGen2GroupServed.lean:294-331 | :331 | Core N-B (the body of `Tools.ShippingGen2.GroupPortWidths.group_childPortWidths`, Tools/ShippingGen3GroupPortWidths.lean:38-65, built g3pw-ba9b9c82) | the same N-B application, with `hNW := group_composedNW L P p hdata hfe hdec n h` (already in the proof) | as P3 | GroupServed must import Core. `Tools/ShippingGen3GroupPortWidths.lean` imports GroupServed, so the lemma CANNOT stay there once `group_childShips` uses it (cycle): at S3 the term goes inline into `group_childShips`, and `group_childPortWidths` is either kept as a thin corollary in that file (conclusion `ChildPortWidths p b`, proof = the same N-B application) or deleted; the check file follows |
| P6 | `oneOutSl_childShips` (S5 B2) | Tools/ShippingGen2SlotlessParentRun.lean:288-322 | :322 | N-C: `Tools.ShippingGen2.SlotlessPortWidths.oneOutSl_childPortWidths` (Tools/ShippingGen3SlotlessPortWidths.lean:119-149, built g3nc-ce4c32a4, exit 0) | `oneOutSl_childPortWidths L P p hdata hins hsimple hsl0 hA hpost ran hdec h n` — all arguments are B2's own binders | `calls_ports_sl` (A1) fourth conjunct, inside N-C | SlotlessParentRun imports `Tools.ShippingGen3SlotlessPortWidths` (no cycle: it imports SlotlessParent, Core, GroupServed, ChildPortWidths; not Run) |
| P7 | `groupSl_childShips` (S5 B3) | Tools/ShippingGen2SlotlessParentRun.lean:340-375 | :375 | N-C `groupSl_childPortWidths` (SlotlessPortWidths.lean:152-181) | `groupSl_childPortWidths L P p hdata hins hfe hsl0 hpost hdec n h` (B3's binders) | as P6 | as P6 |

**S5 slotless-parent producers: supplier present.** P6/P7 have a built supplier (N-C), which was the S3 gate of the
rev3 review (ba9b9c82 / ce4c32a4). Their `hpost`, `hdec`, `h` are the producers' own binders, so no premise is added. The
corollary signatures omit `hext`, `hA`/`ran` partly (see the Lean file); the call may need `hA ran` or not exactly as
written above: the exact argument lists are the S3 implementer's to take from the built signatures, not claimed here.

**Not covered (stated, not claimed):**
- **StepStmt proof (M2-b):** not in the tree (`grep StepStmt` finds only statements and checks). Nothing to fix and
  nothing supplied. It will have to dispatch to P1-P7 by parent kind.
- **Gate route [M4]:** no `ChildShips` producer in the tree at fa84af5d (par/gen4-gate is a separate branch). This
  investigation found no supplier and no producer; it does not show that none can exist.
- **T2 / other future producers:** none found at fa84af5d.

### R4.3 `ChildShips`-run consumers (rewrite `hcs …` → `hcs.2 …`)
These apply the old `ChildShips` as a function (`∀ dsn …`). After S3 they must apply `.2`. Each is one token.

| # | site | file:line | pattern / application | fix |
|---|---|---|---|---|
| C1 | `seqFactsRN_of_callDec` (sequential half) | Tools/ShippingGen2Connect.lean:137-140 | `obtain ⟨hmod, Dc, ⟨_, q', hq', _, hcs⟩, hcons⟩ := hmc` (ShipsAt); `hcs dsn hcons hmod i` | `hcs.2 dsn hcons hmod i` |
| C2 | GroupServed sequential half | Tools/ShippingGen2GroupServed.lean:80, :83 | `⟨_, q', hq', _, hcs⟩`; `(hcs dsn hcons hmod i)` | `hcs.2 …` |
| C3 | GroupServed combinational half | Tools/ShippingGen2GroupServed.lean:94, :97 | same | `hcs.2 …` |
| C4 | `hserve` in OneOut | Tools/ShippingGen2OneOut.lean:200-203 | `⟨_, ⟨q', n', hq', _, hcs'⟩, _⟩`; `(hcs' D hDc hmod i)` | `(hcs'.2 D hDc hmod i)` (pattern unchanged) |
| C5 | `hserve` in FitChain | Tools/ShippingGen2FitChain.lean:946, :949 | same shape | `(hcs'.2 D …)` |
| C6a | `oneOutWidthAt` | Tools/ShippingGen2OneOutTop.lean:312, :315 | `⟨_, ⟨q, n', hq, _, hCS⟩, _⟩`; `hCS D hDc hmod i0` | `hCS.2 D …` |
| C6b | `oneOutWidthAt` (O copy) | Tools/ShippingGen2OneOutTopO.lean:305, :308 | same | `hCS.2 D …` |
| C7 | `argLen_of_shipsRes` (U-ARITY) | Tools/ShippingGen3Arity.lean:84, :87 | `childRunN_argLen (hCS D hDc hmod i)` | `hCS.2 D …` |
| C8 | `callOutRange_of_closing` | Tools/ShippingGen5T2Conn.lean:112, :117 | `⟨-, ⟨q0, n, hq0, -, hCS⟩, -⟩ := hS`; `hCS dsn hDc hmc i` | `hCS.2 dsn …` |
| C9 | `callField_at` | Tools/ShippingGen5T2Tie.lean:222, :225 | same | `hCS.2 dsn …` |
| C10 | `childShips_congr` | Tools/ShippingGen2T1.lean:141-145 | `intro dsn hg hmc i; exact hc dsn …` | `exact ⟨hc.1, fun dsn hg hmc i => hc.2 dsn (by rw [h]; exact hg) hmc i⟩` (the width conjunct does not mention `Dc`) |

C8 and C9 are NEW relative to rev0-rev3 (T2 files, `par/gen5-t2`, now in the tree). Tests that quote these sites
(`Tests/Gen3/ArityCheck.lean`, `Tests/Gen3/T1Check.lean` `#print axioms childShips_congr`, `Tests/Gen2/S3GroupCheck.lean`
C-1 :507-536, `Tests/Gen2/S5Check.lean` ExpB2/ExpB3 :296-350, `Tests/Gen5/T2TieCheck.lean`) state `ChildShips` by name only,
or pin a producer whose TEXT conclusion `ChildShips p (n + 1) b D` is unchanged: they need re-elaboration, not an edit
(expectation; the S3 build is the check). `S3GroupCheck.lean:320-322` pins `group_childShips`' conclusion by head
`ChildShips` and arg index 3 (`n`): unchanged by the new first conjunct.

### R4.4 Mixed / re-elaborate-only definitions and files (no text change expected)
| site | file:line | note |
|---|---|---|
| `ShipsRes`, `ShipsAt`, `CacheShips`, `InvAt`, `IHAt`, `BodyKeepsInv`, `ChildKeepsInv`, `KeepBodyStmt`, `KeepChildStmt`, `ServedShipsStmt`, `StepStmt`, `MemParentStmt'`, `MemParentStmt`, `LeafStmt` | Tools/ShippingGen2Defs.lean:143, 155, 323, 339, 351 and neighbours | text unchanged; meaning per R4.1. No relation claimed at mixed positions (rev3 §R3.2 c stands) |
| `ShipsResOld`, `CacheShipsOld`, `InvAtOld`, `StepStmtOld`, `shipsRes_old`… | Tools/ShippingGen2PostFacts.lean:68-123 (`ChildShips` at :69, :95) | pre-InstClosed copies, NOT pre-ChildPortWidths copies; they carry the width conjunct after S3 |
| KeepChild / InstKeep / PostFactsProof / Served | Tools/ShippingGen2{KeepChild,InstKeep,PostFactsProof,Served}.lean | generic in `ShipsRes`; no `ChildShips` destructuring found by grep (`hw.1.1…` projections in KeepChild:77-152, :306 are on `InvAt`/`RealChildA`, not on the `ChildShips` conjunct) |
| `MemParentStmt'` text copy | Tools/ShippingGen2MemParent.lean:57-69 | the `∀ n, TopShips … ∧ ChildShips …` conclusion; same meaning change as Defs :339 |
| instances | Tests/Gen2/{LeafInstance:67, SlotlessLeafInstance:57, MemParentInstance:55, QuantInstance:136}.lean | state `ChildShips` through the theorems; re-elaborate |

### R4.5 The new-file machinery after S3 (Gen3 files that currently define or use `Tools.ShippingGen3ChildPortWidths.ChildPortWidths`)
The local definition `Tools.ShippingGen3ChildPortWidths.ChildPortWidths` moves to Defs as
`Tools.ShippingGen2.ChildPortWidths`; the old one is deleted (no alias, so a stale reference is a compile error, not a silent
second definition).

| file | now | at S3 |
|---|---|---|
| Tools/ShippingGen3PortWidthsCore.lean | conclusions are the BODY of the width statement (built; imports C6, MemData, PortWidthsPure) | unchanged text; first consumer from Leaf/SlotlessLeaf/MemShips/GroupServed |
| Tools/ShippingGen3ChildPortWidths.lean | defines `ChildPortWidths`; own N-A/N-B copies (imports OneOut, PortWidthsPure); P1-P4 | delete the local def and the N-A/N-B copies; P1-P4 remain as thin corollaries (proofs re-pointed to Core, conclusion `Tools.ShippingGen2.ChildPortWidths`); used by checks only |
| Tools/ShippingGen3GroupPortWidths.lean | `group_childPortWidths` (imports GroupServed, Core, ChildPortWidths) | the term is moved into `group_childShips`; file becomes a thin corollary or is deleted (R4.2 P5) |
| Tools/ShippingGen3SlotlessPortWidths.lean | N-C + `oneOutSl_`/`groupSl_childPortWidths`, conclusion `Tools.ShippingGen3ChildPortWidths.ChildPortWidths p b`; imports ChildPortWidths | conclusion repointed to Defs' name; the import of Gen3ChildPortWidths is dropped (it is needed only for the name) |
| Tests/Gen3/ChildPortWidthsCheck.lean | `checkExpected ``ChildPortWidths ``ExpectedCPW`, mutants, `pbh_cpw_*` examples (:50, :234, :245-246, :289-302) | `ChildPortWidths` now Defs' constant; expected types of P1-P4 follow the new name |
| Tests/Gen3/PortWidthsPrepCheck.lean | :63, :117, :141-151 (compares Core with the Gen3ChildPortWidths copies) | the copy comparison (:141-147) must be deleted or reduced to Core vs Core (the copies are gone) |
| Tests/Gen3/SlotlessPortWidthsCheck.lean | :79, :95, :162, :178-179, :212, :228, :244-245 | name repointed; the `hpw`-added mutants stay mutants |
| lakefile.lean | entries :4635-4711 | no new `lean_lib` required; add none unless a new file is created |

### R4.6 PkgCompat (Tests/Gen2/PkgCompat.lean) — C6 `childShips_gen` old ⇒ new is UNPROVED: premise form
`Old.ChildShips` (PkgCompat:49) has no width conjunct, and this investigation found no lemma deriving
`ChildPortWidths (.gen q) mc` from it (this is not a claim that none exists or that it fails). So the lifts take the
width as an EXPLICIT compat premise `hpw`, as G-POST's `hic` does. `hpw` is a premise of these COMPAT lemmas only; it
is NOT added to any production producer (review note at ba9b9c82, binding). Current text at fa84af5d:
`childShips_gen` :317-319; `shipsRes_lift` :333-337 (already has `hic`); `shipsAt_lift` :339-342; `cacheShips_lift`
:344-348; `invAt_lift` :350-354; `memParentStmt'_gen` ≈:395-417 (uses `topShips_ofOld_wired`, S2); `memParentStmt_gen` ≈:419-438;
`leafStmt_gen` ≈:440-459; `#print axioms` :473-.

Types after S3 (the rev3 §R3.2 types, re-checked against the fa84af5d text; `ChildPortWidths` = `Tools.ShippingGen2.ChildPortWidths`):
```lean
theorem childShips_gen (q : SrcPkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design)
    (hpw : ChildPortWidths (.gen q) mc) :
    Old.ChildShips q n mc Dc → ChildShips (.gen q) n mc Dc :=
  fun h => ⟨hpw, fun dsn h1 h2 i => Or.inl (h dsn h1 h2 i)⟩

theorem shipsRes_lift … (r : Tools.ShippingChildInv.Res) (hic : InstClosed r)
    (hpw : ∀ q, P c = some q → ChildPortWidths (.gen q) r.1) : Old.ShipsRes L P c r → ShipsRes L (Pkgs.lift P) c r
theorem shipsAt_lift … (r : Tools.ShippingChildInv.Res)
    (hpw : ∀ q, P c = some q → ChildPortWidths (.gen q) r.1) : Old.ShipsAt L P n c r → ShipsAt L (Pkgs.lift P) n c r
theorem cacheShips_lift … (hic : ∀ c r, Reach c → m.get? c = some r → InstClosed r)
    (hpw : ∀ c r, Reach c → m.get? c = some r → ∀ q, P c = some q → ChildPortWidths (.gen q) r.1) : …
theorem invAt_lift … (hic : …)
    (hpw : ∀ c r, Reach c → (Tools.ShippingChildBndCore.cv w).get? c = some r →
      ∀ q, P c = some q → ChildPortWidths (.gen q) r.1) : Old.InvAt L P Reach D w → InvAt L (Pkgs.lift P) Reach D w
```
The three `.gen` statement forms (`memParentStmt'_gen`, `memParentStmt_gen`, `leafStmt_gen`) each gain ONE premise
`ChildPortWidths (.gen q) b →` immediately before `∀ n`, and the proof changes `intro … h13 n` to `intro … h13 hpw n` and
`childShips_gen q _ _ _ this.2` to `childShips_gen q _ _ _ hpw this.2` (:417, :438, :459). The `TopShips` conjunct stays
as S2 left it (`topShips_ofOld_wired`). **These are the only added hypotheses of the whole change, and they live in
compat theorems.** They do not count as supplied width facts.
The PkgCompat `Old ⇒ new` direction for widths therefore stays **UNPROVED** and is documented as such in the PkgCompat header.

### R4.7 Docs and the GEN2_DEFS copy
- `scripts/gen2/GEN2_DEFS.lean.txt` is replaced by `cp Tools/ShippingGen2Defs.lean scripts/gen2/GEN2_DEFS.lean.txt` in
  the S3 commit; `cmp` must exit 0 before and after.
- `scripts/gen2/*.md` that quote `ChildShips` (grep list at fa84af5d: GENERAL_SPEC, STEP_IFACE_FREEZE, LEAF_*, MEMPARENT_*,
  LOOPPKG_*, T1_CONNECT_*, CALLFIELD_FREEZE, S3_GROUP_FREEZE, S4_*, G3GEN_CALL_PLAN, LEAD_UNITS_PLAN, ROUTE_CENSUS,
  STEP_S2_VACUITY_REPORT, STEP_S6_RESULT, GPOST_*, TOP_CONTRACT_REVISION, SERVED_*, S5_SLOTLESS_FREEZE, DPORT_ROUTE_REPORT):
  add a one-line note in a result document; history entries stay unchanged.

### R4.8 Verification plan for S3 (after approval; nothing here has been run)
1. Edit in this order inside ONE commit: Defs + GEN2_DEFS copy; Core imports in Leaf/SlotlessLeaf/MemShips/GroupServed;
   P1-P7 `refine ⟨…, ?_⟩`; C1-C10; Gen3 file repointing (R4.5); PkgCompat (R4.6).
2. Serial builds in the Pod (`kjob lake build`), first the producers upstream-to-downstream:
   `Tools.ShippingGen2Defs`, `Tools.ShippingGen3PortWidthsCore`, `…Gen2MemShips`, `…Leaf`, `…SlotlessLeaf`,
   `…OneOut`, `…Connect`, `…GroupServed`, `…FitChain`, `…OneOutTop`, `…OneOutTopO`, `Tools.ShippingGen3{Arity,ChildPortWidths,GroupPortWidths,SlotlessPortWidths}`,
   `…Gen2SlotlessParentRun`, `…Gen2T1`, `…Gen5T2{Conn,Tie}`, then the Tests listed in R3.5.
3. The full reverse-import closure of `Tools.ShippingGen2Defs` is computed from `lake` (not grep) by the coder; every
   lakefile target in it is built (the clean issue-linked build is the coder's, per the common rule for Lean commits).
4. `cmp` on the GEN2_DEFS copy; `#print axioms` roots ⊆ {propext, Classical.choice, Quot.sound}, no `sorryAx`.
5. Mutants in the check files are rejections by signature/defeq (`checkExpected` / `checkMutant`) of a changed
   statement; they are **not semantic counterexamples**.

### R4.9 Open items and what is NOT claimed (rev4)
- NOT built: nothing in rev4 has been compiled; line numbers and "no cycle expected" claims are from reading and from
  the import lists of the files (Leaf→MemShips→C6; Core→C6, MemData, PortWidthsPure; GroupServed→GroupComb, Connect; SlotlessParentRun→SlotlessParent, GroupServed, …). The
  S3 build is the check.
- The exact argument lists of the P6/P7 calls are to be taken from the built signatures (SlotlessPortWidths.lean:119-181);
  rev4 does not claim they match as written.
- Supply status: P1-P7 have a built supplier; StepStmt proof (M2-b) and the gate route [M4] have none in the tree. The
  final-FG obligation (§4) is therefore NOT complete: no `StepStmt` proof exists to dispatch to P1-P7.
- Old ⇒ new `ChildShips`/`ChildPortWidths`: UNPROVED (compat premise `hpw`, R4.6).
- Merge/push, poc/main integration, Co-Authored-By: out of scope.

## rev5 — S3 applied (branch kjob/g3pt-s3b, base d5f25c0a)

Done as in R4.1-R4.7: Defs `ChildPortWidths` + first conjunct of `ChildShips` (GEN2_DEFS copy `cmp`-identical); P1-P7 each insert
`refine ⟨<supplier>, ?_⟩` with no added premise (P2 SlotlessLeaf: placed at the start of the proof, because `hpost` is
rewritten later); C1-C10 use `.2`; Gen3 N-A/N-B copies deleted (P1-P4 are thin corollaries of Core); PkgCompat takes the
explicit compat premise `hpw` (compat lemmas only). Core-vs-Core comparison in PortWidthsPrepCheck was deleted and not
counted; Core lemmas are checked against independent Expected types in ChildPortWidthsCheck (mutants are signature/defeq
rejections, not semantic counterexamples).

Focused `kjob lake build` in the Pod, one target at a time, all exit 0: Defs, Core, MemShips, Leaf, SlotlessLeaf, OneOut,
Connect, GroupServed, FitChain, OneOutTop(O), Gen3{Arity,ChildPortWidths,GroupPortWidths,SlotlessPortWidths},
SlotlessParentRun, T1, Gen5T2{Conn,Tie}, Comb, KeepChild, MemParent, PostFacts(Proof), Served(Run), SlotlessTop,
Gen3ArgSupply, ArgWidthSrc, Gen5{T1ND,T2OutTy,T2Range}, and the Tests ChildPortWidthsCheck, PortWidthsPrepCheck,
SlotlessPortWidthsCheck, PkgCompat, LeafInstance, MemParentInstance, PMem4Check, QuantInstance, S3GroupCheck, S5Check,
S5SlotlessProbe, SlotlessLeafInstance, TopNCCheck, ArityCheck, ServedCheck, T1NDCheck, T2{Conn,OutTy,Tie}Check, T1Check.
NOT done here: full reverse-import closure of Defs and AllTests (coder's clean build).
Done afterwards by the coder (record sync, comment only): clean issue-linked build s3v-cca7d3f1 at cca7d3f1 (exit 0, 1844 jobs:
the 35 reverse-import leaves of Tools.ShippingGen2Defs + Tests.AllTests; every axiom list standard). Its only `sorry`
warnings are the pre-existing ones in Tests/TestTemporal.lean at lines 156, 162, 166 and 171 (4 warnings, outside this
change). Reviewer approved at cca7d3f1.
Not supplied: StepStmt proof, gate route [M4], general coverage. Old ⇒ new width: UNPROVED (compat premise).
Mixed-position old/new equivalence: not claimed.
