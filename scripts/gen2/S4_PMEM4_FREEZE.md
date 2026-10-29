# S4 P-MEM-4 freeze: where does the one-output consumer chain consume `hnomem`'s NAME half? (design only)

**Status: rev3 — §2 accepted (limited) at 0efea824 (g2pm4-0efea824 exit 0); audit revised after review R1/R2.** Research at par/gen2-spec 48775f38
(grep/read only; no lake/lean run); implementation files written on cd026658 (see §7), not built or elaborated. Line
numbers are at 48775f38 (the originals are unchanged since then). Obligation: scripts/gen2/S4_PMEM_FREEZE.md §4.2 (P-MEM-4).

rev2 changes (review): §5 c is now a TRANSITIVE premise audit (was a direct `getUsedConstants` check of the types); §3
records that the transitive check is that audit; wording: no minimality / strictness claim (§2, §4); §4 build is a normal
incremental build; §7 lists the implementation.

## 0 Question

`hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (memChild? x.1).isNone = true` has an ORIGIN half (`.1`)
and a NAME half (`.2`). `Tools/ShippingGen2DataBridge.lean` `hord_of_row` supplies only the origin half
(`∀ k < insts.length, (instOrigins.getD k .ord).child? = none`) for one-output parents. The name half is FALSE on a legitimate
one-output parent whose ordinary callee has a memory-placeholder name (`collPlainCD_nomem_false`,
Tests/Compiler/MemNameCollisionPlainCertTest.lean:177-180). Which theorems reached from `Tools/ShippingGen2OneOutTop.lean`
consume which half, and which copy range gives types that carry no name half?

## 1 Trace table

Terminal-consumer patterns searched in all chain files: `nomem_tag`, `nomem_name`, `nomem_tags`, `notag_at`, `real_of_kid`,
`kid_of_real`, `kid_iff_real_of_nomem`, `Kid.real`, `(h _ _).2`, `memChild?`, and implicit-hypothesis tactics
(`assumption`, `simp_all`, `‹›`, `[*]`, `aesop`). Hits outside signatures: only the two `nomem_tag` sites below.

| theorem | file:line | `hnomem` consumed how | terminal name-half sites |
|---|---|---|---|
| `core_kids_facts_ranA` | Tools/ShippingParentTailsA.lean:48 (premise :57) | ORIGIN, terminal: `nomem_tag hnomem hk'` at :183 (excludes the `child? = some y` branch of `ChildrenRealA`, used only for conjunct 5 "every `g ∈ D.modules` comes from a `RealChildA`") | none |
| `core_linkedWF_ranA` | TailsA:197 (:206) | passed to `core_kids_facts_ranA` at :261, `.2.1` only (`b.body = M.body`) | none |
| `core_instOuts_not_assigned_ranA` | TailsA:269 (:278) | passed to `core_linkedWF_ranA` at :286 | none |
| `core_hierGate_anyA` | Tools/ShippingParentDesignA.lean:50 (:59) | passed to `core_kids_facts_ranA` at :66, `.2.1` only | none |
| `core_kidsComb_raw₁A` | DesignA:177 (:187) | passed to `core_kids_facts_ranA` at :194, `.2.1` only | none |
| `core_instNames₁A` | DesignA:204 (:214) | passed to `core_kids_facts_ranA` at :221, `.2.1` only | none |
| `core_noSelfRead₁A` | DesignA:233 (:243) | passed to `core_kids_facts_ranA` at :250, `.2.1` only | none |
| `core_outsExtracted₁A` | DesignA:269 (:279) | passed to `core_kids_facts_ranA` at :287 (`.2.1`) and `core_instOuts_not_assigned_ranA` at :288-289 | none |
| `core_rst_anyA` | DesignA:402 (:412) | UNUSED (body :417-489 never mentions it) | none |
| `core_runFactsHA` | DesignA:494 (:504) | passed to the six components at :511-516 | none |
| `core_callPorts_oneA` | Tools/ShippingGen2OneOutTop.lean:51 (:61) | passed to `core_kids_facts_ranA` at :76, `.2.1` only | none |
| `core_instOutWidthsOk_oneA` | OneOutTop:198 (:212-213) | passed to `core_callPorts_oneA` at :230 and `core_kids_facts_ranA` at :232 (`.2.1`) | none |
| `oneOutWidthAt` | OneOutTop:289 (:293-294) | ORIGIN, terminal: `nomem_tag hnomem hk` at :307 (excludes the `child? = some md` branch of `Served1P`) | none |
| `oneOut_topShips` | OneOutTop:340 (:343-344) | passed to `core_runFactsHA` (:386-396, five projections), `core_linkedWF_ranA` (:388), `core_instOutWidthsOk_oneA` (:398), `oneOutWidthAt` (:400) | none |

Key observations:
- **The NAME half is consumed nowhere in this chain.** Both terminal consumptions are `Tools.ShippingChildInv.nomem_tag`
  (Tools/ShippingChildInv.lean:522-530), which projects `.1` only.
- Every use of `core_kids_facts_ranA` in the chain takes `.2.1` (`b.body = M.body`). That conjunct's proof (TailsA:63-148:
  run destructuring, `wired`'s `hcall1`/`hGcall`/`hcleanAny`, `hhas`, `hbeq`) uses NO part of `hnomem`. So the origin half
  at TailsA:183 is also never needed by OneOutTop's chain; the ONLY needed consumption is OneOutTop:307.
- The run evidence dispatches by ORIGIN, not by name:
  - `MachineRanA` (Tools/ShippingParentRanA.lean:47-58) carries `ChildrenRealA O shape children`;
  - `ChildrenRealA` (Tools/ShippingChildRunAKids.lean:51-56): `(instOrigins.getD k .ord).child? = some y ∨ RealChildA O (insts[k]).1 y`;
  - `MemChildren` (Tools/ShippingMachineEntry.lean:877-879): keyed on `(instOrigins.getD k .ord).child?`;
  - `Served1P` (Tools/ShippingGen2Defs.lean:231-240): `(∃ md, (instOrigins.getD k .ord).child? = some md ∧ mc = md.1) ∨ …`.
  None of these mentions `memChild?`. The name-route definitions (`Kid`, ShippingKid.lean:154-157; `Kid.real` :220-221;
  `kid_iff_real_of_nomem` :252-253; `real_of_kid`/`kid_of_real` :260-271) are not reached from this chain.

## 2 Copy set and replacements

Because no theorem body needs the name half, the copies only change TYPES: drop `hnomem`, and where the origin half is
really used, take the index form that `hord_of_row` already produces:
`hord : ∀ k < p.d.shape.insts.length, (p.d.shape.instOrigins.getD k .ord).child? = none`.
(The list form `∀ o ∈ instTagged, o.2.child?.isNone = true` converts to it by `notag_at`, ChildInv.lean:544-551.)

Proposed copy range (suffix `O` = origin-keyed or premise-free; no minimality is claimed or proved):

| new theorem | copied from | premise | replacement |
|---|---|---|---|
| `core_bodyEq_ranO` | TailsA:48-148 (prefix of `core_kids_facts_ranA`, conjunct `b.body = M.body` only) | NO memory premise | none needed (no consumption) |
| `core_linkedWF_ranO` | TailsA:197-263 | none | `(core_kids_facts_ranA … hnomem …).2.1` → `core_bodyEq_ranO …` |
| `core_instOuts_not_assigned_ranO` | TailsA:269-287 | none | calls `core_linkedWF_ranO` |
| `core_hierGate_anyO`, `core_kidsComb_raw₁O`, `core_instNames₁O`, `core_noSelfRead₁O` | DesignA:50-94, 177-199, 204-227, 233-262 | none | `.2.1` → `core_bodyEq_ranO` |
| `core_outsExtracted₁O` | DesignA:269-395 | none | `.2.1` → `core_bodyEq_ranO`; `core_instOuts_not_assigned_ranA` → `…_ranO` |
| `core_rst_anyO` | DesignA:402-489 | none | delete the unused premise only |
| `core_runFactsHO` | DesignA:494-516 | none | the six `O` components |
| `core_callPorts_oneO` | OneOutTop:51-193 | none | `.2.1` → `core_bodyEq_ranO` |
| `core_instOutWidthsOk_oneO` | OneOutTop:198-255 | none | `core_callPorts_oneO`, `core_bodyEq_ranO` |
| `oneOutWidthAtO` | OneOutTop:289-335 | `hord` (index form) | :307 `rw [nomem_tag hnomem hk] at hmd` → `rw [hord k hk] at hmd` |
| `oneOut_topShipsO` | OneOutTop:340-421 | `hord` (index form) | the `O` callees; `hord` passed only to `oneOutWidthAtO` |

Not copied: the conjunct 5 of `core_kids_facts_ranA` (its origin use at TailsA:183 is not needed by the chain; if a later
consumer needs it, a copy replaces `nomem_tag hnomem hk'` by `hord k hk'`, or uses `realChild_of_childrenRealT`-style
reasoning on `ChildrenRealA` — ChildInv.lean:560-575 is its `ChildrenReal` analogue). `core_closed_typedIn_ranA`,
`core_kidsPass_anyA`, `core_designCheckHA` are not reached from OneOutTop and are not copied.
`Tools.ShippingMemKid.kidT_of`/`kidT_ofO` (ShippingKid.lean:191-215) are NOT needed: the chain never classifies a kid; it only
uses `ChildrenRealA`/`Served1P`, already origin-dispatched.

Composition with the row (unchanged file): `oneOut_topShipsO … (hord := hord_of_row hrow hsimple) …`.

### 2.1 Why the existing hnomem-free `…AM` family does not apply (coder check)
`Tools/ShippingSrm3Iface.lean` (`core_kids_facts_ranAM`, :59) and `Tools/ShippingSrm4Core1.lean` / `Core2.lean`
(`core_linkedWF_ranAM`, `core_hierGate_anyAM`, …) already drop `hnomem`, but each adds `hfne : d.shape.instFields ≠ []`
(Srm4Core1.lean:5). `hfne` is used to pick the `MemChildren` branch of the closing evidence
(Srm3Iface.lean:162-165, `rcases hcc with ⟨hfe, -⟩ | ⟨-, -, h⟩; exact absurd hfe hfne`). A one-output parent has
`instFields = []`, so `hfne` is false there and the `…AM` family is unusable. The `…O` copies above need neither
`hfne` nor `MemChildren`: the chain only takes `b.body = M.body` (prefix before Srm3Iface:160 / TailsA:149) and the
origin fact at `oneOutWidthAtO`.

## 3 Stops

None found. No site in the chain needs the name; no shared definition used by the chain states its fact by `memChild?`
(checked: `MachineRanA`, `ChildrenRealA`, `MemChildren`, `Served1P`, `ServedP` :242-244). The premises of
`oneOut_topShips` other than `hnomem` (`MemParentDataOk`, `MachineTaken`, `CallDec`, `MachineTraceLBX`, `OneOutWidth`, `Laws`)
were not unfolded by reading. The transitive check is done by the premise audit of §5 c (`pmAuditRoot` in
Tests/Gen2/PMem4Check.lean): from each new theorem's type it unfolds every Prop-level definition, Prop structure field
and Prop inductive constructor reached (and type formers, class instances, every inductive's constructor types). A
forbidden name (`memChild?`, `Kid`) reached on that LOGICAL path is a STOP to report, not to patch. Opaque / `partial` /
axiom / extern boundaries on the logical path are printed as UNCHECKED: the audit never claims absence through them.

## 4 Plan & size

Verbatim copies; only signatures and the listed call sites change. Estimated (from the source ranges):

| new file | content | lines |
|---|---|---|
| `Tools/ShippingParentTailsO.lean` | `core_bodyEq_ranO` (~95), `core_linkedWF_ranO` (~67), `core_instOuts_not_assigned_ranO` (~19) | ~200 |
| `Tools/ShippingParentDesignO.lean` | hierGate (~45), kidsComb (~23), instNames (~24), noSelfRead (~30), outsExtracted (~127), rst (~88), runFactsH (~23) | ~380 |
| `Tools/ShippingGen2OneOutTopO.lean` | callPorts (~143), instOutWidths (~58), `oneOutWidthAtO` (~47), `oneOut_topShipsO` (~82) | ~360 |
| `Tests/Gen2/PMem4Check.lean` | controls §5 + `#print axioms` | ~80 |

Total ~1000 lines, of which ~940 copied. Rules check:
- New files only; no edit to TailsA / DesignA / OneOutTop / ShippingChildInv / DataBridge / Defs; Elab/compiler untouched.
- The only touch of an existing file is the established append-only `lean_lib` entry per new module in `lakefile.lean`
  (as for `Tools.ShippingGen2DataBridge`, lakefile.lean:4605-4606). If that counts as a shared-file edit, it needs the
  user's OK first.
- FG not narrowed (no definition changed). The enumerated premise (`hnomem`) is removed; no premise is added except
  `hord` in the two top theorems (`oneOutWidthAtO`, `oneOut_topShipsO`), in the form `hord_of_row` already supplies.
  No minimality or overall strictness of the premise set is claimed or proved.
- Originals stay; existing signature audits (Tests/Compiler/Srm5AuditExpected.lean:150 etc., RanThreadingStatementsTest:89)
  are unaffected. A copy does not follow later changes of its original (same caveat as TailsA:265-268).
- The `lakefile.lean` append (four `lean_lib` entries at the end) is authorised for this work.
- Build: a normal issue-linked, incremental, focused `kjob lake build` of the three new modules and the test (no forced
  cold build; whatever the cache gives).

## 5 Controls

a. **Positive (name collides, origin ord):** `collPlainCD_D` (Tests/Compiler/MemNameCollisionPlainCertTest.lean:136-144;
   `instFields = []`, one entry `SparkleMem.sync.4.8` of origin `.ord`, two registers). Add
   `theorem collPlainCD_hord : ∀ k < collPlainCD_D.shape.insts.length, (collPlainCD_D.shape.instOrigins.getD k .ord).child? = none`
   by `decide`, next to the existing `collPlainCD_nomem_false` (:177-180): the new premise holds where the old one is
   provably false. This is a premise-level control; an end-to-end `oneOut_topShipsO` instance at `collPlainCD` needs a
   `Pkg`/`MachineTaken` for it that does not exist (not claimed). Also, if `callerL` (Tests/Gen2/DataBridgeCheck.lean:138-148)
   has a `Pkg`, instantiate `hord` via `hord_of_row` there (type-checks the composition).
b. **Negative:** `memShape0` (DataBridgeCheck.lean:151-158, memory origin, no fields): `¬ ∀ k < insts.length, (… ).child? = none`
   by `decide`, so the new theorems cannot be applied to a memory-origin one-output entry. Out of range (`memShapeX`, :167-175)
   stays excluded by the `k < insts.length` form.
c. **Audit (transitive; replaces the direct `getUsedConstants` check of rev1).** In Tests/Gen2/PMem4Check.lean:
   (o) expected types: for each of the 14 (original, copy) pairs, the copy's binders are the original's (names, binder
   infos, types compared after instantiating the copy with the original's fvars) with `hnomem` deleted, or replaced at
   the same position by `hord` whose type is `hord_of_row`'s conclusion; equal conclusions (`core_bodyEq_ranO`: the
   original's second conjunct); `==`, with a logged `isDefEq` fallback.
   (i) `pmAuditRoot` over the 14 copies, forbidden names `Sparkle.Compiler.MachMemory.memChild?`,
   `Tools.ShippingMemKid.Kid`. A breadth-first walk from the root's TYPE with a visited set, recording for every hit the
   full path root → … → name. Unfolding targets (LOGICAL): definitions whose type ends in `Prop` (predicates) or in a
   sort (type formers, e.g. `abbrev Pkgs`); definitions whose type ends in a class (instances, e.g. behind `∈`); every
   inductive reached — Prop structures (their fields' types via the constructor type, with the parameters), Prop
   inductives (constructor types), and data structures/inductives too (conservative); constructors → their inductive.
   Boundaries: a definition whose type ends in neither a sort nor a class is COMPUTATIONAL — not unfolded logically; its
   body is scanned depth/fuel-bounded. A forbidden name found there is classified by the boundary definition reached on
   the logical path (rev3, review R1): Bool-valued ⇒ BOOLCHECK (a Bool check the premise requires: `f x = true`,
   `decide`, a data row) — counted like a logical hit, a `STOP` for the copies; any other result type ⇒ UNCLASSIFIED
   (needs review; neither pure computation nor absence). Not scanned (depth cut, fuel exhausted, opaque inside a body) ⇒
   UNEXPLORED, printed with path. `opaque` / `partial` / `axiom` / missing / Prop-level `extern`/`implemented_by`
   constants on the logical path are UNCHECKED boundaries, printed, never counted as absence. Theorems (proof terms),
   quotient primitives and recursors met in a type are SKIPPED, every one printed with reason and path (review R2).
   Output per root: LOGICAL and BOOLCHECK hits (must be EMPTY for the 14 copies, else `throwError "STOP: …"`),
   UNCLASSIFIED hits, UNCHECKED, UNEXPLORED, SKIPPED, the count of logical constants unfolded. A visit cap aborts with
   "absence NOT established" rather than passing. LOGICAL 0 / BOOLCHECK 0 is not used to mean that the premises carry no
   name condition.
   Fixtures (the check fails if one is not detected): a hidden ≥2-level fixture `fxRoot (h : Fx3)` with
   `structure Fx3 : Prop where h : Fx2`, `def Fx2 : Prop := Fx1`, `def Fx1 : Prop := ∀ c, memChild? c = none` — detected
   with path fxRoot → Fx3 → Fx2 → Fx1 → memChild?; a direct one-level fixture; NEGATIVE Bool-check fixtures
   `fxCompRoot (h : fxComp a = true)` and `fxComp2Root` (one Bool wrapper deeper), both detected as BOOLCHECK; a non-Bool
   computational fixture `fxNatRoot (h : fxNat a ≤ 7)` reported as UNCLASSIFIED; an opaque Prop (an unchecked
   boundary). Positive control: the ORIGINAL `oneOutWidthAt` has a logical hit via `hnomem`.
   (ii) only `oneOutWidthAtO`/`oneOut_topShipsO` mention `InstOrigin.child?` in a binder (`hord`);
   (iii) `#print axioms` of the 14 copies and the controls = [propext, Classical.choice, Quot.sound]. (Pattern:
   Tests/Compiler/Srm20AuditTest.lean, Tests/Compiler/ChildVertAuditTest.lean.)

## 6 Not claimed

- Accepted (limited) only as removal/replacement of the enumerated premise in the 14 theorems; no claim of overall strictness or minimality.
- Not claimed: that the row (G-DATA, P-MEM-1) holds for every successful compilation; coverage stays open.
- Not claimed: an end-to-end shipping result for `collPlainCD` or any other collision parent.
- Not claimed: anything about memory parents (`instFields ≠ []`), the group closing, or `core_*` theorems outside the
  OneOutTop chain (e.g. `core_closed_typedIn_ranA`, `core_designCheckHA`, the `Kid`-based `core_*M` chains).
- The transitive unfolding of premises other than `hnomem` was not done by reading; §5 c is the planned check.

## 7 Implementation (built at 0efea824, g2pm4-0efea824; audit revised in rev3)

Written on par/gen2-spec cd026658, committed and built at 0efea824 (exit 0, 14 TYPE OK, standard axioms). Copies generated from the originals'
lines by a script (verbatim except the listed changes; the per-file diff against the original shows only those).

| file | declarations |
|---|---|
| `Tools/ShippingParentTailsO.lean` (ns `Tools.ShippingParentTailsO`) | `core_bodyEq_ranO`, `core_linkedWF_ranO`, `core_instOuts_not_assigned_ranO` |
| `Tools/ShippingParentDesignO.lean` (ns `Tools.ShippingParentDesignO`) | `core_hierGate_anyO`, `core_kidsComb_raw₁O`, `core_instNames₁O`, `core_noSelfRead₁O`, `core_outsExtracted₁O`, `core_rst_anyO`, `core_runFactsHO` |
| `Tools/ShippingGen2OneOutTopO.lean` (ns `Tools.ShippingGen2`, as the originals) | `core_callPorts_oneO`, `core_instOutWidthsOk_oneO`, `oneOutWidthAtO`, `oneOut_topShipsO` |
| `Tests/Gen2/PMem4Check.lean` (ns `Tests.Gen2.PMem4Check`) | expected-type check (14 pairs), `pmAuditRoot` + fixtures `Fx1`/`Fx2`/`Fx3`/`fxRoot`/`fxDirect`/`fxComp`/`fxCompRoot`/`FxOp`/`fxOpRoot`, controls `collPlainCD_hord`, `memShape0P`/`memShape0P_hord_false`, `oneOut_topShipsO_of_row`, `#print axioms` |
| `lakefile.lean` | four `lean_lib` entries appended at the end |

`hord` (both top copies, at the position of `hnomem`):
`∀ (k : Nat) (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none`.
`core_bodyEq_ranO` keeps the proof of `core_kids_facts_ranA` up to `hbout` (TailsA:68-148) and ends with `exact hbody'`.
The test imports Tests.Compiler.MemNameCollisionPlainCertTest (for `collPlainCD_D`); `memShape0` is restated as
`memShape0P` (Tests/Gen2/DataBridgeCheck.lean is not imported).
