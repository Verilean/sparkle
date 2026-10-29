# M4 lead: route census and the first independent route unit — freeze rev2 (FOR RE-REVIEW; rev1 48704c38 changes_requested, fixes (1)-(5))

- **Issue:** `sparkle-gen4-routes`.
- **Plan:** LEAD_UNITS_PLAN.md (cf029631).
- **Status:** read-only survey, no Lean. All file:line references are at par/gen2-spec cf029631.

## 1. Dispatch, fallback, cache and entry modes (dispatch `synthesizeFromConst`, Sparkle/Compiler/Elab.lean:5288-5414; constant from `entryConst` :5271-5282)

**These rows are NOT eight exclusive success paths** (review (1)). They overlap:
- Row 4 is a TRANSITION into the fallback rows 5/6, not a route with its own result.
- Row 8 is a cache; a child-cache MISS runs the full entry, i.e. one of rows 1-6.
- Row 7 is an entry mode: symbolic mode, whose top is row 6.
- Row 3m is part of row 3.
| # | route | condition / function | soundness family today |
|---|---|---|---|
| 1 | first gate | `certifiedShape? = some` (:5292), `synthesizeCertified` (:2934); off in symbolic mode or with parameters (:2319) | top: `synthesizeCombinationalCore_sound` / `CertifiedOutcome` (EntrySoundness:1117). Child facts (FirstGateChild*, FirstGateKid*) are marked WRITTEN, NOT BUILT |
| 2 | mixed gate (also instance roots) | `mixedCertifiedShape? = some` (:5299), `synthesizeMixedCertified` (:2959) | `GateDefines` (GateDefines:72). Leaf child: `gate_child_fullG` → `ChildFn` (EntryReadsLinked:345), `childFull_of_realA` (CallsGateA:48), `gateChild_ifaceP_of_real` (GateChildIfaceP:174). Gate parents: `gate_parent_run` (GateParentRun:191) on the old `RefLaws`; the G-variants are NOT BUILT |
| 3 | machine | `machineShape? = some` and `synthesizeMachineCertified = some` (:5252-5313) | `MachineTaken`, `machine_ships_hierC_noHstR`, `machine_linkedT_callsServed`, the gen2 `Pkg`/`ChildShips`/`TopShips` |
| 3m | memory child inside route 3 | `closeInstsGM`, `o.child? = some md` (:5236-5239) | `MemDec`/`MemFacts` |
| 4 | machine read, synthesis refused (a TRANSITION, not a result) | `closeLets = none` (:5263), or `closeInsts*M = none` (:5209, :5234); continues to row 5/6 | only excluded by `MachineClosesAtA` (`T1Hyp.closes`) |
| 5 | memo `sparkleSubModuleCache` | not symbolic, and cached (:5334-5338) | `MemoInv`/`KeepsMemo`/`MemoSound` (MemoInv:44, :130, :209); G-MEMO open |
| 6 | legacy | other `defnInfo` (:5340-5412) | `legacy_translate_contract` (LegacySemContract:264, :327): a CONTRACT only (gap G2) |
| 7 | parametric | `synthesizeCombinationalWithParameters` (:8940), symbolic mode | none found. The top is always route 6; its children go through `synthesizeChild` and can take any route |
| 8 | child cache (`synthesizeChild`) | hit returns the cached result (:8929-8933); a MISS runs the full entry (rows 1-6) and inserts | `RealChildA`/`CacheInvA`, `CacheShips` |

Every non-memory child, whatever the parent's route, is a route-8 result of the full entry (`childSynthEntry`, :8706-8730).

## 2. What the current interface (`Pkg`, A-COMB `ChildShips`, `TopShips`, `T1Hyp`) can express
- **Expressible:** route 3, 3m (through `MemDec`) and 8, for reached machine names.
- **Not expressible:**
  - **Routes 1 and 2** have no `MachineData`/`GenFacts`.
    - `T1Hyp.defines` (Defs:192) requires `MachineDefines`, which requires `certifiedShape? = none ∧ mixedCertifiedShape? = none` (MachineEntry:2345-2357).
    - `T1Hyp.closed` (:203-205) puts every non-memory callee into `Reach`. So under the current `T1Hyp`, a machine parent with a gate child cannot satisfy the hypotheses.
    - **FG is not narrowed by this.** T1 is the M3 deliverable and is explicitly not FG. The coverage obligation is M4.
    - A gate LEAF child meeting `childFull_of_realA`'s premises (`mixedGatePeel value = some (bs, quote …)`, the `quote` form) has one output `"out"`, an assignment-only body and an empty design (`ChildFull`, GateChildComb:165-170). Its interface is then `CombChildRunN` with `outsC = [out]`. This does NOT cover route-2 gate parents with instances (`unifiedInstanceRoot`), whose shape is outside those premises (review (2)).
  - **Route 4** results are route 5/6 modules; `T1Hyp.closes` removes them from `Reach`.
  - **Route 5** needs a `MemoInv` with a ships-like `Φ`, and so a package for every route that writes the memo (1, 2, 3, 6).
  - **Routes 6 and 7** have no trace and no package; there is a contract only.

## 3. Blocking order for FG (earliest first)
1. Route 2 gate leaf children of machine parents (the G-ONEOUT parents).
   - **No producer:** nothing supplies `ChildShips` for these children.
   - **The consumer side is not finished either** (review (4)). The pure bridges `childFn_of_combRun`/`combS_pointwise` are BUILT (Tools/ShippingGen2CombKid.lean, 1df67a82). The served one-output consumer (a `machine_linked_callsRA` variant fed from `Served1P (ShipsRes …)`) is PLANNED, not written.
2. Route 1 children: the same consumer; the child facts are NOT BUILT.
3. Route 6 (and route 4 into it): a contract only, which is M4's risk clause.
4. Route 5 (memo): after 1-3.
5. Gate tops (routes 1/2 `TopShips`).
6. Gate parents with instances (old `RefLaws`; G-variants NOT BUILT).
7. Route 7 (parametric).

## 4. Interface finding for M2 (G-ONEOUT; to be checked in the kernel)
- **The rule.** `CallDec` (Defs:102) requires a callee output `o` with `o.name = p.d.shape.instFields.getD k ""`. For a one-output parent (`instFields = []`) that is `""`.
- **What `instStmt` enforces** (Machine.lean:272-287): the callee has exactly ONE output (`let [outP] := mc.outputs`). It does NOT force that output's name (review (3)).
- **The potential mismatch.** It arises whenever the callee's single output name is not `""`. In particular, a gate leaf child's output is `"out"` (`ChildFull`). For a machine-route one-output child, the name is the layout's single out field name.
- **The probe (kernel), in the S4 consumer unit, before `CallDec` is used for one-output parents:**
  - take a real G-ONEOUT parent from the corpus: a machine parent whose calls go through `closeInsts` (`instFields = []`);
  - evaluate `instFields`, the callee's `layout.outs` names / the gate child's `"out"`, and whether `CallDec`'s name conjunct can hold;
  - report the decided Booleans.
- **If the mismatch is confirmed:** a reviewed `CallDec` amendment, either "the callee's single output" for one-output parents or a separate one-output decoding.

## 5. First independent route unit (proposal): gate leaf child → `CombChildRunN`
It is run level, with no `Pkg` change.
```lean
noncomputable def gateS (bs : List (Name × MixedGateBinder)) {srt : SType} (e : Term srt)
    (bpos vpos : Nat → Nat) : (Nat → List Nat) → List (Nat → Nat) :=
  fun vals => [fun τ => (pack srt (eval (fun j => decB bs (vals τ) (bpos j))
                                    (fun j w => decV bs (vals τ) (vpos j) w) e)).toNat]

theorem gate_combChildRunN (O : RefLawsAOps MkRefd mref cref) {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)} {kb kv : Nat} {vw bpos vpos : Nat → Nat}
    {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChildA O c y) :
    y.2.modules = [] ∧ ∃ o : OutField, o.name = "out" ∧ y.1.outputs = [{ name := o.name, ty := o.ty }] ∧
      ∀ (dsn : Design) (n : Nat),
        CombChildRunN (childMap dsn.modules) dsn n y.1 bs [o] (gateS bs e bpos vpos)
```
- **Its premises** are those of the existing `childFull_of_realA` / `#gate_child`.
- **Suppliers:**
  - `childFull_of_realA` (CallsGateA:48): assigns, `readsClosedB`, the `out` output, distinct allocated inputs, port types, `modules = []`;
  - `not_alloc_clk`/`not_alloc_rst`/`not_alloc_out` (GateChildIfaceP:78-90);
  - `ChildFull.tys` + `inPortsOf_of_alloc` (:98), for the `argPorts` length;
  - `RealChildA.run` + `gate_child_fullG` (EntryReadsLinked:345): `ChildFn` at `env "rst" = 0`;
  - S1 `runModule_seed_local` (Gen2Comb:28): reset is irrelevant (`"rst"` ∉ inputs, closed);
  - `runModule_assigns_total` (GateDesign:92), `RunOn_instFree`, `instFree_of_assigns`: run existence at every `T` and `n`.
- **Acceptance:**
  - **a concrete instance, with premises separated** (review (5)):
    - SUPPLIED for the concrete gate leaf: `entry`/`old`/`peel`/`he`/`hb`/`hv` (as in the existing `#gate_child` tests) and `gateS … ≠ []`;
    - REMAINING hypotheses: `RealChildA O c y` (a past run); no run existence is claimed;
    - `gateS ≠ []` alone is not run-level non-vacuity. If run existence is ever claimed, its evidence (a concrete `RealChildA` from a proved run) is required;
  - a round trip with `childFn_of_combRun` (S4-b) that recovers the same function;
  - standard axioms.
- **Not covered:**
  - a `Pkg` constructor or re-keying `ChildShips`/`CallDec` on an interface record (the follow-on unit, after §4);
  - a route-indexed `T1Hyp`;
  - `ShipsRes`/`CacheShips` for gate names;
  - route-1 children, gate tops, gate parents with instances;
  - repeated callees (`hnodup` in `callsPureA_of_gateKids`, CallsGateA:65);
  - routes 4-7.
- **The plan change it implies (UNAPPLIED proposal, together with M3).** A route-indexed `T1Hyp`: `Reach`, `defines` and `closed` per route, so that gate children are reached without `MachineDefines`.
  - **The intended design:** extend the induction with ONE common semantic child interface (the A-COMB `ChildShips` data `(bsC, outsC, S)` and `ShipsRes`) and route-specific PRODUCERS (machine: `Pkg` + `StepStmt`/`LeafStmt'`; gate leaf: `gate_combChildRunN`; later others).
  - **Consumers stay route-agnostic.** The M3 freeze (`sparkle-gen3-induct`) is to be aligned with this.
  - **Status:** an amendment, reviewed before use.
