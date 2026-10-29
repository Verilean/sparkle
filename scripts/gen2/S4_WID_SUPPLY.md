# S4-WID: supplying `hW : ∀ k, OneOutWidth P p k` (coverage obligation G-ONEOUT-WID), read-only plan

Base: `par/gen2-spec` at e1fd0d0e. Every lemma below is UNBUILT.
rev2 (reviewer decisions applied): (b)'s `oneOutWidth_of_strict` and the b1 `kidOutsP` agreement lemma are now WRITTEN
(UNBUILT) in Tools/ShippingGen2DataBridge.lean, controls in Tests/Gen2/DataBridgeCheck.lean (§3 (b), "Implementation");
(c) reworded (not supplied by existing exports; bridges unproved; no compiler guard now); b2's `MachineDefines.shape_eq`
conditions made explicit; generalisation claims withdrawn; §4 gives the REVISION TABLE required before any shared
`T1Hyp`/`DataOkB` strengthening. FG is NOT narrowed; the data bridge is a supplier-local result; coverage is tracked
separately.

## 0. The premise and its two consumers
`OneOutWidth` (Tools/ShippingGen2FitChain.lean:893-896):
```lean
def OneOutWidth (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length) (q : Pkg ι dom), P (p.d.shape.insts[k]).1 = some q →
    ∀ o : OutField, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth
```
It is used twice:
- `machine_linked_callsServed1F`, to build `CallOutWidths` (FitChain:951-971; the use is at :965).
- `oneOutWidthAt`, to build `RunFacts.wid` (Tools/ShippingGen2OneOutTop.lean:283-345; the use is at :345, consumed at :398-401).

Both consumers already hold THE served child. `ShipsRes` (Tools/ShippingGen2Defs.lean:135-136) starts with `RealChildA L.O c r`. FitChain:944 and OneOutTop:326 currently discard that conjunct.

## 1. Where the two widths come from
**Parent.** `machInstCall?` (Sparkle/Compiler/Elab.lean:3721-3728) looks up `senv.inst c`. Here `senv.inst` is `instSignature? envR'` (`structEnv`, Elab:4394-4397; `envR'` is the env read in `MachineDefines`, Tools/ShippingMachineEntry.lean:2345-2357). `instSignature?` (Elab:4373-4383) returns `res := machResultKind? ci.type` (Elab:4326-4332), which is the result kind of c's DECLARED constant. `machInstance` (Elab:4049-4080) pushes `(c, js, res)`. A `.bool` result sets `instStruct` (Elab:4056-4058), which makes `instFields` non-empty (Elab:5197). So under `hsimple : instFields = []` every entry has a `.bits w` result.

The binder list is `bs ++ instBinders ++ …` (Elab:5181-5185). Therefore the kind of the binder at `bs.length + k` is `insts[k].2.2`. The proved lemma is `machineShape?_callBinder` (Tools/ShippingMachineShapeTail.lean:61-71).

The Lean type of the call term `c args` is never consulted. `machInstCall?` requires `args.length == kinds.length`, and `telescopeKinds` (Elab:4366-4368) accepts only hardware binders. So c has no type parameters and nothing is instantiated. The answer to question (1) is therefore not "the typechecker gives the call term c's result type". It is that **both readers read the same constant's type**.

**Callee.** `MachineDefines c q.d.shape` (T1Hyp.defines, Defs:198-199) is `machineShape?` run on `entryConst … ci` (Entry:2354-2357). The type of that constant is either `ci.type` or `userInliner envR ci.type` (entryConst at Elab:5272-5282; inlinedConst rewrites `type` at Elab:3409-3411). Its outputs are `machTupleKinds?`/`machOuts?` of that type (Elab:5065-5067, 3859-3876). They become `layout.outs = machOutFields W outs` (Elab:5191, 4463-4467) with `ty := machHWType kind` (Elab:4456-4458).

**Proved agreement pieces (real reader, old compiler):**
- P1, `instSignature?_some` (Tools/ShippingInstSignature.lean:18).
- P2, `machOuts?_of_resultKind` (Tools/ShippingReaderResultKind.lean:112-113): the same type expression gives the single output `out` of the same kind.
- `machineShape?_single_out` (ShapeTail:74-80).
- `childLink_realA` (Tools/ShippingChildLinkA.lean:41-48): from `MachineDefines c sc`, `ResDeclAt c res`, `P5At c res` and `RealChildA O c y`, it gives `machineShape? false [] (.defnInfo dE) senv = some sc ∧ machResultKind? dE.type = some res`.
- `kindTy_eq_machHWType` (Tools/ShippingCallWidthsDeclared.lean:67).
- `machResultKind?_ne_domain` (ReaderResultKind:129).

**What is not proved:**
- R1 for the `partial` `machInstance`: the entry carries the signature's kind.
- P5: the production `userInliner` on a type. It is opaque, and is proved only for the candidate `userInlinerC`, `resKind_userInlinerC` (Tools/ShippingInlTypeReads.lean:13-17).
- Env identity between the parent's `envR'` and the callee's `getConstInfo c`.

The file headers already record that no agreement lemma exists and that the condition is "a premise per pair, like `outTy`" (Tools/ShippingCallWidths.lean:17-37; ChildReal.lean:137-155 define `ResDeclAt`/`P5At` as explicit premises).

## 2. Existing width checks, and how each is supplied
| check | file:line | supply |
|---|---|---|
| `callWidthsOk` | CallWidths.lean:51-56 | VACUOUS when `instFields = []` (the name `""`; CallWidthsStrict.lean:3-10). The generator emits only this row (Tools/ShippingSeqParentGenD2.lean:261-263) |
| `callWidthsStrict` / `callWidthsStrict_at` | CallWidthsStrict.lean:37-42 / 45-71 | `decide` per declaration: `callerL_strict` (Tests/Compiler/OneOutCallerLTest.lean:271-278), callerLN (Tests/Compiler/OneOutCallerLNTest.lean:146), hftByte (Tests/Compiler/OneOutHftByteTest.lean:398) |
| `#machine_oneout_any` rows | Tools/ShippingOneOutAnyGenCommand.lean:66-86, 474-496 | `decide` per declaration: `c.leaf_outW` (every layout output has width W) and `f.oneout_entries` (binder at `nDecl+k` has width W), assembled per entry into `hkidW` |
| `callWidthsStrict_realA` | Tools/ShippingCallWidthsChildRealA.lean:67-84 | from `ChildrenRealA`, `MachineDefines`, plus the premises `ResDeclAt`, `P5At` and `PB` (the parent binder is `machHWType res`) |
| `callArgsOkAt` (argument widths, not the result) | Tools/ShippingGen2Adapt.lean:73-77 | `decide` per k (scripts/gen2/UADAPT_RESULT.md:43). The generic supply G-DATA-CALL needs `PortTie`, which has not been found (scripts/gen2/G3GEN_CALL_PLAN.md:65-70, 83-90) |
| `hkidW` (group parents) | Tools/ShippingParentRunFactsA.lean:582-586 | a premise. `hkidW_of_dataA` (:613-) takes `callWidthsOk` (per-declaration data) plus `ChildOutTys`. Not from the run |

Every existing supply is a **per-declaration `decide`**. None of them is derived from the run.

## 3. Options

### (c) Run-local: not supplied by existing exports
`instStmt` (Sparkle/IR/Machine.lean:272-288) checks only that `outW` is a wire by NAME (:283). `closeInsts` (:396-427) has no width conjunct. `instOutWidthsOk` does not occur under `Sparkle/` (grep).

No existing export links the two widths; the bridges that would (`ResDeclAt`, `P5At`, R1 for `machInstance`, env
identity; §1, route (a)) are UNPROVED. This is a statement about what is exported today, not an impossibility claim.
The run gives two facts that nothing exported links:
- `declWidth b outW` equals the binder width (`core_callPorts_oneA`, OneOutTop:47-).
- `mc.outputs = q.layout.outs` as ports (from `ChildShips`, OneOutTop:328-331).

`CallDec`'s equation (Defs:102-114) is value-level: `posEnc` of the binder equals `f τ`. A callee whose output is constantly 0 satisfies it at any parent width, so it cannot force widths. `HPointAt` (Tools/ShippingQuadHPoint.lean:27-38) is the same.

A guard `wireWidth m.wires outW == outP.ty.bitWidth` in `instStmt` would make this a run fact (`wireWidth` is already used at Machine.lean:190). That would be a compiler change (user decision, corpus measurement, re-proofs of `CallStmt`/`closeInsts_insts`). **Reviewer decision: no compiler guard now.**

### (a) Generic, from both reflections: possible as a run-local lemma, but it moves the gap rather than closing it
Proposed lemma (missing; every ingredient exists):
```lean
theorem oneOutWidth_of_realA {mctx : Meta.Context} {cctx : Core.Context}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (P : Pkgs ι dom) (p : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    (hpos : (p.d.shape.binders[p.kD + k]?).map (·.2) = some (p.d.shape.insts[k]).2.2)
    (hDq : ∀ q, P (p.d.shape.insts[k]).1 = some q →
      MachineDefines mctx mref cctx cref (p.d.shape.insts[k]).1 q.d.shape)
    (ResD : Tools.ShippingCallWidthsChildReal.ResDeclAt mref cref (p.d.shape.insts[k]).1 (p.d.shape.insts[k]).2.2)
    (P5 : Tools.ShippingCallWidthsChildReal.P5At mref cref (p.d.shape.insts[k]).1 (p.d.shape.insts[k]).2.2)
    {y : Res} (hy : Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y) :
    OneOutWidth P p k
```
Proof:
1. `childLink_realA (hDq q hq) ResD P5 hy` gives the link and the result kind.
2. `machineShape?_single_out` then gives `q.layout.outs = [{name := "out", …, ty := machHWType r}]`.
3. `hpos`, `kindTy_eq_machHWType` and `machResultKind?_ne_domain` finish it.

Taking ResDeclAt at the parent's RECORDED kind `insts[k].2.2` folds R1 and env identity into one premise.

Supply status of each premise:
- `hpos` is decidable on `p.d` alone, so it is a single-package data row (a `DataOk` conjunct).
- `hDq` is T1Hyp.defines.
- `hy` is in hand at both consumers.
- `ResD` and `P5` are left: an env-stability/reflection premise per callee, and the opaque inliner. Neither is decidable, and P5 is candidate-only.

Using this lemma also means re-threading FitChain:944 and OneOutTop:326 so that they keep the `RealChildA` conjunct. **Recorded as the generic route. It is not a supply today: `ResDeclAt`, `P5At` (and the R1/env-identity content they fold in) are unproved bridges.**

### (b) Per-declaration decidable cross-package row (recommended as a SUPPLIER-LOCAL bridge)
Generalisation limit: the row is decidable only on concrete data and a concrete `P`. Under an abstract `P` (as in FG)
it is still an EXTRA premise; this route does not avoid a new premise and gives no all-source coverage. Per-declaration
`decide` or generator emission is evidence for the declarations decided, not an all-source success guarantee.

Bridge lemma (the proof is `callWidthsStrict_at` with a vacuous name side):
```lean
def kidOutsP (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : List OutField :=
  match (p.d.shape.insts.map (·.1))[k]? with
  | some c => match P c with | some q => q.d.shape.layout.outs | none => []
  | none => []

theorem oneOutWidth_of_strict (P : Pkgs ι dom) (p : Pkg ι dom) (kidOuts : Nat → List OutField)
    (hcw : Tools.ShippingCallWidthsStrict.callWidthsStrict p.d p.kD kidOuts = true)
    (hsimple : p.d.shape.instFields = [])
    (hkid : ∀ k (hk : k < p.d.shape.insts.length) q, P (p.d.shape.insts[k]).1 = some q →
      kidOuts k = q.d.shape.layout.outs) :
    ∀ k, OneOutWidth P p k
```
Proof: `intro k hk q hq o ho`. Then `o ∈ kidOuts k` follows from `hkid` and `ho`. Apply `callWidthsStrict_at hcw hk _ (fun f hf => by simp [hsimple] at hf)`. Note that `nDecl = p.kD` directly, so `closingNDecl_eq_kD` (S4_CONSUMER_FREEZE.md:510-512) is not needed.

There are two ways to discharge `hkid`:
- **(b1)** `kidOuts := kidOutsP P p`. Then `hkid` is `kidOutsP_eq`, and `hcw` is one `decide` against a concrete `P`. Risk: the kernel has to reduce `P c` to a `Pkg` value (control `callerL_strictPL`, untested until built).
- **(b2)** `kidOuts := fun k => [C₀.machineData.shape.layout.outs, …].getD k []`. This is the form of `callerL_strict`. Here `hkid` needs `q.d.shape = Cₖ.machineData.shape`. It comes from D-GEN `Generated` (G3GEN_CALL_PLAN.md:55-60), or from a missing lemma `MachineDefines.shape_eq`. **Name equality alone is insufficient** for that lemma: `MachineDefines` (Tools/ShippingMachineEntry.lean:2345-2357) quantifies over the run's reads, so two shapes agree only when (i) both are stated in the SAME context (`mctx`/`mref`/`cctx`/`cref`), (ii) one read exists (`getConstInfo c` and both `getEnv` runs return; from `RealChildA` via `synthesizeCombinationalCore_reads`, as in ChildLinkA:53-56), and (iii) for comparing with the generator's `Cₖ.machineData`, the meta-time environment, `ci`, `entryConst` arguments (`instancePredicate envR`, `userInliner envR`, `structEnv envR`) and the reader's `structEnv envR'` agree with the run's. (iii) is an environment/read/entryConst condition, not decided by the data, and is unproved.

**Implementation (rev2, UNBUILT; Tools/ShippingGen2DataBridge.lean):** `kidOutsP` (:66, written with `Option.bind`/`getD`, same meaning as the `match` above), `insts_map_fst_getElem?` (:70), the agreement lemma `kidOutsP_eq` (:77), the vacuous case `kidOutsP_none` (:90) and `kidOutsP_allNone` (:103), `callWidthsStrict_empty` (:116), `oneOutWidth_of_strict` (:123, `nDecl = p.kD`) and the b1 instance `oneOutWidth_of_strictP` (:142). Controls (Tests/Gen2/DataBridgeCheck.lean; no `callerL` package exists, so parent controls take `p.d = callerL.machineData`, `p.kD = 1` as premises): positive `callerL_oneOutWidth` (table form) and `callerL_oneOutWidthP` (b1, via `callerL_strictPL`); negative `callerL_strict_bad` + `callerL_bad_width` (16-bit table, row false); vacuous `empty_table_passes` / `oneOutWidth_PN` (`P c = none` ⇒ empty table passes). **Call existence is not given by the row**: with `P c = none` the row is vacuously true; existence is supplied by `hdec`/the supplier (`T1Hyp.dec`).

**Generator work:**
- Emit `@P@.epD2_callWidthsStrict` next to the vacuous row (SeqParentGenD2:261-263), with a per-k table.
- For `#machine_oneout_any` parents, derive the same row from the existing `oneout_entries` and `leaf_outW`, or emit it directly.

## 4. What remains a coverage obligation (no new FG premise added silently)
G-ONEOUT-WID stays a **named, static, relational premise**. It cannot be a `DataOk q` conjunct, because it mentions `P`.

A CONDITIONAL intermediate theorem that takes a `T1Hyp.wid`-style premise is acceptable as a plan. Proposed field, for
review only (NOT applied; shared definitions unchanged):
```lean
  /-- G-ONEOUT-WID: one-output result widths (supplied per declaration by `oneOutWidth_of_strict` + a decided
  `callWidthsStrict` row). -/
  wid : ∀ c, Reach c → ∀ q, P c = some q → q.d.shape.instFields = [] → ∀ k, OneOutWidth P q k
```
**Coverage (tracked separately):** every reached one-output declaration would need the row decided plus `hkid`
(D-GEN identity). That is a generator-emission obligation in the same class as G-DATA. Generator emission or a
per-declaration `decide` is NOT an all-source success guarantee. Declarations whose row fails would be width-mismatched
parents; the source reading (§1) suggests none, but this is neither proved nor measured.

### 4.1 REVISION TABLE (required before strengthening shared `T1Hyp` / `DataOkB`; nothing applied)
| change | old ↔ new | downstream users (every one) | supply unit | final-FG obligation |
|---|---|---|---|---|
| add `T1Hyp.wid` (above) | new `T1Hyp` ⇒ old (forget `wid`); old ⇏ new (`wid` is not derivable from `pkg`/`defines`/`closes`/`dec`/`closed` by any exported lemma, §3 (a)/(c)). So every statement with `T1Hyp` as antecedent gets WEAKER: old `T1Stmt`/`ServedShipsStmt` ⇒ new, not conversely | Tools/ShippingGen2Defs.lean: `T1Hyp` (:194-212), `ServedShipsStmt` (:251-253), `T1Stmt` (:347-349) and its doc (:343-345); scripts/gen2/GEN2_DEFS.lean.txt (cmp-identical copy, must change with it); Tests/Gen2/PkgCompat.lean: `Old.T1Hyp` (:106-109), `T1Stmt`/`ServedShipsStmt` copies (:127-128, :199-200), `t1Hyp_iff` (:332-333: the iff breaks unless `Old.T1Hyp` gets the same field or it becomes one direction), notes :263, :297; docs: GENERAL_SPEC.md, T1_CONNECT_FREEZE.md, STEP_IFACE_FREEZE.md, CALLFIELD_FREEZE.md (they quote `T1Hyp`). No Lean file constructs a `T1Hyp` value today (grep) | the consumers `oneOutWidthAt` (OneOutTop:289-345) / `machine_linked_callsServed1F` (FitChain:903-918) take `hW` from `wid`; per declaration `wid` is supplied by `oneOutWidth_of_strictP` + a decided row (this file) | `wid` MUST NOT remain in the final FG: it has to be discharged from the run (route (a) bridges `ResDeclAt`/`P5At`/R1/env identity, or a later user-decided compiler guard, route (c)) and then removed, restoring old `T1Hyp`. Until then it is listed as an open gap row (G-ONEOUT-WID) |
| add the P-MEM row (S4_PMEM_FREEZE.md §4) to `DataOkB` | new `DataOkB p` ⇒ old (one more `&&` conjunct); old ⇏ new (fails on e.g. `memShape0`-like data). Every `DataOk`-antecedent statement gets weaker | Tools/ShippingGen2Data.lean (:17-23); Tools/ShippingGen2MemData.lean (:20), MemParent.lean (:7, :38, :44), Leaf.lean (:44, :49, :68); every decided instance must re-decide: Tests/Gen2/U0Check.lean:25, LeafInstance.lean:44, SlotlessLeafInstance.lean:36, MemParentInstance.lean:31, CallDecInstance.lean:135, QuantInstance.lean:75; PkgCompat.lean (:208-214 `MemParentDataOkB` copy and the lift lemmas) | `OneOutNoMemRow` / `hord_of_row` (Tools/ShippingGen2DataBridge.lean) | the row's coverage (G-DATA via the UNPROVED `MemFlag` plan + O1/O2) must be discharged, or the conjunct removed, before the final FG; and the name half of `hnomem` is a separate supplier obligation (S4_PMEM_FREEZE.md §4.2) |

Neither change is applied in this round. Both data bridges are kept supplier-local (Tools/ShippingGen2DataBridge.lean),
independent of the shared definitions.

**Stops / open items:**
- Written but UNBUILT: `kidOutsP`, `kidOutsP_eq`, `oneOutWidth_of_strict`, `oneOutWidth_of_strictP` and the controls.
- (b1) `decide` through `P` is untested until the build (`callerL_strictPL`).
- `MachineDefines.shape_eq` (with conditions (i)-(iii) of (b2)) and `oneOutWidth_of_realA` are missing.
- Route (a) still needs `ResDeclAt` and `P5At`, which nothing supplies (unproved bridges).
- Route (c): no compiler guard now (reviewer decision).
- Shared `T1Hyp`/`DataOkB` unchanged; any strengthening goes through §4.1 first.
