# S4 P-MEM freeze: is a memory-origin entry excluded from a one-output closing? (design only)

Branch `par/gen2-spec` at e1fd0d0e. Read-only research. Line numbers are at e1fd0d0e.
rev2 (reviewer decisions applied): `hord_of_row` restricted to `k < insts.length`; the name half of `hnomem` recorded as a
separate supplier obligation (§4.2); `MemFlag` marked an UNPROVED plan; route (3) recorded as an insufficient-evidence
finding (not a formal refutation); the row is an extra premise, not "no new semantic premise". The row and `hord_of_row`
are now written and BUILT at 5d6ca626 (kjob g2db-5d6ca626: exit 0, 749 jobs, head=base=source=end, no sorry, all 22 roots standard axioms; reviewer accepted the Lean as supplier-local) in Tools/ShippingGen2DataBridge.lean with controls in Tests/Gen2/DataBridgeCheck.lean (§4.1).
Question (S4_CONSUMER_FREEZE.md §7, probe P-MEM, :591-617):
```lean
oneOut_noMem : shape.instFields = [] → ∀ k, (shape.instOrigins.getD k .ord).child? = none
```

## 1. Answer
- **By the source text: yes.** The reader excludes memory-origin entries when `instFields = []`. The closing does not.
- **In the kernel, from the run (`MachineDefines`): not supplied today.** The fuel route proposed in this survey (§3) needs O1/O2, which are currently unsupplied; the general statement STOPS there. This is a limit of that route as surveyed, not an impossibility claim for every route.
- **Supplier-local route:** a decided per-declaration data row (§4). The row is still an EXTRA premise of whoever uses
  it (under an abstract package nothing decides it); a fuel-candidate plan (§3.2, UNPROVED) would be its G-DATA coverage
  argument, modulo O1/O2. Coverage is tracked separately; FG is not narrowed.
- **Route (3), "the run gives the exclusion through `instStmt`": insufficient evidence.** The source reading of §2 finds
  no path by which the run excludes a memory-origin entry; this is a finding about the code read, NOT a formal
  refutation over all successful `MachineDefines` (no counterexample run is exhibited).

## 2. Route (3): the run itself (insufficient evidence; not a formal refutation)
- `closeInstsM` (Sparkle/Compiler/Elab.lean:5206-5218) computes `children ← shape.insts.mapM fun (c, _, _) => synth c`
  (:5211). It calls `synth` of the entry NAME for every entry and never reads `instOrigins`. Only `closeInstsGM` (:5229-5243)
  dispatches on `o.child?` (:5235-5238).
- `synth` is `synthesizeChild` (Elab.lean:8928-8934, set at :8934; ref declared at :1040-1042). Its type is
  `Name → MetaM (Module × Design)`, and it compiles the DECLARATION named `c`. It never calls `memModule`.
- So for a `.mem combo aw dw` entry on this path, `c = memChildName combo aw dw` (MachMemory.lean:42-44). The served
  result is the compile of a declaration with that name, if one exists. Such declarations exist in the test corpus
  (Tests/Compiler/MemNameCollision*Test.lean, e.g. MemNameCollisionPlainCertTest.lean:40-49; MachInstOrigin.lean:5-12).
  That compile can be combinational (no clk), so `instStmt`'s clk/rst refusal (Sparkle/IR/Machine.lean:278) does not fire.
  If no such declaration exists, `synthesizeCombinational` fails as a MetaM exception, not as `none`.
- `memModule`'s `clk`/`rst` inputs (MachMemory.lean:52-56) are therefore irrelevant on this path.
- **Conclusion:** on this reading, route (3) would need an environment premise, "no declaration carries a placeholder
  name, or its compile has clk". That is a new semantic premise, so the route is not pursued. This is an
  insufficient-evidence finding: no theorem says the run CANNOT exclude such entries, and none is claimed.

## 3. Route (1): a reader invariant

### 3.1 The source facts (production reader)
- `instStruct` has its default `false` (Elab.lean:3585). It is written only with `:= true`, at three places:
  - :3960, the memory arm, right AFTER `machInstance … (.mem combo aw dw)` returns (:3958-3959);
  - :4058, a Bool result;
  - :4125, a structure call.
- `instOrigins` is written only at two places:
  - :4080, by `push org` in `machInstance`, together with `instFields.push "out"` at :4079;
  - :4126, `.field i`, together with `instStruct := true` at :4125.
- The arm at :3947 passes `.ord`. Only :3958 passes `.mem`.
- Shape: `instFields := if st.instStruct then st.instFields.toList else []` (:5196), `instOrigins := st.instOrigins.toList`
  (:5197).
- Hence, on every final state, a `.mem` tag implies `instStruct = true`, which implies `instFields = st.instFields.toList`.
  That list is non-empty, because each push of a tag pushes a field (:4079-4080).

### 3.2 What exists on the fuel candidate `machineShapeF` (Tools/ShippingReaderFuelShape.lean:256-259)
- `InstProv` (Tools/ShippingReaderFuelProv.lean:167-172) gives, per tag, `OriginT` (:149-153).
  - The `.field i` arm carries `b = true` (`instStruct`).
  - The `.mem` arm does NOT: `MemOriginI … ∧ nm = "out"` (:153).
- So `machineShapeF_originT` (Tools/ShippingReaderFuelShapeProv.lean:266) allows `nm? = none` for a `.mem` tag (:222). It
  does not give `oneOut_noMem`. **Missing.**
- Why it is missing: in the fuel reader, the memory arm also sets the flag only after `cInst` returns
  (Tools/ShippingReaderFuelDefs.lean:342-345). The intermediate state is the output of `Call.inst … (.mem …)`, which has a
  `.mem` tag with the flag unchanged (`instProv_push`'s `hb : st'.instStruct = st.instStruct`, ShippingReaderFuelProv.lean:271).
  A plain "mem tag ⇒ flag" state invariant is therefore not kept by `GoodP` (:471-473) as stated.

Needed (all MISSING; an UNPROVED plan — the statements below have not been elaborated, and the arm-by-arm
argument is a sketch, not a proof; intended skeleton: the fuel induction of ShippingReaderFuelProv.lean):
```lean
def MemFlag (st : MachRead) : Prop :=
  ∀ o ∈ st.instOrigins.toList, o.child?.isSome = true → st.instStruct = true
/-- per-call post: the `.mem` inst call alone may break `MemFlag` (its caller restores it) -/
def Call.isMemInst : Call → Bool          -- `.inst _ _ (.mem ..) ..` ↦ true
def GoodPM (senv : StructEnv) (h : Hs) : Prop :=
  ∀ c, CallPreP senv c → InstProv senv (Call.inSt c) → MemFlag (Call.inSt c) →
    ∀ v, h c = some (some v) →
      InstProv senv (Call.outSt c v) ∧ (c.isMemInst = false → MemFlag (Call.outSt c v))
theorem machineShapeF_final_memFlag (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∃ p m st v, InstProv senv st ∧ MemFlag st ∧ shapePost ai p m st v = some sp
theorem machineShapeF_oneOut_noMem (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hf : sp.instFields = []) : ∀ k, (sp.instOrigins.getD k .ord).child? = none
```

Proof sketch of the last theorem:
- Use `shapePost_instFields` (ShapeProv.lean:64), `shapePost_insts`, and `shapePost_instOrigins`
  (Tools/ShippingReaderFuelShapeR5.lean:343).
- Case `instStruct = true`: `st.instFields.toList = []`. The two size conjuncts of `InstProv` then make `instOrigins` empty,
  so `getD` gives `.ord`, and `child? .ord = none` (MachInstOrigin.lean:28-30).
- Case `instStruct = false`: `MemFlag` gives `child? = none` for every stored tag. Past the end, `getD` gives `.ord`.
- Arm obligations:
  - the `.ord` push keeps `MemFlag` (`child? .ord = none`);
  - the `.mem` arm restores it with the flag `:= true`;
  - `instEntry` and the `.field` append set or keep the flag (cf. `instEntry_prov`, ShippingReaderFuelProv.lean:642);
  - `machReserve` does not touch the fields (ShapeProv.lean header :25-30).

**STOP (general statement).** This theorem is about `machineShapeF` only.
- `MachineDefines` (Tools/ShippingMachineEntry.lean:2345-2357) states `machineShape? … = some shape` of the PRODUCTION
  reader. Its readers are `partial` (`machInstance`, Elab.lean:4049), so they are opaque to the kernel.
- The existing agreement runs in the other direction: fuel success ⇒ old (`readF_agree_old` …,
  Tools/ShippingReaderFuelOldEq.lean:985-1001), under `OldEq`.
- The needed direction, old success ⇒ some fuel, is O1. That the compiled partials satisfy `OldEqV`
  (Tools/ShippingReaderFuelVerbatim.lean:490) is O2. Both are outside the kernel (docs/parallel/R-reader-fuel.md:37-43,
  :448-449, :552-555).
- Along this fuel route, a kernel proof of `oneOut_noMem` from `MachineDefines` alone is therefore not available today
  (O1/O2 unsupplied). Adding O1/O2 would be a new semantic premise. Other routes are not ruled out.

## 4. Route (2): a decided per-declaration data row (recommended)
- `p.d` is the literal `<f>.machineData` that the generator emits from the meta-time reader run
  (Tools/ShippingMachineCommand.lean:2513-2522). The kernel decides any Bool row on it.
- The tie of the data to the run is the EXISTING `MachineDefines … p.decl p.d.shape` premise of `StepStmt`
  (Tools/ShippingGen2Defs.lean:300-308). The row is nevertheless an EXTRA premise of its consumer: it is decided only on
  concrete data, so under an abstract package it stays a hypothesis, and that every successful compilation passes it is
  the separate coverage obligation of §4.3.
- Existing analogue, `hnomem` with both halves, appears in:
  - Tools/ShippingOneOutKidDepth.lean:62;
  - Tools/ShippingLinkedFresh.lean:175;
  - the origin-half variant `hnomemO`, Tools/ShippingCallsGateA.lean:72.
- `hnomem` is decided for real parents:
  - `callerL_nomem` (Tests/Compiler/OneOutCallerLTest.lean:251-252, `by decide`);
  - `callerLN_nomem` (OneOutCallerLNTest.lean:112);
  - `topshareM_nomem` (Srm4ParentTest.lean:57, `decide | decide +kernel`).
- `caller` (Tests/Compiler/ShippingMachineInstTest.lean:38, endpoint :152) has NO such theorem yet. The row is MISSING
  there. The expected proof is `by decide` on `caller.machineData` as for callerL, but it was not run.

Proposed stage-C row. It is the IMPLICATION form, so it does not exclude memory parents (they have `instFields ≠ []`):
```lean
-- conjunct of DataOkB (Tools/ShippingGen2Data.lean:17-21); class D, coverage G-DATA (GENERAL_SPEC.md:383-394)
p.d.shape.instFields.isEmpty → p.d.shape.instTagged.all (fun x => x.2.child?.isNone)
-- as Bool:  (!p.d.shape.instFields.isEmpty || p.d.shape.instTagged.all (fun x => x.2.child?.isNone))
theorem hord_of_row (h : OneOutNoMemRow p = true) (hf : p.d.shape.instFields = []) (k : Nat)
    (hk : k < p.d.shape.insts.length) :
    (p.d.shape.instOrigins.getD k .ord).child? = none
```
- **Range (rev2).** `instTagged` (Elab.lean:5223-5225) zips `insts`, so it covers exactly `insts`' range. A shape with
  extra `instOrigins` beyond `insts` can pass the row and still have a memory origin at `k ≥ insts.length`
  (control `memShapeX_row` / `memShapeX_outOfRange`). So the conclusion is claimed only for `k < insts.length`, the range
  every consumer indexes (`OneOutWidth`, `nomem_tag` at OneOutTop:307 take the same `hk`). No `instOrigins.length` premise
  is added.
- **Proof:** `notag_at` (Tools/ShippingChildInv.lean:544-547) after `List.all_eq_true` on the row's right disjunct.
- **Missing:**
  - the row in `DataOkB` (NOT added: shared definitions unchanged; before adding it, the revision table of
    S4_WID_SUPPLY.md §4.1 applies: old ↔ new implications, every downstream user, supply unit, final-FG obligation);
  - the generator's `decide` per declaration (and `caller`'s instance).

### 4.1 Implementation (rev2, BUILT at 5d6ca626, g2db-5d6ca626)
- Tools/ShippingGen2DataBridge.lean: `noMemRowS` (:33), `OneOutNoMemRow` (:37, standalone, the Bool form above),
  `OneOutNoMemRow_eq` (:40), `hord_of_rowS` (:43), `hord_of_row` (:57). No shared definition is edited.
- Tests/Gen2/DataBridgeCheck.lean: `callerL_row` (decided), `callerL_hord` (every package with `callerL`'s data;
  no `callerL` package exists), negative `memShape0_row` (memory origin, no fields: row false), implication-form
  `memShape1_row` (memory parent passes), out-of-range `memShapeX_row` + `memShapeX_outOfRange`. The memory controls are
  SYNTHETIC shapes (not compiled declarations); `callerL` is a data-level positive with no parent package exhibited.
- Supplier-local result: FG is not narrowed; coverage is tracked separately (§4.3).
- Then `memDec_vacuous_of_ord` (S4_CONSUMER_FREEZE.md:610-613, a candidate) applies per `k`. That removes `hnomem`'s origin
  half as a case restriction for one-output parents.
- The NAME half (`memChild? x.1 = none`) is NOT implied and must not be in this row. It excludes legitimate ordinary
  callees with placeholder names: `collPlainCD_nomem_false`, MemNameCollisionPlainCertTest.lean:177-178.

### 4.2 Separate supplier obligation: removing the existing `core_*` name condition
The row removes only `hnomem`'s ORIGIN half. The existing run lemmas still take both halves: `core_callPorts_oneA`
(Tools/ShippingGen2OneOutTop.lean:61), `core_instOutWidthsOk_oneA` (:212-213), and through them
`Tools.ShippingParentTailsA.core_kids_facts_ranA` (used at OneOutTop:76, :232). Removing the name half there is a SEPARATE
obligation of the supplier, not implied by this row: those `core_*` proofs (or origin-keyed copies of them) must use the
origin (`child? = none` ⇒ `synthesizeChild c` is served, cf. the origin dispatch of `closeInstsGM`, Elab.lean:5235-5238)
instead of `memChild? c = none` (the name route of `Tools/ShippingKid.lean:157, :221, :253`). Until that is done, a
consumer of `hord_of_row` still needs the name half as a case restriction for one-output parents. Not started.

### 4.3 Coverage (separate)
The row's G-DATA coverage argument would be §3.2's `machineShapeF_oneOut_noMem` (UNPROVED plan) plus O1/O2. That is a
coverage obligation in the class-D sense, not a premise of FG, and it is tracked separately. Per-declaration `decide`
(or generator emission) is evidence for the declarations decided, not an all-source success guarantee.

## 5. Stops
- **P-MEM-1 (general, kernel):** along the fuel route proposed here, `MachineDefines` ⇒ `oneOut_noMem` needs O1+O2, which
  are currently unsupplied; so the general statement is not claimed. Not an impossibility claim for all routes.
- **P-MEM-2 (fuel candidate):** `MemFlag` / `GoodPM` / `machineShapeF_oneOut_noMem` are an UNPROVED plan (missing; the
  intended proof copies the Prov induction with a per-call post). Not built, not elaborated.
- **P-MEM-3 (data row):** the row and `hord_of_row` are written and built (g2db-5d6ca626) in Tools/ShippingGen2DataBridge.lean
  (`OneOutNoMemRow`, `hord_of_row` with `hk : k < insts.length`). Missing: the `DataOkB` conjunct (not added; shared
  definitions unchanged), the generator's emission, `caller`'s decided instance. G-DATA coverage stays open (P-MEM-1).
- **P-MEM-4 (name half):** removing the existing `core_*` name condition (`memChild? x.1 = none`) is a separate supplier
  obligation (§4.2), not implied by the row.
- **Route (3)** is not pursued (insufficient evidence, §2). No consumer should cite `instStmt`'s clk refusal as the
  exclusion.
