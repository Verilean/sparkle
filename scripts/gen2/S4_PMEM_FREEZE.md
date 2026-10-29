# S4 P-MEM freeze: is a memory-origin entry excluded from a one-output closing? (design only)

Branch `par/gen2-spec` at e1fd0d0e. Read-only research. Nothing here is built or proved. Line numbers are at e1fd0d0e.
Question (S4_CONSUMER_FREEZE.md §7, probe P-MEM, :591-617):
```lean
oneOut_noMem : shape.instFields = [] → ∀ k, (shape.instOrigins.getD k .ord).child? = none
```

## 1. Answer
- **By the source text: yes.** The reader excludes memory-origin entries when `instFields = []`. The closing does not.
- **In the kernel, from the run (`MachineDefines`): no route without a new premise.** The general statement STOPS at O1/O2 (§3).
- **Supply route that needs no new semantic premise:** a decided per-declaration data row (§4), plus a fuel-candidate
  lemma (§3.2) that serves as its G-DATA coverage argument, modulo O1/O2.
- **Route (3), "the run refutes it through `instStmt`": FALSE.** It cannot give the exclusion (§2).

## 2. Route (3): the run itself (refuted)
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
- **Conclusion:** route (3) would need an environment premise, "no declaration carries a placeholder name, or its compile
  has clk". That is a new semantic premise, so it is rejected.

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

Needed (all MISSING; same fuel induction skeleton as ShippingReaderFuelProv.lean, copied arm by arm):
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
- A kernel proof of `oneOut_noMem` from `MachineDefines` alone is therefore unavailable. Adding O1/O2 would be a new
  semantic premise.

## 4. Route (2): a decided per-declaration data row (recommended)
- `p.d` is the literal `<f>.machineData` that the generator emits from the meta-time reader run
  (Tools/ShippingMachineCommand.lean:2513-2522). The kernel decides any Bool row on it.
- The tie of the data to the run is the EXISTING `MachineDefines … p.decl p.d.shape` premise of `StepStmt`
  (Tools/ShippingGen2Defs.lean:300-308). No new semantic premise is needed.
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
theorem hord_of_row (hrow : …row… = true) (hf : p.d.shape.instFields = []) :
    ∀ k, (p.d.shape.instOrigins.getD k .ord).child? = none
```
- **Existing pieces:**
  - `notag_at` (Tools/ShippingChildInv.lean:544-547) gives the claim for `k < insts.length`;
  - for `k ≥ length`, the claim holds because `getD` defaults to `.ord`, which needs `instOrigins.length ≤ insts.length` or
    a direct `List.getD` case.
- **Missing:**
  - the row in `DataOkB`;
  - `hord_of_row`;
  - the generator's `decide` per declaration.
- Then `memDec_vacuous_of_ord` (S4_CONSUMER_FREEZE.md:610-613, a candidate) applies per `k`. That removes `hnomem`'s origin
  half as a case restriction for one-output parents.
- The NAME half (`memChild? x.1 = none`) is NOT implied and must not be in this row. It excludes legitimate ordinary
  callees with placeholder names: `collPlainCD_nomem_false`, MemNameCollisionPlainCertTest.lean:177-178.

The row's G-DATA coverage argument is §3.2's `machineShapeF_oneOut_noMem` plus O1/O2. That is a coverage obligation in
the class-D sense, not a premise of FG.

## 5. Stops
- **P-MEM-1 (general, kernel):** `MachineDefines` ⇒ `oneOut_noMem` needs O1+O2. There is no kernel route, so the general
  statement is not claimed.
- **P-MEM-2 (fuel candidate):** `MemFlag` / `GoodPM` / `machineShapeF_oneOut_noMem` are missing but provable. They are a
  copy of the Prov induction with a per-call post. Not built.
- **P-MEM-3 (data row):** the row, `hord_of_row`, and the generator's emission (and `caller`'s decided instance) are
  missing. G-DATA coverage stays open (P-MEM-1).
- **Route (3)** is closed as refuted. No consumer should cite `instStmt`'s clk refusal as the exclusion.
