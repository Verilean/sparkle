# A: the harness shell — `HarnessStill` and `EntryStill` as theorems — round par/a-37

Base: `poc/roundtrip-proof` 3227149c (par/a-36 BUILT and integrated).
Branch `par/a-37`. **NOTHING here was built or run**: WRITTEN, NOT BUILT.
"READ" = read at 3227149c. No built file is modified; `RefLaws` untouched.
The integrator's lessons of the last build are applied: every `WHo.pure`
carries its postcondition (`(Q := fun _ => True)`), and no test evaluates
reflected data in compiled code (kernel `decide` only).

## 0. Result

The two statements par/a-34 left open are theorems for the declarations
concerned:

* `HarnessStill L c bs body` — for a body that is the quotation of a
  well-formed term of the fragment `wfrag` (`harnessStill_frag`);
* `EntryStill L c` — for a machine without calls (`entryStill_leaf`) and
  for a gate child on the mixed route (`entryStill_gate`).

Instances (target-only test): `midH_harnessStill`, `cnt_harnessStill`,
`cnt_entryStill`, `rcH_entryStill`, and **`midH_entryOk_closed`: `EntryOk L
midH (· = rcH)` from the two reflections only**. `rcH`'s gate term needed no
new constructor. `mid2` and the closing of `mixDeep` are NOT written (§4).
No endpoint is connected or narrowed.

## 1. What is written — `Tools/ShippingHarnessStill.lean`

```lean
theorem WHo.throwQ, WHo.ite, WHo.withReader, diagM, addInput_S, addOutput_S
theorem wbound_keep (h : WBound ctx i) : WBound { ctx with varMap := (fv, wire) :: ctx.varMap } i
theorem bindInputPort_S (fv) (bn) (ty) (k) (B) (hB : ∀ i ∈ B, WBound ctx i)
    (hk : ∀ ctx', (∀ i ∈ fv :: B, WBound ctx' i) → WSt … ctx' k) : WSt … ctx (bindInputPort fv bn ty k)
theorem bind_S (k) : ∀ l ctx B, (∀ i ∈ B, WBound ctx i) →
    (∀ ctx', (∀ i ∈ B, WBound ctx' i) → (∀ p ∈ l, p.1.2 ≠ .domain → WBound ctx' p.2) → WSt … ctx' k) →
    WSt … ctx (bindMixedCertifiedInputs k l)
theorem emitLeaves_S (b) (cacheRef) : ∀ leaves fw idx,
    (∀ p ∈ leaves, WSt … ctx (translateExprToWire p.2 p.1 false true)) →
    WSt … ctx (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cacheRef (profLogIO b) leaves fw idx)
theorem finishSynth_world (h : RunsTo (finishSynth declName [] false st) … w r w') : w' = w
theorem bool_pos_of_map, bits_pos_of_map      -- the positions, from the form `MachineData.ok` decides

theorem harnessStill_frag (L) (he : e.WF kb kv vw) (hf : wfrag e = true)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hbody : body = quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e) :
    HarnessStill L declName bs body

theorem machine_leaf_val (L) (hstill : HarnessStill L declName shape.binders shape.body)
    (hno : shape.insts = []) (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hr : RunsTo (synthesizeMachineCertified … (profLogIO b) declName shape) … w r w') : L.val w' = L.val w
theorem entryStill_leaf (L) (hB) (hH) (entry : ∀ mctx cctx, MachineDefines mctx mref cctx cref c shape)
    (closes : ∀ mctx cctx, MachineClosesAt mctx mref cctx cref c shape) (hno : shape.insts = [])
    (hstill : HarnessStill L c shape.binders shape.body) : EntryStill L c

theorem sfc_mixed_val (L) (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hst : HarnessStill L declName bs body) (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hr : RunsTo (synthesizeFromConst … (profLogIO b) declName [] false true ci isInst) … w (m, d) w') :
    L.val w' = L.val w
theorem entryStill_gate (L) (hB) (entry : ∀ mctx cctx, EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, quote dom … e))
    (he : e.WF kb kv vw) (hf : wfrag e = true) (hb) (hv) : EntryStill L c
```

How each piece is obtained (READ, `Sparkle/Compiler/Elab.lean`):

| piece | code | proof |
|---|---|---|
| fresh ids | 2959 `bs.mapM fun _ => mkFreshFVarId` | `mapM_hoare` (BUILT) with `Framed.freshFVar` |
| the translation cache | 2962 `IO.mkRef` | `Framed.mkExprCache` |
| binder walk | 2947–2954; `bindInputPort` 2103–2107; `withVarMapping` 128–131 | `bind_S`: `makeWire`, `addInput`, the reader's map gets `(id, wire)` in front — `lookup_cons_self` / `lookup_cons_ne` (BUILT, `Tools/ShippingEntrySoundness.lean` 245, 249) make every non-domain binder `WBound` inside the continuation |
| leaf emission | 2154–2191 | `emitLeaves_S`: the text of the built `emitLeaves_tripleC` (`Tools/ShippingChildHarness.lean` 204–292), its do-block restated as there; clock `Framed.monoMs`, counters `sideGet`, logger `Diag.profLog`, the cache update `Framed.exprCacheModify`, `addOutput`, `emitAssign` |
| the body | `instFVars ids body` | `instantiated_quote` + `instantiated_input` (BUILT) turn it into the quotation over `.fvar ids[pos]!`; `zip_member` (BUILT) puts each id in the walked list; then `walk_still` |
| `finishSynth` | 2215–2233 | `finishSynth_world`: a `return` or a throw |
| machine without calls | `synthesizeMachineCertified` 5229–5241 | harness, then `pure` (`insts = []`); around it `coreVia_of` (BUILT, par/a-35) |
| gate, mixed route | `synthesizeFromConst` 5277–5282 | log (`Diag.profLog`), harness, memo insert (`SideRef.subModule`), `return`; around it `core_reads_val` (BUILT); the route from `EntryDefines` + `term_gate` (BUILT) as in `gate_child_fullFacts` |

Side conditions: `e.WF`, `wfrag e` (Booleans / decidable), the positions
(`bool_positions` / `bits_positions` for a gate, `bool_pos_of_map` /
`bits_pos_of_map` from the decided form for a machine), `hbody` / `peel`
(the built reflection facts `machine_body` / `gate_peel`), `insts = []`
(`decide`). The route premises are the ones the endpoints carry
(`MachineDefines`, `EntryDefines`) and built closings. No hypothesis about
runs.

## 2. Instances — `Tests/Compiler/CacheChainClosedTest.lean`

```lean
theorem midH_harnessStill (L) : HarnessStill L ``midH midH.machineData.shape.binders midH.machineData.shape.body
theorem cnt_harnessStill (L) : HarnessStill L ``cnt cnt.machineData.shape.binders cnt.machineData.shape.body
theorem cnt_noInsts : cnt.machineData.shape.insts = []
theorem cnt_entryStill (L) (hRc : MachineDefines … ``cnt cnt.machineData.shape) : EntryStill L ``cnt
theorem rcH_frag : wfrag rcH.gateTerm = true
theorem rcH_entryStill (L) (hRr : EntryDefines … ``rcH rcH.gateValue) : EntryStill L ``rcH
theorem midH_entryOk_closed (L) (hRm : MachineDefines … ``midH midH.machineData.shape)
    (hRr : EntryDefines … ``rcH rcH.gateValue) : EntryOk L ``midH (fun k => k = ``rcH)
```

`rcH`'s quotation (`rcH.gateTerm`; source: `Signal.mux (x === 0#8) 1#8
(x + x)`) uses `mux` at bits, `compare`, `bitsLit`, `binary`, one bits
input — all already in `wfrag`: **no constructor was added** (`rcH_frag` is
a kernel `decide`; if it is `false` the file stops there and the missing
constructor is to be read off `rcH.gateTerm`).

The test `#check`s `@midH_entryOk_closed` (the binder list), prints the
axioms of four theorems, and a run command THROWS if the statement of
`midH_entryOk_closed` mentions `HarnessStill`, `EntryStill` or `CoreVia`, or
fails to mention `MachineDefines`, `EntryDefines`, `EntryOk`.

## 3. PROVED (written) vs. NOT shown

| statement | state |
|---|---|
| the shell (`bind_S`, `emitLeaves_S`, `finishSynth_world`), `harnessStill_frag` | PROVED (written), from `RefLaws` and BUILT lemmas |
| `entryStill_leaf`, `entryStill_gate` | PROVED (written) |
| `midH_harnessStill`, `cnt_harnessStill`, `cnt_entryStill`, `rcH_entryStill` | PROVED (written) |
| `midH_entryOk_closed` (no underived hypothesis) | PROVED (written) |
| `EntryOk` of `cnt` | one term (`entryOk_leaf` with `cnt_entryStill` and `cnt`'s child facts on `RealChild`: the name and the empty design — the built leaf facts by name; NOT written) |
| `EntryOk` of `mid2` | NOT written (§4) |
| the closing of `mixDeep` | NOT written (§4) |
| the eleven constructors outside `wfrag`; legacy-route declarations | NOT shown |

## 4. What `mid2` and `mixDeep` still need

`mid2` (callee `midH`, the general closing): `entryOk_machine` with
`mid2_coreVia` (BUILT), `harnessStill_frag` on `mid2`'s packed term (a
`decide` on `wfrag mid2.machineData.packed`, not evaluated here), `hout`
from `hout_of_data` over `mid2`'s data facts (their names are the fields of
`Tests.Compiler.NoPortsTopD2Test.mid2_kid`: `machine_ok`, `machine_body`,
and the `callsOk` / slot / domain facts — I did not read which constants
fill them), `midH_entryOk_closed` weakened to the key set `{midH, rcH}`
(`EntryOk.mono`), and `mid2 ∉ {midH, rcH}`. No new statement is needed —
only terms.

The closing of `mixDeep` (`machine_closes_of_entryOk`) would then have,
besides the reflections of the five declarations: `hS` (the BUILT
`machineClosesAtS_of_kids` instance), `HarnessStill mixDeep`
(`harnessStill_frag`, if its packed term is in the fragment), `EntryOk` of
`mid2`, `midH`, `cnt` over `K = {mid2, midH, rcH, cnt}`, the callee
membership facts — all of the kinds discharged above — and ONE hypothesis
that is not of that kind:

    hp : Prov (L.val w)        -- the cache at the machine synthesis's start world

It holds when the run is OUTERMOST (after the depth-0 clear the cache is
`{}`; `prov_empty`; frame steps to the machine synthesis — the depth-0
sibling of `core_reads_val`, not written). For a NESTED start world it is
not derivable: the endpoint's premise `MachineClosesAt mixDeep` ranges over
every `InvW` world of positive depth, whose cache may hold an entry of
`mid2` and an entry of `midH` that do not agree, and nothing built excludes
it. So the endpoint cannot lose `MachineClosesAt mixDeep` at its present
scope by this route; restricting it to depth-0 starts would narrow it, and
is not done.

## 5. Build queue (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingHarnessStill» where
      roots := #[`Tools.ShippingHarnessStill]

`Tests/AllTests.lean`: nothing (target-only test).

Order: (1) `Tools.ShippingHarnessStill` (imports `Tools.ShippingWalkStill`,
`Tools.ShippingUnifiedExecutionSoundness`); (2)
`Tests.Compiler.CacheChainClosedTest` (imports `CacheChainMidHTest`,
`WalkStillFragTest`, `Tools.ShippingGateChild`).

## 6. UNVERIFIED, in risk order

1. `emitLeaves_S`: the restated do-block (copied from the built proof; it
   must elaborate to the unfolded definition's term again, in another
   namespace with other `open`s — `get`, `throw`, `toMessageData`,
   `Syntax.missing` are written unqualified there too).
2. `bindInputPort_S`: `subst hold` after the reader's read, `dsimp only`
   on the `let newState`, and `WHo.withReader L _ (hk _ ?_)` against
   `withReader (fun _ => newState) k`.
3. `harnessStill_frag`: the `mapM_hoare` step (a tactic block), the two
   `split at hr` / `RunsTo.bind` on the run of the compiler
   (`(compiler.run ctx).run st`), `simpa using hp` for membership in a
   singleton, `rw [hq]` after `show`, the `exfalso` branch (an `error` with
   a placeholder exception against a `throw`).
4. `bind_S`: the four-pattern recursion with the hypothesis functions; the
   `.domain` case (`rw [e] at hne`).
5. `finishSynth_world`: `simp only` then `RunsTo.ite` (the built
   `finishSynth_triple` does the same with `Triple.ite`).
6. `sfc_mixed_val`: three binds and a `pure` (the built
   `synthesizeFromConst_mixed_run` peels the same on `MReturns`).
7. `entryStill_gate`: `term_gate` and `EntryDefines` applied as in
   `gate_child_fullFacts` (BUILT).
8. The test: `decide` on the two position conditions per machine (the
   implicit `kb` / `bpos` come from `machine_body` by unification);
   `cnt.machine_closes mc _ cc _` as a `MachineCloses`; `rcH.gate_old` /
   `gate_peel` / `gate_wf` in the argument forms of `childFull_of_real`;
   `rcH_frag`.

## Integrator's build record (2026-10-13)

BUILT on tree `76b6856ba700bacd9ee98140c70305aea44fc740` (poc 7d8d56b1 + these files), cgrun 3 GiB swap 0, worker's files unchanged, FIRST
ATTEMPT: `a37-shell` (`Tools.ShippingHarnessStill`, exit 0, peak 0.84 GB), `a37-test`
(`Tests.Compiler.CacheChainClosedTest`, target-only, exit 0, 0.31 GB). Printed by the test:
`midH_harnessStill`, `cnt_entryStill`, `rcH_entryStill`, `midH_entryOk_closed` each on
`[propext, Classical.choice, Quot.sound]`; the statement check passed: `midH_entryOk_closed : EntryOk L
midH (· = rcH)` with premises `MachineDefines midH`, `EntryDefines rcH` only — no `HarnessStill`, no
`EntryStill`, no `CoreVia`.

STATE: for the fragment (`wfrag`) and instance-free / machine-route shapes, `HarnessStill` and
`EntryStill` are theorems; for `midH` the per-declaration unit of preservation (`EntryOk`) holds from the
two reflections. NOT done: `cnt` / `mid2` `EntryOk` (terms), the closing of `mixDeep`, the eleven
constructors outside `wfrag`, legacy-route declarations. No endpoint changed. A `mixDeep` closing by
this route needs `Prov` of the cache at the start world: derivable for an outermost run (after the
depth-0 clear), not for a nested start with an arbitrary cache.
