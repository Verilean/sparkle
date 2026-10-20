# B — the SOURCE side of the gate-route entry: the Signal-level form (round par/b-36)

Branch `par/b-36` from `0a0a4f71`. **WRITTEN, NOT BUILT.** No `lean`, `lake`
or `iverilog` was started. Nothing here is a claim that an endpoint exists.
Marks: [R] read (file:line at 0a0a4f71), [M] measured by the integrator,
[P] predicted.

## 1. What was read

| piece | where [R] | gives |
|---|---|---|
| `gate_core_facts` | `Tools/ShippingGateChild.lean` 56 | for the CORE module of a run on a gate declaration: `∀ bools bits initial mems, SourceInputs f bs ids cache bools bits initial → RawValueAt … (pack srt (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) e)).toNat` — ONE evaluation, already under `SourceInputs`, for ARBITRARY Bool / BitVec values |
| `RawValueAt` | `Tools/ShippingMixedEntrySoundness.lean` 536 | the evaluation succeeds, `result "out" = expected`, `TypedPostReady`, `SimpleStmts`, `weOf m = moduleWidths m`, `"out" ∈ m.outputs.map name` |
| `f.machineSource` of a gate declaration | `Tools/ShippingMachineCommand.lean` 2693 (`generateSourceDefs` = `generateCore … (defsOnly := true)`, reader with `allowGate`), 1954–1956 (`combProof`: the source is `[fun t => BitVec.toNat ((f args).val t)]` / `encodeBool …`) | the same definition the machine route gives a slotless leaf; the CHECKS (`machine_result` …) are skipped for a gate declaration (2530) |
| `machine_trace_of_comb`'s `hres` | `Tools/ShippingMachineLoop.lean` 139–145 | the machine route's pointwise equation: `(src i bools bits).map (fun g => g t) = d.outs.map fun o => enc o.1 (eval (… typedVal … t …) o.2)`, a kernel `rfl` per declaration (`f.machine_result`) |
| `f.gate_child`'s `hF` | `Tools/ShippingGateChildCommand.lean` 115–118 | `childValue f.machineSource f.gateBinders i0 vs = (pack srt (eval (decB …) (decV …) e)).toNat` by `fun _ _ => rfl` — the same reduction at CONSTANT Signals and time 0 [M: built for pick, pickD, rcH, keccakRcHW] |

Conclusion of the reading: pointwise-ness is NOT a general theorem about
`Term`s that could be transported — `eval` of a `Term` is on VALUES
(`Tools/ShippingUnifiedSource.lean` 118), there is no Signal-level
denotation of a `Term` in the gate's vocabulary; the link between the Lean
declaration (a function on Signals) and the term is, in this code base,
always ONE definitional equation per declaration, checked by the kernel
(`machine_result` on the machine route, `hF` for gate children). So the
unit is: that equation at arbitrary input Signals and time (`f.gate_pointwise`),
and a general theorem that consumes it.

It does not go through `childValue` at all: `gate_core_facts` is already
under `SourceInputs`, so the detour "values → InRange → ChildFn" of
`gate_design0` is not needed for the Signal form.

## 2. Files and statements (WRITTEN, NOT BUILT)

### `Tools/ShippingGateSource.lean`

* `singleton_get : [x][k]? = some y → x = y` (pure).
* `post_eval` (pure): for `TypedPostReady M`, `M.body.all isAssign`, and `b =
  dz M ∨ b = mergeChecked (dz M)`: `b.inputs = M.inputs ∧ b.outputs =
  M.outputs ∧ ∀ mems init e, evalAssigns (weOf M) mems M.body init = some e →
  evalAssigns (weOf b) mems b.body init = some e`.
* `text_run_of_steps` (pure): `outName ∈ b.outputs.map name`, `forwardCheck
  (checkedOptimize b)`, `SimpleStmts b.body`, and

      hstep : ∀ k st mems', k < T → ∃ e, evalAssigns (declWidth b) mems' b.body (seedR b ins k st) = some e ∧
                ∀ s, s + k + 1 = T → e outName = G s

  give `∃ envsO, TextRun (checkedOptimize b) (seedR b ins) T st0 mems envsO ∧
  envsO.length = T ∧ ∀ j hj, envsO[j] outName = G j`. The middle of the
  proof is the text of the BUILT `gate_design_of_childFn` (spliced by
  script, not retyped).
* `gate_entry_design0S`: binders of `gate_child_full` (the run,
  `EntryDefines`, `old`, `peel`, `he`, `hb`, `hv`) and

      hsrc : ∀ i bools bits t, (src i bools bits).map (fun g => g t) =
               [(pack srt (eval (fun j => (bools (bpos j)).val t) (fun j w => (bits (vpos j) w).val t) e)).toNat]

  conclusion

      ∃ raw, (b = dz raw ∨ b = mergeChecked (dz raw)) ∧
        ∃ ids, ids.Nodup ∧ ids.length = bs.length ∧ ∃ cache,
          ∀ i bools bits T ins st0 mems kids,
            (∀ t st, t < T → SourceInputs f bs ids cache (fun j => (bools j).val (T-1-t))
                               (fun j n => (bits j n).val (T-1-t)) (seedR b ins t st)) →
            (∀ t x, x ∈ b.inputs.map name → ins t x < 2 ^ declWidth b x) →
            (∀ t x, x ∈ b.inputs.map name → ins t x < 2 ^ weS (checkedOptimize b) x) →
            Bounded (weS (checkedOptimize b)) st0 →
            (∃ envsO, DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedR b ins) T ⟨st0, mems, kids⟩ envsO ∧
               envsO.length = T ∧ ∀ j hj k f, (src i bools bits)[k]? = some f → envsO[j] "out" = f j)
            ∧ ∀ envs', DesignSV … envs' → envs'.length = T ∧ ∀ j hj k f, … → envs'[j] "out" = f j

### `Tools/ShippingGateSourceCommand.lean`

* `f.gate_pointwise` — `hsrc` at `f.machineSource`, `f.gateSort`,
  `f.gateTerm`, `f.gateBpos.getD j 0`, `f.gateVpos.getD j 0`. The statement
  is elaborated from syntax (binder types from `f.machineSource`), the proof
  is `Eq.refl` of the left side under the binders
  (`Tools.ShippingMachineCommand.reflProof`), added with `addDecl`: the
  KERNEL decides it; the elaborator's `isDefEq` is not asked.
* `#gate_design0S f` — `f.gate_design0S := fun hr entry =>
  gate_entry_design0S hr entry f.gate_old f.gate_peel f.gate_wf
  (bool_positions (by decide)) (bits_positions (by decide)) f.gate_pointwise`.
  The statement is the elaborated term's inferred type (not written a second
  time). Checked: `Tools.ShippingGateDesignCommand.checkStatement` (two
  proposition binders — the run, `EntryDefines f f.gateValue` —, one
  existential, no antecedent that is not ALLOWED, `DesignSV` over
  `childMap`, no forbidden constant) plus: mentions `SourceInputs` and
  `f.machineSource`; does NOT mention `childValue` or `InRange`.
* `#gate_source_sweep`, `_summary`, `_expect` — the discipline of
  `#gate_design_sweep`.

`#gate_design0` / `f.gate_design0` are unchanged. `Tools/ShippingDesignCoverage.lean`:
`gate_design0S` is recognised as a design-level constant (one disjunct).

### `Tests/Compiler/GateSourceSweepTest.lean` (target-only)

`pick`, `pickD`, `rcH`; summary; three `#gate_source_sweep_expect … "GENERATED"`
lines — PREDICTED, to be corrected from the measurement.

## 3. Against `f.machine_design_comb0`: what still differs

| | `machine_design_comb0` | `gate_design0S` |
|---|---|---|
| reflection binder | `MachineDefines f f.machineData.shape` | `EntryDefines f f.gateValue` |
| antecedent under `∃ raw` | `ChildBnd` | none (stays absent) |
| binders in `SourceInputs`, `ids.length` | `d.bsIn`, `d.shape.binders.length` | `f.gateBinders` (`f.gate_binders : f.machineData.bsIn = f.gateBinders`, built by `#gate_child`; not rewritten into the statement) |
| output port | `q.name` for `d.shape.layout.outs[k]? = some q` | the literal `"out"` — DERIVED (`RawValueAt` evaluates `out`; it is an output port of the returned module, used in the proof). Not stated separately: `b.outputs = [⟨"out", _⟩]` (`PrintBaseAt.output` gives it for the core module; `post_eval` carries the outputs). A one-line corollary if wanted |
| source clause | `outs[k]? = some q → (src i bools bits)[k]? = some f → envs[j] q.name = f j` | `(src i bools bits)[k]? = some f → envs[j] "out" = f j` (by `hsrc` only `k = 0` is inhabited) |
| per-declaration kernel work | 11 data conditions + 1 | two `decide` (binder positions) + one `Eq.refl` (`gate_pointwise`) |

Everything else is the same text.

## 4. PREDICTED

| item | PREDICTED | if not |
|---|---|---|
| `f.gate_pointwise` for pick, pickD, rcH | accepted by the kernel: all three results are `BitVec 8`, the observation is `BitVec.toNat ((f args).val t)` and `Value.toNat (pack (.bits 8) v)` reduces to `v.toNat`; the same reduction `hF` does at constant Signals [M] and `machine_result` does at free Signals for 32 slotless leaves [M] | FAILED row naming `gate_pointwise`. For a BOOL result the two sides are `encodeBool b` and `Value.toNat (.bool b)` — whether those are the same normal form I did not check (no Bool-result gate declaration is in the sweep) |
| `f.gate_design0S` | GENERATED ×3, 2 premise lines ALLOWED, 0 antecedents, audit OK, gap `[]` | most likely: the elaboration of the proof term WITHOUT an expected type (the implicit `ι`, `sdom`, `src` must come from `f.gate_pointwise` by unification; `sdom` is a pattern `?sdom i`) |
| `Tools/ShippingGateSource.lean` | risk points: `post_eval`'s `rw [h, mergeChecked_assign hall0]`; `hdw : declWidth b = weOf b := rfl` (the built code proves the same by `rfl` after a rewrite, `ShippingGateChild.lean` gate_childFn); the `first` block for `h1` | local |

## 5. Not determined by reading

* Whether the kernel's reduction of `f.gate_pointwise` is fast for large
  gate declarations (tables like `keccakRcHW`: 24 nested muxes; `hF` for it
  is built, at constant inputs).
* Whether `Term.elabTermAndSynthesize` of a `fun {…} (hr : …) (entry : …) =>
  …` without expected type yields implicit binders in the inferred type in
  this Lean version (the statement check does not depend on binder kinds).
* Bool-result gate declarations (above).

## 6. Integrator

    lean_lib «Tools.ShippingGateSource» where
      roots := #[`Tools.ShippingGateSource]

    lean_lib «Tools.ShippingGateSourceCommand» where
      roots := #[`Tools.ShippingGateSourceCommand]

Build order: `Tools.ShippingGateSource` → `Tools.ShippingGateSourceCommand` →
`Tests.Compiler.GateSourceSweepTest` (imports `GateDesignSweepTest`).
`Tests/AllTests.lean`: nothing required; after the measurement
`import Tests.Compiler.GateSourceSweepTest`.

SCOPE of a GENERATED `f.gate_design0S`: ONE gate-route declaration as an
entry, depth 0, no call, no register, one output `out`; the run and
`EntryDefines f f.gateValue` are premises; the source on Signals under
`SourceInputs`; `DesignSV` of the module list over the returned design's
child map — not the SV string, not `#sim`; seeding `seedR` (`rst` low).

## Integrator's build record (2026-10-13) — MEASURED

BUILT on tree `5253d16de4f9dba0980eaf45809683f49deebc90` (poc + par/b-36's files), cgrun 3 GiB swap 0, worker's files unchanged, FIRST ATTEMPT:
run `b36` (exit 0, peak 0.37 GB): `Tools.ShippingGateSource`, `…GateSourceCommand`, `GateSourceSweepTest`,
`Tools.ShippingHierRunTotal`, `SlotlessParentProbeTest`, `Tools.ShippingDesignCoverage`,
`Tools.ShippingCorpusSweep`, `CorpusSweepSelfTest`; run `b36-all`: `Tests.AllTests` with
`GateSourceSweepTest` imported, and the census.

* `f.gate_design0S` GENERATED for `pick`, `pickD`, `rcH` (2 premise lines: the run, `EntryDefines`;
  0 antecedents; 0 NOT ALLOWED; audit OK; expect lines "as expected"). Source side: the Signal-level
  source under `SourceInputs`, port `"out"` — the form of `machine_design_comb0` except: reflection
  `EntryDefines`, no `ChildBnd`, binders `f.gateBinders`.
* Slotless-parent probe (`parentUse`, `wrapAdd`, `parentMix`, `parentTwoCalls`, …): the machine reader
  REFUSES each ("a combinational gate takes it"); the mixed gate accepts only WITH the instance predicate;
  the real compile emits 1–2 instance statements and a design with the child. They have no generated data,
  so they are NOT rows of the census: "129 declarations, 128 covered" counts declarations with generated
  data, not every hardware declaration of the built files.
* Corpus tooling: `CorpusSweepSelfTest` 3 candidates, 3 COVERED (comb0, gate_design0, leaf0);
  `design_sweep.sh` on its TWO-FILE SELF-TEST LIST ONLY (files already in AllTests' closure):
  2 of 2 measured (3 s and 6 s, peaks 0.29 / 0.33 GB), 12 candidates: GATE COVERED 2, LEAF-REG COVERED 1,
  PARENT NOT-ATTEMPTED 9. No corpus file was run.
