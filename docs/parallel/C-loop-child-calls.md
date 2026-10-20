# C — a loop child WITH calls as a child of a machine-route parent (round par/c-1)

Branch `par/c-1` from poc `258d59cc`. **WRITTEN, NOT BUILT.** No `lean`,
`lake` or `iverilog` was started; nothing below is proved-and-built. Marks:
[R] read (file:line at 258d59cc), [M] measured earlier by the integrator,
[P] PREDICTED, [?] not known.

How far it got: steps 0–3 are written (two new Tools files, the additive
edit of `Tools/ShippingMachineCommand.lean` as a separate commit, the probe
steps). Step 4 is answered by reading: the next refusal is at the SHIP-level
depth generator, before any `GenKidM` bridge (§7).

## 1. What was read

| what | where [R] |
|---|---|
| `causalFactE`, whole | `Tools/ShippingMachineCommand.lean` 1245–1578 |
| `causalOf` (local to `causalFactE`) | 1396–1414 |
| `causalProof`, whole | 1684–1906 |
| `loopProof` and its `where`-local `loopCalls` | 2111–2192, 2197–2301 |
| `treeSigma` (the encoder `σ`), `loopRegsT` | 2090–2109 |
| `generateCore` (children first, `checkCloses`, the check theorems, `extra`, the transport, `machine_sound`) | 2443–2675 |
| `Ctx`, `CtxAgree`, `.mono/.b/.v/.of_state`, `causal_of_pointwise_ctx`, `field_causal(B)_ctx`, `causal_congr_ctx`, `src_causal_of_data_causal` (+ its `hjoint`), `src_causal_of_loop`, `machine_trace_of_loop_causal` | `Tools/ShippingMachineCausalCtx.lean` 28–497 (whole file) |
| `truncLoop`, `loop_val_succ`, `src_causal_of_loop_causal` | `Tools/ShippingMachineLoopCausal.lean` (whole file) |
| `extendBits`, `extendBits_val`; `extendBools`, `extendBools_val` | `Tools/ShippingMachineAuto.lean` 377–394; `Tools/ShippingMachineCausal.lean` 618–630 |
| `addDef`, `reflProof`, `progress` | `Tools/ShippingMachineCommand.lean` 548–567 |
| the probe | `Tests/Compiler/MemDepthProbeTest.lean` (whole file) |
| depth generator: `generateRunOfR`, `generateCoreNR` up to the head, `preClose`, the command | `Tools/ShippingMachineDepthCommandR.lean` 60–96, 517–702, 998–1049 |
| `endpointParts` | `Tools/ShippingMachineSeqCommand.lean` 70–91 |
| `ComposedNW`; `MachineRunNC`, `seqChildRunN_of_composedC` (statement) | `Tools/ShippingMachineDepthRun.lean` 33–65; `Tools/ShippingMachineDepthRunR.lean` 37–50, 114–146 |
| `machine_linkedT_mem` (statement), `#machine_composedT`'s generator | `Tools/ShippingMachineMemLinked.lean` 190–251; `Tools/ShippingMachineMemCommand.lean` 60–113 |
| `KT`, `KSn`, `ResetN` | `Tools/ShippingHierStateG.lean` 621–630; `Tools/ShippingMachineDepth.lean` 49–60 |
| refusal lines of the closing / check-free generators (grep of `throwError` only, NOT the code around them) | `ShippingMachineClosesAtGen.lean` 90–111, `ShippingMachineClosesAtGenG.lean` 34–46, `ShippingNoPortsKidsCommand.lean` 79–126, `ShippingNoPortsDeepCommand.lean` 142–203, 625 |

`Tools/ShippingMachineCausal.lean` was read where the above uses it (the
`extendBools` block, the names `src_causal_of_data(_ext)`, `typedVal_congrB`),
NOT all 789 lines.

## 2. Step 0: what `loopCalls` / `causalOf` build today for a loop child

**The context type is `Ctx D α` with `α` the loop's RAW state type** — not
the `HList` of a `circuit do`, and not "the state only".

* `loopCalls` [R 2197–2301] opens `state : Signal D α` (`L`), reads the call
  entries of the body over `L`, and for every entry `k` calls

      causalFactE declName D Unit i bools bits L cl term cidx (kindOf k) earlier
        (facts.extract 0 k0) (declName ++ machine_call_{k0}) comb α (fun S => S)

  i.e. `σT := α`, `stOf := id`, `regsF := L` [R 2238–2239]. Inside
  `causalFactE`, `hlistT := σT = α`, `ctxT := Ctx D α`, and
  `over e x := e[L := x.S, bools := x.B, bits := x.V]` [R 1265–1276].
* `causalOf e ty` [R 1396–1414] abstracts `e` to `g S B V` (the earlier
  entries read from the families at their positions), proves pointwiseness
  by `reflProof` and returns `causal_of_pointwise_ctx D α ty g FB FV hpt hFB
  hFV : ∀ x x' t, CtxAgree x x' t → (g x.S (FB x) (FV x)).val t = …` —
  causal over the WHOLE context: inputs and state.
* For a memory entry [R 1420–1434] the four operands go through `causalOf`,
  then `memory_causal_ctx` / `memoryComboRead_causal_ctx` over the same
  `Ctx D α`, then `transport` (`causal_congr_ctx`) back to the entry as
  written. The result is `fun i => (… : ∀ x x' t, CtxAgree x x' t →
  ((fun x => over term x) x).val t = ((fun x => over term x) x').val t)`.
* `loopCalls` adds it as the THEOREM `f.machine_causal_{k}` [R 2240–2244].
  So for a loop child the per-entry fact that exists in the environment is
  ALREADY joint in the inputs and the raw state:

      f.machine_causal_{k} : ∀ i (x x' : Ctx D α) t, CtxAgree x x' t →
        (entry_k over x).val t = (entry_k over x').val t

* The state-only fact `hcE` (the endpoint's `hcausal`) is only the LAST step
  [R 2266–2300]: the chain `extendBits_val` / `extendBools_val` over
  `facts[k] i ⟨bools, bits, l⟩ ⟨bools, bits, l'⟩ t (CtxAgree.of_state …)`,
  started from `rfl` on the inputs. It is passed as `extra` and applied as
  the 23rd argument of `machine_trace_of_loop_causal` [R 2185, 2192, 2547].
* `causalProof` (a `circuit do` parent) does the same with `σT := HList αs`,
  `stOf := regsOf`, and additionally builds the context-level chain from
  `CtxAgree.v` / `CtxAgree.b` and adds it as `f.machine_ext_causal`
  [R 1762–1796, 1866–1887]. `loopCalls` has no such declaration: that chain
  is what `#machine_ext_joint` adds (as `f.machine_ext_ctx`).

Consequence: `child.machine_ext_joint` does not need a new causality
builder, and it is not specific to memories — it is the built per-entry
theorems chained at differing inputs, plus the passage from RAW-state
agreement (`CtxAgree`) to ENCODED-state agreement (`hjoint`'s premise).

**The encoder.** `f.machineSigma := fun i x => (leaf₁, (leaf₂, …, ()))`
[R 2154–2158, `treeSigma` 2099–2109]: the leaves of the body's tree of
`bundle2` / `pairS`, each a chain of `Prod.fst` / `Prod.snd` on `x`, as a
right-nested tuple ending in `Unit.unit`. For `memCounterH`:
`fun _ x => (x.1, (x.2, ()))`.

## 3. Injectivity of `σ`: had, generally, by a left inverse

`σ` lists every leaf of a full binary tree of pairs, so the state is
rebuilt from the tuple: there is `τ` with `τ (σ x) = x` by `rfl` (projection
of a pair, then the kernel's eta for `Prod`). A function with a left inverse
is injective (`eq_of_leftInv`, general). `τ` depends on the tree, so it is
generated per declaration — from the VALUE of `f.machineSigma` (the leaves'
projection paths), not from the loop body again. This is not "products of
BitVec/Bool" only: the leaf types are arbitrary; a leaf that is itself a pair
is one component. No raw-state variant of `src_causal_of_loop_causal` was
needed, so none was written.

## 4. Statements (WRITTEN, NOT BUILT)

### `Tools/ShippingMachineLoopJoint.lean` (new; namespace `Tools.ShippingMachineLoopJoint`)

    theorem eq_of_leftInv {α β : Type} (σ : α → β) (τ : β → α) (hτ : ∀ x, τ (σ x) = x)
        (x x' : α) (h : σ x = σ x') : x = x'

    theorem ext_joint_of_ctx (d : MachineData) {ι : Type} (dom : ι → DomainConfig) {α : ι → Type}
        (σ : (i : ι) → α i → HList (tys d.ss))
        (ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) →
          Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        (extB : … → Signal (dom i) (α i) → Nat → Signal (dom i) Bool)
        (hinj : ∀ (i : ι) (x x' : α i), σ i x = σ i x' → x = x')
        (hctx : ∀ (i : ι) (x x' : Ctx (dom i) (α i)) (t : Nat), CtxAgree x x' t →
          (∀ p w, (ext i x.B x.V x.S p w).val t = (ext i x'.B x'.V x'.S p w).val t) ∧
          (∀ p, (extB i x.B x.V x.S p).val t = (extB i x'.B x'.V x'.S p).val t)) :
        ∀ (i : ι) (B B' : Nat → Signal (dom i) Bool)
          (V V' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
          (l l' : Signal (dom i) (α i)) (t : Nat),
          (∀ p c, c ≤ t → (B p).val c = (B' p).val c) →
          (∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) →
          (∀ c, c ≤ t → σ i (l.val c) = σ i (l'.val c)) →
          (∀ p w, (ext i B V l p w).val t = (ext i B' V' l' p w).val t) ∧
          (∀ p, (extB i B V l p).val t = (extB i B' V' l' p).val t)

The conclusion is, binder for binder, the `hjoint` of
`src_causal_of_loop_causal` [R `ShippingMachineLoopCausal.lean` 121–128].
Neither hypothesis renames the conclusion: `hinj` is about `σ` alone, `hctx`
is the raw-state context form; both are discharged per declaration by the
generator below.

### `Tools/ShippingMachineLoopCausalCommand.lean` (new): `#machine_ext_joint f`

Requires `f.machine_sound` with the head `machine_trace_of_loop_causal` and
exactly 23 arguments (`cargs`). Adds, each by `addDecl` (kernel-checked, no
asynchronous checking, the environment put back on any failure, the axiom
test of `#machine_endpoint`):

    f.machine_sigma_inj : ∀ (i : ι) (x x' : α i), f.machineSigma i x = f.machineSigma i x' → x = x'
    f.machine_ext_ctx   : ∀ (i : ι) (x x' : Ctx (dom i) (α i)) (t : Nat), CtxAgree x x' t →
        (∀ p w, (f.machineExt i x.B x.V x.S p w).val t = (f.machineExt i x'.B x'.V x'.S p w).val t) ∧
        (∀ p, (f.machineExtB i x.B x.V x.S p).val t = (f.machineExtB i x'.B x'.V x'.S p).val t)
    f.machine_ext_joint : ∀ i B B' V V' (l l' : Signal (dom i) (α i)) t,
        (∀ p c, c ≤ t → (B p).val c = (B' p).val c) →
        (∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) →
        (∀ c, c ≤ t → f.machineSigma i (l.val c) = f.machineSigma i (l'.val c)) →
        (∀ p w, (f.machineExt i B V l p w).val t = (f.machineExt i B' V' l' p w).val t) ∧
        (∀ p, (f.machineExtB i B V l p).val t = (f.machineExtB i B' V' l' p).val t)

with `ι, dom, α, σ, ext, extB := cargs[2], [3], [4], [7], [12], [13]`. The
three STATEMENTS are not written by hand: each is the binder type of the
theorem it is passed to (`inferType (…partial application…)`, first binder) —
`machine_ext_joint`'s is the `hjoint` binder of `src_causal_of_loop_causal`
applied to `cargs`, the other two the `hinj` / `hctx` binders of
`ext_joint_of_ctx`. So what `causalFactE` builds in step 2 fits by
construction.

Proofs:

* `machine_sigma_inj`: the value of `f.machineSigma` is opened (`fun i x =>
  body`); the leaves are read off the `Prod.mk` spine (it must end in
  `Unit.unit`), each must be a chain of `Prod.fst` / `Prod.snd` (or `.proj`)
  on `x` — its path. `τ := fun h => tree`, the tree built by `invTree` (the
  component at a path is the leaf with that path — `h.2.….2.1` — or the pair
  of the two components below it; refused if some component is read by no
  leaf). Term: `fun i x x' h => eq_of_leftInv (fun x => body) τ (fun x =>
  rfl) x x' h`.
* `machine_ext_ctx`: the values of `f.machineExt` / `f.machineExtB` are
  beta-applied to `i, x.B, x.V, x.S` (and to `x'`), the `extendBits` /
  `extendBools` chains read innermost first; the entry index of position `p`
  is `p - (least position)` (positions are `nDecl + k`; they are required to
  be consecutive); the proof is `causalProof`'s `joint` chain [R 1770–1796]:
  from `CtxAgree.v h` / `CtxAgree.b h`, one `extendBits_val` /
  `extendBools_val` per entry with `f.machine_causal_{k} i x x' t h`.
* `machine_ext_joint := ext_joint_of_ctx d dom σ ext extB f.machine_sigma_inj f.machine_ext_ctx`.

Nothing reflected is evaluated; there is no `decide`, no tactic block, no
named hole in the generator.

## 5. The built-file edit (separate commit `3fb645a7`)

`Tools/ShippingMachineCommand.lean`, 13 insertions, 3 deletions, all in
`causalFactE`'s sequential-child part plus one import:

    + import Tools.ShippingMachineLoopCausal
      let isLoop := …machine_trace_of_loop
    + let isLoopC := th.value.isAppOf ``Tools.ShippingMachineCausal.machine_trace_of_loop_causal
    - unless … || isExt || isCausal || isLoop do
    + unless … || isExt || isCausal || isLoop || isLoopC do
        throwError "…is not machine_trace_of_data(_ext/_causal) or _of_loop"      -- text unchanged
    - let srcC := if isLoop then cargs[12]! else if isCausal then cargs[11]! else if isExt then cargs[10]! else cargs[9]!
    + let srcC := if isLoopC then cargs[14]! else if isLoop then cargs[12]! else if isCausal then cargs[11]!
    +   else if isExt then cargs[10]! else cargs[9]!
    - let causalHead ← if isLoop then
    + let causalHead ← if isLoopC then do
    +     unless (← getEnv).contains (child ++ `machine_ext_joint) do
    +       throwError "{declName}: the child {child} (a hand-written loop with calls) has no machine_ext_joint: run #machine_ext_joint {child} after its #machine_endpoint"
    +     pure (mkAppN (mkConst ``Tools.ShippingMachineLoopCausal.src_causal_of_loop_causal)
    +       (cargs.push (mkConst (child ++ `machine_ext_joint))))
    +   else if isLoop then
          pure (mkAppN (mkConst ``…src_causal_of_loop) cargs)

Position 14: `declName 0, d 1, ι 2, dom 3, α 4, inst 5, ρ 6, σ 7, inits 8, f
9, res 10, obsR 11, ext 12, extB 13, src 14` (the loop head without calls
has `src` at 12 — the built branch — and this head has `ext`, `extB` before
it).

**Why every path of the four existing heads is unchanged.** The head of a
theorem's value is ONE constant, so for a child whose head is
`machine_trace_of_data`, `_data_ext`, `_data_causal` or `_of_loop`,
`isLoopC = false`. Then: the `unless` condition is the old disjunction `∨
false`; `srcC`'s first test fails and the rest is the old expression;
`causalHead`'s first test fails and the rest is the old chain. No other line
is touched; `isLoopC` occurs nowhere else. For a head that is none of the
five (e.g. `_of_regs`, or a transported endpoint `Eq.mpr …`) the `unless`
throws the same message as before. The only behavioural change is for a
child whose head is `machine_trace_of_loop_causal`: before, the old message;
now, either the new message (no `machine_ext_joint`) or the new causality
constant. What the edit cannot leave unchanged: the import adds
`Tools.ShippingMachineLoopCausal`'s three declarations to the environment of
every file downstream of `ShippingMachineCommand` (a census or fingerprint
that enumerates declarations by module would see them [? whether any does]),
and everything downstream is rebuilt.

## 6. Build order, `lean_lib` lines, predictions

Build order:

1. `Tools.ShippingMachineLoopJoint` (imports the built
   `Tools.ShippingMachineLoopCausal` only) — independent of the edit.
2. `Tools.ShippingMachineCommand` with the edit (commit `3fb645a7`), then
   everything downstream: the whole suite, the fingerprint pin test, the
   census.
3. `Tools.ShippingMachineLoopCausalCommand` (imports
   `Tools.ShippingMachineCommand`, `…LoopCausal`, `…LoopJoint`). It does not
   need the edit: it can be built on commit `1f26d39a` alone.
4. `Tests.Compiler.MemDepthProbeTest` (target-only, a measurement).

`lakefile.lean` (I did not edit it):

    lean_lib «Tools.ShippingMachineLoopJoint» where
      roots := #[`Tools.ShippingMachineLoopJoint]

    lean_lib «Tools.ShippingMachineLoopCausalCommand» where
      roots := #[`Tools.ShippingMachineLoopCausalCommand]

(`grep MemDepthProbe lakefile.lean` finds no line for the probe at
258d59cc; the integrator built it before, by whatever target that was.)
Nothing for `Tests/AllTests.lean`.

### PREDICTED outcomes of the probe (all [P]; nothing measured)

The old steps, with the edit in place:

| step | PREDICTED |
|---|---|
| C1–C5 | as measured before: OK, OK, OK, FAILED "no sequential child", OK |
| P1.1–P1.4 `memParent1` | unchanged: FAILED "the machine synthesis does not tie the lets", then for lack of data |
| P2.1 `#machine_endpoint memParent` | FAILED with the NEW message "…the child …memCounterH (a hand-written loop with calls) has no machine_ext_joint: run #machine_ext_joint …" |
| P2.2–P2.5, G.1–G.4 | FAILED as before (G.1 with the new message, through `memParent`) |

The new steps:

| step | PREDICTED | basis |
|---|---|---|
| J1 `#machine_ext_joint memCounterH` | OK | §4; the per-entry theorem `memCounterH.machine_causal_0` exists after C1 [M: C1 OK] |
| Q2.1 `#machine_endpoint memParent` | OK | the only refusal measured was the head test; after it the path is the built one for a loop child (`hsrc`, families, `hobs` by `rfl`, `field_causal_ctx`). Not certain: no built example of a loop child with BitVec arguments was read |
| Q2.2 `#machine_design_svNR memParent 1` | FAILED — "child …memCounterH: …memCounterH: no sequential child" | `generateCoreNR memParent 1`: `memCounterH` is not a leaf (`insts ≠ []`: the memory placeholder) → `generateRunOfR memCounterH 0` → `generateCoreNR memCounterH 0` (its `instFields ≠ []`), whose `seqKids` (callees that are not placeholders) is empty → line 693 [R]. NOT the refusal at 827 |
| Q2.3 `#machine_closes_at memParent` | FAILED — a kid with calls of its own / a memory child "not derived here" | grep of the refusal lines only (`ClosesAtGenG` 38, 44; `ClosesAtGen` 103, 105); which one fires was not read [?] |
| Q2.4 `#machine_no_ports_kids memParent 1` | FAILED — "the callee …memCounterH has calls of its own under the GENERAL closing (instFields ≠ [])…" | `ShippingNoPortsKidsCommand.lean` 103, in the scope test before anything is generated |
| Q2.5 `#machine_no_ports_deep memParent 2` | REFUSED — "…the general-closing callee …memCounterH's callee SparkleMem.combo.4.8 is a memory child (no KidFacts for it)" | `ShippingNoPortsDeepCommand.lean` 149, 194. The command reports a refusal as an information line (625), so the wrapper may print `OK` for this step with the refusal in the log [?] |
| H.1 `#machine_endpoint memGrand` | OK if Q2.1 is | `memParent`'s head is `machine_trace_of_data_causal` and `causalProof` adds `memParent.machine_ext_causal` [R 1869–1887]: the built third head |
| H.2 `#machine_design_svNR memGrand 2` | FAILED — "child …memParent: child …memCounterH: …no sequential child" | as Q2.2, one level down |
| H.3–H.5 | FAILED / REFUSED where `memParent`'s steps are | |

If J1 fails, the first suspects are in §8.

## 7. Step 4: what stops next, and the next missing piece

After Q2.1 the class is no longer stopped at `#machine_endpoint`. By
reading, the next stop is the grouped depth generator, and it is NOT the
head table / the refusal at 827 and NOT yet the `GenKidM` bridge of
`B-mem-depth.md` §4:

`generateCoreNR` treats every callee that is not a memory PLACEHOLDER as a
sequential kid [R 549–550]. A kid with calls needs its own composed theorem
one depth down, in the form

    ∀ {mctx mref cctx cref w w' m design}, RunsTo … (m, design) w' → MachineDefines … →
      MachineClosesAt … → Bnd … → ComposedNW n c d kD m design dom src ext extB

(the `composed` premise of `seqChildRunN_of_composedC`,
`ShippingMachineDepthRunR.lean` 126–132; 12 binders, `bndOfComposed`). For a
kid with calls it is made by `generateCoreNR c (dep - 1)` itself
[R 517–520], which requires at least one SEQUENTIAL child of `c`
(`pcCases.head?`, 693). `memCounterH`'s only calls are memory placeholders.
Its composed theorem exists in ANOTHER form: `memCounterH.machine_composedT`
(`machine_linkedT_mem`: `runModuleT` over `KidState`, the memories and read
latches zeroed by two premises, no `MachineWired`, no run binders).

**The next missing piece (NOT written):** the depth-0 composed theorem of a
memory-only machine in the depth generator's form,

    theorem composedNW0_of_mem {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
        {ι : Type} {dom : ι → DomainConfig} {src ext extB lsrc}
        (h : the wired trace of `machine_traceL_of_loop_causalRA` — `MachineTraceLB …` together
             with `MachineWired declName d.shape ids cache m dsn regs lets`)
        (hfe … kD hkD hI hIlen hSL hSlen hLlen hNIn hcalls : exactly the premises of machine_linkedT_mem) :
        ComposedNW 0 declName d kD m dsn dom src ext extB

`ComposedNW 0` [R `ShippingMachineDepthRun.lean` 34–65] asks the run
`runModuleTG (KSn (childMap dsn.modules) 0) …` over `kids : String → KT 0`
under `∀ iname mc, (inst of mc in m.body) → moduleByName … = some mc →
ResetN dsn 0 mc (kids iname)`. `KT 0 = KidState` and `KSn _ 0 = flatKS`
[R `ShippingHierStateG.lean` 623–630], and `ResetN dsn 0 mc s` gives
"memories zero" and "the read latch of every `Stmt.memory` of `mc` zero"
[R `ShippingMachineDepth.lean` 52–57]. So the proof would be
`machine_linkedT_mem` plus three facts I did NOT read for:

1. `runModuleTG flatKS … ⟨st0, mems, kids⟩` against `runModuleT … st0 mems kids`
   [? the name of the built equation];
2. from `ResetN dsn 0 mc (kids iname)` for every instance of `m` to
   `(kids iname).mems n a = 0` (direct: the second conjunct) and
   `(kids iname).st "out_rdata" = 0` (the third conjunct gives it only when
   `mc`'s body has a `Stmt.memory` whose read register is `"out_rdata"` — true
   of a sync memory module presumably; for a COMBO memory module the premise
   of `machine_linkedT_mem` asks the latch zero too, and whether `ResetN`
   gives it there is [?]);
3. `MachineWired` and the `lets` component from the `RA` head (the form
   `generateCoreNR` gets from `endpointParts`).

and then a `generateRunOfR` branch "a kid whose calls are all placeholders"
in a NEW command file (the built `generateRunOfR` cannot be edited), i.e. a
copy of the entry of the depth generator with that branch — its size was not
measured. Only after that does the check-free level (`#machine_no_ports_kids`
103, `_deep` 149: the `GenKidM` chain of `B-mem-depth.md` §4) become the
frontier.

Whether the built memory-entry chain (`#machine_no_ports_mem`,
`machine_design_noPortsR0_closed`) already contains a `ComposedNW 0`-shaped
intermediate for a memory-only machine was not read [?] — if it does, piece
`composedNW0_of_mem` is a re-export, not a proof.

## 8. Risks, in order

1. **`machine_sigma_inj`, the kernel check of `fun x => rfl`.** It needs
   `τ (σ x) ≡ x` by projection reduction and eta for `Prod`, with the leaves
   written as `Prod.fst` / `Prod.snd` APPLICATIONS (what `mkAppM` builds).
   Expected to hold; if the kernel refuses, the fallback is a proof by
   `Prod.ext` per node (not written).
2. **`T` against `HList (tys d.ss)`.** `eq_of_leftInv` is applied at
   `β := T` (the inferred type of the tuple, `A × B × Unit`), the premise `h`
   is an equation in `HList (tys f.machineData.ss)`. The kernel must unfold
   the data to see them equal — the same unfolding it did when
   `f.machineSigma` was added (its value against its declared type).
3. **The 23 arguments.** `#machine_ext_joint` refuses unless the head has
   exactly 23. Counted from `loopProof` + `generateCore` [R]: 7 + 8
   definitions + 7 check theorems + `hcE`. A transported endpoint (`Eq.mpr`:
   sign normalisation or FUSED loops, e.g. `withMemory`) is refused by the
   head test — such a child is not covered (nor is it by `causalFactE` for
   any head).
4. **The chain read off `machineExt`.** The entry index is taken from the
   position (`p - least`), relying on `loopCalls`' `pos := nDecl + k` and the
   fact names `machine_causal_{k}` [R 2240, 2251]. A mismatch is a kernel
   error at `machine_ext_ctx`, not a wrong theorem.
5. **Meta API spellings not checked by a build:** `Array.findIdx?` returning
   `Option Nat` (as the built file uses it), `List.isPrefixOf`,
   `instantiateForall`, `levelOne`, `Nat.min`, the `let .forallE … := … |
   throwError` form, `while` in `do`.
6. **Q2.1 after the head.** The `hobs` `rfl` reads the child's source at
   input families extended at BitVec positions (`extendBits` with a `cast`);
   built for other heads, not read for a loop child with three arguments.
7. **The import** (§5): new declarations visible downstream; a long rebuild.
8. The probe's old steps P2.1 / G.1 change their message (expected, §6).

## 9. Not determined by reading

* Whether J1 / Q2.1 pass (no build).
* Which refusal `#machine_closes_at memParent` gives (Q2.3).
* Whether `#machine_no_ports_deep`'s refusal is an error or an information
  line for the probe's wrapper (Q2.5).
* §7: the three facts under `composedNW0_of_mem`, and whether a
  `ComposedNW 0` form for a memory-only machine already exists.
* Whether any census / fingerprint test enumerates the declarations of the
  modules `ShippingMachineCommand` imports.
* `memParent1` stays out (the compiler's machine synthesis does not close
  it — `B-mem-depth-2.md` §1.2); not looked at again.

## Integrator's build record (2026-10-13) — MEASURED

BUILT on poc ef4d020a + these files, cgrun 3 GiB swap 0, run `c1` (exit 0, peak 1.21 GB), worker's files
unchanged, FIRST ATTEMPT: `Tools.ShippingMachineLoopJoint`, `Tools.ShippingMachineLoopCausalCommand`,
`MemDepthProbeTest`, then `Tests.AllTests` (1327 jobs, 348 s — everything downstream of the edited
`Tools/ShippingMachineCommand.lean` rebuilt, i.e. every generated endpoint of the suite regenerated and
re-audited, `DepthSwitchPinTest` included) and the census.

No change for existing declarations: suite green; census identical to before the edit (129 declarations,
128 covered, same counts per form).

Probe, every prediction confirmed:
* J1 `#machine_ext_joint memCounterH`: OK. Q2.1 `#machine_endpoint memParent`: OK. H.1
  `#machine_endpoint memGrand`: OK. — the ship-level trace endpoints (`machine_sound`) of a parent and a
  grandparent of a memory-machine child now exist.
* Q2.2 / H.2 `#machine_design_svNR`: FAILED "child memCounterH: no sequential child"; Q2.3 / H.3
  `#machine_closes_at`, Q2.4 / H.4 `#machine_no_ports_kids`, Q2.5 / H.5 `#machine_no_ports_deep`: FAILED
  as predicted.
STATE: endpoint `memParent.machine_sound` / `memGrand.machine_sound` exist (trace level). No design-level
endpoint for them; the next stop is the ship-level depth generator, which has no composed theorem
(`ComposedNW 0 …`) for a child whose only calls are memory placeholders. The class stays OPEN at the
design level; these declarations are test declarations of the probe, not in AllTests.
