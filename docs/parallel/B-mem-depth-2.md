# B — a machine-route parent of a MEMORY-MACHINE child, at the ship level (round par/b-39)

Branch `par/b-39` from poc `2858bca5`. **No Lean file was written in this
round; nothing was run.** Unit 1 (where the two refusals come from, what the
child must expose) is answered by reading; unit 2 stops BEFORE its first
lemma, with the exact next statement (§3). Units 3 and 4 are not started.
Marks: [R] read (file:line at 2858bca5), [M] measured by the integrator
(the b-38 probe), [?] not known.

## 1. The two refusals

### 1.1 `memParent`, `memGrand`: "the child memCounterH's endpoint is not machine_trace_of_data(_ext/_causal) or _of_loop" [M]

[R: `Tools/ShippingMachineCommand.lean` 1437–1450, inside `causalFactE`.]
A parent with registers gets its endpoint from `causalProof`; for every
call it needs the fact "the call's value at time `t` depends on the context
(inputs and state) up to `t` only". For a call of a SEQUENTIAL child that
fact is built from the child's own endpoint `child.machine_sound`, by the
HEAD of its proof term:

| head of `child.machine_sound` | causality theorem used | child kind |
|---|---|---|
| `machine_trace_of_data` | `src_causal_of_data` (`ShippingMachineCausal.lean` 407) | `circuit do` without calls |
| `machine_trace_of_data_ext` | `src_causal_of_data_ext` (495) | … with combinational calls |
| `machine_trace_of_data_causal` | `src_causal_of_data_causal` (`ShippingMachineCausalCtx.lean` 130) + the child's `machine_ext_causal` | … with sequential calls / memories |
| `machine_trace_of_loop` | `src_causal_of_loop` (282) | a hand-written `Signal.loop` WITHOUT calls |
| anything else | the `throwError` at 1450 | |

`memCounterH` is a hand-written `Signal.loop` WITH a call (the memory
read): its endpoint's head is `machine_trace_of_loop_causal`
(`ShippingMachineCausalCtx.lean` 412) — the fifth head, for which there is
no `src_causal_…` theorem and no branch. (The same refusal the note of
`DepthRegsChildTest.lean` 70–78 records for a `_of_regs` child.)

So the obstacle is NOT the memory as such, and not a causal loop through the
child: a memory read directly in a parent is handled (1425–1435:
`memory_causal_ctx` / `memoryComboRead_causal_ctx`), and a `circuit do`
child with a memory has the `_causal` head, which IS in the table. The gap
is one combination: **loop child × calls**.

### 1.2 `memParent1`: "the machine synthesis does not tie the lets" [M]

[R: 2460–2463.] This is `generate`'s `checkCloses` test, before any proof:

    unless (← synthesizeMachineCertified translate (fun _ => pure ()) declName r.shape).isSome do
      throwError "{declName}: the machine synthesis does not tie the lets"

— the READER reads `memParent1` as a machine shape, but the COMPILER's own
machine synthesis returns `none` on that shape. So `memParent1` (a register
parent whose only call is a one-output sequential child) is not compiled by
the machine route at all; the real compile takes another route. This is a
fact about the compiler (reader and closing disagree on this shape), not a
missing theorem: nothing in `Tools/` can give `memParent1` a machine
endpoint, and I must not edit `Sparkle/`. It is the same class as the
note's "a parent whose only calls are one-output … the reader does not take"
— here the reader takes it and the closing does not [? which closing step
returns `none`: `closeInsts` under `instFields = []` expects one-output
COMBINATIONAL children (`gateCallsOk`); not read further].
`memParent1` is therefore OUT of this unit; the smallest case is `memParent`.

### 1.3 `memCounterH`: `#machine_design_svR0` FAILED "no sequential child" [M]

Not read in this round. Recorded because the b-38 doc predicted OK: the
built `memCounter` chain evidently reaches `#machine_no_ports_mem` (OK [M])
without that command.

## 2. What a memory-machine child exposes, and what the parent needs

`memCounterH.machine_sound` IS in the trace form (`MachineTraceWith…`: the
module's run shows `src i bools bits` at every cycle), with `src i bools
bits = obsR i (res i bools bits (Signal.loop (f i bools bits)))` (`hsrc` of
`machine_trace_of_loop_causal`, 412–470) — a function of the input SIGNALS.
The memory is not a separate state at this level: in the source it is
`Signal.memoryComboRead wa wd we addr`, a Signal function, and its value
enters the loop's step through the extension families `ext` / `extB`
(the calls' values as functions of the inputs and of the loop's state
signal). The T-indexed run form (`runModuleT`, `machine_composedT`,
`quantModule`) is the RTL side of the child as an ENTRY; a parent's trace
theorem does not consume it.

What the parent's `causalProof` consumes of a sequential child is ONE
statement (the conclusion of every `src_causal_of_*`):

    ∀ i B B' V V' t, (∀ p c, c ≤ t → (B p).val c = (B' p).val c) →
      (∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) →
      ∀ k f₁ f₂, (src i B V)[k]? = some f₁ → (src i B' V')[k]? = some f₂ → f₁ t = f₂ t

"the child's source is causal in its inputs". For a loop child without
calls it is `src_causal_of_loop`: the encoded states agree up to `t` by
induction (`loop_stream`), then `hres` at `t`. With calls the same argument
needs the calls' values to agree when the INPUTS agree up to `t` — and the
endpoint's own premise `hcausal` (462–467) only says they agree when the
loop STATE agrees, at the SAME inputs.

## 3. The exact next statement (NOT written)

    theorem src_causal_of_loop_causal {declName : Name} (d : MachineData) {ι : Type}
        (dom : ι → DomainConfig) {α : ι → Type} [∀ i, Inhabited (α i)] {ρ : ι → Type}
        (σ) (inits) (f) (res) (obsR) (ext) (extB) (src)          -- as machine_trace_of_loop_causal
        (_ok) (_hbody) (_hinit) (h0) (writes) (hres) (hsrc)       -- as machine_trace_of_loop_causal
        (hjoint : ∀ (i : ι) (B B' : Nat → Signal (dom i) Bool)
            (V V' : (j n : Nat) → Signal (dom i) (BitVec n)) (l l' : Signal (dom i) (α i)) (t : Nat),
            (∀ p c, c ≤ t → (B p).val c = (B' p).val c) →
            (∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) →
            (∀ c, c ≤ t → l.val c = l'.val c) →
            (∀ p w, (ext i B V l p w).val t = (ext i B' V' l' p w).val t) ∧
            (∀ p, (extB i B V l p).val t = (extB i B' V' l' p).val t))
        (i : ι) (B B' …) (V V' …) (t : Nat) (hb …) (hv …) :
        ∀ k f₁ f₂, (src i B V)[k]? = some f₁ → (src i B' V')[k]? = some f₂ → f₁ t = f₂ t

`hjoint` is `hcausal` strengthened to differing inputs (at `B = B'`, `V = V'`
it is `hcausal`). Proof plan: `src_causal_of_loop`'s (282–345) with

* the state stream of a loop WITH causal calls — the lemma inside
  `machine_trace_of_loop_causal`'s proof ("the loop's step at `t + 1` sees
  the loop truncated after `t`"; after line 470, NOT read) in the place of
  `loop_stream`;
* in the induction step and at `hres`, the congruence of `typedVal` in the
  extension families as well (`typedVal_congrB`, `ShippingMachineCausal.lean`
  30, takes the Bool and BitVec families — here `extB i B V L` against
  `extB i B' V' L'`, equal at `t` by `hjoint` and the induction hypothesis),
  as `src_causal_of_data_causal` does with its own `hjoint` (265–277).

Then, for the generator (a NEW command file; `#machine_endpoint` unchanged):

1. `child.machine_ext_joint` for a loop child: `hjoint` at the child's
   `machineExt` / `machineExtB`. For `memCounterH` each call is a memory
   read, whose joint causality is the BUILT `memoryComboRead_causal_ctx` /
   `memory_causal_ctx` (the lemmas `causalFactE` already applies at
   1430–1434, over the context type `Ctx` of inputs AND state): the loop's
   `loopCalls` (2195–…) builds the state-only fact `hcE` by
   `withLocalDeclD state …`; the joint one is the same construction over
   `Ctx` [? whether `causalFactE` can be called with the child's own
   `ctxT` from outside `generateCore`; it is a `where`-local or a def — not
   checked].
2. `child.machine_src_causal := src_causal_of_loop_causal … child.machine_ext_joint`
   — the constant `causalFactE` looks up (1459–1461: `child ++
   machine_src_causal`, reused when it EXISTS). So the new command only has
   to ADD `memCounterH.machine_src_causal` before `#machine_endpoint
   memParent` runs … except that the head test at 1447–1450 throws BEFORE
   the lookup. Hence the branch cannot be a pre-step: the parent's endpoint
   needs a variant of `causalFactE` accepting the fifth head — i.e. a copy
   of `causalProof`'s per-call part in the new file (the rule "no edits to
   built Tools files" excludes the one-line change in place). Its size was
   not measured.

## 4. How far it got

| unit | status |
|---|---|
| 1 — the refusals; what the child exposes | answered by reading (§1, §2) |
| 2 — the missing head | NOT written; the exact statement and proof plan in §3. `memParent1` is out (a compiler fact, §1.2); `memParent` needs the head AND a generator variant |
| 3 — generator branch, sweep | not started |
| 4 — the design-level bridge (b-38 §4) | not started; it presupposes 2–3 |

## 5. Not determined by reading

* The state-stream lemma for a loop with causal calls (inside
  `machine_trace_of_loop_causal`'s proof): its name and exact form.
* Whether `causalFactE` / `loopCalls` are callable from another file.
* Which step of the compiler's closing returns `none` for `memParent1`.
* Why `#machine_design_svR0 memCounterH` says "no sequential child".
* After the head exists: whether the parent's depth generator
  (`#machine_design_svNR memParent 1`) has a grouped entry for a child whose
  endpoint head is `_of_loop_causal` (`ShippingMachineDepthCommandR.lean`
  827 is the refusal for an unknown entry) — the b-38 probe never reached
  that step.

---

# Continuation (after the integrator's decision): the head theorem is written; the chain stops before the generated `machine_ext_joint`

**WRITTEN, NOT BUILT.** Nothing was run. The built file
`Tools/ShippingMachineCommand.lean` was **NOT edited** in this round: the
additive branch is step 4, and step 3 is not complete (§8).

## 6. What was read (step 1)

* `machine_trace_of_loop_causal`'s proof [R: `Tools/ShippingMachineCausalCtx.lean`
  470–493]: there is NO separate state-stream lemma. The proof gives the
  stream inline: the state at 0 by `Signal.loopGo_eq` and `h0`; the state at
  `t + 1` by `Signal.loopGo_eq` and `writes` at the loop TRUNCATED after `t`
  (`⟨fun s => if s < t + 1 then Signal.loopGo … s else default⟩`), then
  `hcausal` between the truncated loop and the loop (equal raw values up to
  `t`) and `typedVal_congrB`.
* `Signal.loopGo_eq` [R: `Sparkle/Core/Signal.lean` 928–930]: `loopGo f t =
  (f ⟨fun i => if i < t then loopGo f i else default⟩).val t`.
* `src_causal_of_loop` [R: 282–345]: the encoded states agree up to `t` by
  induction over `loop_stream`, then `hres` at `t`.
* `causalFactE`, the sequential-child part [R: `Tools/ShippingMachineCommand.lean`
  1437–1480]: `cargs := th.value.getAppArgs` are the arguments of the child's
  endpoint head BEFORE its run binders; the causality constant
  `child.machine_src_causal` is `mkAppN (mkConst src_causal_of_…) cargs`
  (for `_data_causal`: `cargs.push (mkConst (child ++ machine_ext_causal))`),
  added once per child; `srcC` is read by POSITION (`cargs[12]!` for a loop,
  `[11]` causal, `[10]` ext, `[9]` data).
* NOT read: `loopCalls` beyond its first lines (2195–2215, in the b-36
  round), `causalOf`, `causalProof`'s assembly. That is where step 3 stops.

## 7. `Tools/ShippingMachineLoopCausal.lean` (new; step 2)

    def truncLoop (g : Signal D α → Signal D α) (c : Nat) : Signal D α :=
      ⟨fun s => if s < c + 1 then Signal.loopGo g s else default⟩
    theorem truncLoop_val (g) (c) (hs : s ≤ c) : (truncLoop g c).val s = (Signal.loop g).val s
    theorem loop_val_succ (g) (c) : (Signal.loop g).val (c + 1) = (g (truncLoop g c)).val (c + 1)

    theorem src_causal_of_loop_causal {declName} (d) {ι} (dom) {α} [∀ i, Inhabited (α i)] {ρ}
        (σ) (inits) (f) (res) (obsR) (ext) (extB) (src)
        (_ok) (_hbody) (_hinit) (h0) (writes) (hres) (hsrc) (_hcausal)     -- the binders of machine_trace_of_loop_causal, in its order
        (hjoint : ∀ i B B' V V' (l l' : Signal (dom i) (α i)) t,
            (∀ p c, c ≤ t → (B p).val c = (B' p).val c) →
            (∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) →
            (∀ c, c ≤ t → σ i (l.val c) = σ i (l'.val c)) →
            (∀ p w, (ext i B V l p w).val t = (ext i B' V' l' p w).val t) ∧
            (∀ p, (extB i B V l p).val t = (extB i B' V' l' p).val t))
        (i) (B B') (V V') (t) (hb) (hv) :
        ∀ k f₁ f₂, (src i B V)[k]? = some f₁ → (src i B' V')[k]? = some f₂ → f₁ t = f₂ t

One change against §3: `hjoint`'s state premise is about the ENCODED state
(`σ i (l.val c) = σ i (l'.val c)`), not the raw one. Reason: the induction
over two runs on different inputs gives agreement of `σ i ((Signal.loop …).val
c)` only — `h0` / `writes` speak of `σ` of the state, and nothing says `σ` is
injective. (At equal inputs and equal raw states `hjoint` is `_hcausal`.)

The binder prefix through `_hcausal` is `machine_trace_of_loop_causal`'s, so
`mkAppN (mkConst src_causal_of_loop_causal) (cargs.push (mkConst (child ++
machine_ext_joint)))` is the term, with `srcC := cargs[14]!` (declName 0, d
1, ι 2, dom 3, α 4, the instance 5, ρ 6, σ 7, inits 8, f 9, res 10, obsR 11,
ext 12, extB 13, src 14).

`lakefile.lean`:

    lean_lib «Tools.ShippingMachineLoopCausal» where
      roots := #[`Tools.ShippingMachineLoopCausal]

Builds alone (imports the built `Tools.ShippingMachineCausalCtx`). PREDICTED
failure points, in order: `loop_val_succ` (the `rw [Signal.loopGo_eq]` may
or may not close the goal: `all_goals rfl` follows); the `step` rewrite
chain (three rewrites must land the goal syntactically on the stated right
side); the `rw […, typedVal_congrB … _ _ _ _ c _ hb' hv']` in the
induction (copied from the built `src_causal_of_loop` /
`machine_trace_of_loop_causal`, with the families `extB i B V (truncLoop …)`
in the place of `B`).

## 8. Where it stops: step 3, the exact next statement

    theorem memCounterH.machine_ext_joint :
        hjoint at  σ := memCounterH's state encoding, ext := memCounterH.machineExt,
                   extB := memCounterH.machineExtB

i.e. for the child's generated extension families (`loopCalls`,
`Tools/ShippingMachineCommand.lean` 2195–…, defines `machineExt` /
`machineExtB` over the loop's state signal and proves the state-only
`hcausal`): the same fact with differing inputs and with the state premise
through `σ`.

What it needs, none of which I read far enough to write:

1. `loopCalls` / `causalOf`: the state-only proof is built by `causalOf`
   over a context containing the state signal `L`; the joint proof is the
   same construction over the context of inputs AND state — which the
   generator already has for `circuit do` parents (`Ctx`, `CtxAgree`,
   `memoryComboRead_causal_ctx` at 1425–1434). Whether `causalOf` can be
   instantiated at a context whose state component is the loop's RAW state
   signal, or only at the `HList` state stream of a `circuit do`, decides
   whether this is a call or a new builder.
2. From `σ`-agreement to agreement of what the calls read. `memCounterH`'s
   call reads `Signal.fst st`; `σ` of a pair state is, by reading the
   endpoint's statement only, an `HList` of the slots. The step
   "`σ i x = σ i x' → x.1 = x'.1`" is a per-declaration fact about the
   generated `σ` (a `congrArg` with the right `HList` projection) — its
   generation was not written. If `σ` is not componentwise injective for
   some state type, `hjoint` in the `σ` form is NOT dischargeable and the
   theorem needs a second variant with a raw-state invariant; for pairs of
   `BitVec`s I expect it to be.

Then step 4 (the additive edit, NOT made — recorded so it can be reviewed
before it is written):

    -- Tools/ShippingMachineCommand.lean, in causalFactE (1444–1470), additive only
    + import Tools.ShippingMachineLoopCausal
    + let isLoopC := th.value.isAppOf ``Tools.ShippingMachineCausal.machine_trace_of_loop_causal
      unless … || isLoop || isLoopC do throwError …                 -- one disjunct added
      let srcC := if isLoopC then cargs[14]! else if isLoop then …   -- one branch added in front
      let causalHead ← if isLoopC then do                            -- one branch added in front
          unless (← getEnv).contains (child ++ `machine_ext_joint) do throwError "… has no machine_ext_joint"
          pure (mkAppN (mkConst ``Tools.ShippingMachineLoopCausal.src_causal_of_loop_causal)
            (cargs.push (mkConst (child ++ `machine_ext_joint))))
        else if isLoop then …

For the four existing heads `isLoopC` is false and every path is the old
one. After it, `#machine_endpoint memParent` is the EXISTING command; the
only new command is the one that generates `child.machine_ext_joint` (or
`loopCalls` generates it next to `hcausal`, a second additive edit).

## 9. How far it got

| step | status |
|---|---|
| 1 — reading | the proofs of `machine_trace_of_loop_causal`, `src_causal_of_loop`, `causalFactE`'s sequential part: read. `loopCalls`, `causalOf`, `causalProof`: NOT read in full |
| 2 — `src_causal_of_loop_causal` | written, not built |
| 3 — `child.machine_ext_joint`, generated | NOT written; §8 |
| 4 — the additive branch | NOT made (it follows step 3); the diff is described in §8 |
| 5 — probe steps | not appended (nothing new to measure before step 4) |
| 6 — depth generator, design-level bridge | not started |

## Integrator's build record (2026-10-13)

BUILT on poc 2858bca5 + this file, cgrun 3 GiB swap 0, run `b39` (exit 0, peak 0.84 GB), worker's file
unchanged, first attempt: `Tools.ShippingMachineLoopCausal` (`truncLoop`, `loop_val_succ`,
`src_causal_of_loop_causal`). STATE: the fifth head's causality theorem exists, with `hjoint` as a
hypothesis the generator must discharge per child. NOT written: `child.machine_ext_joint`, the additive
branch in `Tools/ShippingMachineCommand.lean` (no built file was edited). `#machine_endpoint memParent`
still fails; the class stays OPEN.
