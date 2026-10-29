# Loop-form source package and the real-IP instance: design freeze (for review)

Issue `sparkle-gen2-loop-pkg` (milestone `sparkle-gen2`). Base `par/gen2-spec` (M2-a approved; Lean f1a4367f).
- **Purpose:** M2's required acceptance item, a non-vacuous memory-parent instance on a REAL IP top
  (`Sparkle.IP.Video.H264.QuantSynth.quantModule`).
- **The obstacle:** loop-form declarations (hand-written `Signal.loop`) do not fit the circuit-do `SrcPkg`/`GenFacts`.
- **Scope:** loop-form machine declarations stay in FG (route 3). Nothing is excluded.

## 1. What the sources show (read-only probe; file:line at ea5f5cda)
- **Loop heads:**
  - `machine_trace_of_loop` (Tools/ShippingMachineLoop.lean:55), for no calls.
  - `machine_trace_of_loop_causal` (Tools/ShippingMachineCausalCtx.lean:412), with calls and memory reads.
- **Their data:** `σ : α i → HList (tys d.ss)`, `inits`, `f` (the loop body, returning registers), `res`, `obsR`,
  `ext`/`extB` over `Signal (α i)`, and `src`.
- **Their premises:** `ok`, `hbody`, `hinit`, `h0`, `writes` (one cycle after), `hres`, `hsrc`, and `hcausal` (inline,
  not a named constant).
- **The generator** (`generateCore` loop branch, Tools/ShippingMachineCommand.lean:2213-2356, :2581-2613) emits
  `X.machineSigma`, `machineInits`, `machineBody` (= `f`), `machineRes`, `machineResult`, `machineExt`/`ExtB` and
  `machineSource`. It checks `machine_ok`/`_body`/`_inits`/`_reset`/`_writes`/`_result`/`_source` by refl, then emits
  `machine_sound : MachineTraceWithB …`. That is NOT the `MachineTraceLBX (ServedRealA …)` that `genTrace` gives.
- **The wired twin exists only on the OLD boundary:** `machine_traceL_of_loop_causalRA_ran`
  (Tools/ShippingMachineSeqLinkedR.lean:32), with `ServedReal`/`MachineRan`, over `letObsLoop d dom σ f ext extB`
  (Tools/ShippingMachineSeqLinked.lean:22).
- **The shared stream lemma.** Both forms end in the one stream lemma `machine_trace_lets_of_streamBRA_ranA`
  (Tools/ShippingServedRealATrace.lean:36), whose stream premise is form-agnostic. The circuit-do A-proof
  (Tools/ShippingParentSeqComposedA.lean:96-111) and the loop old-proof (SeqLinkedR:90-117) differ only in how they build
  that witness.
- **Loop `MemFacts` are produced** by `#machine_composedT` (Tools/ShippingMachineMemCommand.lean:143, `callsTactic`) over
  `letObsLoop` and `ext … (Signal.loop f)` (Tests/Compiler/ShippingMachineMemLinkedTest.lean: `memCounter`, `mixedMems`,
  `twoMems`).
- **`quantModule`** (IP/Video/H264/QuantSynth.lean:95-203): one `Signal.loop` over `bundleAll!` registers, 4 slots, and
  2 memory entries (combo 4 16, sync 4 16).
  - It reaches the `loopProof` + causal head. No generator refusal condition on that path matches its shape. That is
    a STRUCTURAL assessment; nothing was run.
  - The main risk is the kernel refl checks on a 57-binder top (heartbeats or time).
  - No test runs the generator on it today. A historical measurement, e1589937, reported "quantModule 1/1", but
    nothing is committed.

## 2. Design options
### (a) Derive a circuit-do `GenFacts` package from the loop facts (statements unchanged)
**Missing:**
- a per-declaration inverse `τ` of `σ` (not emitted today);
- signal pack/unpack helpers;
- `bodyL`, built from `f`/`res`;
- the key lemma `stateLoop inits (bodyL …) = Signal.map σ (Signal.loop f)`;
- the five `GenFacts` fields for a transported `ext`;
- transport lemmas from the loop `MemFacts` (`letObsLoop`, `ext (Signal.loop f)`) to `p.lsrc`/`p.extS`.

That is about 5-7 new lemmas plus a generator-side `τ`.

### (b) A sum of package forms (recommended)
Keep `SrcPkg` (circuit-do) unchanged. Add a loop package and a sum:
```lean
structure SrcPkgL (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  α : ι → Type
  inh : (i : ι) → Inhabited (α i)
  ρ : ι → Type
  σ : (i : ι) → α i → HList (tys d.ss)
  inits : HList (tys d.ss)
  f : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → Signal (dom i) (α i)
  res : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → ρ i
  obsR : (i : ι) → ρ i → List (Nat → Nat)
  ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → Nat → Signal (dom i) Bool
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    List (Nat → Nat)
  facts : LoopFacts d … σ inits f res obsR ext extB src   -- the loop head's premises, as a Prop structure

inductive Pkg (ι : Type) (dom : ι → DomainConfig) where
  | gen (p : SrcPkg ι dom)
  | loop (p : SrcPkgL ι dom)
```

**`LoopFacts`** is EXACTLY the premise list of `machine_trace_of_loop_causal` (CausalCtx:412-463): `ok`, `hbody`,
`hinit`, `h0`, `writes`, `hres`, `hsrc` and `hcausal`. It is the loop analogue of `GenFacts`. Each field is a generated
refl-checked fact of the declaration, and none of them is a run-level or semantic conclusion.

**Accessors**, defined by cases:
- `Pkg.decl`, `.d`, `.kD`, `.src`;
- `Pkg.extS` (`gen`: `SrcPkg.extS`; `loop`: `ext … (Signal.loop (f …))`), `Pkg.extBS`;
- `Pkg.lsrc` (`gen`: `letObsB`; `loop`: `letObsLoop d dom σ f ext extB`);
- `Pkg.ports`, `Pkg.S`.

**Theorems** (not fields):
- **`Pkg.trace`** (by cases). `gen` is `genTrace`. `loop` is the NEW `genTraceL`, which is
  `machine_traceL_of_loop_causalRA_ranA`: SeqLinkedR:32-117 on the A-boundary, with
  `machine_trace_lets_of_streamBRA_ranA` in place of `_streamBRA_ran`, wrapped like QuadComposed:156-180.
- **`Pkg.ok`, `Pkg.body_eq`:** projections of `GenFacts` or `LoopFacts`.
- **`Pkg.lsrc_hl`:** `letObsB_hl` or a NEW `letObsLoop_hl` (the same proof as QuadCalls:195).

**Statement surface change (for review):**
- The generic definitions and theorems take `Pkg` in place of `SrcPkg`: `TopShips`, `ChildShips`, `MemDec`, `CallDec`,
  `ExtInS`, `MemOrigin`, `MemParentDataOk`, `MemParentStmt'` and `memParent_ships`.
- Their bodies already use only `p.extS`/`extBS`/`lsrc`/`src`/`d`/`kD` (and `genTrace`, `body_eq`, `letObsB_hl`, `inh`
  at about 6 sites), which become the `Pkg` accessors and theorems.
- `SrcPkg`-stated theorems are recovered by `Pkg.gen`.
- This widens the covered source forms. It is not a guarantee change.

**Recommendation: (b).**
- Its new mathematics is two near-verbatim copies: the A-boundary `genTraceL` and `letObsLoop_hl`.
- It uses the generated loop facts and loop `MemFacts` as they are.
- It does not need a generator-side `τ`.
- It never introduces a semantic field: `Pkg.trace` is a theorem by cases.

The statement-surface change is a reviewed amendment. It does not narrow FG, so no user decision is proposed.

## 3. Steps, if (b) is approved
0. **Generator probe [measure, test file]:** `Tests/Gen2/QuantEndpoint.lean` runs `#machine_endpoint
   Sparkle.IP.Video.H264.QuantSynth.quantModule` and `#machine_composedT …quantModule` (for the loop `MemFacts`).
   - **Exit 0:** the generated loop facts exist.
   - **Failure:** a BLOCKER (generator coverage, M5 G3-GEN). The error is reported, and the IP item is not fulfilled.
   - Done first, because the rest is pointless if the generator refuses.
1. `LoopFacts`, `SrcPkgL`, `genTraceL` (A-boundary), `letObsLoop_hl`.
2. `Pkg`, its accessors and theorems; the refactor of the generic definitions and theorems to `Pkg` (mechanical);
   `memParent_ships` re-proved over `Pkg`; the `leafM` instance re-checked through `Pkg.gen`.
3. **quantModule instance:**
   - `qPkg := Pkg.loop {…}` from the generated `quantModule.machine*` and the `LoopFacts` fields (the generated refl
     checks; `hcausal` from `machine_sound`'s argument or a named constant);
   - `MemDec` from the generated loop `MemFacts`;
   - `ExtInS`, `MemOrigin`, `MemParentDataOk` and the case premises (decide/rfl);
   - `memParent_ships` applied. It stays conditional on the run premises, as for leafM.
   - axioms.

**Acceptance:** steps 0-3 proved and built, then reviewed. A failure in step 0 or 3 is a blocker for M2, not a fulfilment.

## 4. Not claimed
No proof yet. The generator assessment is structural. M2/FG are not complete.
