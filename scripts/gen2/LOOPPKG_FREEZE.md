# Loop-form source package and the real-IP instance: design freeze (for review)

Issue `sparkle-gen2-loop-pkg` (milestone `sparkle-gen2`). Base `par/gen2-spec` (M2-a approved; Lean f1a4367f).
- **Purpose:** M2's required acceptance item, a non-vacuous memory-parent instance on a REAL IP top
  (`Sparkle.IP.Video.H264.QuantSynth.quantModule`).
- **The obstacle:** loop-form declarations (hand-written `Signal.loop`) do not fit the circuit-do `SrcPkg`/`GenFacts`.
- **Scope:** loop-form machine declarations stay in FG (route 3). Nothing is excluded.

## 1. What the sources show (read-only probe; file:line at ea5f5cda). SUPERSEDED in part by §5.1 (the generator WAS run; `hcausal` is not a refl field)
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
`hinit`, `h0`, `writes`, `hres`, `hsrc` and `hcausal`. It is the loop analogue of `GenFacts`. [SUPERSEDED by §5.2: the
first seven are refl-checked generated facts; `hcausal` is a source-level causality obligation.]

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

## 5. Rev1 (review 500bc675): step-0 inventory, the supply path (R1), and compatibility (R2)

### 5.1 Step 0 result (generator probe, APPROVED step)
- **Probe:** `Tests/Gen2/QuantEndpoint.lean` runs `#machine_endpoint` and `#machine_composedT` on
  `Sparkle.IP.Video.H264.QuantSynth.quantModule`.
- **Builds:**
  - `g2lp-1ff48ce9`: exit 0, head = base = 1ff48ce9, log SHA-256 prefix `74658400d0ba4b62`.
  - Failed diagnostics: `g2lp-6619ad15` and `g2lp-f1bde40d`. Only the inventory `run_cmd` failed (a shadowed variable;
    `String.take` returns a `Slice`). Both generator commands had already succeeded in them.
- **Axioms:** `machine_sound` depends only on `[propext, Classical.choice, Quot.sound]`.
- **Generated constants** (prefix `…quantModule.`):
  - **defs:** `machineData`, `machineSigma`, `machineInits`, `machineBody` (the loop body `f`), `machineRes`,
    `machineResult` (`obsR`), `machineExt`, `machineExtB`, `machineSource`.
  - **theorems:**
    - `machine_ok`, `machine_body`, `machine_inits`, `machine_reset` (= `h0`), `machine_writes`, `machine_result`,
      `machine_source` (refl-checked);
    - `machine_causal_0`, `machine_causal_1` (per-call context agreement, over `Ctx i (BitVec 2 × BitVec 5 × Bool ×
      BitVec 16)`);
    - `machine_sound`, `machine_composedT`.
- **Source tie:** `machine_source : machineSource i bools bits = machineResult i (machineRes i bools bits (Signal.loop
  (machineBody i bools bits)))`.
  - No `machineSourceDecl` was emitted, so no normalisation/transport happened and none is needed.
  - That `machineBody` is `quantModule`'s own loop is the generator's construction (G3-DECL, by construction; not proved
    here).
- **NOT available by name:**
  - the loop head's `hcausal` (assembled inline, Tools/ShippingMachineCommand.lean:2243-2268, :2288-2356, :2603-2605);
  - the per-call `MemFacts` (proved inside `#machine_composedT` by `callsTactic`, Tools/ShippingMachineMemCommand.lean:59,
    :119; not exported).

### 5.2 R1: supply path, with fields classified honestly
**`LoopFacts`** = the premises of `machine_trace_of_loop_causal` (Tools/ShippingMachineCausalCtx.lean:412-463), with
their kinds:

| field | kind | quantModule supplier |
|---|---|---|
| `ok`, `hbody`, `hinit`, `h0`, `writes`, `hres`, `hsrc` | generated, refl-checked | `machine_ok`, `machine_body`, `machine_inits`, `machine_reset`, `machine_writes`, `machine_result`, `machine_source` |
| `hcausal` | **source-level causality obligation** (not DATA, not refl) | a NAMED lemma `quant_hcausal` in the instance file, assembled exactly as `loopCalls` does: unfold `machineExt`/`machineExtB` (`extendBits`/`extendBools` chains), `extendBits_val`/`extendBools_val` case splits, and `machine_causal_0`/`_1` via `CtxAgree.of_state`. Its type is checked against `LoopFacts.causal` by the kernel. Nothing is extracted from proof terms |

**`genTraceL`** (exact signature, A-boundary):
```lean
theorem genTraceL (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} (p : SrcPkgL ι dom) (h : p.decl = declName) {D₀ : Nat} {m : Module} {design : Design}
    (ran : Tools.ShippingServedRealA.MachineRunJQC O mctx cctx (D₀ + 1) declName p.d.shape m design) :
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedRealA O declName p.d.shape m design) declName p.d m design dom p.src
      (fun i b v => p.ext i b v (Signal.loop (p.f i b v))) (fun i b v => p.extB i b v (Signal.loop (p.f i b v)))
      (Tools.ShippingMachineSeqLinked.letObsLoop p.d dom p.σ p.f p.ext p.extB)
```
It is proved like `genTrace` (QuadComposed:156-180):
- the A-form loop proof `machine_traceL_of_loop_causalRA_ranA` is SeqLinkedR:90-117, with
  `machine_trace_lets_of_streamBRA_ranA O (bodyStepC_of_tele O T) hA (htr_of_tele O hA T D₀)` (ServedRealATrace:36) in
  place of `_streamBRA_ran`;
- `ran : MachineRunJQC … (D₀ + 1)`, exactly as `genTrace`.

It NEVER uses `MachineRan`/`ServedReal`.

**MemDec for the loop package:** stated over `Pkg.lsrc (.loop p) = letObsLoop …` and `Pkg.extS (.loop p) = p.ext …
(Signal.loop (p.f …))`. That is exactly the form in which `#machine_composedT` proves its `MemFacts`. The instance
re-proves them with the generator's `memTactic`/`callsTactic` steps (`rfl`/`decide` per entry) as a named
`quant_memDec`. It is not extracted.

**Step-0 completion criterion (R1).** The package counts as complete only when `quant_hcausal`, `quant_memDec` and
`ExtInS` (`rfl` through `extendBits`) are proved for `quantModule`. Otherwise it is a blocker.

### 5.3 R2: compatibility and verification scope
**Change surface.** The whole of `Tools/ShippingGen2Defs.lean` moves from `SrcPkg` to `Pkg`:
- `SrcPkg.ports`/`S` become `Pkg.ports`/`S`;
- `Pkgs` becomes `Name → Option (Pkg ι dom)`;
- `ChildShips`, `CallDec`, `MemDec`, `ShipsRes`, `CacheShips`, `ShipsAt`, `InvAt`, `IHAt`, `BodyKeepsInv`,
  `ChildKeepsInv`, `KeepBodyStmt`, `KeepChildStmt`, `T1Hyp`, `ServedGP`/`Served1P`/`ServedP` (unchanged: no package),
  `ServedShipsStmt`, `ServedPC`, `TopShips`, `StepStmt`, `MemParentStmt`, `LeafStmt` and `T1Stmt` switch to `Pkg`;
- `MemParentDataOk`, `ExtInS`, `MemOrigin` and `MemParentStmt'` in Tools/ShippingGen2MemParent.lean switch too.

**Importer table:**

| file | change |
|---|---|
| Tools/ShippingGen2Connect.lean | `SrcPkg` → `Pkg`; `stableA_invAt` is unchanged in substance |
| Tools/ShippingGen2Keep.lean | none beyond the types |
| Tools/ShippingGen2Data.lean (U0 `DataOkB`) | stays on `SrcPkg` (U0 artefact). `DataOk` for `Pkg` via `Pkg.gen` |
| Tools/ShippingGen2CallDec.lean, Tools/ShippingGen2Adapt.lean | `letObsB_hl` → `Pkg.lsrc_hl`; types |
| Tools/ShippingGen2MemFacts/MemParent/MemData/MemTop/MemShips/C6 | `genTrace` → `Pkg.trace`, `p.gen.body_eq` → `Pkg.body_eq`, `p.inh` → per-form; types |
| Tests/Gen2/U0Check, CallDecInstance, AdaptInstance, MemParentInstance | packages wrapped with `Pkg.gen` |

**Exact types of the accessors/theorems** (`namespace Tools.ShippingGen2`):
- `Pkg.decl : Pkg ι dom → Name`, `Pkg.d`, `Pkg.kD`;
- `Pkg.src : (p : Pkg ι dom) → (i : ι) → (Nat → Signal (dom i) Bool) → (…) → List (Nat → Nat)`;
- `Pkg.extS`/`extBS`/`lsrc` with the same types as `SrcPkg.extS`/`extBS`/`lsrc`, by cases;
- `Pkg.ports`, `Pkg.S`;
- `Pkg.trace : … MachineRunJQC O mctx cctx (D₀+1) p.decl p.d.shape m design → MachineTraceLBX (ServedRealA O p.decl
  p.d.shape m design) p.decl p.d m design dom p.src p.extS p.extBS p.lsrc` (a theorem, by cases);
- `Pkg.ok : p.d.ok = true`, `Pkg.body_eq`, `Pkg.lsrc_hl` (the statement of `letObsB_hl` over `Pkg.lsrc`).

**Specialization tests (acceptance).** `Tests/Gen2/PkgCompat.lean` copies the OLD texts of every changed definition
(from f1a4367f, under `namespace Old`) and proves, for every `p : SrcPkg ι dom`:
- `TopShips (.gen p) … = Old.TopShips p …` by `rfl`, and the same for each changed def;
- for `Pkgs`: `Old.X P … ↔ X (fun c => (P c).map Pkg.gen) …`, by `Iff.rfl` or a short proof.

**No new semantic premise anywhere.**

**Focused verification.**
- Re-build U0Check, CallDecInstance, AdaptInstance and MemParentInstance through `Pkg.gen`.
- Add the quantModule instance.
- No full rebuild.
- `SrcPkg`-specific lemmas (`genFacts_restrict`, `letObsB_hl`, U0's `DataOkB`) stay on `SrcPkg`. Their boundary is the
  `Pkg.gen` wrapper.


## 6. Rev2 (review 752b0084): exact interface, compatibility rules, supersession
**Supersession.** §1's "nothing was run" and §2's "each field is refl-checked" are superseded by §5.1/§5.2.
`machine_source` is the equation between the GENERATED `src` and the loop. The tie to the original `quantModule` is
G3-DECL by construction. It is not counted as derived by the kernel.

**Step 1 is done.** `Tools/ShippingGen2Loop.lean` was built by `g2lp-84865a42` (exit 0, head = base). It contains:
- `machine_traceL_of_loop_causalRA_ranA` (A-boundary; `MachineRunJQC`, `bodyStepC_of_tele`/`htr_of_tele` through
  `genTraceL`; never `MachineRan`/`ServedReal`);
- `LoopFacts` (verbatim premise list);
- `SrcPkgL` (with `inh : ∀ i, Inhabited (α i)`, applied by `@`/`letI`);
- `genTraceL`, `letObsLoop_hl`.

Failed diagnostics:
- `g2lp-97db82ab`: INVALID. It was submitted after a failed generator script, with the target file missing.
- `g2lp-c3a564e1`: `Inhabited` for the `p.facts` projections.

**The exact step-2 interface is elaborated** as `Tools/ShippingGen2Pkg.lean` (ADDITIVE; nothing existing is changed).
Diagnostic `g2lp-cc71fc33`: exit 0, head = base; failed diagnostic `g2lp-ad1a6492`. Contents:
- `inductive Pkg (ι) (dom) | gen (p : SrcPkg ι dom) | loop (p : SrcPkgL ι dom)`.
- Accessors by cases, with exact types in the file: `Pkg.decl`, `d`, `kD`, `src`, `extS`, `extBS`, `lsrc`. Also
  `Pkg.ports` and `Pkg.S`, defined exactly as `SrcPkg.ports`/`S`.
- Theorems by cases, not fields:
  - `Pkg.ok : p.d.ok = true`;
  - `Pkg.body_eq`;
  - `Pkg.lsrc_hl` (the statement of `letObsB_hl` over `Pkg.lsrc`);
  - `Pkg.trace (O) (T) (hA) (p) (ran : MachineRunJQC O mctx cctx (D₀+1) p.decl p.d.shape m design) :
    MachineTraceLBX (ServedRealA O p.decl p.d.shape m design) p.decl p.d m design dom p.src p.extS p.extBS p.lsrc`.
- `Pkgs.lift P := fun c => (P c).map Pkg.gen`.
- `DataOkLiftCompat DataOk : Pkg → Prop`: the old `DataOk` on `.gen`, `False` on `.loop`. It is used ONLY by the
  compatibility tests and never restricts a real theorem.
- `rfl` checks: `(Pkg.gen p).extS/extBS/lsrc/ports/S = p.extS/extBS/lsrc/ports/S`.

**Refactor rule** (mechanical, file by file, per the §5.3 importer table):
- `SrcPkg ι dom` → `Pkg ι dom` in the generic definitions and theorems;
- `Pkgs` := `Name → Option (Pkg ι dom)`;
- `p.gen.ok` → `Pkg.ok p`, `p.gen.body_eq` → `Pkg.body_eq p`;
- `genTrace … p.gen ran` → `Pkg.trace … p ran`;
- `letObsB_hl` at a package → `Pkg.lsrc_hl p`;
- `letI := p.inh` is dropped where it only served those.

No new premise is added anywhere. If a proof needs one, it stops for review.

**Compatibility tests (rules, not one blanket claim).** `Tests/Gen2/PkgCompat.lean` uses the OLD texts copied from
f1a4367f under `namespace Old`.
- **Pointwise definitions** (`ChildShips`, `CallDec`, `MemDec`, `TopShips`, `MemOrigin`, `ExtInS`, `MemParentDataOk`, and
  `ShipsAt` at a lifted `P`): `X (.gen p) … = Old.X p …` by `rfl`. For `P`-taking definitions, `X (Pkgs.lift P) … ↔
  Old.X P …`.
- **Statements that quantify over all packages** (`MemParentStmt'`, `LeafStmt`, `StepStmt`, `T1Stmt`, `ServedShipsStmt`,
  `KeepBodyStmt`, `KeepChildStmt`):
  - the NEW statement implies the OLD one (`new → old`), by instantiating the package quantifier at `.gen p`;
  - or the NEW statement's body restricted to `.gen p` is equivalent to the old body.

  `old → new` is NOT claimed, because the new statements include the loop case.
- **`DataOk`-parameterised statements** (`StepStmt`, `LeafStmt`, `T1Hyp`): compared with `DataOkLiftCompat DataOk`.

**Focused verification** after the refactor:
- `Tests/Gen2/PkgCompat`;
- re-builds of U0Check, CallDecInstance, AdaptInstance and MemParentInstance through `Pkg.gen`;
- then step 3 (quantModule).

No full rebuild.
