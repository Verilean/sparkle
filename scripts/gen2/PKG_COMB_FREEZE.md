# `Pkg.comb`: package for slotless, call-free machine-route declarations — freeze rev1 (FOR REVIEW)

- **Issue:** `sparkle-gen2-step` (G-SLOTLESS).
- **Status:** design direction approved after the S2 stop-report. This is an INDEPENDENT freeze; no existing `Pkg`/Defs edit before approval.
- **Source:** read-only survey at par/gen2-spec 9b544350.

## 1. What the generator actually emits (`generateCore`, MachineCommand.lean:2507, branch `slots.isEmpty` → `combProof` :2008-2024)
For `pickByteH` (ι = `Unit`: no domain binder, :2532):
- `machineData : MachineData`;
- `machineInits : HList (tys machineData.ss) := ()`;
- `machineSource i bools bits := resultObsOf … (pickByteH (bits 0 16) (bits 1 2))`: the Lean source's own observations (:2017-2019, :626-643, :2556);
- `machine_ok`, `machine_body`, `machine_inits`, and
  `machine_next : ∀ i bools bits t, machineInits = evalTerms (…typedVal… bools bits t machineInits…) d.nexts`;
- **`machine_result : ∀ i bools bits t, (machineSource i bools bits).map (· t) = d.outs.map (fun o => enc o.1 (eval (…typedVal… bools bits t machineInits…) o.2))`**. This is the SOURCE ↔ IR TIE. Each fact is an `Eq.refl` checked by the kernel against the elaborated declaration (`reflProof`, :618-622), the same kind as `GenFacts.source/result`.
- old-boundary endpoints `machine_sound`, `machine_ships_comb` (:2709-2728, through `machine_traceL_of_comb` with `lsrc := fun _ _ _ => []`), `machine_closes`, `machine_child`, `machine_combKid`, `machine_combPos`.

**What `SlotlessLeaf`/`CombKid` are.** They are STRUCTURAL conditions, not the source trace (review). The source meaning comes from `machine_result` alone.

## 2. Exact definitions (new file `Tools/ShippingGen2CombPkg.lean`)
```lean
structure CombFacts (d : MachineData) {ι : Type} (dom : ι → DomainConfig) (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop where
  ok : d.ok = true
  hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
            (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  hinit : d.initOk inits = true
  hnext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
    inits = evalTerms (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).b (d.bpos j))
      (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).v (d.vpos j) w) d.nexts
  hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
    (src i bools bits).map (fun g => g t) =
      d.outs.map fun o => enc o.1 (eval (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).b (d.bpos k))
        (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).v (d.vpos k) w) o.2)

structure CombPkg (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  inits : HList (tys d.ss)
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)
  facts : CombFacts d dom inits src

def CombPkg.extS  (p : CombPkg ι dom) := fun (i : ι) (_ : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) => bits
def CombPkg.extBS (p : CombPkg ι dom) := fun (i : ι) (bools : Nat → Signal (dom i) Bool) (_ : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) => bools
noncomputable def CombPkg.lsrc (p : CombPkg ι dom) := letObsComb p.d dom p.inits (fun i _ bits => bits) (fun i bools _ => bools)
```
- **`src` is NOT the IR meaning.** It is the declaration's elaborated observations, `machineSource`. `hres` ties it to the IR, so the Lean-source correspondence is not skipped (review).
- **`lsrc` is the let observations,** not `[]` (`letObsComb`, SeqLinked.lean:138-149). That is required by `Pkg.lsrc_hl` (Pkg.lean:91-99), since `pickByteH` has lets.

## 3. The A-boundary adapter (same run, same witness)
```lean
theorem machine_traceL_of_comb_callsRA_ranA (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O) (hA : AdmCtx O.quiet mctx cctx)
    {n : Nat} (htr : ∀ tenv e hint top named, KeepsCP mctx mref cctx cref (JQC O n) (translateExprToWire tenv e hint top named))
    (d) (dom) (inits) (src) (hF : CombFacts d dom inits src)
    (ran : MachineRunJQC O mctx cctx n declName d.shape m design) :
    MachineTraceLBX (ServedRealA O declName d.shape m design) declName d m design dom src
      (fun _ _ bits => bits) (fun _ bools _ => bools) (letObsComb d dom inits (fun _ _ bits => bits) (fun _ bools _ => bools))
```
- **Proof:** a copy of `machine_traceL_of_comb_callsRA_ran` (SeqLinkedR.lean:195-237), with `machine_trace_lets_of_streamBRA_ranA O hB hA htr …` (ServedRealATrace.lean:36-80, built) in place of `_streamBRA_ran`. The witness is `⟨fun _ => inits, rfl, hnext, hres, letObsComb …⟩`. No causality premise is needed, since `ext` does not read a state signal.
- **The wrapper `combTrace O T hA p ran`:** `bodyStepC_of_tele O T` and `htr_of_tele O hA T D₀`, as in `genTrace` (QuadComposed:156-182) and `genTraceL` (Gen2Loop:212-218). It uses the SAME `ran`.
- **Not reused:** `machine_traceL_of_comb` (old `RunsTo`/`MachineCloses`, `lsrc = []`).

## 4. The `Pkg` change (applied only after approval)
- **The constructor:** `Pkg := gen SrcPkg | loop SrcPkgL | comb CombPkg`.
- **New `.comb` cases:**
  - in Gen2Pkg.lean: the accessors `decl`/`d`/`kD`/`src`/`extS`/`extBS`/`lsrc`, and `Pkg.ok`, `Pkg.body_eq`, `Pkg.lsrc_hl` (proof: `List.getElem?_map` + `enc_lt`, as `letObsLoop_hl`), `Pkg.trace` (`combTrace`);
  - `DataOkLiftCompat`: `.comb _ => False`, compatibility tests only;
  - `Pkg.src_length` (Gen2CombKid.lean:56): from `facts.hres … 0` + `List.length_map`.
- **Generic, unchanged** (surveyed: no other `cases` on `Pkg`): every Defs statement, `LeafStmt'`/`leaf_ships`, `SlotlessLeafStmt`/`slotlessLeaf_ships`, `slotless_closed_ofRun`, MemTop/`memParent_ships`, CallDec/Adapt.
- **Compatibility.** Every statement quantified over all packages now also ranges over `.comb`. Existing proofs of such statements were per-constructor only through the accessor theorems above, so they extend once the `.comb` cases exist. PkgCompat's `.gen` checks are unchanged. Every proved `∀ p : Pkg` statement is rebuilt.

## 5. Probe / instance (`Tests/Gen2/CombPkgInstance.lean`)
- **The package:** `pbhC : CombPkg Unit (fun _ => defaultDomain) := { decl := ``pickByteH, d := pickByteH.machineData, kD := pickByteH.machineData.bsIn.length, inits := pickByteH.machineInits, src := pickByteH.machineSource, facts := ⟨machine_ok, machine_body, machine_inits, machine_next, machine_result⟩ }`.
- **The data:** `LeafDataOk (.comb pbhC)` by `decide`, `ExtInS` by `rfl`, `insts = []`/`slots = []` by `decide`, `d.ls ≠ []` decided (non-vacuity of `lsrc`).
- **The application:** `slotlessLeaf_ships`, the S2 lemma (still under review), applied to `.comb pbhC`.
- **RESIDUAL hypotheses:** `hA`, `JQC … (dv w) w`, the core `RunsTo`, `hpost`, `MachineDefines` (reflection), `MachineTaken` (route evidence). For T1, `MachineClosesAtA`: the generated `machine_closes` is old-boundary, and whether an A-boundary lift exists is open.

## 6. Scope and stop conditions
- **Scope.** Call-free, slotless, machine-route declarations. NOT covered here:
  - multi-output/slotless parents (separate coverage, S5);
  - gate leaves (M4 producer);
  - declarations transported by sign normalisation. `machineSourceDecl` has no named equation to `machineSource`, because `heq` lives only inside `machine_sound` (:2633-2645). For them the package `src` would be the rewritten value: a stop condition, recorded.
- **Stops:**
  - `machine_next`/`machine_result` do not fit `CombFacts` by defeq;
  - `LeafDataOk` fails for `pickByteH`.

  Either is reported, not patched.
- **The goal.** Extending the general theorem's reach. The instance is a check, not completion; G-SLOTLESS completion still needs the parents' consumers.
