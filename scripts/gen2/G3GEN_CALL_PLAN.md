# G3-GEN-CALL: dependency and acceptance plan (rev1, proposal for review; nothing applied)

Requested by the approval of `sparkle-gen2-calldec` (5c1b78a1). Rev1 answers review 86e98a51.
- **Kept unchanged until approval:** G-CALLDEC is UNSUPPLIED in general; M2's text, `T1Hyp.dec`, `CallDec` and the
  t1/t2/t3 placement are only PROPOSED.
- **R1:** a POINTWISE adapter per ordinary call (§1). No all-ordinary restriction, and memory calls never need
  ordinary packages.
- **R2:** the obligations are bound to generated packages and successful runs. Relations that are not yet designed are
  NAMED, and their design is a prerequisite (§2). There is a run-local route to `StepStmt` (§3).

## 1. The pointwise adapter (unit U-ADAPT, placed BEFORE any use of the decomposition in M2-b)
The accepted bridges are global over all calls (`callFactF_of_hPointAt_pkg`, `callDec_of_callFactF`, `call_inRange`).
For a mixed parent, the adapter goes per call. Exact interfaces (`namespace Tools.ShippingGen2`, opens as in
Tools/ShippingGen2CallDec.lean):

```lean
/-- The k-th slice of `callArgsOk` (Tools/ShippingPortsMatchRaw.lean:199), against a width list `ws`. -/
def callArgsOkAt (d : MachineData) (nDecl k : Nat) (ws : List Nat) : Bool :=
  (List.range ws.length).all fun j =>
    decide ((((d.shape.insts[k]?).bind fun c => c.2.1[j]?).bind fun a =>
      (d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]?).map
        fun bn => (kindTy bn.2).bitWidth) = ws[j]?)

/-- A callee package's declared non-domain port widths. -/
def SrcPkg.portWidths (q : SrcPkg ι dom) : List Nat := q.ports.map fun b => (kindTy b.2).bitWidth

/-- Local `InRange` (the per-k body of `call_inRange`, QuadCalls:112-150, with local tables). -/
theorem call_inRange_at (p q : SrcPkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hok : p.d.ok = true) (hco : p.d.callsOk p.kD = true)
    (hslots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hargsK : callArgsOkAt p.d p.kD k q.portWidths = true)
    (hlenK : (p.d.shape.insts[k]).2.1.length = q.ports.length)
    (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    ∀ τ, InRange (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1 τ) q.ports

/-- **The pointwise adapter**: one ordinary call's COMPLETE `HPointAt` (output relation included) and local data
give `CallDec` at that call. No fact about any other call is used. -/
theorem callDec_of_hPointAt_at (P : Pkgs ι dom) (p q : SrcPkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]).1 = some q)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hH : HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k)
    (hok : p.d.ok = true) (hco : p.d.callsOk p.kD = true)
    (hslots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hargsK : callArgsOkAt p.d p.kD k q.portWidths = true)
    (hlenK : (p.d.shape.insts[k]).2.1.length = q.ports.length) :
    CallDec p q k
```

**Memory calls** are handled entirely by `MemDec` (G-MEMCALLS, M2-a). They need no package in `P`, and the adapter is
never applied to them. `hw` (the global width table) is NOT needed by the adapter. It is PLANNED as a one-line lemma
only for the existing global route, and is not proved.

## 2. The obligations, bound to generated packages and successful runs
### 2.1 Relations that are named now and designed first (prerequisite design unit D-GEN, before any proof below)
- **`Generated X p : Prop`.** `p` is THE package the generator produces for `X`:
  - `p.decl = X`;
  - `p.d` is the reader's data for `X`'s shape, the same shape as `MachineDefines … X p.d.shape`;
  - `p.ext`/`p.extB`/`p.src`/`p.body` are the generator's terms (the construction of
    Tools/ShippingMachineCommand.lean:1174, :1737, :1924, :2028-2073).

  To be designed as a Prop over the reader's output. It must not be a semantic field.
- **`ClosingRun O mctx cctx X p raw D` : Prop.** A successful machine-route run of `X` (`MachineTaken`), with emitted
  `raw` in `D`, and the `ids`/`cache` witness of its trace. That is `MachineTraceLBX` with `MachineWired`, as already
  produced by the run.
- **`PortTie p k mc` : Prop** (the module-port / source-package correspondence; to be designed). For the instance of
  ordinary call `k` in `raw`, served by child module `mc`, the `argPorts mc` widths equal the widths of `p`'s binders
  for the lets `args[k]`, and their count equals `args[k].length`.
  - It relates EMITTED modules to SOURCE binder widths.
  - `connsG` only builds name connections, and `closeInstsG`/`stmtsG` act on emitted modules. `PortTie` is therefore
    NOT implied by the closing checks without a proof. It is a lemma to be found or proved.

### 2.2 The conditional statements (over admissible packages and runs; never over arbitrary packages)
- **G3-GEN-CALL (static, generator; M5):**
  ```
  ∀ X p, Generated X p → ∀ mctx cctx, AdmCtx … → MachineDefines … X p.d.shape →
    ∀ P, (∀ c q, P c = some q → Generated c q) → ∀ k (hk : k < p.d.shape.insts.length),
      (p.d.shape.instOrigins.getD k .ord).child? = none → ∀ q, P (p.d.shape.insts[k]).1 = some q →
      HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k
  ```
  Parts: t1 (the generated `ext` at `nDecl + k` is the call term), t2 (the call term's arguments are the let
  observations at `args`, from `body_eq` and the reader's call entries), t3 (the callee's `src` is its own outputs).
  Each is a lemma about `Generated`.
- **G-DATA-CALL (run-local; candidate route, M3):**
  ```
  ClosingRun … X p raw D → ∀ k ordinary, ∀ mc served to call k (ServedP's correspondence), ChildShips q n mc Dc →
    PortTie p k mc → callArgsOkAt p.d p.kD k q.portWidths = true ∧ (insts[k]).2.1.length = q.ports.length
  ```
  It needs `PortTie` and `ChildShips`'s port conjunct (`(argPorts mc).length = q.ports.length`) together with the
  child's port widths equal to `q.portWidths`. That last fact is a further lemma to be designed (child module ports ↔
  its package).

### 2.3 Early read-only analysis (before M3; unit D-PORT)
Locate or refute, in the sources, the `PortTie` correspondence. It runs from the closing's instance statement
(`connsG mc argWs outs outWs`, the `argWs` wire names) to the parent's let wires, their declared widths
(`declWidth`), and the source binder widths in `p.d.shape.binders`. Report the existing lemmas (MachineWired fields,
the width link `hWd_of_wired`, Srm32Width.lean:28) and the missing ones. Measurement only.

## 3. How run-local data reaches the one-level rule
- **What is static and what is not.** `T1Hyp.dec` is a static `∀` over reached packages and calls. The data rows of
  §2.2 are RUN-LOCAL. `StepStmt` already takes its per-entry decodings INSIDE the run context: its premise is stated
  for the run's `p` and the trace.
- **Proposed amendment (reviewed separately, not applied).** Split `T1Hyp.dec` into:
  - `T1Hyp.decH`: static — the `HPointAt` of every ordinary call, and `MemDec` of every memory call;
  - G-DATA-CALL: run-local, applied INSIDE the T1 induction step to the run at hand.

  The step then has `ClosingRun` (from `MachineTaken` and the trace), the served `mc` (G-SERVED) and the child's
  `ChildShips` (IH). G-DATA-CALL gives the local rows, and U-ADAPT gives `CallDec`.
- **No circularity.** The data rows come from the run and the IH, never from `T1Hyp.dec`. If G-DATA-CALL fails, the
  rows stay static `T1Hyp` data premises with their coverage obligation (G-DATA), and nothing is assumed silently.

## 4. Placement, deliverables and acceptance (proposed)
| unit | milestone | deliverable | accept |
|---|---|---|---|
| U-ADAPT | M2-b (first) | `callArgsOkAt`, `SrcPkg.portWidths`, `call_inRange_at`, `callDec_of_hPointAt_at` | proved; the topshare2 instance re-derived pointwise (k by k, its own `HPointAt` per k from `b_topshare2_hFP`'s per-call content) |
| D-GEN | M5 (first) | `Generated` designed | reviewed design |
| D-PORT | before M3 | `PortTie` analysis | report |
| G-DATA-CALL | M3 | the run-local statement of §2.2 | proved, or a reviewed consumer that uses the closing's actual port widths |
| G3-GEN-CALL t1/t2/t3 | M5 | the static statement of §2.2 | proved for every `Generated` package; closure audit: the C4/C5/topshare2 parents re-derived without their `CallFactF`/`b_*_hFP` theorems |
| `T1Hyp` amendment | M3 freeze | `decH` + run-local data | reviewed |

`hw` (the global table) is planned as a definitional lemma for the existing global route only, and is not proved.

## 5. Failure routes (evaluated separately before any user decision)
- **t2 is not stateable from `body_eq` and the reader:** a generator-exported, kernel-checked, uniform theorem.
  - (a) Every success provably comes with it, tied to the same source and result: evidence eliminated inside FG, no
    guarantee change.
  - (b) Its availability is unproved: a guarantee change.
  - (c) Sources are restricted to those with it: a scope change.
- **`PortTie` is false for some successful run:** that is a counterexample to G-DATA-CALL's route, not to FG. Use a
  consumer stated over the emitted ports. A scope change goes only through the user.

## 6. Roadmap effect (only after approval)
- **M2:** U-ADAPT first in M2-b. G-CALLDEC is described as reduced, never as supplied.
- **M3:** D-PORT, G-DATA-CALL and the `T1Hyp` amendment.
- **M5:** D-GEN and G3-GEN-CALL t1/t2/t3.
