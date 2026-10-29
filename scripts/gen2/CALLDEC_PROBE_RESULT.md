# G-CALLDEC probe: result

Issue `sparkle-gen2-calldec`.
- **Plan:** scripts/gen2/CALLDEC_PROBE_FREEZE.md rev1, approved for implementation at 16c6ca4b.
- **Branch:** `par/gen2-spec`.
- **Changes:** new proof/test files (`Tools/ShippingGen2CallDec.lean`, `Tests/Gen2/CallDecInstance.lean`) and their
  lakefile registrations. No production or compiler change.

## Builds
| job | head = base | result |
|---|---|---|
| `g2cd-30ea37f1` | 30ea37f1 | exit 0: `Tools.ShippingGen2CallDec` (step 1, bridge (ii), 2a) |
| `g2cd-b09a2c0b` | b09a2c0b | **exit 0, 923 jobs**: `Tests.Gen2.CallDecInstance` (steps 2b-2c, axioms). Log SHA-256 prefix `9d5608e1b4cb4eba` |
| `g2cd-2c71c114`, `g2cd-81a6cad6` | — | failed diagnostics, instance file only: `SrcPkg.S` unfolding, the `kindTy` namespace, rewrites through `tm2Pkg.d` |

**Elaboration setting:** Tests/Gen2/CallDecInstance.lean sets `set_option maxHeartbeats 4000000` at file scope. That
is the same budget as the QuadCallsTest it imports. It is there for the `decide` of the three `DataOkB` checks and the
`simp` over the concrete `MachineData`. It is an elaboration budget only; the kernel checks the proofs as usual.

**Axioms** (`#print axioms`, `g2cd-b09a2c0b`): `callDec_of_callFactF`, `callFactF_of_hPointAt_pkg`, `genFacts_restrict`,
`tm2_callDec` and `tm2_dataOk` each depend only on `[propext, Classical.choice, Quot.sound]`. No `sorry`.

## Step 1: the generic reduction (PROVED)
`Tools.ShippingGen2.callDec_of_callFactF` (Tools/ShippingGen2CallDec.lean) has the frozen §2 signature with ONE
deviation: the premise `hargsLets` is REMOVED. It is derived by `callsOk_argsLets` from `callsOk`'s second conjunct
(`insts.all (·.2.1.all (· < ls.length))`, Tools/ShippingCallsShape.lean:106-108). The statement is therefore weaker in
its premises and the same in its conclusion. The final premises:

| premise | status in the proof |
|---|---|
| `hk`, `hP`, `hnone` | hypotheses (call `k` valid, its package, an ordinary origin) |
| `hF : CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i)` | **hypothesis**, about every call of `p`: a stronger sufficient input than one `CallDec` |
| `hok`, `hco`, `hslots` | hypotheses (a `GenFacts` field / `DataOkB` rows) |
| `widths`, `hargs : callArgsOk p.d p.kD widths = true`, `hw`, `hlen` | **hypotheses**: call/port tables of `p` against the callees' packages (D rows, coverage open) |

Derived inside the proof:
- `kD ≤ bsIn.length` and `hIlen`, by `callsOk_nIn` + `ok_bsIn_length`;
- the argument bounds, by `callsOk_argsLets` + `letObsB_hl`;
- the arity `args.length = q.ports.length`, from `hlen` with `hP`;
- `InRange`, by `call_inRange`;
- the output field and the equation, from `hF` at `k` with `hP`.

## Step 2: the real instance (PROVED)
**Instance:** `Tests.Gen2.CallDecInstance` (Tests/Gen2/CallDecInstance.lean), with parent `topshare2` and callees
`wrapQ`, `wrapP`.
- **2a:** `genFacts_restrict` restricts `b_wrapQ_gen` and `b_wrapP_gen` (at `(DomainConfig, id)`) to
  `(Unit, fun _ => defaultDomain)`. Every field, `causal` included, is a `∀ i` instantiated at `D₀`.
- **2b:** the packages `tm2Pkg` (`gen := b_gen`), `wQPkg` and `wPPkg`, all with `kD = 3`; the assignment `P2`; and
  `P2_outs`, `P2_bs`, `P2_S`, the equalities with `quadOutsOf`/`quadBsF`/`quadSrcF`.
- **2c:**
  - `tm2_hF : CallFactF tm2Pkg… (pkgOutsC P2) (pkgS P2 ·)`, from the existing `b_topshare2_hFP` rewritten by
    `P2_outs`/`P2_S`;
  - **`tm2_callDec : ∀ k (hk : k < tm2Pkg.d.shape.insts.length), ∃ q, P2 (insts[k]).1 = some q ∧ CallDec tm2Pkg q k`**;
  - `tm2_dataOk : DataOk tm2Pkg ∧ DataOk wQPkg ∧ DataOk wPPkg` (by `decide`).

**The instance's suppliers, all existing and named:**
- `b_gen`, `b_wrapQ_gen`, `b_wrapP_gen`: the generated `machine_*` facts;
- `b_topshare2_hFP`: `CallFactF`, extracted from the generated `topshare2.machine_composedNR2` group facts
  `gfHb*`/`gfHv*`;
- `b_quadAll`: the decided data facts, including `callArgs`, `argsN`, `hNIn`, `child` and `c12`.

The instance is a valid instance test. It is NOT generic coverage.

## Step 3
### (ii) Conditional bridge (PROVED)
`callFactF_of_hPointAt_pkg (P) (p) (hH : ∀ k < insts.length, HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P)
(pkgBsC P) (pkgSrc P) k) : CallFactF … (pkgOutsC P) (pkgS P ·)`.
- The dispatch equation `pkgS P i c vals = pkgSrc P i c (boolsOf (pkgBsC P c) vals) (bitsOf …)` is PROVED
  (`pkgS_dispatch`).
- The bridge is conditional on the COMPLETE `HPointAt` of every call.

**Interpretation (review 16c6ca4b, point 1).** `HPointAt`'s witnesses `A`, `B` can always be chosen as the decoded
families `boolsOf …`/`bitsOf …`. So its first two conjuncts carry no information on their own. The content that ties
the generated call is the combined output relation: the callee's `src` on `A`, `B` equals, at every time, the parent's
`ext` at `nDecl + k`. Nothing here claims that the decoding half solves anything.

### (i) Observed implementation route (read; not evidence of a generic supplier)
- **The parent's `X.machineExt`/`machineExtB`:** the input families extended at `nDecl + k` by the call TERM
  (`combCallsProof`, Tools/ShippingMachineCommand.lean:2028-2073; the other endpoint shapes use the same
  `extName`/`extBName` construction at :1174, :1737, :1924).
- **The callee's `machineSource`:** the observed outputs of its own declaration.
- **The facts `gfHb*`/`gfHv*`:** components of the generated `X.machine_composedNR2`. They state that the decoded let
  observations at the call's arguments are the argument families of the call term. With them, `decoded_eq` + `rfl`
  close the output equation (QuadCallsTest:77-100).

### (iii) Generic construction correctness / coverage: NOT proved
**The required statement:** for every accepted machine-route declaration `X` with generated package `p` and every
ordinary call `k` to `c` with package `q = P c`, `HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P)
(pkgSrc P) k`.

**The source ties it needs:**
- (t1) `p.ext` at `nDecl + k` is the call term of `X`'s body. This is the generator's construction (i), and it is not
  a `GenFacts` field.
- (t2) The call term applies `c` to arguments that are let-bound in the body. Their values are the let observations
  `p.lsrc` at `args`; that is the `gfHb*`/`gfHv*` content. It relates `body_eq`'s quoted body to `letObsB`.
- (t3) `c`'s Lean meaning on those arguments is `q.src` on the decoded families. That is G3-DECL for `c`: `src` is
  `c`'s own observed outputs, and the probe has only an `rfl` instance of it.

**Size and existing pieces:**
- (t3) is per declaration by construction.
- (t1) and (t2) are what the generator produces as `machine_composedNR2` today. A generic proof needs the generator's
  call-term reading as a lemma over `MachineShape`/`body_eq`. No such lemma was found.

## Status of G-CALLDEC after this probe
- G-CALLDEC is **UNSUPPLIED in general**.
- `T1Hyp.dec` and `CallDec` are UNCHANGED (review point 2).
- The probe provides a SUPPLIER DECOMPOSITION. `CallDec` follows from `callDec_of_callFactF`, whose `hF` follows from
  the complete `HPointAt` per call (`callFactF_of_hPointAt_pkg`).
- `hF` is not the whole gap. The tables `widths`/`hargs`/`hw`/`hlen` (call-pair data) stay explicit D rows with open
  coverage, next to the U0 rows (outHead → N1 obligation).

## Proposed roadmap change (for review; NOT applied)
**G3-GEN-CALL**, a sub-obligation of M5 G3-GEN:
- **Obligation:** the (iii) statement above, for every accepted machine-route declaration and ordinary call.
- **Source ties:** (t1)-(t3).
- **Deliverable:** a generic lemma from the generator's call-term reading (over `MachineShape` and `body_eq`) to
  `HPointAt` of the generated package, with the C4/C5/topshare2 instances as checks.
- **Failure route:** if (t2) cannot be stated generically from `body_eq`, the alternative is a generator export: a
  kernel-checked theorem with a uniform statement, emitted for every declaration. Whether this changes the guarantee
  depends on what is proved. The cases are evaluated separately before any user decision:
  - (a) Every successful compilation provably produces that certificate, and its connection to the same source and
    result is proved. Then it is existential evidence eliminated inside FG, and the guarantee does not change.
  - (b) The certificate's availability is an unproved premise. That is a guarantee change.
  - (c) The accepted sources are restricted to those with a certificate, or the compiler's successful-source domain
    changes. That is a scope change.

  Neither generic coverage nor any certificate route is proved here.
- **Effect on M2:** `StepStmt` keeps `CallDec` as a premise (unchanged). M2's acceptance text on G-CALLDEC would read
  "supplied by `callDec_of_callFactF` + `callFactF_of_hPointAt_pkg` from `HPointAt` + D rows; generic `HPointAt` = M5
  G3-GEN-CALL".

## Not claimed
- No generic supply of `CallFactF`/`HPointAt`/`CallDec`. No FG/T1/M2 completion.
- The instance proves one parent's calls. It is not coverage.
