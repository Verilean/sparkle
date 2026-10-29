# G-CALLDEC probe: frozen plan (rev1)

Issue `sparkle-gen2-calldec` (milestone `sparkle-gen2`).
- **Base:** `par/gen2-spec` (spec approved d622ad71; U0 approved, source 6bd02a3a).
- **Changes:** new Tools/Tests files plus lakefile registrations. No production or compiler change.

**Rev1** answers review b0c759da:
- R1: exact signatures and the classification of every premise (§2, §4).
- R2: three separate evidence levels, and no rescheduling without an approved revised plan (§5).
- R3: the real-instance proof is part of the acceptance; a missing connection is a blocker (§3).

## 1. Facts read from the sources (provenance, not proofs)
- **`CallDec p q k`** (Tools/ShippingGen2Defs.lean:104) is about ONE ordinary call `k`.
- **`CallFactF`** (Tools/ShippingQuadCalls.lean:223) quantifies EVERY call `k < insts.length`. Its per-call body equals
  the last conjunct of `CallDec`, when `outsC`/`S` are `pkgOutsC P`/`pkgS P i`.
- **`call_inRange`** (QuadCalls:112) gives `CallDec`'s `InRange` conjunct. Its inputs are `ok`, `kD ≤ bsIn.length`,
  `hIlen`, the slot count, `callsOk`, `callArgsOk d n widths` with the width table `hw`, the arity table `hlen`, and
  the let bound `hl`.
- **`letObsB_hl`** (QuadCalls:195) supplies `hl` for `lsrc := letObsB …`, which is `SrcPkg.lsrc`.
- **`ok_bsIn_length`** (QuadCalls:68) and **`c_callsOk_nIn`** (Tests/Compiler/C4ComposedTest.lean:124) give `hkD` and
  `hIlen` from `ok` and `callsOk`.
- **Instance provenance.** In instances, `CallFactF` is extracted from a generated per-design theorem
  (`oldGroupFact%` on `X.machine_composedNR2`: the facts `gfHb*`/`gfHv*`), then closed by `decoded_eq` and
  `fun τ => rfl`.
  - The generator defines `X.machineExt` by extending the input families at `nDecl + k` with the call term
    (Tools/ShippingMachineCommand.lean:2028-2073).
  - The header of `CallFactF` (QuadCalls:216-221) says it is not derivable from `GenFacts`. That is provenance
    guidance, not an impossibility theorem.
- **The typed decomposition already exists:** `HPointAt` (Tools/ShippingQuadHPoint.lean:15) and
  `callFactF_of_hPointAt` (:41). It is used below as the typed form of "ArgsDecode" and "ExtIsCall" (§4), so no new,
  untyped names are introduced.

## 2. Step 1 [proof]: the exact generic reduction
New file `Tools/ShippingGen2CallDec.lean`, `namespace Tools.ShippingGen2`, `set_option autoImplicit false`, with the
same opens as `Tools/ShippingGen2Connect.lean`, plus `open Tools.ShippingQuadCalls (CallFactF call_inRange ok_bsIn_length
letObsB_hl)` and `open Tools.ShippingPortsMatchRaw (callArgsOk)`.

```lean
variable {ι : Type} {dom : ι → DomainConfig}

theorem callDec_of_callFactF (P : Pkgs ι dom) (p q : SrcPkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hP : P (p.d.shape.insts[k]).1 = some q)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    -- (F) the output equation of EVERY call of p: a STRONGER sufficient input than CallDec's one call
    (hF : CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i))
    -- data of p
    (hok : p.d.ok = true) (hco : p.d.callsOk p.kD = true)
    (hslots : p.d.ss.length = p.d.shape.layout.slots.length)
    -- call tables of p against its callees' packages
    (widths : Nat → List Nat) (hargs : callArgsOk p.d p.kD widths = true)
    (hw : ∀ (k : Nat) (hk : k < p.d.shape.insts.length), widths k =
      ((pkgBsC P (p.d.shape.insts[k]).1).filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth)
    (hlen : ∀ (k : Nat) (hk : k < p.d.shape.insts.length), (p.d.shape.insts[k]).2.1.length =
      ((pkgBsC P (p.d.shape.insts[k]).1).filter fun b => b.2 != .domain).length)
    -- the arguments of call k are lets of p
    (hargsLets : ∀ (r : Nat) (hr : r < (p.d.shape.insts[k]).2.1.length), (p.d.shape.insts[k]).2.1[r] < p.d.ls.length) :
    CallDec p q k
```

| premise | supplier | status |
|---|---|---|
| `hk`, `hP`, `hnone` | the call (k valid, its package, an ordinary origin) | hypotheses of the caller (`StepStmt` per k) |
| `hF` | `CallFactF` of `p` | **hypothesis**. It is the G-CALLDEC content. In the instance (§3) it is an existing generated theorem |
| `hok` | `p.gen.ok` | package projection (proved in the probe as `p.gen.ok`; `hok` is kept explicit for readability) |
| `hco`, `hslots` | `DataOkB` rows | D rows (U0) |
| `widths`, `hargs`, `hw`, `hlen` | call/port tables of `p` and its callees | **hypotheses**, decidable per declaration pair. A new D row of call-pair data; it needs coverage (G-DATA) |
| `hargsLets` | candidate: derived from `callsOk` | **the probe tries to prove it from `hco`**. If that fails, it stays a hypothesis and is reported |
| `hkD`, `hIlen` (needed by `call_inRange`) | `ok_bsIn_length` + `c_callsOk_nIn` (restated generically) | proved in the probe |
| `hl` (needed by `call_inRange`) | `letObsB_hl` | proved (applied) |
| `CallDec`'s arity `args.length = q.ports.length` | `hlen` at `k` with `hP` | proved |

## 3. Step 2 [proof]: the real instance (part of this Issue's acceptance)
**Candidate:** `Tests.Compiler.SharedLeafGenTest.topshare2`, with callees `wrapQ`, `wrapP`, at `kD = 3`, in
Tests/Compiler/QuadCallsTest.lean. All of its suppliers exist in that file:
- `b_gen` (the parent's `GenFacts`, :289), `b_wrapQ_gen` (:297), `b_wrapP_gen` (:305);
- `b_topshare2_hFP : CallFactF topshare2.machineData 3 … (quadOutsOf …) (quadSrcF …)` (:387);
- the decided data facts of that file.

**Index mismatch, a frozen sub-step.** The parent's package is at `ι := Unit`, `dom := fun _ => defaultDomain`; the
callees' `GenFacts` are at `ι := DomainConfig`, `dom := id`. `SrcPkg`/`Pkgs` need ONE index.
- **Sub-step 2a [proof]:** `genFacts_restrict`, the restriction of a `GenFacts` at `(DomainConfig, id)` to
  `(Unit, fun _ => D₀)` by instantiating `i := D₀`. Every field is `∀ i …`, and `causal : HCausalOf …` is checked when it
  is written.
- **Sub-step 2b [proof]:** the packages `tm2Pkg`, `wQPkg`, `wPPkg` at `Unit`, the assignment `P2`, and the equations
  `pkgOutsC P2 = quadOutsOf …` and `pkgS P2 () = quadSrcF … ()` (by `funext` + `rfl`, or `simp`).
- **Sub-step 2c [proof]:** `CallDec tm2Pkg wQPkg k` / `CallDec tm2Pkg wPPkg k` for every ordinary call `k` of
  `topshare2`, by `callDec_of_callFactF`, together with `DataOk` of the three packages.

**If 2a fails** (`HCausalOf` does not restrict): this is a BLOCKER. A reviewed replacement plan is submitted: either
generalise `CallDec`/`Pkgs` to per-package index types (a GEN2_DEFS change, re-reviewed), or choose another candidate
whose parent and callees share an index. The probe is not counted as successful.

## 4. Step 3 [measure]: the generic route, at three evidence levels
**The typed interface.** "ArgsDecode" and "ExtIsCall" are the two halves of `HPointAt dP nP D lsrc ext extB outsC bsOf
src k` (QuadHPoint:15):
- **ArgsDecode:** its witnesses `A`, `B`, with `boolsOf (bsOf c) (valsOf lsrc args) = A` and `bitsOf … = B`. These are
  the decoded argument families.
- **ExtIsCall:** `∃ k' o f`, the output field, with `(src i c A B)[k']? = some f` and the `posEnc … (nP + k) … = f τ`
  equation.
- `callFactF_of_hPointAt` (QuadHPoint:41) turns one `HPointAt` per call into `CallFactF`.

**The levels, kept apart:**
- **(i) Observed implementation route** [read]. The generator's `machineExt` is the call term; the callee's
  `machineSource` is its own declaration's outputs; `gfHb*`/`gfHv*` are the decoded families of the arguments. These
  are reported with file:line. It is NOT evidence of a generic supplier.
- **(ii) Exact conditional bridge** [proof, in this probe]: `callFactF_of_hPointAt` instantiated at the package fields
  (`dP := p.d`, `lsrc := p.lsrc`, `ext := p.extS`, `src` from `P`). This gives `CallFactF` of `p` from `HPointAt` per
  call plus the dispatch equation `hS` (the `S` ↔ `src` tie).
  - It is stated and proved as `callFactF_of_hPointAt_pkg`.
  - It is conditional on `HPointAt`. That is the remaining G-CALLDEC content, tied to the same declaration, call index,
    arguments and callee package.
- **(iii) Generic construction correctness / coverage** [NOT in this probe]. A proof that, for every accepted
  declaration and every ordinary call, `HPointAt` holds of the actual generated package. That needs the
  correspondence between the call term in `d.shape.body` (`GenFacts.body_eq`), the let terms, and the callee's package,
  over the same `X.machineExt`.
  - The probe only reports what such a proof would need: the source ties, the size, and the existing generator
    lemmas.

## 5. Decision and acceptance (fixed now)
**Accept this Issue when all of these hold:**
- step 1 is proved with the §2 signature;
- step 2 is proved: 2a-2c, a real `CallDec` on `topshare2`;
- step 3 (ii) is proved;
- step 3 (i)/(iii) are reported;
- the reviewer approves.

**What acceptance does NOT do:**
- G-CALLDEC stays UNSUPPLIED in general.
- `T1Hyp.dec` keeps it as a named premise, now in the precise form `HPointAt` per call (via (ii) and step 1).

**Moving the generic supply (iii) to M5** (as G3-GEN-CALL) requires a revised dependency/acceptance plan that names:
- the exact obligation (`∀` accepted declarations and ordinary calls, `HPointAt` of the generated package);
- its source ties;
- its deliverable;
- its failure route.

That plan is submitted for reviewer approval BEFORE the roadmap is changed. A guarantee or scope change (for example,
keeping a per-declaration certificate in FG) goes to the user.

**Blockers:**
- If step 1 or 2 cannot be proved, the probe finishes as an investigation with a blocker report and a reviewed
  replacement plan. It is NOT accepted as a derivation.
- If `hargsLets` does not follow from `callsOk`, it is recorded as a further D row with its coverage obligation.

## 6. Builds
- `kjob -N sparkle-dev run --issue sparkle-gen2-calldec --name g2cd-<sha8> -n <node> -m 12Gi -c 4 -- kjob lake build sparkle_barrier sparkle_jit <target>`.
- **Targets:** `Tools.ShippingGen2CallDec`, `Tests.Gen2.CallDecInstance`. Exact head. Failed runs are recorded as
  diagnostics.

## 7. Not claimed
- No generic supply of `CallFactF` or `HPointAt`. No FG/T1/M2 completion. `CallFactF` is not renamed into a premise and
  called supplied.
