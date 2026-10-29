# G-CALLDEC probe: frozen plan

Issue `sparkle-gen2-calldec` (milestone `sparkle-gen2`).
- **Base:** `par/gen2-spec` (spec approved d622ad71; U0 approved, source 6bd02a3a).
- **Changes:** new Tools/Tests files plus lakefile registrations. No production change.

## Question
Where does `CallDec p q k` (GEN2_DEFS §3; GENERAL_SPEC §4.2) come from for a real generated parent, and what is a
GENERIC supplier for it?

## What the sources already show (read, not proved)
- **What `CallDec` adds to `CallFactF`.** It is `CallFactF` (Tools/ShippingQuadCalls.lean:223) at call `k`, plus:
  - (a) the arity `args.length = q.ports.length`;
  - (b) `args[r] < d.ls.length ∧ ∃ g, lsrc[args[r]]? = some g`;
  - (c) `InRange`.

  (c) is derived by `call_inRange` (QuadCalls:112) from data: `ok`, `callsOk`, `callArgsOk` with port widths, and the let
  bound.
- **Provenance of `CallFactF` in instances.** For example `a_topshare_hFP`, Tests/Compiler/QuadCallsTest.lean:77:
  - the decoded-argument facts `gfHb*`/`gfHv*` are extracted (`oldGroupFact%`) from the GENERATED per-design theorem
    `topshare.machine_composedNR2`;
  - then `decoded_eq` and `fun τ => rfl`.
- **The header of `CallFactF`** (QuadCalls:216-221) says it is "NOT derivable from `GenFacts`".
- **Why the output equation closes by `rfl`.** The generator defines `X.machineExt`/`machineExtB` by extending the
  input families at the call positions with the call TERM itself (`combCallsProof`, Tools/ShippingMachineCommand.lean:2028-2073:
  `extendBits D eV (nDecl + k) w term`). The callee's `machineSource` is its own declaration's observed outputs. So
  once the decoded families equal the call's actual arguments, the equation is definitional.
- **What `CallDec` therefore needs, beyond data:**
  - **ArgsDecode:** the decoded let observations at the call's arguments ARE the call term's argument signals (the
    content of `gfHb*`/`gfHv*`);
  - **ExtIsCall:** the parent's `ext` at `nDecl + k` IS the call term. This is definitional for generated packages.

## Probe steps
1. **[proof] Generic reduction.** `callDec_of_callFactF` (new, `Tools/ShippingGen2CallDec.lean`):
   ```
   CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i) → P (insts[k]).1 = some q →
   (origin k).child? = none → (data: callsOk, callArgsOk widths, arity, let bound) → CallDec p q k
   ```
   This turns G-CALLDEC into exactly `CallFactF` plus data, with (c) by `call_inRange`.
2. **[proof] Non-vacuity instance.** `CallDec` for the calls of one real generated parent, from its existing
   `CallFactF` theorem and step 1. The candidate is `Tests.Compiler.SeqDeepGenDiffTest.topshare` with
   `a_topshare_hFP`, if the callees' packages (their `GenFacts`) exist. Otherwise the first parent in
   `Tests/Compiler/QuadCallsTest.lean` whose callees have them.
   - If none exists, step 2 reports that, and the instance moves to M2-b.
3. **[measure] Generic route.** State `ArgsDecode p k` and `ExtIsCall p k` as Props over the package.
   - **Probe A:** whether they follow from `GenFacts` (`writes`, `result`, `causal`) together with the call term
     quoted in `d.shape.body` (`body_eq`), with no per-design fact. The expected answer, by the header above, is NO.
   - **Probe B:** whether they hold by construction for a GENERIC package construction that defines `ext` by the call
     term and `lsrc` by the let terms. That construction is G3-GEN.
   - Report the route, its size and the missing pieces.

## Decision rule (fixed now)
- **If (1) and (3B) hold:** G-CALLDEC is a component of G3-GEN.
  - It is re-scheduled from M2 to M5 (G3-GEN) as an explicit sub-obligation `G3-GEN-CALL` (ArgsDecode/ExtIsCall).
  - It stays a NAMED premise of `T1Hyp.dec` until M5 discharges it.
  - This is a re-sequencing. FG and its guarantee are unchanged, M5 completion still requires it, and it is NOT a
    settlement.
  - The M2 goal text is updated to say that G-CALLDEC is supplied by `callDec_of_callFactF` from `CallFactF`, whose
    generic supply is `G3-GEN-CALL`.
- **If (3B) fails** (no generic construction gives ArgsDecode): this is a BLOCKER. A revised route is proposed: a
  generator export, or a compiler-side certificate, with impact, cost and recommendation.
  - If the route changes the guarantee (a per-declaration certificate in FG), it goes to the user before anything is
    accepted.

## Builds
- `kjob -N sparkle-dev run --issue sparkle-gen2-calldec --name g2cd-<sha8> -n <node> -m 12Gi -c 4 -- kjob lake build sparkle_barrier sparkle_jit <target>`.
- Exact head, focused targets only. Failed runs are recorded as diagnostics.

## Not claimed
- No derivation of `CallFactF` from `GenFacts` is claimed (its header says it is not derivable).
- Step 3 is a measurement until it has a proof.
- No FG/T1/M2 completion.
