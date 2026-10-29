# M5 lead: G3-GEN-CALL t2 — route freeze rev1 and kernel probe plan (FOR REVIEW)

Issue `sparkle-gen5-t2probe`.
- **Plan:** LEAD_UNITS_PLAN.md (cf029631).
- **Survey:** read-only. All file:line references are at par/gen2-spec HEAD.
- **Status:** no Lean yet; the probe is planned in §4.

## 1. What t2 is, against the actual generator
- **The obligation.** G3-GEN-CALL (G3GEN_CALL_PLAN.md §2.2) needs, for each ordinary call `k` of a generated package `p`, `HPointAt … k`.
- **The parts.**
  - t1: the generated `ext` at `nDecl + k` is the call term.
  - t2: the call term's arguments are the let observations `p.lsrc` at `args[k]`.
  - t3: the callee's `src` is its own outputs.
- **The generator** (Tools/ShippingMachineCommand.lean).
  - `combCallsProof` (:2028) takes `callEntriesG senv inst` (:2038, def :1228): each call term is a Lean `Expr` subterm of the instantiated source body.
  - It places each term with `extendBits`/`extendBools` at `nDecl + k` (:2047-2052) and `addDef X.machineExt` (:2059-2063).
  - Calls over the state go through `instExtension` (:729-783) and `collectInsts` (:716, zeta-reduced).
- **Today's t2 evidence is per declaration.** `gfHb*`/`gfHv*` are tactic proofs inside `proveGroup` (Tools/ShippingMachineDepthCommandR.lean:352, :406, :432-444, :718-778).
  - They unfold `X.machineExt`, locate the call with `sigAtPos`/`findCall` (Tools/ShippingMachineSeqCommand.lean:103-125), and close by `decB/decV_valsOf … rfl`.
  - The load-bearing step is `decV_valsOf`'s `hl : lsrc[args[q]]? = some (fun τ => (B.val τ).toNat)` (Tools/ShippingMachineCallsLinkedT.lean:299-302). It is discharged by kernel `rfl` between the IR evaluation of `d.ls[a]` and the source argument term `B`.
  - SR19 already emits `P.epD2M_hPoint{k} : HPointAt …` per call (Tools/ShippingSeqParentGenD2MSG.lean:123-170). It does so opt-in (`sparkle.sharedLeafCandidate`), for class QUAD only, and falls back silently (Tools/ShippingSeqParentGenD2MS.lean:37-48).

## 2. Finding: t2 has no generic derivation from the reader's data (read-only; to be kernel-checked by P2)
- **`body_eq` only equates two reader outputs.** `d.shape.body = quote d.dom … d.packed` (QuadComposed.lean:121) is syntax. No lemma gives a `Lean.Expr` a meaning.
- **`GenFacts` does not pin a let that only feeds call arguments.** `GenFacts.writes/result/source` (:125-149) tie the Lean `body` to the IR only through `d.nexts`/`d.outs`. A call output is an input position `nDecl + k`, so its argument lets enter neither.
- **`machineExt`/`machineBody`/`machineSource` are elaborated Lean terms, not functions of `MachineData`.** `SrcPkg.ext/body/src` are free fields constrained only by `GenFacts`.
- **Consequence:** a package with the same `d` but rewired to another callee of the same widths satisfies `GenFacts` and violates `HPointAt` (P2).
- **Status:** t2, like `GenFacts` itself, is a per-declaration kernel fact of the generator. Today the only links are per-declaration `rfl`s.

## 3. The exact unsupplied Prop and the `Generated` fragment it needs
```lean
/-- t1+t2 together: the parent's call-result signal at `kD + k` factors through the let observations at the
call's arguments. -/
def CallFactors (p : SrcPkg ι dom) (k : Nat) (G : (i : ι) → (Nat → List Nat) → Nat → Nat) : Prop :=
  ∀ i bools bits τ,
    posEnc (fun q => (p.extBS i bools bits q).val τ) (fun q n => (p.extS i bools bits q n).val τ)
      (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain)
    = G i (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1) τ

/-- The per-let tie the generator's `rfl`s establish (t2 proper). -/
def LetTie (p : SrcPkg ι dom) (k : Nat) (callArgs : (i : ι) → … → List (Signal …)) : Prop :=
  ∀ i bools bits q (hq : q < ((p.d.shape.insts[k]).2.1).length),
    (p.lsrc i bools bits)[((p.d.shape.insts[k]).2.1)[q]]? = some (fun τ => enc ((callArgs i bools bits)[q]) τ)
```
- **The exact form of `LetTie`** (the type of `callArgs`, `enc` for Bool/BitVec arguments) is fixed by the probe from `decB_valsOf`/`decV_valsOf`'s premises.
- **t3 then reads:** `G i vals = ((pkgS P i c vals)[k']?).getD 0`, with `o.name = instFields.getD k ""`. With `pkgS_dispatch` this gives `HPointAt`, the witnesses being the decoded families.
- **The fragment of `Generated X p` needed:** `p.ext = X.machineExt` (t1, by unfolding), `p.lsrc` from `X.machineData`, and `LetTie p k (X's call argument terms)` for every ordinary `k`.

## 4. Kernel probe (small; own worktree from reviewed base 1fdbc18d; new files only)
- **P1, positive generic conditional lemma** `hPointAt_of_ties` (new, `Tools/ShippingGen2T2Probe.lean`).
  - Premises:
    - t1 as `extS … (kD+k) w = F i (callArgs …)`, via `extendBits_of_ne` (QuadCallFacts.lean:91) and `extendBits_val`;
    - t2 as `LetTie`;
    - t3 as the callee field.
  - Conclusion: `HPointAt …` (or `CallDec` through U-ADAPT `callDec_of_hPointAt_at`).
  - Proof by existing lemmas only: `decB/decV_valsOf`, `boolsOf_at`/`bitsOf_at`, the absorb chain `extendBools_absorb`/`extendBits_absorb`, `decoded_eq`.
- **P1 application** to two existing declarations (`wrapQ` call 0, `topshare2` call 0), with t1 by `unfold …machineExt; rfl`, `LetTie` by per-argument `rfl` and t3 by `rfl`. It uses NO `oldGroupFact%`/`gfHb*`/`b_*_hFP`.
  - **What it shows:** t2 reduces exactly to the per-let `rfl`, and the rest of the chain is generic.
- **P2, negative** (`Tests/Gen2/T2Neg.lean`). A `SrcPkg` with `topshare2.machineData` and `body`/`ext`/`src` rewired to a different callee of the same widths.
  - Prove `GenFacts` (by the generated facts / `rfl`).
  - Prove `¬ HPointAt … 0` by `decide` at one time and one input.
  - **What it shows:** "not derivable from `GenFacts` + reader data" becomes a kernel fact.
- **Not done in the probe:** no compiler or generator change; no change to `GenFacts`, `SrcPkg`, `T1Hyp` or the spec.

## 5. Classification for FG (for review; NO change applied)
**Where t2 sits.** FG already takes per-declaration G3 reflection as a premise class, and `GenFacts` is a generator-produced per-declaration kernel fact of that class. t2/`LetTie` is the same kind of fact.

**What is NOT shown:**
- that the generator emits it for every successful compilation (coverage);
- that it is tied to the same run.

Mapped onto G3GEN_CALL_PLAN.md §5:
- **(a) No guarantee change.** This needs the tie checked by the run, or a proof that every successful compilation's generator emits `LetTie` for the same source and result. Not available today: one side of the tie is source meaning outside the run's data, and SR19 emission is opt-in, QUAD-only, with a silent fallback.
- **(b) Guarantee change.** `LetTie` availability becomes a premise of `Generated`/G3-GEN.
- **(c) Scope change.** FG is restricted to declarations whose generator emits `LetTie`.
- **(d) Compiler/generator change** (needs approval). Define `ext` at `nDecl + k` FROM the reader's data, as the callee applied to the decoded `letObsB` values. t1/t2 then hold by construction, and the source tie moves into the existing `writes`/`result`/`source` rfl fields. Risk: circularity, since `letObsB` reads `ext`, which needs the `stateLoop` causal fixpoint.

**What this unit does NOT decide.** The choice among (a)-(d) is a guarantee/scope matter. After the probe, I bring it to the user with tradeoffs and a recommendation, through the reviewer. This freeze asks only to approve the probe P1/P2 and the Prop definitions of §3.

## 6. Acceptance of this unit
- **P1 built**, with standard axioms and no use of per-declaration group facts.
- **P2 built:** `GenFacts` together with `¬ HPointAt`.
- **A result document** with the evidence for §5's decision.
- **Not claimed:** G3-GEN-CALL, G3-GEN, coverage, FG.
