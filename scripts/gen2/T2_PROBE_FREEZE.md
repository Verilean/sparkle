# M5 lead: G3-GEN-CALL t2 — route freeze rev2 and kernel probe plan (FOR RE-REVIEW; rev1 be1110c3 changes_requested)

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

## 2. Finding: t2 has no generic derivation from `GenFacts` + the reader's data (a READ-ONLY argument, not yet kernel-checked)
- **`body_eq` only equates two reader outputs.** `d.shape.body = quote d.dom … d.packed` (QuadComposed.lean:121) gives no `Lean.Expr` a meaning.
- **`GenFacts` does not constrain a let that feeds only call arguments.** `GenFacts.writes/result/source` (:125-149) tie `body` to the IR only through `d.nexts`/`d.outs`. A call output is the input position `nDecl + k`, so the call's argument lets enter neither.
- **`machineExt`/`machineBody`/`machineSource` are elaborated Lean terms,** not functions of `MachineData`. `SrcPkg.ext/body/src` are fields constrained only by `GenFacts`.
- **What this is, and is not.** It is an argument about what `GenFacts` + reader data IMPLY; the probe P2 (§4) tests it. It is NOT:
  - a claim that the real generator has a bug;
  - a claim that t2 fails for some successful source;
  - a claim that generic supply is impossible by other means.

## 3. Exact Props (namespace `Tools.ShippingGen2`; opens as Tools/ShippingGen2CallDec.lean)
The callee's argument families of call `k`, as the generator builds them (MachineDepthCommandR.lean:765-778: `extendBools`/`extendBits` over the decoded base, one step per callee port) are a parameter:
```lean
/-- The argument families of an ordinary call, per index/input (the generator's `A`/`B`). -/
abbrev ArgFamB (ι : Type) (dom : ι → DomainConfig) :=
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool
abbrev ArgFamV (ι : Type) (dom : ι → DomainConfig) :=
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)

/-- **t2 (`LetTie`)**: the parent's let observations at call `k`'s arguments, decoded with the CALLEE package `q`'s
port list, are the call's argument families (the shape of the generated `gfHb`/`gfHv`, MachineDepthCommandR.lean:406). -/
def LetTie (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) (A : ArgFamB ι dom) (B : ArgFamV ι dom) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    boolsOf (D := dom i) (q.d.bsIn.take q.kD) (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1) = A i bools bits ∧
    bitsOf (D := dom i) (q.d.bsIn.take q.kD) (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1) = B i bools bits

/-- **t1+t3 (`CallOut`)**: on the call's argument families, the callee `q`'s source has the output named by the
call's field, with an explicit index/name/existence witness, and the parent's call-result signal is it. -/
def CallOut (p q : Pkg ι dom) (k : Nat) (A : ArgFamB ι dom) (B : ArgFamV ι dom) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
      q.d.shape.layout.outs[k']? = some o ∧ o.name = p.d.shape.instFields.getD k "" ∧
      (q.src i (A i bools bits) (B i bools bits))[k']? = some f ∧
      ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
        (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ
```
- **Fixed by the types:**
  - argument positions `(insts[k]'hk).2.1`;
  - their decoding with `q`'s ports, `q.d.bsIn.take q.kD`, which is `pkgBsC P c` (Gen2Connect.lean:99);
  - the output index `k'`, the name `o.name` and existence `(… )[k']? = some f`, as explicit witnesses, with no `getD` hiding a missing output.
- **The arity** (`args.length = q.ports.length`) is NOT part of `LetTie`. It stays `CallDec`'s conjunct, supplied as in U-ADAPT.

**The conditional generic lemma (full telescope):**
```lean
theorem hPointAt_of_ties (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hP : P (p.d.shape.insts[k]?.map (·.1)).getD default = some q)
    (hk : k < p.d.shape.insts.length) (A : ArgFamB ι dom) (B : ArgFamV ι dom)
    (h2 : LetTie p q k hk A B) (h13 : CallOut p q k A B) :
    HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k
```
- **Proof:** for each `i bools bits hk'`, take `A i bools bits`/`B i bools bits` as the existential witnesses. `h2` gives the two family equations, after rewriting `pkgBsC P c = q.d.bsIn.take q.kD`. `h13` gives the third conjunct, through `pkgOutsC`/`pkgSrc` at `hP`.
- **What it does not show:** nothing deep. It certifies that `HPointAt` is EXACTLY `∃ A B, LetTie ∧ CallOut`, the decomposition t1/t2/t3 rests on.
- **The precise `hP` form** (`(insts[k]).1` with `hk`) is fixed in the probe file to match `HPointAt`'s use of `dP.shape.insts[k]`.

**The fragment of `Generated X p` needed:**
- `p.ext = X.machineExt` and `p.extB = X.machineExtB` (t1);
- `p.lsrc` from `X.machineData` and `X.machineBody` (letObsB);
- for each ordinary `k`, the generator's argument families `(A, B)` with `LetTie` (t2) and `CallOut` (t1+t3).

## 4. Kernel probe (own worktree from reviewed base 1fdbc18d; new files only)
**P1, positive, `Tests/Gen2/T2Probe.lean`** (the lemma in `Tools/ShippingGen2T2Probe.lean`):
- **Instances:** `topshare2` (QuadCallsTest) call `k = 0` to `wrapQ`, and `wrapQ` call 0 to `leaf16`.
- **`A`/`B`:** the generator's own families (the `extendBools`/`extendBits` chain over the decoded base, with `callArgs` from the unfolded `X.machineExt`), written as terms.
- **`LetTie` by:** `funext` + the absorb chain + `decB/decV_valsOf … rfl`, the per-let kernel `rfl`.
- **`CallOut` by:** unfolding `X.machineExt` (t1) and `rfl` on the callee source (t3).
- **Then:** `hPointAt_of_ties`.
- **Forbidden:** `oldGroupFact%`, `gfHb*`/`gfHv*`, `b_*_hFP`, `machine_composedNR2` (closure audit).
- **What it shows:** on these two calls, t2 is exactly the per-let `rfl`, and the rest is generic.

**P2, negative, `Tests/Gen2/T2Neg.lean`.** It must break ONLY t2.
- **The package.** `p₀` is `tm2Pkg` (Tests/Gen2/CallDecInstance.lean). `p₁` is `p₀` with ONE change: the reader data's let `a₀ := ((p₀.d.shape.insts[0]).2.1)[0]`, an argument of call 0, gets a different expression in `d.ls`. `d.shape.body` is recomputed so that `body_eq` holds.
- **Unchanged:** `insts`, `ext`/`extB` (the call term, t1), the callee assignment `P2` (wrapQ/wrapP packages) and `src` of the callee (t3).
- **Proof obligations:**
  - `GenFacts` for `p₁`: `writes`/`result`/`source` unchanged because `a₀` feeds no `nexts`/`outs` entry. To be checked by `rfl`/`decide`.
  - `CallOut p₁ q 0 A B`: unchanged, the positive part.
  - `¬ LetTie p₁ q 0 hk A B`, by specialisation: fix `i := ()`, the constant input families `bools := fun _ => Signal.pure false` and `bits := fun j n => Signal.pure (BitVec.ofNat n (j + 1))`, time `τ := 0` and the port index of `a₀`. Then `decide` that `((bitsOf … (valsOf (p₁.lsrc …) args)) port w).val 0 ≠ ((B () bools bits) port w).val 0`. This is a finite mismatch, not the negation of a `∀` function equality.
  - **Positive control:** the same specialised equation holds for `p₀` (by `decide`, or by P1's `LetTie`).
- **If `GenFacts p₁` cannot be established** (e.g. `a₀` turns out to feed `nexts`/`outs`, or `rfl` fails), I stop and report, and P2's conclusion is LIMITED. A rewired-callee package then shows only "`GenFacts` alone does not give `HPointAt`". That package changes t1/t3, so it says nothing specific about t2, and is labelled so.

## 5. Classification for FG (for later; NO choice requested now)
- **Where t2 sits.** FG already takes per-declaration G3 reflection; `GenFacts` is a generator-produced per-declaration kernel fact. `LetTie` is the same kind of fact.
- **What is NOT shown:** that every successful compilation comes with it (coverage), and that it is tied to the same run.
- **The options** (G3GEN_CALL_PLAN.md §5 cases):
  - (a) tie checked by, or provably emitted for, every successful run: no guarantee change; NOT available today;
  - (b) `LetTie` availability as a premise of `Generated`: a guarantee change;
  - (c) restrict FG to declarations with it: a scope change;
  - (d) a generator change that builds `ext` at `nDecl + k` from the reader's data.
- **(d) is a proposal with UNPROVED consequences.** It is NOT shown that the source tie then moves into the existing `writes`/`result`/`source` fields; that would itself need a proof, and `letObsB` reads `ext`, which needs a causal fixpoint argument.
- **When the choice comes.** No guarantee or scope choice is requested now. After P1/P2, the evidence goes to the user, with tradeoffs and a recommendation.

## 6. Acceptance of this unit
- P1 and P2 built, with standard axioms and the closure audit.
- P2's conclusion stated exactly as obtained: t2-specific, or the limited fallback.
- A result document.
- **Not claimed:** G3-GEN-CALL, G3-GEN, coverage, FG; no generator bug and no impossibility for successful sources.
