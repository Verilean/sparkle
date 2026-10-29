# G-ONEOUT output selection: `CallField` freeze (FOR REVIEW; nothing applied)

- **Base:** `par/gen2-spec` c7948139. **Trigger:** `par/gen4-gate` scripts/gen4/ONEOUT_CALLDEC_RESULT.md (approved): `CallDec` (Tools/ShippingGen2Defs.lean:95-105, name conjunct :102) is unsatisfiable for `callerL → pickByteH` (`instFields = []`, callee outs `["out"]`, `getD 0 "" = ""`).
- **Direction (reviewed):** `HPointAt` (Tools/ShippingQuadHPoint.lean:15-38), `CallFactF` (Tools/ShippingQuadCalls.lean:223-239), `SeqFactsRN` (Tools/ShippingMachineCallsLinkedTNR.lean:23-42) are NOT changed. Gen2 gets ONE selection predicate `CallField`. Group parents use adapters to the old texts. One-output parents go to a dedicated bundle.
- **Why one-output is right:** `instStmt` (Sparkle/IR/Machine.lean:271-287) connects the callee's single output, whatever its name (`let [outP] := mc.outputs | none`, :280). `instFields` is `[]` exactly when the result is not a structure (Sparkle/Compiler/Elab.lean:5196).

## 1. Definitions (Tools/ShippingGen2Defs.lean, inserted before `CallDec`; mirror into scripts/gen2/GEN2_DEFS.lean.txt, which is currently cmp-identical)

```lean
/-- Which callee output the parent's call `k` reads. Group parents read the field named by `instFields`; one-output
parents (`instFields = []`, `closeInsts`/`instStmt`, Machine.lean:280) read the callee's ONLY layout output. -/
def CallField (p q : Pkg ι dom) (k : Nat) (o : OutField) : Prop :=
  if p.d.shape.instFields = [] then q.d.shape.layout.outs = [o]
  else o.name = p.d.shape.instFields.getD k ""

def CallDec (p q : Pkg ι dom) (k : Nat) : Prop :=
  (p.d.shape.instOrigins.getD k .ord).child? = none ∧
  ∃ args, (p.d.shape.insts.map (·.2.1))[k]? = some args ∧
    args.length = q.ports.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      (∀ r (hr : r < args.length), args[r] < p.d.ls.length ∧ ∃ g, (p.lsrc i bools bits)[args[r]]? = some g) ∧
      (∀ τ, InRange (valsOf (p.lsrc i bools bits) args τ) q.ports) ∧
      ∃ (k' : Nat) (o : OutField) (f : Nat → Nat), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
        (q.S i (valsOf (p.lsrc i bools bits) args))[k']? = some f ∧
        ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ
```
Only :102's `o.name = p.d.shape.instFields.getD k ""` changes. The `if` uses `instDecidableEqList` (String has `DecidableEq`).

## 2. New file `Tools/ShippingGen2CallField.lean`
It imports `Tools.ShippingGen2Adapt` (which brings CallDec/Connect) and `Tools.ShippingGen2CombKid` (`Pkg.src_get`, :79). No cycle: neither imports the other's dependants (Adapt.lean:1, CombKid.lean:1).

### 2.1 Selection lemmas
```lean
theorem callField_group {p q : Pkg ι dom} {k : Nat} {o : OutField} (hG : p.d.shape.instFields ≠ []) :
    CallField p q k o ↔ o.name = p.d.shape.instFields.getD k "" := by
  unfold CallField; rw [if_neg hG]
theorem callField_one {p q : Pkg ι dom} {k : Nat} {o : OutField} (h1 : p.d.shape.instFields = []) :
    CallField p q k o ↔ q.d.shape.layout.outs = [o] := by
  unfold CallField; rw [if_pos h1]
```
`if_neg`/`if_pos` are rewrites under `hG`/`h1`, not `rfl` (review of 1973de8e).

### 2.2 Old text and the group adapter
`CallDecOld` is Defs:95-105 at c7948139, verbatim, renamed:
```lean
def CallDecOld (p q : Pkg ι dom) (k : Nat) : Prop :=
  (p.d.shape.instOrigins.getD k .ord).child? = none ∧
  ∃ args, (p.d.shape.insts.map (·.2.1))[k]? = some args ∧
    args.length = q.ports.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      (∀ r (hr : r < args.length), args[r] < p.d.ls.length ∧ ∃ g, (p.lsrc i bools bits)[args[r]]? = some g) ∧
      (∀ τ, InRange (valsOf (p.lsrc i bools bits) args τ) q.ports) ∧
      ∃ (k' : Nat) (o : OutField) (f : Nat → Nat), q.d.shape.layout.outs[k']? = some o ∧ o.name = p.d.shape.instFields.getD k "" ∧
        (q.S i (valsOf (p.lsrc i bools bits) args))[k']? = some f ∧
        ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

theorem callDec_group_old {p q : Pkg ι dom} {k : Nat} (hG : p.d.shape.instFields ≠ []) :
    CallDec p q k → CallDecOld p q k
theorem callDecOld_group {p q : Pkg ι dom} {k : Nat} (hG : p.d.shape.instFields ≠ []) :
    CallDecOld p q k → CallDec p q k
```
Both proofs: destructure, then map the name conjunct with `(callField_group hG).mp`/`.mpr`.

### 2.3 Amended `seqFactsRN_of_callDec` (Tools/ShippingGen2Connect.lean:109-133)
```lean
theorem seqFactsRN_of_callDec {L : Laws mref cref} {P : Pkgs ι dom} {p q : Pkg ι dom} {k n : Nat} {c : Name}
    (dsn : Design) (body : List Stmt) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hG : p.d.shape.instFields ≠ [])
    (hP : P c = some q) (hdec : CallDec p q k)
    (hseq : ∀ mc, ServedPC (ShipsAt L P n) dsn c mc → "clk" ∈ mc.inputs.map (·.name)) :
    Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN (childMap dsn.modules) n p.d.shape dsn body
      (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits)
      (pkgBsC P) (pkgOutsC P) (pkgS P i) (ServedPC (ShipsAt L P n) dsn) k c
```
In the proof, `hon` at :122 becomes `((callField_group hG).mp hon)`. Without `hG` the old conclusion cannot be derived: SeqFactsRN:39 asks for `o.name = getD k ""`. The theorem stays in Connect.lean, which imports Defs, so `callField_group` must go into Connect.lean (or Defs) and not only the new file. **Placement: `callField_group`/`callField_one` go in Connect.lean, next to `pkgBsC` (:98); the new file re-exports them.**

### 2.4 Route-aware per-call residue (Gen2; shares `CallField`)
These are `HPointAt` at the exact instantiation used by the adapters (Adapt.lean:169), with the name conjunct replaced:
```lean
def HPointG (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hk : k < p.d.shape.insts.length),
    ∃ (A : Nat → Signal (dom i) Bool) (B : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      boolsOf (D := dom i) (pkgBsC P (p.d.shape.insts[k]).1) (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1) = A ∧
      bitsOf (D := dom i) (pkgBsC P (p.d.shape.insts[k]).1) (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1) = B ∧
      ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
        (pkgOutsC P (p.d.shape.insts[k]).1)[k']? = some o ∧ CallField p q k o ∧
        (pkgSrc P i (p.d.shape.insts[k]).1 A B)[k']? = some f ∧
        ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

def CallOutG (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hk : k < p.d.shape.insts.length),
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
      (pkgOutsC P (p.d.shape.insts[k]).1)[k']? = some o ∧ CallField p q k o ∧
      (pkgS P i (p.d.shape.insts[k]).1 (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1))[k']? = some f ∧
      ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
        (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ
```
`q` is a parameter because `CallField` reads `q.d.shape.layout.outs` in the one-output branch. Under `hG`, `CallField` does not mention `q`, so the group adapters hold for every `q` and need no `hP`.
```lean
theorem hPointAt_of_hPointG_group {P : Pkgs ι dom} {p q : Pkg ι dom} {k : Nat} (hG : p.d.shape.instFields ≠ []) :
    HPointG P p q k → HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k
theorem hPointG_of_hPointAt_group {P : Pkgs ι dom} {p q : Pkg ι dom} {k : Nat} (hG : p.d.shape.instFields ≠ []) :
    HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k → HPointG P p q k
theorem callFactF_of_callOutG_group {P : Pkgs ι dom} {p : Pkg ι dom} (hG : p.d.shape.instFields ≠ [])
    (h : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, CallOutG P p q k) :
    CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i)
theorem callOutG_of_callFactF_group {P : Pkgs ι dom} {p q : Pkg ι dom} (hG : p.d.shape.instFields ≠ [])
    (hF : CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i)) (k : Nat) : CallOutG P p q k
```
Each of these is a destructure plus `callField_group hG` on the name conjunct. The Gen2 producer for both routes is `callDec_of_hPointG_at`: the same signature as `callDec_of_hPointAt_at` (Adapt.lean:166-174) with `hH : HPointG P p q k`, and no `hG`. Its proof is that proof, passing `hcf` unchanged, since `pkgOutsC P c = q.d.shape.layout.outs` by `hP`.

### 2.5 One-output consumer data
```lean
def OneOutCall (p q : Pkg ι dom) (k : Nat) : Prop :=
  (p.d.shape.instOrigins.getD k .ord).child? = none ∧
  ∃ args, (p.d.shape.insts.map (·.2.1))[k]? = some args ∧
    args.length = q.ports.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      (∀ r (hr : r < args.length), args[r] < p.d.ls.length ∧ ∃ g, (p.lsrc i bools bits)[args[r]]? = some g) ∧
      (∀ τ, InRange (valsOf (p.lsrc i bools bits) args τ) q.ports) ∧
      ∃ (o : OutField), q.d.shape.layout.outs = [o] ∧
        (∀ v : List Nat, ∃ g, (q.S i (fun _ => v))[0]? = some g) ∧
        ∃ f : Nat → Nat, (q.S i (valsOf (p.lsrc i bools bits) args))[0]? = some f ∧
          ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
            (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

theorem oneOutCall_of_callDec {p q : Pkg ι dom} {k : Nat} (h1 : p.d.shape.instFields = []) :
    CallDec p q k → OneOutCall p q k
```
Here is what each part supplies:
- `k' = 0`: `callField_one h1` gives `outs = [o]`. Then `ho : [o][k']? = some o` forces `k' = 0` (`cases k'`; `[o][j+1]? = none`), so `hf` becomes `[0]?`.
- The `S4-b` `hS` premise (STEP_IFACE_FREEZE.md:172), from `Pkg.src_get q i _ _ 0 o (by rw [hsing]; rfl)`. `q.S i vals` unfolds to `q.src i (boolsOf …) (bitsOf …)` (Tools/ShippingGen2Pkg.lean:84-86). It is stated for every `v`, which is stronger than S4-b's `InRange`-guarded form.
- The posEnc equation is CallDec's `hpos` unchanged.
- **`o` sits inside `∀ i`, like CallDec.** For an empty `ι` CallDec is vacuous and yields no `o`. Lifting `o` out would need `[Nonempty ι]`. The consumer takes `outs = [o]` at its own `i`.

The run-level half lives outside CallDec because `mc` is a run object:
```lean
theorem oneOut_outputs {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn : Design} {n : Nat}
    {mc : Sparkle.IR.AST.Module} {bsC : List (Name × MixedGateBinder)} {o : OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)} :
    ChildRunN children dsn n mc bsC [o] S → mc.outputs = [({ name := o.name, ty := o.ty } : Port)]
```
The proof is the first conjunct of either disjunct (Tools/ShippingMachineDepth.lean:67, Defs:61). It is applied to `ChildShips q` (Defs:87-90, `outsC := q.d.shape.layout.outs`) rewritten by `outs = [o]`. So `instStmt`'s `outP` is `⟨o.name, o.ty⟩`, and the connection `(outP.name, .ref outW)` (Machine.lean:287) reads exactly `o.name`. That is what `CombChildRunN`'s output clause (Defs:74-75, `outsC[0]? = some o`) gives.

## 3. Every use of `CallDec` (Gen2 `Tools.ShippingGen2.CallDec`) and the change it needs
The structure `Tools.ShippingSeqParentGenD2MSD.CallDec` (:17, used in KaryThreeTest/GenD2MSG/MSK) is an unrelated name and is not touched.

| Use | Change |
|---|---|
| Defs:95-105 (+ GEN2_DEFS.lean.txt:95-105) | §1 text; insert `CallField` before it. |
| `T1Hyp.dec` Defs:201-202 | No textual change; meaning follows `CallDec`. |
| `StepStmt` Defs:303 | No textual change; one-output entries now satisfiable. |
| `seqFactsRN_of_callDec` Connect.lean:109 | Add `hG`, as in §2.3. Its only other mention is `#print axioms` (Tests/Gen2/U0Check.lean:30), with no change. |
| `callDec_of_callFactF` CallDec.lean:58-96 | Add `(hG : p.d.shape.instFields ≠ [])` (CallFactF is group-only, QuadCalls:236). At :93, `hon` becomes `((callField_group hG).mpr hon)`. |
| `callDec_of_hPointAt_at` Adapt.lean:166-189 | Add `hG`. At :185, `hon` becomes `((callField_group hG).mpr hon)`. |
| Tests/Gen2/CallDecInstance.lean:126-130 (`tm2_callDec`) | Pass `(by decide)` for `tm2Pkg.d.shape.instFields ≠ []` (fallback `decide +kernel`, as at :134), in both calls. |
| Tests/Gen2/AdaptInstance.lean:31, :43 (`tm2_callDec_at`) | Same `hG` argument. |
| PkgCompat:248 `CallDec (.gen p) (.gen q) k = Old.CallDec p q k := rfl` | No longer `rfl`; replaced (§4). `Old.CallDec` (:50) stays frozen. |
| PkgCompat:304-357 `t1Hyp_iff` (`hcd` passed directly at :323, :352) and `t1Stmt_compat` :397 (if it goes through `t1Hyp_iff`) | Conditional (§4). |

`quantModule` (loop package) has no ordinary call through CallDec in the current tree; grep finds no other instance. Tools/ShippingGen2MemFacts.lean:1 and LoopRestrict.lean:5 only import or mention the file, so they need no change.

## 4. PkgCompat classification (new checks)
- **Pointwise `CallDec`: CHANGED, conditional.** For `instFields ≠ []` the two texts are equivalent; for `instFields = []` they are INCOMPARABLE (old: `o.name = ""`; new: `outs = [o]`). The replacement for :248:
  ```lean
  theorem callDec_gen_group (p q : SrcPkg ι dom) (k : Nat) (hG : p.d.shape.instFields ≠ []) :
      CallDec (.gen p) (.gen q) k ↔ Old.CallDec p q k :=
    ⟨fun h => callDec_group_old hG h, fun h => callDecOld_group hG h⟩
  ```
  This relies on `(Pkg.gen p).d = p.d` (Pkg.lean:46) and on `Old.CallDec p q k` being `CallDecOld (.gen p) (.gen q) k` by `rfl`. That `rfl` is checked as its own `example`.
- **Positions.** `CallDec` is positive in `T1Hyp.dec` (a hypothesis T1Hyp provides). It is negative in `StepStmt` (a premise at Defs:303). It is negative in `T1Stmt`/`ServedShipsStmt` through their `T1Hyp` premise.
- **`t1Hyp_iff`: CHANGED, conditional.** It holds under `GroupOnly P Reach := ∀ c, Reach c → ∀ q, P c = some q → q.d.shape.instFields ≠ [] ∨ q.d.shape.insts = []`. In the `dec` case the parent is `q` with `k < insts.length`, so the left disjunct applies; `.lift`'s `d` is `rfl`. Without it no direction is claimed.
- **`t1Stmt_compat`: CHANGED, NEW → OLD under `GroupOnly`.**
- **`StepStmt`:** it is already MIXED/withdrawn since A-COMB (PkgCompat:263-266). No new claim.

## 5. Acceptance (for the implementing unit)
The build is one scoped `kjob lake build` of `Tools.ShippingGen2CallField`, `Tests.Gen2.CallDecInstance`, `Tests.Gen2.AdaptInstance`, `Tests.Gen2.PkgCompat`, `Tests.Gen2.U0Check`. Lakefile entries are needed for the new file and the new test. `#print axioms` on every new theorem must show at most `[propext, Classical.choice, Quot.sound]`.

Add a kernel test `Tests/Gen2/OneOutCallField.lean`: for the gen4 `callerL`/`pickByteH` data, `CallField`'s one-output branch is satisfiable, i.e. `pickByteH.machineData.shape.layout.outs = [o]` for its `o`, by `decide`. This is the non-vacuity of the new conjunct. A `Pkg.comb` for `pickByteH` and the S4 consumer remain separate obligations.

**Stop conditions:**
- If `if_neg`/`if_pos` do not rewrite (Decidable instance mismatch), switch to `match p.d.shape.instFields with | [] => … | _ => …` and report it. Do not use `instFields.isEmpty`.
- If `Old.CallDec p q k = CallDecOld (.gen p) (.gen q) k` is not `rfl`, stop and report.
