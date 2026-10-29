# S4-WID: supplying `hW : ∀ k, OneOutWidth P p k` (coverage obligation G-ONEOUT-WID), read-only plan

Base: `par/gen2-spec` at e1fd0d0e. Nothing was built or changed. Every proposed lemma below is UNBUILT.

## 0. The premise and its two consumers
`OneOutWidth` (Tools/ShippingGen2FitChain.lean:893-896):
```lean
def OneOutWidth (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length) (q : Pkg ι dom), P (p.d.shape.insts[k]).1 = some q →
    ∀ o : OutField, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth
```
It is used twice:
- `machine_linked_callsServed1F`, to build `CallOutWidths` (FitChain:951-971; the use is at :965).
- `oneOutWidthAt`, to build `RunFacts.wid` (Tools/ShippingGen2OneOutTop.lean:283-345; the use is at :345, consumed at :398-401).

Both consumers already hold THE served child. `ShipsRes` (Tools/ShippingGen2Defs.lean:135-136) starts with `RealChildA L.O c r`. FitChain:944 and OneOutTop:326 currently discard that conjunct.

## 1. Where the two widths come from
**Parent.** `machInstCall?` (Sparkle/Compiler/Elab.lean:3721-3728) looks up `senv.inst c`. Here `senv.inst` is `instSignature? envR'` (`structEnv`, Elab:4394-4397; `envR'` is the env read in `MachineDefines`, Tools/ShippingMachineEntry.lean:2345-2357). `instSignature?` (Elab:4373-4383) returns `res := machResultKind? ci.type` (Elab:4326-4332), which is the result kind of c's DECLARED constant. `machInstance` (Elab:4049-4080) pushes `(c, js, res)`. A `.bool` result sets `instStruct` (Elab:4056-4058), which makes `instFields` non-empty (Elab:5197). So under `hsimple : instFields = []` every entry has a `.bits w` result.

The binder list is `bs ++ instBinders ++ …` (Elab:5181-5185). Therefore the kind of the binder at `bs.length + k` is `insts[k].2.2`. The proved lemma is `machineShape?_callBinder` (Tools/ShippingMachineShapeTail.lean:61-71).

The Lean type of the call term `c args` is never consulted. `machInstCall?` requires `args.length == kinds.length`, and `telescopeKinds` (Elab:4366-4368) accepts only hardware binders. So c has no type parameters and nothing is instantiated. The answer to question (1) is therefore not "the typechecker gives the call term c's result type". It is that **both readers read the same constant's type**.

**Callee.** `MachineDefines c q.d.shape` (T1Hyp.defines, Defs:198-199) is `machineShape?` run on `entryConst … ci` (Entry:2354-2357). The type of that constant is either `ci.type` or `userInliner envR ci.type` (entryConst at Elab:5272-5282; inlinedConst rewrites `type` at Elab:3409-3411). Its outputs are `machTupleKinds?`/`machOuts?` of that type (Elab:5065-5067, 3859-3876). They become `layout.outs = machOutFields W outs` (Elab:5191, 4463-4467) with `ty := machHWType kind` (Elab:4456-4458).

**Proved agreement pieces (real reader, old compiler):**
- P1, `instSignature?_some` (Tools/ShippingInstSignature.lean:18).
- P2, `machOuts?_of_resultKind` (Tools/ShippingReaderResultKind.lean:112-113): the same type expression gives the single output `out` of the same kind.
- `machineShape?_single_out` (ShapeTail:74-80).
- `childLink_realA` (Tools/ShippingChildLinkA.lean:41-48): from `MachineDefines c sc`, `ResDeclAt c res`, `P5At c res` and `RealChildA O c y`, it gives `machineShape? false [] (.defnInfo dE) senv = some sc ∧ machResultKind? dE.type = some res`.
- `kindTy_eq_machHWType` (Tools/ShippingCallWidthsDeclared.lean:67).
- `machResultKind?_ne_domain` (ReaderResultKind:129).

**What is not proved:**
- R1 for the `partial` `machInstance`: the entry carries the signature's kind.
- P5: the production `userInliner` on a type. It is opaque, and is proved only for the candidate `userInlinerC`, `resKind_userInlinerC` (Tools/ShippingInlTypeReads.lean:13-17).
- Env identity between the parent's `envR'` and the callee's `getConstInfo c`.

The file headers already record that no agreement lemma exists and that the condition is "a premise per pair, like `outTy`" (Tools/ShippingCallWidths.lean:17-37; ChildReal.lean:137-155 define `ResDeclAt`/`P5At` as explicit premises).

## 2. Existing width checks, and how each is supplied
| check | file:line | supply |
|---|---|---|
| `callWidthsOk` | CallWidths.lean:51-56 | VACUOUS when `instFields = []` (the name `""`; CallWidthsStrict.lean:3-10). The generator emits only this row (Tools/ShippingSeqParentGenD2.lean:261-263) |
| `callWidthsStrict` / `callWidthsStrict_at` | CallWidthsStrict.lean:37-42 / 45-71 | `decide` per declaration: `callerL_strict` (Tests/Compiler/OneOutCallerLTest.lean:271-278), callerLN (Tests/Compiler/OneOutCallerLNTest.lean:146), hftByte (Tests/Compiler/OneOutHftByteTest.lean:398) |
| `#machine_oneout_any` rows | Tools/ShippingOneOutAnyGenCommand.lean:66-86, 474-496 | `decide` per declaration: `c.leaf_outW` (every layout output has width W) and `f.oneout_entries` (binder at `nDecl+k` has width W), assembled per entry into `hkidW` |
| `callWidthsStrict_realA` | Tools/ShippingCallWidthsChildRealA.lean:67-84 | from `ChildrenRealA`, `MachineDefines`, plus the premises `ResDeclAt`, `P5At` and `PB` (the parent binder is `machHWType res`) |
| `callArgsOkAt` (argument widths, not the result) | Tools/ShippingGen2Adapt.lean:73-77 | `decide` per k (scripts/gen2/UADAPT_RESULT.md:43). The generic supply G-DATA-CALL needs `PortTie`, which has not been found (scripts/gen2/G3GEN_CALL_PLAN.md:65-70, 83-90) |
| `hkidW` (group parents) | Tools/ShippingParentRunFactsA.lean:582-586 | a premise. `hkidW_of_dataA` (:613-) takes `callWidthsOk` (per-declaration data) plus `ChildOutTys`. Not from the run |

Every existing supply is a **per-declaration `decide`**. None of them is derived from the run.

## 3. Options

### (c) Run-local: not available without a compiler change
`instStmt` (Sparkle/IR/Machine.lean:272-288) checks only that `outW` is a wire by NAME (:283). `closeInsts` (:396-427) has no width conjunct. `instOutWidthsOk` does not occur under `Sparkle/` (grep).

The run gives two facts that nothing links:
- `declWidth b outW` equals the binder width (`core_callPorts_oneA`, OneOutTop:47-).
- `mc.outputs = q.layout.outs` as ports (from `ChildShips`, OneOutTop:328-331).

`CallDec`'s equation (Defs:102-114) is value-level: `posEnc` of the binder equals `f τ`. A callee whose output is constantly 0 satisfies it at any parent width, so it cannot force widths. `HPointAt` (Tools/ShippingQuadHPoint.lean:27-38) is the same.

A guard `wireWidth m.wires outW == outP.ty.bitWidth` in `instStmt` would make this a run fact (`wireWidth` is already used at Machine.lean:190). That is a compiler change. Under the compiler-output policy it needs a user decision, a corpus measurement, and re-proofs of `CallStmt`/`closeInsts_insts`. **Not recommended now.**

### (a) Generic, from both reflections: possible as a run-local lemma, but it moves the gap rather than closing it
Proposed lemma (missing; every ingredient exists):
```lean
theorem oneOutWidth_of_realA {mctx : Meta.Context} {cctx : Core.Context}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (P : Pkgs ι dom) (p : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    (hpos : (p.d.shape.binders[p.kD + k]?).map (·.2) = some (p.d.shape.insts[k]).2.2)
    (hDq : ∀ q, P (p.d.shape.insts[k]).1 = some q →
      MachineDefines mctx mref cctx cref (p.d.shape.insts[k]).1 q.d.shape)
    (ResD : Tools.ShippingCallWidthsChildReal.ResDeclAt mref cref (p.d.shape.insts[k]).1 (p.d.shape.insts[k]).2.2)
    (P5 : Tools.ShippingCallWidthsChildReal.P5At mref cref (p.d.shape.insts[k]).1 (p.d.shape.insts[k]).2.2)
    {y : Res} (hy : Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y) :
    OneOutWidth P p k
```
Proof:
1. `childLink_realA (hDq q hq) ResD P5 hy` gives the link and the result kind.
2. `machineShape?_single_out` then gives `q.layout.outs = [{name := "out", …, ty := machHWType r}]`.
3. `hpos`, `kindTy_eq_machHWType` and `machResultKind?_ne_domain` finish it.

Taking ResDeclAt at the parent's RECORDED kind `insts[k].2.2` folds R1 and env identity into one premise.

Supply status of each premise:
- `hpos` is decidable on `p.d` alone, so it is a single-package data row (a `DataOk` conjunct).
- `hDq` is T1Hyp.defines.
- `hy` is in hand at both consumers.
- `ResD` and `P5` are left: an env-stability/reflection premise per callee, and the opaque inliner. Neither is decidable, and P5 is candidate-only.

Using this lemma also means re-threading FitChain:944 and OneOutTop:326 so that they keep the `RealChildA` conjunct. **Recorded as the generic route. It is not a supply today.**

### (b) Per-declaration decidable cross-package row (RECOMMENDED)
Bridge lemma (missing, small; the proof is `callWidthsStrict_at` with a vacuous name side):
```lean
def kidOutsP (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : List OutField :=
  match (p.d.shape.insts.map (·.1))[k]? with
  | some c => match P c with | some q => q.d.shape.layout.outs | none => []
  | none => []

theorem oneOutWidth_of_strict (P : Pkgs ι dom) (p : Pkg ι dom) (kidOuts : Nat → List OutField)
    (hcw : Tools.ShippingCallWidthsStrict.callWidthsStrict p.d p.kD kidOuts = true)
    (hsimple : p.d.shape.instFields = [])
    (hkid : ∀ k (hk : k < p.d.shape.insts.length) q, P (p.d.shape.insts[k]).1 = some q →
      kidOuts k = q.d.shape.layout.outs) :
    ∀ k, OneOutWidth P p k
```
Proof: `intro k hk q hq o ho`. Then `o ∈ kidOuts k` follows from `hkid` and `ho`. Apply `callWidthsStrict_at hcw hk _ (fun f hf => by simp [hsimple] at hf)`. Note that `nDecl = p.kD` directly, so `closingNDecl_eq_kD` (S4_CONSUMER_FREEZE.md:510-512) is not needed.

There are two ways to discharge `hkid`:
- **(b1)** `kidOuts := kidOutsP P p`. Then `hkid` holds by `simp [kidOutsP, hk, hq]`, and `hcw` is one `decide` against a concrete `P`. Risk: the kernel has to reduce `P c` to a `Pkg` value.
- **(b2)** `kidOuts := fun k => [C₀.machineData.shape.layout.outs, …].getD k []`. This is the form of `callerL_strict`. Here `hkid` needs `q.d.shape = Cₖ.machineData.shape`. It comes from D-GEN `Generated` (G3GEN_CALL_PLAN.md:55-60), or from a missing one-line lemma `MachineDefines.shape_eq`: two `MachineDefines` of the same declaration agree, given one read (`Option.some.inj`). The read comes from `RealChildA` via `synthesizeCombinationalCore_reads`, as in ChildLinkA:53-56.

**Generator work:**
- Emit `@P@.epD2_callWidthsStrict` next to the vacuous row (SeqParentGenD2:261-263), with a per-k table.
- For `#machine_oneout_any` parents, derive the same row from the existing `oneout_entries` and `leaf_outW`, or emit it directly.

## 4. What remains a coverage obligation (no new FG premise added silently)
G-ONEOUT-WID stays a **named, static, relational premise**. It cannot be a `DataOk q` conjunct, because it mentions `P`.

Proposed T1Hyp amendment, for review only (not applied):
```lean
  /-- G-ONEOUT-WID: one-output result widths (supplied per declaration by `oneOutWidth_of_strict` + a decided
  `callWidthsStrict` row). -/
  wid : ∀ c, Reach c → ∀ q, P c = some q → q.d.shape.instFields = [] → ∀ k, OneOutWidth P q k
```
**Coverage:** every reached one-output declaration must have the row decided. That is a generator-emission obligation, in the same class as G-DATA, plus `hkid` (D-GEN identity). Declarations whose row fails would be width-mismatched parents. None is expected, because both widths are read from the same constant type (§1). The count is not measured.

**Stops / open items:**
- Nothing is built.
- (b1) `decide` through `P` is untested.
- `MachineDefines.shape_eq`, `kidOutsP`, `oneOutWidth_of_strict` and `oneOutWidth_of_realA` are all missing.
- Route (a) still needs `ResDeclAt` and `P5At`, which nothing supplies.
- Route (c) needs a user decision on a compiler change.
