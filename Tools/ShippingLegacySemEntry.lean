import Tools.ShippingLegacySemContract
import Tools.ShippingUnifiedExecutionSoundness

variable {tenv : Lean.Environment}

/-! # The legacy arm of the entry: what it must satisfy to reach an output statement

Target (the acceptance unit): for a REAL declaration that the entry compiles
on the legacy route — a combinational one such as `useDbl x := dbl x` — the
emitted module's output is the source's value.

How the certified entry gets there (`Tools/ShippingUnifiedExecutionSoundness.lean`,
`synthesizeMixedCertified_term_sound_at`): the entry runs ONE harness,

```
bindMixedCertifiedInputs (emitLeaves translate cache logProf [("out", leaf)] none 0) (bs.zip ids)
```

from the fresh builder state; `prepare` / `Admissible` describe the input
ports it binds and the admissible input values; from the leaf's `Contract`
and its order statement (`ActionOrder`) at the prepared context, the generic
leaf lemmas `emitLeaves_from_ports` / `emitLeaves_postReady_at`
(`Tools/ShippingUnifiedEntrySoundness.lean` — stated for ANY leaf expression
with a contract) give `RawValueAt`: the module's assignments evaluate, `out`
has the leaf's value, the module is typed, simple and printable. The
execution theorems downstream (`term_execution`, the SV endpoints) consume
`RawValueAt`.

The legacy arm of `synthesizeFromConst` runs the SAME `emitLeaves` and the
same `bindInputPort`, through a different front: `openRecordInputs`,
`stripMemoizeWrappers`, `lambdaTelescope`, `splitReturnLeaves`,
`bindInputsLegacy`, then `finishSynth`. So the connection has three parts,
stated here over the existing types:

| Part | Statement | Status |
|---|---|---|
| `LegacyEntryReduces` | a successful run of the legacy arm on the declaration IS a run of the certified harness on some leaf `leafOf ids`, with the module finished the same way | **needs-walk**, with oracle premises: `lambdaTelescope` (fresh variables, the instantiated body), `fvarId.getDecl`, `isSignalBinderType`, `inferHWTypeFromSignal` on each binder (that the type oracle returns the binder's kind), `splitReturnLeaves` (one leaf named `out` for a scalar Signal result). The memo read of `sparkleSubModuleCache` is another heap read (a hit returns a cached module with no run at all: a premise that it misses, or a cache invariant) |
| `HarnessSound` | the harness on ANY leaf with a `Contract` and an `ActionOrder` at the prepared context gives `RawValueAt` | **provable-now**: it is `synthesizeMixedCertified_term_sound_at` with its two uses of the quoted fragment (`translateExprToWire_contract`, `translateExprToWire_orders`) replaced by hypotheses; every other step of that proof is already about an arbitrary leaf. Not re-proved here (about eighty lines to copy; to be done with the build loop) |
| the leaf's `LegacyDom` | the leaf, at the prepared context and input values, is in the combined domain at value `v` | per declaration: **provable-now** for the certified part; for a legacy inline arm it carries `NotCore`, `ReachesInline` (now reduced to the walks of `Tools/ShippingLegacySem*`, with the premises listed there: `PlainHead`, `HasMappedFVar`, `NoSubModule`, and — for cacheable calls — the shim) and the unfoldings' membership (reflection) |
| the leaf's `ActionOrder` | the translation of the leaf keeps the order invariant (`OrderInv`) | **needs-proof**: `Tools/ShippingUnifiedProtection.lean` proves it for the quoted fragment only (`translateExprToWire_orders`). The legacy inline arm needs the same statement: an `ActionOrder` analogue of `legacy_translate_contract` (the inline attempt adds no statement of its own, so it should follow from the unfolding's order by the same `tryInlineUnfold_returns`; not written) |
| `0 < v.kind.width` | the value's width is positive | provable-now per declaration |

**Proved here**: `legacy_leaf_output` — the composition: given
`HarnessSound`, a harness run, the leaf's `LegacyDom` and `ActionOrder`, the
module has `RawValueAt` at the leaf's value. And `legacy_entry_output` — the
same from `LegacyEntryReduces` and a run of the legacy arm.

Nothing here discharges a hypothesis; the file fixes the STATEMENT the
remaining work has to meet, in the certified entry's own terms. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-- The compiler context and builder state the harness translates the leaf in
(the certified entry's `prepare` of its `start`). -/
abbrev setupOf (declName : Name) (bs : List (Name × MixedGateBinder)) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) (bools : FVarId → Bool)
    (bits : (id : FVarId) → (n : Nat) → BitVec n) : Tools.ShippingMixedEntrySoundness.Setup :=
  Tools.ShippingMixedEntrySoundness.prepare bools bits (bs.zip ids)
    (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))

/-- A successful run of the certified harness on an arbitrary leaf. -/
def HarnessRun (tenv : Lean.Environment) (logProf : String → IO Unit) (declName : Name)
    (bs : List (Name × MixedGateBinder)) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) (leaf : Lean.Expr) (returned : String)
    (st : CircuitState) : Prop :=
  Returns (bindMixedCertifiedInputs
      (emitLeaves (fun e hint top named => translateExprToWire tenv e hint top named) cache logProf
        [("out", leaf)] none 0) (bs.zip ids))
    (entryCompilerState false cache) (CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)) returned st

/-- **Harness soundness for any leaf** (PROVABLE-NOW, not proved here: the
proof of `synthesizeMixedCertified_term_sound_at` with the leaf's contract
and order as hypotheses). -/
def HarnessSound (tenv : Lean.Environment) : Prop :=
  ∀ (logProf : String → IO Unit) (declName : Name) (bs : List (Name × MixedGateBinder))
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (leaf : Lean.Expr)
    (returned : String) (st : CircuitState) (m : Sparkle.IR.AST.Module),
    HarnessRun tenv logProf declName bs ids cache leaf returned st →
    m = (addClockResetIfSequential st.module).finalize →
    Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true →
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) (mems : MEnv),
    Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
      (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName)) →
    ∀ v : Value, 0 < v.kind.width →
    Tools.ShippingUnifiedRecursion.Contract
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (setupOf declName bs ids cache bools bits).context
      (Tools.ShippingUnifiedMeaning.inputValues (setupOf declName bs ids cache bools bits).bools
        (setupOf declName bs ids cache bools bits).bits)
      (Tools.ShippingMixedOutputSoundness.declaredWidths st) mems initial leaf v →
    Tools.ShippingUnifiedProtection.ActionOrder (translateExprToWire tenv leaf "out" false true)
      (setupOf declName bs ids cache bools bits).context
      (Tools.ShippingUnifiedMeaning.inputValues (setupOf declName bs ids cache bools bits).bools
        (setupOf declName bs ids cache bools bits).bits)
      (Tools.ShippingMixedOutputSoundness.declaredWidths st) mems initial →
    Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width bs m initial mems v.toNat

/-- **The legacy arm reduces to the harness** (NEEDS-WALK, with oracle
premises; not proved): a successful run of `synthesizeFromConst` that takes
its legacy arm on `ci` and returns `(m, d)` is a run of the certified harness
on the leaf `leafOf ids` for some distinct binder variables `ids`, finished
like the certified entry finishes it. `bs` and `leafOf` are what the
declaration's binders and body are (as the telescope oracles return them). -/
def LegacyEntryReduces (tenv : Lean.Environment) (declName : Name) (ci : ConstantInfo)
    (bs : List (Name × MixedGateBinder)) (leafOf : List FVarId → Lean.Expr) : Prop :=
  ∀ (logProf : String → IO Unit) (isInst : Lean.Expr → Bool) (m : Sparkle.IR.AST.Module)
    (d : Design),
    MReturns (synthesizeFromConst (fun e hint top named => translateExprToWire tenv e hint top named)
      logProf declName [] false false ci isInst) (m, d) →
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (returned : String)
      (st : CircuitState),
      ids.Nodup ∧ ids.length = bs.length ∧
      HarnessRun tenv logProf declName bs ids cache (leafOf ids) returned st ∧
      m = (addClockResetIfSequential st.module).finalize ∧
      Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true

/-- **The output of a legacy-route leaf.** From a run of the harness, the
leaf in the combined domain at `v` and its order statement, the finished
module evaluates and `out` carries `v`. -/
theorem legacy_leaf_output (hs : HarnessSound tenv) {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {leaf : Lean.Expr} {returned : String}
    {st : CircuitState} {m : Sparkle.IR.AST.Module}
    (run : HarnessRun tenv logProf declName bs ids cache leaf returned st)
    (hm : m = (addClockResetIfSequential st.module).finalize)
    (legal : Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true)
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) (mems : MEnv)
    (values : Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
      (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName)))
    (v : Value) (pos : 0 < v.kind.width)
    (dom : LegacyDom tenv (setupOf declName bs ids cache bools bits).context
      (Tools.ShippingUnifiedMeaning.inputValues (setupOf declName bs ids cache bools bits).bools
        (setupOf declName bs ids cache bools bits).bits) leaf v)
    (ord : Tools.ShippingUnifiedProtection.ActionOrder (translateExprToWire tenv leaf "out" false true)
      (setupOf declName bs ids cache bools bits).context
      (Tools.ShippingUnifiedMeaning.inputValues (setupOf declName bs ids cache bools bits).bools
        (setupOf declName bs ids cache bools bits).bits)
      (Tools.ShippingMixedOutputSoundness.declaredWidths st) mems initial) :
    Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width bs m initial mems v.toNat :=
  hs logProf declName bs ids cache leaf returned st m run hm legal bools bits initial mems values
    v pos (legacy_translate_contract dom) ord

/-- **The output of a legacy-route declaration**, from the reduction of its
entry to the harness: for the binder variables and the builder state of the
run, every admissible input valuation at which the leaf is in the combined
domain (and ordered) gives the output's value. -/
theorem legacy_entry_output (hs : HarnessSound tenv) {declName : Name} {ci : ConstantInfo}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    (hred : LegacyEntryReduces tenv declName ci bs leafOf)
    {logProf : String → IO Unit} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Design}
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire tenv e hint top named)
      logProf declName [] false false ci isInst) (m, d)) :
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (st : CircuitState),
      ids.Nodup ∧ ids.length = bs.length ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName)) →
      ∀ v : Value, 0 < v.kind.width →
      LegacyDom tenv (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits) (leafOf ids) v →
      Tools.ShippingUnifiedProtection.ActionOrder
        (translateExprToWire tenv (leafOf ids) "out" false true)
        (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits)
        (Tools.ShippingMixedOutputSoundness.declaredWidths st) mems initial →
      Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width bs m initial mems v.toNat := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, legal⟩ := hred logProf isInst m d hr
  refine ⟨ids, cache, st, nd, len, ?_⟩
  intro bools bits initial mems values v pos dom ord
  exact legacy_leaf_output hs run hm legal bools bits initial mems values v pos dom ord

end Tools.ShippingLegacySem
