import Tools.ShippingLegacySemProj
import Tools.ShippingLegacySemPacked

/-! # The `Signal.fst` class of the legacy route: the entry statement over the PACKED input

The census (`Tests/Compiler/LegacyArmCensusTest.lean`, round 20): 39 of the
90 RETURNED declarations have a leaf headed by `Signal.fst` — a chain of
`Signal.fst` / `Signal.snd` over ONE Signal binder whose payload is a nested
product, plus the domain binder (`Sparkle.IP.RV32.SoC.SoCState.*`, the
accessors `declare_signal_state` generates).

**The statement that needs no new value model.** The legacy walk binds the
structured Signal as one port of the oracle's type, `bitVector N`
(`bindInputsLegacy` does not look at the payload: `inferHWTypeFromSignal`
returns a hardware type, the binder is a hardware binder). So the binder is
a `.bits N` binder of the certified `prepare` AS IT IS — `TypeOk (.bits N)`,
the input value `Value.bits N (bits x N)`: the PACKED vector, the same view
the emitted port has. The result is then a slice of that vector:

* `sliceValue v lo rk` — the value of the `rk`-kinded slice of `v` at the low
  offset `lo`: `Value.bits w (v.extractLsb' lo w)` for `rk = .bits w`,
  `Value.bool (v.getLsbD lo)` for `rk = .bool` (a `bit` wire).

**Defined here**

* `FstChainLeaf declName bs leafOf i N lo rk` — THE OBLIGATION OF THE WALK
  (item 3 of round 23; not proved): in every prepared setup in which the
  variable `x` at position `i` is mapped to the packed input
  `Value.bits N (bits x N)`, the leaf is in the leaf domain at
  `sliceValue (bits x N) lo rk`. This is a statement about the TRANSLATOR on
  the leaf (`LeafDom`: frame, outcome and order of `translateExprToWire`),
  not about the module.

**Proved here**

* `sliceValue_width`.
* `fst_entry_output_of_chain` — the ENTRY part, complete: for a declaration
  whose stripped value is `lams sp b` over binders `bs` with a `.bits N`
  binder at position `i`, a scalar Signal result that is not a lambda, and
  `FstChainLeaf`: a successful run of the shipping entry (certified front end
  on, the three gates declining) is a memo hit, or the module's `out`
  carries `sliceValue (bits x N) lo rk` — the slice of the PACKED input.
  The telescope (any arity), the binder walk with the domain skip, the input
  fact and the harness are discharged (`telescopeIn_of_lamsN`,
  `list_entry_outputDN`, `prepare_inputValue`).

(Round 24: the three decisions below were taken — sub-flags in
`HandlerCase`, and the two "run / world" premises `ArgRunsBody` and
`WireWidthReads` — and the walk is in `Tools/ShippingLegacySemFstArm.lean`;
the class's entry theorem is `fst_entry_output`,
`Tools/ShippingLegacySemFstEntry.lean`, with the chain's value as a function
of the packed input. This file is kept as round 23 left it.)

So what separates the 39 declarations from a theorem with the premise
classes of `proj_entry_output` is exactly `FstChainLeaf`. Why it is not
proved this round — three points that need a decision, in the order the walk
meets them (details and line numbers: `docs/parallel/G2-legacy-round23.md`):

1. `HandlerCase` asks the sub-expressions at the node's OWN hint and name
   flag; the `Signal.fst` arm translates its argument at hint `"s"`,
   `isNamed = false`. The arm is not a `HandlerCase` as that structure is
   defined (an existing Tools file).
2. That argument call is CACHEABLE (`!isNamed && !e.isFVar && !isTopLevel`)
   unless the argument is the input variable itself: for a chain of depth
   ≥ 2 the shim may return an unvalidated hit of the `IO.Ref` expression
   cache (`legacyShim_returns`' second disjunct).
3. The slice bounds are computed from `CompilerM.getWireWidth wireS`, which
   reads the `IO.Ref` width cache before the builder state: an unvalidated
   read of the world.

**Premises of `fst_entry_output_of_chain`, classified**

| Premise | Class |
|---|---|
| `old`, `mixed`, `hmach` | reflection of the environment |
| `htel : LamTelescopeND` | Meta-library fact |
| `hbody` (shape, `TypesOkFrom`, leaf equation) | reflection + binder-type oracle (`InfersHW T (bitVector N)` on the structured binder's type: the oracle's product arm) |
| `hfield`, `hpos` | closed facts |
| `hlam` | closed computation on the leaf |
| `hres` | result-type oracle |
| `hchain : FstChainLeaf …` | THE OPEN OBLIGATION (the walk of the `Signal.fst` / `Signal.snd` arms) |
| `hr` | the run |
-/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-- The value of the slice of the packed vector `v` at the low offset `lo`,
as a result of kind `rk`. -/
def sliceValue {N : Nat} (v : BitVec N) (lo : Nat) :
    Tools.ShippingUnifiedMeaning.Kind → Value
  | .bool => Value.bool (v.getLsbD lo)
  | .bits w => Value.bits w (v.extractLsb' lo w)

theorem sliceValue_width {N : Nat} (v : BitVec N) (lo : Nat)
    (rk : Tools.ShippingUnifiedMeaning.Kind) :
    (sliceValue v lo rk).kind.width = rk.width := by
  cases rk <;> rfl

/-- **The obligation of the walk** (not proved): the leaf is in the leaf
domain at the slice of the packed input, in every prepared setup that maps
the variable at position `i` to the packed input. -/
def FstChainLeaf (declName : Name) (bs : List (Name × MixedGateBinder))
    (leafOf : List FVarId → Lean.Expr) (i N lo : Nat)
    (rk : Tools.ShippingUnifiedMeaning.Kind) : Prop :=
  ∀ (ids : List FVarId) (x : FVarId) (cache : IO.Ref (ExprStructMap String))
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
    ids.length = bs.length → AtIdx ids i x →
    Tools.ShippingUnifiedMeaning.inputValues
      (setupOf declName bs ids cache bools bits).bools
      (setupOf declName bs ids cache bools bits).bits x =
      some (Value.bits N (bits x N)) →
    LeafDom (setupOf declName bs ids cache bools bits).context
      (Tools.ShippingUnifiedMeaning.inputValues
        (setupOf declName bs ids cache bools bits).bools
        (setupOf declName bs ids cache bools bits).bits)
      "out" true (leafOf ids) (sliceValue (bits x N) lo rk)

/-- **The entry part of the `Signal.fst` class**: from the walk's obligation
`FstChainLeaf`, the output of the shipping entry is the slice of the packed
input. -/
theorem fst_entry_output_of_chain {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {i N lo : Nat} {nm : Name}
    {rk : Tools.ShippingUnifiedMeaning.Kind}
    (old : certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htel : LamTelescopeND)
    (hbody : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      ∃ (sp : List (Name × Lean.Expr × BinderInfo)) (b : Lean.Expr),
        stripMemoizeWrappers body0 = lams sp b ∧
        b.isLambda = false ∧
        TypesOkFrom sp bs #[] ∧
        ∀ ids : List FVarId, ids.length = bs.length →
          b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
            (ids.map Lean.Expr.fvar).toArray = leafOf ids)
    (hfield : AtIdx bs i (nm, MixedGateBinder.bits N))
    (hpos : 0 < rk.width)
    (hlam : ∀ ids : List FVarId, ids.length = bs.length → (leafOf ids).isLambda = false)
    (hres : ∀ ids : List FVarId, ids.length = bs.length → SignalTyped (leafOf ids))
    (hchain : FstChainLeaf declName bs leafOf i N lo rk)
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false true (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    ∃ (ids : List FVarId) (x : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧ ids.Nodup ∧ AtIdx ids i x ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt rk.width bs m initial mems
        (sliceValue (bits x N) lo rk).toNat := by
  have htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (ListScopeDN bs leafOf) := by
    intro body0 hopen
    obtain ⟨sp, b, hb, hl, hT, hi⟩ := hbody body0 hopen
    exact telescopeIn_of_lamsN htel hb hl hT hi
  have hleaf : ∀ ids : List FVarId, ids.length = bs.length →
      (leafOf ids).isLambda = false ∧ SignalTyped (leafOf ids) :=
    fun ids hlen => ⟨hlam ids hlen, hres ids hlen⟩
  rcases list_entry_outputDN (cfe := true) (bs := bs) (leafOf := leafOf)
      (fun _ => old) (fun _ => mixed) (fun _ => hmach) htele hleaf hr with
    hit | ⟨ids, cache, hlen, hnd, H⟩
  · exact Or.inl hit
  · obtain ⟨x, hx⟩ := AtIdx.transfer bs ids i (nm, MixedGateBinder.bits N) hlen hfield
    refine Or.inr ⟨ids, x, cache, hlen, hnd, hx, ?_⟩
    intro bools bits initial mems values
    have hin : Tools.ShippingUnifiedMeaning.inputValues
        (setupOf declName bs ids cache bools bits).bools
        (setupOf declName bs ids cache bools bits).bits x =
        some (Value.bits N (bits x N)) :=
      prepare_inputValue (bools := bools) (bits := bits) bs ids i
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) nm (MixedGateBinder.bits N) x hnd hfield hx
        (by intro h; cases h)
    have dom := hchain ids x cache bools bits hlen hx hin
    have pos : 0 < (sliceValue (bits x N) lo rk).kind.width := by
      rw [sliceValue_width]
      exact hpos
    have out := H bools bits initial mems values (sliceValue (bits x N) lo rk) pos dom
    rw [sliceValue_width] at out
    exact out

end Tools.ShippingLegacySem
