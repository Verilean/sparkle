import Tools.ShippingLegacySemFstEntry

/-! # The tuple-projection class: one entry theorem, the top node either projection

`fst_entry_output` (`Tools/ShippingLegacySemFstEntry.lean`) asks the leaf to
be a `Signal.fst` over a chain. The 39 declarations of the census class all
are (`FST CLASS`, round 23: the class is "head `Signal.fst`", and the three
sampled chains are `fst.snd.….snd` over the variable — the accessors
`declare_signal_state` generates for every field but the last). The last
field of such a state is `snd.….snd`: a top `Signal.snd`. So that no
accessor shape is left out, the top node is here either projection.

**Defined here**

* `TopNode ctx x N e w g` — the leaf `e`, translated at the entry's flags
  (`named = true`: not cacheable, no cache premise for this node), is a
  `Signal.fst` or a `Signal.snd` over a `SubChain`; `g : BitVec N → BitVec w`
  is its value as a function of the packed input.

**Proved here**

* `topSnd_leaf` (beside `topFst_leaf`), `topNode_leaf`.
* `TopNode.pos`, `topNode_slice` (the value is ONE slice of the packed
  input: `g v = v.extractLsb' lo w`, `lo + w ≤ N`).
* `tuple_entry_output` — THE ENTRY THEOREM OF THE CLASS, top node either:
  memo hit, or `out` carries `g (bits x N)`.

Premise classes: those of `fst_entry_output` (its header's table), with
`hchain` now `TopNode … (leafOf ids) w g` in every prepared setup. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-- **The top node `Signal.snd`** at the entry's flags over a chain. -/
theorem topSnd_leaf {ctx : CompilerState} {inputs : FVarId → Option Value} {x : FVarId}
    {N : Nat} {v : BitVec N} {hint : String}
    (thF : TupleHead ``Sparkle.Core.Signal.Signal.fst)
    (thS : TupleHead ``Sparkle.Core.Signal.Signal.snd)
    (hne : ((``Sparkle.Core.Signal.Signal.snd : Name) == ``Sparkle.Core.Signal.Signal.fst) = false)
    (plainF : PlainHead ``Sparkle.Core.Signal.Signal.fst)
    (plainS : PlainHead ``Sparkle.Core.Signal.Signal.snd)
    (hi : inputs x = some (Value.bits N v))
    {f a : Lean.Expr} {M w : Nat} {g : BitVec N → BitVec M}
    (hsub : SubChain ctx x N a M g)
    (nd : TupleNode ctx ``Sparkle.Core.Signal.Signal.snd f a M w) :
    LeafDom ctx inputs hint true (Lean.Expr.app f a)
      (Value.bits w (BitVec.extractLsb' 0 w (g v))) :=
  LeafDom.handled _
    (handlerCase_snd (u := g v) thS plainS hne nd (fun _ => shimBody_named))
    (fun h' n' e' v' hs => by
      obtain ⟨hh, hn, he, hv⟩ := hs
      rw [hh, hn, he, hv]
      exact subChain_leaf thF thS hne plainF plainS hi hsub)

/-- The leaf at the entry's flags: a `Signal.fst` or a `Signal.snd` over a
chain, with its value as a function of the packed input. -/
inductive TopNode (ctx : CompilerState) (x : FVarId) (N : Nat) :
    Lean.Expr → (w : Nat) → (BitVec N → BitVec w) → Prop where
  | fst {f a : Lean.Expr} {M w : Nat} {g : BitVec N → BitVec M} :
      SubChain ctx x N a M g →
      TupleNode ctx ``Sparkle.Core.Signal.Signal.fst f a M w →
      ExprHW a (Sparkle.IR.Type.HWType.bitVector M) →
      TopNode ctx x N (Lean.Expr.app f a) w (fun v => BitVec.extractLsb' (M - w) w (g v))
  | snd {f a : Lean.Expr} {M w : Nat} {g : BitVec N → BitVec M} :
      SubChain ctx x N a M g →
      TupleNode ctx ``Sparkle.Core.Signal.Signal.snd f a M w →
      TopNode ctx x N (Lean.Expr.app f a) w (fun v => BitVec.extractLsb' 0 w (g v))

/-- **The top node is a leaf at the entry's flags.** -/
theorem topNode_leaf {ctx : CompilerState} {inputs : FVarId → Option Value} {x : FVarId}
    {N : Nat} {v : BitVec N} {hint : String}
    (thF : TupleHead ``Sparkle.Core.Signal.Signal.fst)
    (thS : TupleHead ``Sparkle.Core.Signal.Signal.snd)
    (hne : ((``Sparkle.Core.Signal.Signal.snd : Name) == ``Sparkle.Core.Signal.Signal.fst) = false)
    (plainF : PlainHead ``Sparkle.Core.Signal.Signal.fst)
    (plainS : PlainHead ``Sparkle.Core.Signal.Signal.snd)
    (hi : inputs x = some (Value.bits N v))
    {e : Lean.Expr} {w : Nat} {g : BitVec N → BitVec w} (h : TopNode ctx x N e w g) :
    LeafDom ctx inputs hint true e (Value.bits w (g v)) := by
  cases h with
  | fst hsub nd hS => exact topFst_leaf thF thS hne plainF plainS hi hsub nd hS
  | snd hsub nd => exact topSnd_leaf thF thS hne plainF plainS hi hsub nd

/-- The result of a top node has positive width. -/
theorem TopNode.pos {ctx : CompilerState} {x : FVarId} {N : Nat} {e : Lean.Expr} {w : Nat}
    {g : BitVec N → BitVec w} (h : TopNode ctx x N e w g) : 0 < w := by
  cases h with
  | fst _ nd _ => exact nd.pos
  | snd _ nd => exact nd.pos

/-- **The value of the leaf is ONE slice of the packed input.** -/
theorem topNode_slice {ctx : CompilerState} {x : FVarId} {N : Nat} {e : Lean.Expr} {w : Nat}
    {g : BitVec N → BitVec w} (h : TopNode ctx x N e w g) :
    ∃ lo : Nat, lo + w ≤ N ∧ ∀ v : BitVec N, g v = BitVec.extractLsb' lo w v := by
  cases h with
  | @fst f a M w g0 hsub nd hS =>
    obtain ⟨lo, hle, hg⟩ := subChain_slice hsub
    have hwM := nd.le
    refine ⟨lo + (M - w), by omega, ?_⟩
    intro v
    show BitVec.extractLsb' (M - w) w (g0 v) = BitVec.extractLsb' (lo + (M - w)) w v
    rw [hg v]
    exact extract_extract v lo M (M - w) w (by omega)
  | @snd f a M w g0 hsub nd =>
    obtain ⟨lo, hle, hg⟩ := subChain_slice hsub
    have hwM := nd.le
    refine ⟨lo, by omega, ?_⟩
    intro v
    show BitVec.extractLsb' 0 w (g0 v) = BitVec.extractLsb' lo w v
    rw [hg v]
    exact extract_extract v lo M 0 w (by omega)

/-- **The output of a legacy-route declaration whose leaf is a tuple
projection chain over one packed Signal input** (top node `Signal.fst` or
`Signal.snd`), in the shipping configuration: memo hit, or `out` carries
`g (bits x N)`, the chain's function of the packed input (`topNode_slice`:
one slice of it).

As in `fst_entry_output`, `hchain` carries per node two premises of the
class "the run / the world": `WireWidthReads` (false when
`sparkleWireWidthCache` holds a stale width for the argument's wire) and,
for every node below the top, `ArgRunsBody` (false when the cacheable
argument translation hits a stale entry of the expression cache — the gap
of `NoSubModule` / the unvalidated shim hit). No compiler change is
assumed. -/
theorem tuple_entry_output {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {i N w : Nat} {nm : Name}
    {g : BitVec N → BitVec w}
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
    (thF : TupleHead ``Sparkle.Core.Signal.Signal.fst)
    (thS : TupleHead ``Sparkle.Core.Signal.Signal.snd)
    (hne : ((``Sparkle.Core.Signal.Signal.snd : Name) == ``Sparkle.Core.Signal.Signal.fst) = false)
    (plainF : PlainHead ``Sparkle.Core.Signal.Signal.fst)
    (plainS : PlainHead ``Sparkle.Core.Signal.Signal.snd)
    (hlam : ∀ ids : List FVarId, ids.length = bs.length → (leafOf ids).isLambda = false)
    (hres : ∀ ids : List FVarId, ids.length = bs.length → SignalTyped (leafOf ids))
    (hchain : ∀ (ids : List FVarId) (x : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
      ids.length = bs.length → AtIdx ids i x →
      TopNode (setupOf declName bs ids cache bools bits).context x N (leafOf ids) w g)
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
      Tools.ShippingMixedEntrySoundness.RawValueAt w bs m initial mems
        (g (bits x N)).toNat := by
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
    have top := hchain ids x cache bools bits hlen hx
    have dom : LeafDom (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits)
        "out" true (leafOf ids) (Value.bits w (g (bits x N))) :=
      topNode_leaf thF thS hne plainF plainS hin top
    exact H bools bits initial mems values (Value.bits w (g (bits x N))) top.pos dom

end Tools.ShippingLegacySem
