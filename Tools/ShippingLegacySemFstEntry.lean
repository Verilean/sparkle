import Tools.ShippingLegacySemFstArm
import Tools.ShippingLegacySemFst

/-! # The `Signal.fst` class: the chain, and the entry theorem

**Defined here**

* `SubChain ctx x N e M g` — `e` is a chain of `Signal.fst` / `Signal.snd`
  applications over the variable `x` (bound to a packed input of width `N`),
  every node of it translated at the argument flags `("s", false, false)`;
  the chain's packed width is `M` and its value, as a function of the
  packed input, is `g : BitVec N → BitVec M`:
  - `var`: the variable, `g = id`;
  - `fst`: a `Signal.fst` node over a chain of width `M`, result width `w`:
    `g' v = (g v).extractLsb' (M - w) w` — with the node's facts
    (`TupleNode`), the argument's oracle (`ExprHW a (bitVector M)`) and the
    node's cache premise (`ArgRunsBody`, every fuel);
  - `snd`: `g' v = (g v).extractLsb' 0 w`.

**Proved here**

* `subChain_leaf` — by induction on the chain: `e` is in
  `LeafDom ctx inputs "s" false` at `Value.bits M (g v)` when the input map
  gives `x` the packed value `v`.
* `topFst_leaf` — the TOP node (a `Signal.fst` at any hint, `named = true`:
  not cacheable, no cache premise) over a `SubChain`.
* `extract_extract`, `subChain_slice` — OFFSET COMPOSITION: the chain's value
  is one slice of the packed input, `g v = v.extractLsb' lo M` with
  `lo + M ≤ N`.
* `fst_entry_output` — THE ENTRY THEOREM OF THE CLASS: for a declaration
  whose stripped value is `lams sp b` over binders `bs` with a `.bits N`
  binder at position `i`, whose leaf is a `Signal.fst` node over a
  `SubChain` in every prepared setup: a successful run of the shipping
  entry is a memo hit, or `out` carries `g (bits x N)` — a function of the
  PACKED input fixed by the chain (`subChain_slice`: a slice of it).

**Premises of `fst_entry_output`, classified**

| Premise | Class |
|---|---|
| `old`, `mixed`, `hmach` | reflection of the environment |
| `htel : LamTelescopeND` | Meta-library fact |
| `hbody` | reflection (shape, leaf equation) + binder-type oracle (`TypesOkFrom`) |
| `hfield` | closed fact of the binder list |
| `thF`, `thS`, `hne` | closed name tests on `Signal.fst` / `Signal.snd` |
| `plainF`, `plainS` | environment (`PlainHead`: not a hardware module, not a projection) |
| `hlam` | closed computation on the leaf |
| `hres` | result-type oracle |
| `hchain` — per node: `TupleNode.head/arg/size/kind/notCore` | closed computations on the node |
| `hchain` — per node: `TupleNode.mapped` | the body's `whnf` test (`Expr.find?`, kernel-opaque) |
| `hchain` — per node: `TupleNode.nodeHW`, `ExprHW a (bitVector M)` | oracle (`cachedInferType` + `inferHWTypeFromSignal`) |
| `hchain` — per node: `TupleNode.widthReads` (`WireWidthReads`) | THE RUN / THE WORLD — false with a stale `sparkleWireWidthCache` entry |
| `hchain` — per node below the top: `ArgRunsBody` | THE RUN / THE WORLD — false on a stale expression-cache entry (the gap of `NoSubModule` / the unvalidated shim hit) |
| `hr` | the run |
-/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-- A chain of `Signal.fst` / `Signal.snd` over the variable `x`, every node
translated at the argument flags, with its packed width and its value as a
function of the packed input. -/
inductive SubChain (ctx : CompilerState) (x : FVarId) (N : Nat) :
    Lean.Expr → (M : Nat) → (BitVec N → BitVec M) → Prop where
  | var : SubChain ctx x N (Lean.Expr.fvar x) N (fun v => v)
  | fst {f a : Lean.Expr} {M w : Nat} {g : BitVec N → BitVec M} :
      SubChain ctx x N a M g →
      TupleNode ctx ``Sparkle.Core.Signal.Signal.fst f a M w →
      ExprHW a (Sparkle.IR.Type.HWType.bitVector M) →
      (∀ fuel : Nat, ArgRunsBody (translateFuelFix translateStep fuel) ctx (Lean.Expr.app f a)) →
      SubChain ctx x N (Lean.Expr.app f a) w (fun v => BitVec.extractLsb' (M - w) w (g v))
  | snd {f a : Lean.Expr} {M w : Nat} {g : BitVec N → BitVec M} :
      SubChain ctx x N a M g →
      TupleNode ctx ``Sparkle.Core.Signal.Signal.snd f a M w →
      (∀ fuel : Nat, ArgRunsBody (translateFuelFix translateStep fuel) ctx (Lean.Expr.app f a)) →
      SubChain ctx x N (Lean.Expr.app f a) w (fun v => BitVec.extractLsb' 0 w (g v))

/-- **A chain is a leaf at the argument flags**, at its packed value. -/
theorem subChain_leaf {ctx : CompilerState} {inputs : FVarId → Option Value} {x : FVarId}
    {N : Nat} {v : BitVec N}
    (thF : TupleHead ``Sparkle.Core.Signal.Signal.fst)
    (thS : TupleHead ``Sparkle.Core.Signal.Signal.snd)
    (hne : ((``Sparkle.Core.Signal.Signal.snd : Name) == ``Sparkle.Core.Signal.Signal.fst) = false)
    (plainF : PlainHead ``Sparkle.Core.Signal.Signal.fst)
    (plainS : PlainHead ``Sparkle.Core.Signal.Signal.snd)
    (hi : inputs x = some (Value.bits N v))
    {e : Lean.Expr} {M : Nat} {g : BitVec N → BitVec M} (h : SubChain ctx x N e M g) :
    LeafDom ctx inputs "s" false e (Value.bits M (g v)) := by
  induction h with
  | var => exact LeafDom.dom (LegacyDom.input hi)
  | @fst f a M w g _ nd hS hshim ih =>
    exact LeafDom.handled _
      (handlerCase_fst (u := g v) thF plainF nd hS
        (fun fuel => shimBody_of_argRunsBody (hshim fuel)))
      (fun h' n' e' v' hs => by
        obtain ⟨hh, hn, he, hv⟩ := hs
        rw [hh, hn, he, hv]
        exact ih)
  | @snd f a M w g _ nd hshim ih =>
    exact LeafDom.handled _
      (handlerCase_snd (u := g v) thS plainS hne nd
        (fun fuel => shimBody_of_argRunsBody (hshim fuel)))
      (fun h' n' e' v' hs => by
        obtain ⟨hh, hn, he, hv⟩ := hs
        rw [hh, hn, he, hv]
        exact ih)

/-- **The top node**: a `Signal.fst` at the entry's flags (named: the shim
runs the body) over a chain. -/
theorem topFst_leaf {ctx : CompilerState} {inputs : FVarId → Option Value} {x : FVarId}
    {N : Nat} {v : BitVec N} {hint : String}
    (thF : TupleHead ``Sparkle.Core.Signal.Signal.fst)
    (thS : TupleHead ``Sparkle.Core.Signal.Signal.snd)
    (hne : ((``Sparkle.Core.Signal.Signal.snd : Name) == ``Sparkle.Core.Signal.Signal.fst) = false)
    (plainF : PlainHead ``Sparkle.Core.Signal.Signal.fst)
    (plainS : PlainHead ``Sparkle.Core.Signal.Signal.snd)
    (hi : inputs x = some (Value.bits N v))
    {f a : Lean.Expr} {M w : Nat} {g : BitVec N → BitVec M}
    (hsub : SubChain ctx x N a M g)
    (nd : TupleNode ctx ``Sparkle.Core.Signal.Signal.fst f a M w)
    (hS : ExprHW a (Sparkle.IR.Type.HWType.bitVector M)) :
    LeafDom ctx inputs hint true (Lean.Expr.app f a)
      (Value.bits w (BitVec.extractLsb' (M - w) w (g v))) :=
  LeafDom.handled _
    (handlerCase_fst (u := g v) thF plainF nd hS (fun _ => shimBody_named))
    (fun h' n' e' v' hs => by
      obtain ⟨hh, hn, he, hv⟩ := hs
      rw [hh, hn, he, hv]
      exact subChain_leaf thF thS hne plainF plainS hi hsub)

/-- A slice of a slice is a slice. -/
theorem extract_extract {N : Nat} (v : BitVec N) (lo M k w : Nat) (h : k + w ≤ M) :
    BitVec.extractLsb' k w (BitVec.extractLsb' lo M v) = BitVec.extractLsb' (lo + k) w v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : k + i < M := by omega
  first
    | (simp only [BitVec.getLsbD_extractLsb', hi, h1, decide_true, Bool.true_and, Nat.add_assoc])
    | simp [BitVec.getLsbD_extractLsb', hi, h1, Nat.add_assoc]

/-- **Offset composition**: the value of a chain is ONE slice of the packed
input. -/
theorem subChain_slice {ctx : CompilerState} {x : FVarId} {N : Nat}
    {e : Lean.Expr} {M : Nat} {g : BitVec N → BitVec M} (h : SubChain ctx x N e M g) :
    ∃ lo : Nat, lo + M ≤ N ∧ ∀ v : BitVec N, g v = BitVec.extractLsb' lo M v := by
  induction h with
  | var =>
    refine ⟨0, Nat.le_of_eq (Nat.zero_add N), ?_⟩
    intro v
    first
      | exact BitVec.extractLsb'_eq_self.symm
      | simp
  | @fst f a M w g _ nd _ _ ih =>
    obtain ⟨lo, hle, hg⟩ := ih
    have hwM := nd.le
    refine ⟨lo + (M - w), by omega, ?_⟩
    intro v
    show BitVec.extractLsb' (M - w) w (g v) = BitVec.extractLsb' (lo + (M - w)) w v
    rw [hg v]
    exact extract_extract v lo M (M - w) w (by omega)
  | @snd f a M w g _ nd _ ih =>
    obtain ⟨lo, hle, hg⟩ := ih
    have hwM := nd.le
    refine ⟨lo, by omega, ?_⟩
    intro v
    show BitVec.extractLsb' 0 w (g v) = BitVec.extractLsb' lo w v
    rw [hg v]
    exact extract_extract v lo M 0 w (by omega)

/-- **The output of a legacy-route declaration whose leaf is a `Signal.fst`
chain over one packed Signal input**, in the shipping configuration: memo
hit, or `out` carries `g (bits x N)`, the chain's function of the packed
input (`subChain_slice`: a slice `[lo + w - 1 : lo]` of it).

Per node of the chain the premise `hchain` carries, beside closed
computations and oracles, two premises of the class "the run / the world":
`WireWidthReads` (in `TupleNode.widthReads`) — false when
`sparkleWireWidthCache` holds a stale width for the argument's wire — and,
for every node below the top, `ArgRunsBody` — false when the argument's
cacheable translation hits a stale entry of the expression cache (the same
gap as `NoSubModule` and the unvalidated hit of `legacyShim_returns`). No
compiler change is assumed. -/
theorem fst_entry_output {logProf : String → IO Unit} {declName : Name}
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
      ∃ (f a : Lean.Expr) (M : Nat) (g0 : BitVec N → BitVec M),
        leafOf ids = Lean.Expr.app f a ∧
        SubChain (setupOf declName bs ids cache bools bits).context x N a M g0 ∧
        TupleNode (setupOf declName bs ids cache bools bits).context
          ``Sparkle.Core.Signal.Signal.fst f a M w ∧
        ExprHW a (Sparkle.IR.Type.HWType.bitVector M) ∧
        ∀ v : BitVec N, BitVec.extractLsb' (M - w) w (g0 v) = g v)
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
    obtain ⟨f, a, M, g0, he, hsub, nd, hS, hg⟩ := hchain ids x cache bools bits hlen hx
    have dom : LeafDom (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits)
        "out" true (leafOf ids) (Value.bits w (g (bits x N))) := by
      rw [he, ← hg (bits x N)]
      exact topFst_leaf thF thS hne plainF plainS hin hsub nd hS
    exact H bools bits initial mems values (Value.bits w (g (bits x N))) nd.pos dom

end Tools.ShippingLegacySem
