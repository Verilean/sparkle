import Tools.ShippingLegacySemMemoWalk
import Tools.ShippingMemoLawsWith
import Tools.ShippingLegacySemTupleEntry
import Tools.ShippingLegacySemEntryBound

/-! # More legacy entry theorems without the memo disjunct, at the outermost entry

The recipe of `Tools/ShippingLegacySemMemoWalk.lean` (`proj_entry_output_at`
/ `_miss` / `_outer`) applied to two more theorems. Each `_at` proof is the
old proof with `list_entry_outputDN_at` / `legacy_entry_walk_start` in place
of `list_entry_outputDN` / `legacy_entry_walk_in`. All under the extended
boundary `RefLawsM` (`Tools/ShippingMemoLaws.lean` — an EXTENSION of the
trust base; not a completion of the general theorem).

* `tuple_entry_output_at`, `tuple_entry_output_miss`,
  `tuple_entry_output_outer` — the tuple projection class
  (`Tools/ShippingLegacySemTupleEntry.lean`; 39 `SoCState` declarations fit
  its observable premises by census). The per-node premises of the class
  "the run / the world" (`WireWidthReads`, `ArgRunsBody`, inside `hchain`)
  are untouched: they are not memo facts.
* `one_binder_entry_output_bound_at`, `one_binder_entry_output_bound_miss` —
  the one-binder theorem behind `useDbl_output`
  (`Tools/ShippingLegacySemEntryBound.lean`), either front end.
  `useDbl_output_outer` itself is in
  `Tests/Compiler/LegacySemMemoOuterTest.lean` (the declaration lives in a
  test file). -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)
open Tools.ShippingMemo (RefLawsM EntryConstIs outer_reset_reaches)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The tuple class -/

/-- **`tuple_entry_output` for ONE run**: the first disjunct is a fact about
this run's start world. -/
theorem tuple_entry_output_at (L : RefLawsM mref cref)
    {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {i N w : Nat} {nm : Name}
    {g : BitVec N → BitVec w} {w0 w1 : Void IO.RealWorld}
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
    (hr : RunsTo (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false true (.defnInfo dv) isInst) mctx mref cctx cref w0 (m, d) w1) :
    (L.mval w0).get? declName = some (m, d) ∨
    ∃ (ids : List FVarId) (x : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧ ids.Nodup ∧ AtIdx ids i x ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName)) →
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
  rcases list_entry_outputDN_at L (cfe := true) (bs := bs) (leafOf := leafOf)
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
          (Sparkle.IR.ModuleName.ofDecl declName)) nm (MixedGateBinder.bits N) x hnd hfield hx
        (by intro h; cases h)
    have top := hchain ids x cache bools bits hlen hx
    have dom : LeafDom (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits)
        "out" true (leafOf ids) (Value.bits w (g (bits x N))) :=
      topNode_leaf thF thS hne plainF plainS hin top
    exact H bools bits initial mems values (Value.bits w (g (bits x N))) top.pos dom

/-- **The tuple class, no memo disjunct, when the start world's memo has no
entry for the declaration.** -/
theorem tuple_entry_output_miss (L : RefLawsM mref cref)
    {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {i N w : Nat} {nm : Name}
    {g : BitVec N → BitVec w} {w0 w1 : Void IO.RealWorld}
    (hmiss : (L.mval w0).get? declName = none)
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
    (hr : RunsTo (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false true (.defnInfo dv) isInst) mctx mref cctx cref w0 (m, d) w1) :
    ∃ (ids : List FVarId) (x : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧ ids.Nodup ∧ AtIdx ids i x ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName)) →
      Tools.ShippingMixedEntrySoundness.RawValueAt w bs m initial mems
        (g (bits x N)).toNat := by
  rcases tuple_entry_output_at L (i := i) (nm := nm) (g := g) old mixed hmach htel hbody hfield
      thF thS hne plainF plainS hlam hres hchain hr with hit | H
  · rw [hmiss] at hit
    cases hit
  · exact H

/-- **The tuple class at the OUTERMOST entry, with no memo disjunct.** A
returning run of the core entry `synthesizeCombinationalCore declName []
false` from a world at synthesis depth 0, under the extended boundary.
Premises beyond `tuple_entry_output`'s: the boundary (`L`, `L.dval w0 = 0`,
`L.quiet w0`) and the link `EntryConstIs`; `mixed` for the instance
predicate of the environment the run read. -/
theorem tuple_entry_output_outer (L : RefLawsM mref cref) {declName : Name}
    {dv : DefinitionVal}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {i N w : Nat} {nm : Name}
    {g : BitVec N → BitVec w} {w0 w1 : Void IO.RealWorld}
    (h0 : L.dval w0 = 0) (hq : L.quiet w0)
    (hconst : EntryConstIs mctx mref cctx cref declName dv)
    (old : certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : ∀ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
      mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = none)
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
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref
      w0 (m, d) w1) :
    ∃ (ids : List FVarId) (x : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧ ids.Nodup ∧ AtIdx ids i x ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName)) →
      Tools.ShippingMixedEntrySoundness.RawValueAt w bs m initial mems
        (g (bits x N)).toNat := by
  obtain ⟨b, envR, ci, v1, v2, v3, v4, v5, v6, hget, henv, hrun, hempty⟩ :=
    outer_reset_reaches L h0 hq hr
  rw [hconst ci envR v1 v2 v5 v6 hget henv] at hrun
  have hmiss : (L.mval v3).get? declName = none := by
    rw [hempty]
    first
      | done
      | exact Tools.ShippingMemo.get?_empty declName
  exact tuple_entry_output_miss L (i := i) (nm := nm) (g := g) hmiss old
    (mixed envR v5 v6 henv) hmach htel hbody hfield thF thS hne plainF plainS hlam hres
    hchain hrun

/-! ## One `bits n` binder (the theorem behind `useDbl_output`) -/

/-- **`one_binder_entry_output_bound` for ONE run**, either front end: the
first disjunct is a fact about this run's start world. -/
theorem one_binder_entry_output_bound_at (L : RefLawsM mref cref)
    {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {nm : Name} {n : Nat} {T : Lean.Expr}
    {leafOf : FVarId → Lean.Expr} {m : Sparkle.IR.AST.Module} {d : Design} {cfe : Bool}
    {w0 w1 : Void IO.RealWorld}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (OneBinderScope nm T leafOf))
    (hsig : SignalTestFrame T) (hinf : InfersBits T n) (hnt : InfersNoCatch T)
    (hleaf : ∀ id : FVarId, (leafOf id).isLambda = false ∧ SignalTyped (leafOf id))
    (hr : RunsTo (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false cfe (.defnInfo dv) isInst) mctx mref cctx cref w0 (m, d) w1) :
    (L.mval w0).get? declName = some (m, d) ∨
    ∃ (id : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
        ([(nm, MixedGateBinder.bits n)].zip [id])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName)) →
      ∀ v : Value, 0 < v.kind.width →
      LeafDom (setupOf declName [(nm, MixedGateBinder.bits n)] [id] cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName [(nm, MixedGateBinder.bits n)] [id] cache bools bits).bools
          (setupOf declName [(nm, MixedGateBinder.bits n)] [id] cache bools bits).bits)
        "out" true (leafOf id) v →
      Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width
        [(nm, MixedGateBinder.bits n)] m initial mems v.toNat := by
  rcases legacy_entry_walk_start L old mixed hmach htele hr with hit |
    ⟨body0, mctx1, xs, inner, leaves, cache, returned, st, hopen,
      ⟨id, d0, hxs, hinner, hfind, hnm, hty⟩, hsplit, run, hm, legal⟩
  · exact Or.inl hit
  · refine Or.inr ?_
    rw [hinner] at hsplit
    have hl : leaves.toList = [("out", leafOf id)] :=
      splitReturnLeaves_scalar (hleaf id).1 (hleaf id).2 hsplit
    rw [hl] at run
    rw [hxs] at run
    have hsig' : SignalTestFrame d0.type := by
      rw [hty]
      exact hsig
    have hinf' : InfersBits d0.type n := by
      rw [hty]
      exact hinf
    have hnt' : InfersNoCatch d0.type := by
      rw [hty]
      exact hnt
    have bound := bindInputsLegacy_one_bound hfind hsig' hinf' hnt' run
    refine ⟨id, cache, ?_⟩
    rw [hnm] at bound
    have run' : HarnessRun logProf declName [(nm, MixedGateBinder.bits n)] [id] cache
        (leafOf id) returned st := bound
    intro bools bits initial mems values v pos dom
    exact leaf_output run' hm legal bools bits initial mems values v pos dom

end Tools.ShippingLegacySem
