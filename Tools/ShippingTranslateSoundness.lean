import Tools.ShippingAllocationSoundness
import Sparkle.IR.OptCheck
import Tools.ShippingBindingsSoundness

/-! # Success and semantic preservation of the SHIPPING translator

This file fixes the formal shape of the goal "the existing compiler, when it
succeeds, preserves meaning", and proves one branch of the real translator in
that shape. It is a check of the proof METHOD on the actual code, not a smaller
target: the same definitions are meant to carry every handler.

## Decisions (each forced by a measured fact)

1. **Success.** `Returns m ctx s a s'` : there is SOME MetaM/Core environment
   and world in which the real `CompilerM` action `m` returns `a` with final
   builder state `s'`. Theorems are stated as `Returns … → Q`, so they hold in
   every environment. `IO` in this toolchain is the exposed `EST` monad, so the
   rules below (`bind`, `pure`, `liftMetaM`, `throw`, `get`, `set`) are proved
   by definitional unfolding — no `LawfulMonad MetaM` is assumed or needed.
2. **Oracles.** A MetaM query lifted into the compiler has an UNCONSTRAINED
   result (`Returns.liftMetaM` constrains only the builder state). Anything the
   emitted IR depends on must therefore be computed purely from the `Expr`, or
   appear as a named assumption. The width of a canonical operator is now read
   from the instance's literal width argument for this reason.
3. **Recursion.** The translator is a `mutual` block of `partial def`s, which
   the kernel sees as `opaque` (checked: `#print translateExprToWire`). Nothing
   can be proved about it. Branches are therefore written as plain definitions
   parametrised by the recursive call (`TranslateFn`); the shipping translator
   passes itself. The knot must become a fuel-bounded fixpoint (`fuelFix`) for
   the induction hypothesis to be discharged; `fuelFix_correct` is the generic
   argument, proved here, that makes that work.
4. **Source semantics.** `Denotes ρ e n x` is a relation on the `Lean.Expr` the
   compiler consumes. It gives meaning only to canonical LIBRARY instances; each
   clause is tied to the library definition by `rfl` (`library_*` lemmas), so it
   is not a free-standing specification.
5. **Statement.** CompCert-style: IF the source has a defined meaning and the
   compiler succeeds, the returned wire carries that meaning. Coverage (success
   implies defined meaning) is a separate obligation, stated below as open.

## Found while fixing the shape

The operator path dispatched on the METHOD name (`HAdd.hAdd ↦ .add`) and
ignored the instance. A user `HAdd` on `Signal (BitVec 8)` whose `+` is
subtraction compiled to an adder: source 3 + 10 = 249, RTL 13. Fixed in
`Sparkle/Compiler/Elab.lean` (`canonicalSignalBinInsts`,
`canonicalScalarMethodInsts`); such an instance is now refused. Under decision 4
this bug is exactly a clause with no `library_*` lemma. -/

namespace Tools.ShippingTranslateSoundness

open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.IR.Type
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness

/-! ## 1. Success of a real compiler action -/

def Returns {α : Type} (m : CompilerM α) (ctx : CompilerState) (s : CircuitState)
    (a : α) (s' : CircuitState) : Prop :=
  ∃ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld),
    (m ctx s) mctx mref cctx cref w = EST.Out.ok (a, s') w'

theorem Returns.bind {α β : Type} {m : CompilerM α} {f : α → CompilerM β}
    {ctx : CompilerState} {s s'' : CircuitState} {b : β}
    (h : Returns (m >>= f) ctx s b s'') :
    ∃ a s', Returns m ctx s a s' ∧ Returns (f a) ctx s' b s'' := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change (EST.bind (m ctx s mctx mref cctx cref)
    fun p => f p.1 ctx p.2 mctx mref cctx cref) w = _ at hrun
  unfold EST.bind at hrun
  split at hrun
  · rename_i p w1 heq
    exact ⟨p.1, p.2, ⟨mctx, mref, cctx, cref, w, w1, heq⟩, ⟨mctx, mref, cctx, cref, w1, w', hrun⟩⟩
  · cases hrun

theorem Returns.pure {α : Type} {a b : α} {ctx : CompilerState} {s s' : CircuitState}
    (h : Returns (Pure.pure a : CompilerM α) ctx s b s') : b = a ∧ s' = s := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.ok (a, s) w = _ at hrun
  cases hrun; exact ⟨rfl, rfl⟩

/-- An oracle: the builder state is untouched, the result is unconstrained. -/
theorem Returns.liftMetaM {α : Type} {x : MetaM α} {ctx : CompilerState}
    {s s' : CircuitState} {a : α} (h : Returns (CompilerM.liftMetaM x) ctx s a s') :
    s' = s := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change (EST.bind (x mctx mref cctx cref) fun a => EST.pure (a, s)) w = _ at hrun
  unfold EST.bind at hrun
  split at hrun
  · simp only [EST.pure] at hrun; cases hrun; rfl
  · cases hrun

/-- Failure claims nothing: a thrown exception is never a successful run. -/
theorem Returns.throw {α : Type} {e : Exception} {ctx : CompilerState}
    {s s' : CircuitState} {a : α} (h : Returns (throw e : CompilerM α) ctx s a s') : False := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.error e w = _ at hrun
  cases hrun

theorem Returns.get {ctx : CompilerState} {s s' a : CircuitState}
    (h : Returns (MonadState.get : CompilerM CircuitState) ctx s a s') : a = s ∧ s' = s := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.ok (s, s) w = _ at hrun
  cases hrun; exact ⟨rfl, rfl⟩

theorem Returns.set {ctx : CompilerState} {s s' t : CircuitState} {u : PUnit}
    (h : Returns (MonadStateOf.set t : CompilerM PUnit) ctx s u s') : s' = t := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.ok (PUnit.unit, t) w = _ at hrun
  cases hrun; rfl

/-! ## 2. The builder operations the translator calls, lifted -/

/-- The compiler's `makeWire` is the builder's `makeWire`; its extra write to
the `IO.Ref` width cache does not touch the builder state. -/
theorem makeWire_returns {hint : String} {ty : HWType} {named : Bool}
    {ctx : CompilerState} {s s' : CircuitState} {w : String}
    (h : Returns (CompilerM.makeWire hint ty named) ctx s w s') :
    w = (CircuitM.makeWire hint ty named s).1 ∧ s' = (CircuitM.makeWire hint ty named s).2 := by
  unfold CompilerM.makeWire at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  subst hcs hs1
  split at k1
  rename_i name cs' hmk
  obtain ⟨u, s2, hset, k2⟩ := Returns.bind k1
  have hs2 : s2 = cs' := Returns.set hset
  have goal : w = name ∧ s' = s2 := by
    split at k2
    · obtain ⟨u2, s3, hlift, k3⟩ := Returns.bind k2
      have h3 : s3 = s2 := Returns.liftMetaM hlift
      obtain ⟨hw, hs'⟩ := Returns.pure k3
      exact ⟨hw, hs'.trans h3⟩
    · exact Returns.pure k2
  rw [hmk]; exact ⟨goal.1, goal.2.trans hs2⟩

theorem emitAssign_returns {lhs : String} {rhs : Sparkle.IR.AST.Expr}
    {ctx : CompilerState} {s s' : CircuitState} {u : Unit}
    (h : Returns (CompilerM.emitAssign lhs rhs) ctx s u s') :
    s' = (CircuitM.emitAssign lhs rhs s).2 := by
  unfold CompilerM.emitAssign at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  subst hcs hs1
  split at k1
  rename_i cs' hem
  rw [hem]
  exact Returns.set k1

theorem emitAssign_usedNames (lhs : String) (rhs : Sparkle.IR.AST.Expr) (s : CircuitState) :
    (CircuitM.emitAssign lhs rhs s).2.usedNames = s.usedNames := rfl

theorem emitAssign_wires (lhs : String) (rhs : Sparkle.IR.AST.Expr) (s : CircuitState) :
    (CircuitM.emitAssign lhs rhs s).2.module.wires = s.module.wires := rfl

theorem emitAssign_inputs (lhs : String) (rhs : Sparkle.IR.AST.Expr) (s : CircuitState) :
    (CircuitM.emitAssign lhs rhs s).2.module.inputs = s.module.inputs := rfl

/-- Allocation touches the module only by declaring the wire. -/
theorem makeWire_module (hint : String) (ty : HWType) (named : Bool) (s : CircuitState) :
    (CircuitM.makeWire hint ty named s).2.module =
      s.module.addWire { name := (CircuitM.makeWire hint ty named s).1, ty := ty } := by
  have fresh : (CircuitM.freshName (CircuitM.sanitizeName hint) named s).2.module = s.module := by
    have stable (base : String) : (CircuitM.freshNamed base s).2.module = s.module := by
      unfold CircuitM.freshNamed
      split <;> rfl
    cases named with
    | false => rfl
    | true => exact stable _
  show (CircuitM.freshName (CircuitM.sanitizeName hint) named s).2.module.addWire
      { name := (CircuitM.freshName (CircuitM.sanitizeName hint) named s).1, ty := ty } = _
  rw [fresh]; rfl

theorem makeWire_outputs (hint : String) (ty : HWType) (named : Bool) (s : CircuitState) :
    (CircuitM.makeWire hint ty named s).2.module.outputs = s.module.outputs := by
  rw [makeWire_module]; rfl

theorem emitAssign_outputs (lhs : String) (rhs : Sparkle.IR.AST.Expr) (s : CircuitState) :
    (CircuitM.emitAssign lhs rhs s).2.module.outputs = s.module.outputs := rfl

theorem makeWire_inputs (hint : String) (ty : HWType) (named : Bool) (s : CircuitState) :
    (CircuitM.makeWire hint ty named s).2.module.inputs = s.module.inputs := by
  rw [makeWire_module]; rfl

/-! ## 3. Source semantics of the fragment -/

/-- Values of the free variables the fragment reads (inputs, at one cycle). -/
abbrev Valuation := Lean.FVarId → Option (Σ n, BitVec n)

/-- Big-step source semantics on the compiler's input `Lean.Expr`. Only a
canonical LIBRARY Signal instance is given meaning; the `library_*` lemmas tie
each such clause to the library definition. -/
inductive Denotes (ρ : Valuation) : Lean.Expr → (n : Nat) → BitVec n → Prop
  | fvar {id : Lean.FVarId} {n : Nat} {x : BitVec n} :
      ρ id = some ⟨n, x⟩ → Denotes ρ (.fvar id) n x
  | binary {e : Lean.Expr} {m : Name} {us : List Level} {bop : Binary} {n : Nat}
      {x y : BitVec n} :
      e.getAppFn = .const m us →
      signalBinOpOf m = some bop.operator →
      canonicalSignalBinKinds m e.getAppArgs = some (true, true) →
      canonicalSignalBitVecWidth e.getAppArgs = some n →
      Denotes ρ e.getAppArgs[e.getAppArgs.size - 2]! n x →
      Denotes ρ e.getAppArgs[e.getAppArgs.size - 1]! n y →
      Denotes ρ e n (bop.apply x y)
  | pureLit {e : Lean.Expr} {us : List Level} {c : Lean.Expr} {n v : Nat} :
      e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us →
      e.getAppArgs.back? = some c →
      bitVecLitValue? c = some (n, v) →
      Denotes ρ e n (BitVec.ofNat n v)

/-! ### The clauses agree with the library (definitional) -/

open Sparkle.Core.Signal in
theorem library_add (dom) (n : Nat) (a b : Signal dom (BitVec n)) (t : Nat) :
    (a + b).val t = Binary.add.apply (a.val t) (b.val t) := rfl
open Sparkle.Core.Signal in
theorem library_sub (dom) (n : Nat) (a b : Signal dom (BitVec n)) (t : Nat) :
    (a - b).val t = Binary.sub.apply (a.val t) (b.val t) := rfl
open Sparkle.Core.Signal in
theorem library_mul (dom) (n : Nat) (a b : Signal dom (BitVec n)) (t : Nat) :
    (a * b).val t = Binary.mul.apply (a.val t) (b.val t) := rfl
open Sparkle.Core.Signal in
theorem library_and (dom) (n : Nat) (a b : Signal dom (BitVec n)) (t : Nat) :
    (a &&& b).val t = Binary.and.apply (a.val t) (b.val t) := rfl
open Sparkle.Core.Signal in
theorem library_or (dom) (n : Nat) (a b : Signal dom (BitVec n)) (t : Nat) :
    (a ||| b).val t = Binary.or.apply (a.val t) (b.val t) := rfl
open Sparkle.Core.Signal in
theorem library_xor (dom) (n : Nat) (a b : Signal dom (BitVec n)) (t : Nat) :
    (a ^^^ b).val t = Binary.xor.apply (a.val t) (b.val t) := rfl

open Sparkle.Core.Signal in
/-- The two literal forms `bitVecLitValue?` recognises denote `BitVec.ofNat`,
and `Signal.pure` is the constant signal: all definitional. -/
theorem library_pure (dom) (n v : Nat) (t : Nat) :
    (Signal.pure (BitVec.ofNat n v) : Signal dom (BitVec n)).val t = BitVec.ofNat n v := rfl
theorem library_ofNat_literal (n v : Nat) :
    (@OfNat.ofNat (BitVec n) v (BitVec.instOfNat)) = BitVec.ofNat n v := rfl

/-- The method→operator table the compiler uses agrees with the operator whose
meaning the `library_*` lemma fixes, for all six binary operators. -/
theorem signalBinOpOf_binary :
    signalBinOpOf ``HAdd.hAdd = some Binary.add.operator ∧
    signalBinOpOf ``HSub.hSub = some Binary.sub.operator ∧
    signalBinOpOf ``HMul.hMul = some Binary.mul.operator ∧
    signalBinOpOf ``HAnd.hAnd = some Binary.and.operator ∧
    signalBinOpOf ``HOr.hOr = some Binary.or.operator ∧
    signalBinOpOf ``HXor.hXor = some Binary.xor.operator := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 4. The state the translator runs in, and its invariants -/

/-- The builder's statements evaluate, in one combinational cycle, to `env`. -/
def Runs (we : WEnv) (mems : MEnv) (initial : Env) (s : CircuitState) (env : Env) : Prop :=
  evalAssigns we mems s.module.finalize.body initial = some env

theorem runs_of_body_eq {we : WEnv} {mems : MEnv} {initial : Env} {s t : CircuitState}
    {env : Env} (hb : t.module.body = s.module.body) (h : Runs we mems initial s env) :
    Runs we mems initial t env := by
  unfold Runs at *
  simpa [Module.finalize, hb] using h

/-- Declared widths agree with the width environment of the final module. -/
def WidthsAgree (we : WEnv) (s : CircuitState) : Prop :=
  ∀ p ∈ s.module.wires, ∀ k, p.ty = .bitVector k → we p.name = k

theorem WidthsAgree.mono {we : WEnv} {s t : CircuitState}
    (h : WidthsAgree we t) (sub : ∀ p ∈ s.module.wires, p ∈ t.module.wires) :
    WidthsAgree we s := fun p hp k hk => h p (sub p hp) k hk

/-- Declared wires have distinct names, all reserved. What lets a width
environment be READ OFF the final module (`Tools.ShippingEntrySoundness`). -/
def WiresOk (s : CircuitState) : Prop :=
  (s.module.wires.map (·.name)).Nodup ∧ ∀ p ∈ s.module.wires, s.usedNames.contains p.name = true

theorem WiresOk.congr {s t : CircuitState} (hw : t.module.wires = s.module.wires)
    (hu : t.usedNames = s.usedNames) (h : WiresOk s) : WiresOk t := by
  unfold WiresOk; rw [hw, hu]; exact h

/-- Declaring a wire under a fresh name keeps the names distinct. -/
theorem WiresOk.fresh {s t : CircuitState} {r : String} {ty : HWType}
    (hfresh : s.usedNames.contains r = false) (hused : t.usedNames = s.usedNames.insert r)
    (hwires : t.module.wires = { name := r, ty := ty } :: s.module.wires) (h : WiresOk s) :
    WiresOk t := by
  obtain ⟨hnd, hin⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hwires, List.map_cons, List.nodup_cons]
    refine ⟨?_, hnd⟩
    intro hm
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hm
    have := hin p hp
    rw [hpn, hfresh] at this; cases this
  · intro p hp
    rw [hused]
    rw [hwires] at hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst hp; simp [Std.HashSet.contains_insert]
    · simp [Std.HashSet.contains_insert, hin p hp]

/-- Names and declarations only grow, and declared names stay distinct. -/
def Grows (s0 s1 : CircuitState) : Prop :=
  (∀ x, s0.usedNames.contains x = true → s1.usedNames.contains x = true) ∧
  (∀ p ∈ s0.module.wires, p ∈ s1.module.wires) ∧
  (WiresOk s0 → WiresOk s1) ∧
  (∀ p ∈ s0.module.inputs, p ∈ s1.module.inputs)

open Tools.ShippingBindingsSoundness (visible lookupVar_run)

/-- Every variable the valuation gives a value to is found by the REAL lookup
(`lookupVar`: reader-scoped first, then the persistent table) at a reserved
wire. Environment-free, so it can be carried through a call before that call's
semantic facts are known. -/
def BoundLookup (ctx : CompilerState) (ρ : Valuation) (s : CircuitState) : Prop :=
  ∀ id n (x : BitVec n), ρ id = some ⟨n, x⟩ →
    ∃ w, visible ctx s.sourceBindings id = some w ∧ s.usedNames.contains w = true

/-- ... and that wire carries the variable's value at its width. -/
def BoundValues (ctx : CompilerState) (ρ : Valuation) (we : WEnv) (s : CircuitState)
    (env : Env) : Prop :=
  ∀ id n (x : BitVec n) w, ρ id = some ⟨n, x⟩ → visible ctx s.sourceBindings id = some w →
    env w = x.toNat ∧ we w = n

/-- A recorded wire carries the meaning of the expression it was produced for. -/
def RecordOk (ρ : Valuation) (we : WEnv) (s : CircuitState) (env : Env) : Prop :=
  ∀ w e', s.translateRecord.get? w = some e' → ∀ n (x : BitVec n), Denotes ρ e' n x →
    s.usedNames.contains w = true ∧ env w = x.toNat ∧ we w = n

/-- Record entries added during a run are for wires that were fresh at its start. -/
def RecordFresh (s0 s1 : CircuitState) : Prop :=
  ∀ w e', s1.translateRecord.get? w = some e' →
    s0.translateRecord.get? w = some e' ∨ s0.usedNames.contains w = false

/-- The right-hand sides the fragment's translation emits: exactly the simple
shapes `Sparkle.IR.OptCheck.simpleRhs` recognises. -/
def ShapedRhs (r : Sparkle.IR.AST.Expr) : Prop := Sparkle.IR.OptCheck.simpleRhs r = true

/-- A translation at width `n` only PREPENDS statements, each an `assign` of a
const or an operator on two references to a declared width-`n` wire. What the
post-processing proofs need to read off the generated module. -/
def Emits (n : Nat) (s0 s1 : CircuitState) : Prop :=
  s1.module.outputs = s0.module.outputs ∧ s1.module.inputs = s0.module.inputs ∧
  ∃ pre, s1.module.body = pre ++ s0.module.body ∧
    ∀ st ∈ pre, ∃ l r, st = .assign l r ∧ ShapedRhs r ∧
      ({ name := l, ty := .bitVector n } : Port) ∈ s1.module.wires

theorem Emits.refl (n : Nat) (s : CircuitState) : Emits n s s :=
  ⟨rfl, rfl, [], by simp, by simp⟩

/-- The invariant a translation call starts in and ends in. -/
structure Inv (ctx : CompilerState) (ρ : Valuation) (we : WEnv) (mems : MEnv)
    (initial : Env) (s : CircuitState) (env : Env) : Prop where
  runs : Runs we mems initial s env
  lookup : BoundLookup ctx ρ s
  values : BoundValues ctx ρ we s env
  record : RecordOk ρ we s env

theorem BoundLookup.transfer {ctx ρ} {s t : CircuitState} (h : BoundLookup ctx ρ s)
    (hu : ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true)
    (hb : t.sourceBindings = s.sourceBindings) : BoundLookup ctx ρ t := by
  intro id n x hx
  obtain ⟨w, hw, hu'⟩ := h id n x hx
  exact ⟨w, by rw [hb]; exact hw, hu w hu'⟩

/-- Moving to a state with the same bindings and record, more reserved names,
and the same values at every previously reserved name, keeps the invariant. -/
theorem Inv.transfer {ctx ρ we mems initial} {s t : CircuitState} {env env' : Env}
    (h : Inv ctx ρ we mems initial s env) (hr : Runs we mems initial t env')
    (hu : ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true)
    (hb : t.sourceBindings = s.sourceBindings) (hrec : t.translateRecord = s.translateRecord)
    (hv : ∀ z, s.usedNames.contains z = true → env' z = env z) :
    Inv ctx ρ we mems initial t env' := by
  refine ⟨hr, h.lookup.transfer hu hb, ?_, ?_⟩
  · intro id n x w hx hw
    rw [hb] at hw
    obtain ⟨w', hw', hu'⟩ := h.lookup id n x hx
    have hww : w' = w := by rw [hw'] at hw; exact Option.some.inj hw
    subst hww
    obtain ⟨h1, h2⟩ := h.values id n x w' hx hw
    exact ⟨by rw [hv w' hu']; exact h1, h2⟩
  · intro w e' he n x hd
    rw [hrec] at he
    obtain ⟨hu', h1, h2⟩ := h.record w e' he n x hd
    exact ⟨hu w hu', by rw [hv w hu']; exact h1, h2⟩

/-! ### Determinism of the source semantics -/

theorem Binary.operator_inj {a b : Binary} (h : a.operator = b.operator) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [Binary.operator] at h)

theorem signalBinOpOf_pure : signalBinOpOf ``Sparkle.Core.Signal.Signal.pure = none := rfl

theorem Denotes.det {ρ : Valuation} {e : Lean.Expr} {n n' : Nat} {x : BitVec n} {x' : BitVec n'}
    (h : Denotes ρ e n x) (h' : Denotes ρ e n' x') : n = n' ∧ x.toNat = x'.toNat := by
  induction h generalizing n' x' with
  | fvar hρ =>
    cases h' with
    | fvar hρ' => rw [hρ] at hρ'; cases hρ'; exact ⟨rfl, rfl⟩
    | binary hfn _ _ _ _ _ => simp [Lean.Expr.getAppFn] at hfn
    | pureLit hfn _ _ => simp [Lean.Expr.getAppFn] at hfn
  | @binary e m us bop n x1 x2 hfn hop hk hw hd1 hd2 ih1 ih2 =>
    cases h' with
    | fvar _ => simp [Lean.Expr.getAppFn] at hfn
    | @binary _ m' us' bop' n' y1 y2 hfn' hop' hk' hw' hd1' hd2' =>
      rw [hfn] at hfn'; cases hfn'
      rw [hw] at hw'; cases hw'
      rw [hop] at hop'
      have hb : bop = bop' := Binary.operator_inj (Option.some.inj hop')
      subst hb
      obtain ⟨-, e1⟩ := ih1 hd1'
      obtain ⟨-, e2⟩ := ih2 hd2'
      have h1 : x1 = y1 := BitVec.eq_of_toNat_eq e1
      have h2 : x2 = y2 := BitVec.eq_of_toNat_eq e2
      subst h1 h2
      exact ⟨rfl, rfl⟩
    | pureLit hfn' _ _ =>
      rw [hfn] at hfn'; cases hfn'
      rw [signalBinOpOf_pure] at hop; cases hop
  | pureLit hfn hb hl =>
    cases h' with
    | fvar _ => simp [Lean.Expr.getAppFn] at hfn
    | binary hfn' hop' _ _ _ _ =>
      rw [hfn] at hfn'; cases hfn'
      rw [signalBinOpOf_pure] at hop'; cases hop'
    | pureLit hfn' hb' hl' =>
      rw [hb] at hb'; cases hb'
      rw [hl] at hl'; cases hl'
      exact ⟨rfl, rfl⟩

/-- Recording a result that carries its expression's meaning keeps `RecordOk`. -/
theorem RecordOk.insert {ρ we} {s : CircuitState} {env : Env} (h : RecordOk ρ we s env)
    {e : Lean.Expr} {w : String} {n : Nat} {x : BitVec n}
    (hd : Denotes ρ e n x) (hused : s.usedNames.contains w = true)
    (hval : env w = x.toNat) (hwid : we w = n) :
    RecordOk ρ we { s with translateRecord := s.translateRecord.insert w e } env := by
  intro w' e' he n' x' hd'
  simp only [Std.HashMap.get?_insert] at he
  split at he
  · rename_i heq
    have hw : w = w' := by simpa using heq
    subst hw
    cases he
    obtain ⟨hn, hx⟩ := Denotes.det hd hd'
    subst hn
    exact ⟨hused, hval.trans hx, hwid⟩
  · exact h w' e' he n' x' hd'

/-! ## 5. What a translation guarantees, and the recursion -/

/-- The specification of a translation entry. `grows` needs only the
environment-free binding fact, which is what lets the width argument of a
parent call use a LATER sibling call's growth before its semantics. -/
structure Spec (translate : TranslateFn) (ctx : CompilerState) (we : WEnv) (mems : MEnv)
    (initial : Env) (ρ : Valuation) : Prop where
  grows : ∀ e hint named n (x : BitVec n) s0 w s1, Denotes ρ e n x →
    Returns (translate e hint false named) ctx s0 w s1 → BoundLookup ctx ρ s0 →
    Grows s0 s1 ∧ s1.sourceBindings = s0.sourceBindings ∧ RecordFresh s0 s1 ∧ Emits n s0 s1
  sem : ∀ e hint named n (x : BitVec n) s0 env0 w s1, Denotes ρ e n x →
    Returns (translate e hint false named) ctx s0 w s1 →
    Inv ctx ρ we mems initial s0 env0 → WidthsAgree we s1 →
    ∃ env1, Inv ctx ρ we mems initial s1 env1 ∧
      (∀ z, s0.usedNames.contains z = true → env1 z = env0 z) ∧
      s1.usedNames.contains w = true ∧ we w = n ∧ env1 w = x.toNat

theorem spec_of_never {t : TranslateFn} {ctx we mems initial ρ}
    (never : ∀ e h a b s w s', ¬ Returns (t e h a b) ctx s w s') :
    Spec t ctx we mems initial ρ :=
  ⟨fun e h nm _ _ s0 w s1 _ hr => absurd hr (never e h false nm s0 w s1),
   fun e h nm _ _ s0 _ w s1 _ hr => absurd hr (never e h false nm s0 w s1)⟩

/-- The induction that discharges the recursion hypothesis for the SHIPPING
fixpoint `translateFuelFix`. -/
theorem translateFuelFix_spec {step : TranslateFn → TranslateFn} {ctx we mems initial ρ}
    (hstep : ∀ t, Spec t ctx we mems initial ρ → Spec (step t) ctx we mems initial ρ) :
    ∀ k, Spec (translateFuelFix step k) ctx we mems initial ρ
  | 0 => spec_of_never fun _ _ _ _ _ _ _ hr => Returns.throw hr
  | k + 1 => hstep _ (translateFuelFix_spec hstep k)

/-! ## 6. Success rules for the operations of the step -/

theorem Returns.read {ctx : CompilerState} {s s' : CircuitState} {c : CompilerState}
    (h : Returns CompilerM.getCompilerState ctx s c s') : c = ctx ∧ s' = s := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.ok (ctx, s) w = _ at hrun
  cases hrun; exact ⟨rfl, rfl⟩

theorem Returns.modify {ctx : CompilerState} {s s' : CircuitState} {f : CircuitState → CircuitState}
    {u : PUnit} (h : Returns (modify f : CompilerM PUnit) ctx s u s') : s' = f s := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.ok (PUnit.unit, f s) w = _ at hrun
  cases hrun; rfl

/-- The real `lookupVar` (existing equation `lookupVar_run`). -/
theorem lookupVar_returns {id : FVarId} {ctx : CompilerState} {s s' : CircuitState}
    {r : Option String} (h : Returns (CompilerM.lookupVar id) ctx s r s') :
    r = visible ctx s.sourceBindings id ∧ s' = s := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  have hl := lookupVar_run ctx s id
  simp only [StateT.run] at hl
  rw [hl] at hrun
  change EST.Out.ok (visible ctx s.sourceBindings id, s) w = _ at hrun
  cases hrun; exact ⟨rfl, rfl⟩

/-- A validated cache hit is a wire the record says was produced for `e`. -/
theorem cacheLookupValidated_returns {e : Lean.Expr} {ctx : CompilerState}
    {s s' : CircuitState} {r : Option String}
    (h : Returns (cacheLookupValidated e) ctx s r s') :
    s' = s ∧ ∀ w, r = some w → s.translateRecord.get? w = some e := by
  unfold cacheLookupValidated at h
  obtain ⟨c, s1, hread, k1⟩ := Returns.bind h
  obtain ⟨-, hs1⟩ := Returns.read hread
  subst hs1
  split at k1
  · obtain ⟨hr, hs⟩ := Returns.pure k1
    exact ⟨hs, fun w hw => by rw [hr] at hw; cases hw⟩
  · obtain ⟨hit, s2, hlift, k2⟩ := Returns.bind k1
    have h2 : s2 = s1 := Returns.liftMetaM hlift
    subst h2
    split at k2
    · obtain ⟨hr, hs⟩ := Returns.pure k2
      exact ⟨hs, fun w hw => by rw [hr] at hw; cases hw⟩
    · obtain ⟨st, s3, hget, k3⟩ := Returns.bind k2
      obtain ⟨hst, hs3⟩ := Returns.get hget
      subst hst hs3
      split at k3
      · rename_i e' heq
        obtain ⟨hr, hs⟩ := Returns.pure k3
        refine ⟨hs, fun w' hw' => ?_⟩
        rw [hr] at hw'
        split at hw'
        · rename_i hdec
          cases hw'
          have : e' = e := @of_decide_eq_true _ (Sparkle.Compiler.ExprDecEq.exprDecEq e' e) hdec
          rw [heq, this]
        · cases hw'
      · obtain ⟨hr, hs⟩ := Returns.pure k3
        exact ⟨hs, fun w hw => by rw [hr] at hw; cases hw⟩

theorem recordTranslation_returns {e : Lean.Expr} {w : String} {c : Bool}
    {ctx : CompilerState} {s s' : CircuitState} {u : Unit}
    (h : Returns (recordTranslation e w c) ctx s u s') :
    s' = { s with translateRecord := s.translateRecord.insert w e } := by
  unfold recordTranslation at h
  obtain ⟨u1, s1, hmod, k1⟩ := Returns.bind h
  have hs1 := Returns.modify hmod
  split at k1
  · obtain ⟨c', s2, hread, k2⟩ := Returns.bind k1
    obtain ⟨-, hs2⟩ := Returns.read hread
    subst hs2
    split at k2
    · have := Returns.liftMetaM k2; rw [this, hs1]
    · obtain ⟨-, hs⟩ := Returns.pure k2; rw [hs, hs1]
  · obtain ⟨-, hs⟩ := Returns.pure k1; rw [hs, hs1]

/-! ## 7. The three branches of the core, in the invariant -/

theorem evalExpr_const_lt (we : WEnv) (env : Env) (v w : Nat) (h : v < 2 ^ w) :
    evalExpr we env (.const (v : Int) w) = some v := by
  have h1 : (v : Int) % ((2 ^ w : Nat) : Int) = (v : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg v) (Int.ofNat_lt.mpr h)
  simp only [evalExpr, h1, Int.add_emod_right, mask]
  simp [Nat.mod_eq_of_lt h]

theorem bitVecLitValue?_lt {c : Lean.Expr} {w v : Nat} (h : bitVecLitValue? c = some (w, v)) :
    v < 2 ^ w := by
  unfold bitVecLitValue? at h
  split at h
  · split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h
  · split at h
    · split at h
      · split at h
        · cases h; assumption
        · cases h
      · cases h
    · cases h
  · cases h


theorem emitAssign_sourceBindings (lhs : String) (rhs : Sparkle.IR.AST.Expr) (s : CircuitState) :
    (CircuitM.emitAssign lhs rhs s).2.sourceBindings = s.sourceBindings := rfl

theorem emitAssign_translateRecord (lhs : String) (rhs : Sparkle.IR.AST.Expr) (s : CircuitState) :
    (CircuitM.emitAssign lhs rhs s).2.translateRecord = s.translateRecord := rfl

theorem emitAssign_body_cons (lhs : String) (rhs : Sparkle.IR.AST.Expr) (s : CircuitState) :
    (CircuitM.emitAssign lhs rhs s).2.module.body = .assign lhs rhs :: s.module.body := rfl

/-- Like `Inv.transfer`, except that ONE wire `r` may change value: it is
neither a bound variable's wire nor a recorded wire with a meaning. -/
theorem Inv.transfer_except {ctx ρ we mems initial} {s t : CircuitState} {env env' : Env}
    (h : Inv ctx ρ we mems initial s env) (hr : Runs we mems initial t env')
    (hu : ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true)
    (hb : t.sourceBindings = s.sourceBindings) (hrec : t.translateRecord = s.translateRecord)
    (r : String) (hv : ∀ z, s.usedNames.contains z = true → z ≠ r → env' z = env z)
    (hnb : ∀ id n (x : BitVec n), ρ id = some ⟨n, x⟩ → visible ctx s.sourceBindings id ≠ some r)
    (hnr : ∀ e' n (x : BitVec n), s.translateRecord.get? r = some e' → ¬ Denotes ρ e' n x) :
    Inv ctx ρ we mems initial t env' := by
  refine ⟨hr, h.lookup.transfer hu hb, ?_, ?_⟩
  · intro id n x w hx hw
    rw [hb] at hw
    obtain ⟨w', hw', hu'⟩ := h.lookup id n x hx
    have hww : w' = w := by rw [hw'] at hw; exact Option.some.inj hw
    subst hww
    have hne : w' ≠ r := fun heq => hnb id n x hx (by rw [hw', heq])
    obtain ⟨h1, h2⟩ := h.values id n x w' hx hw
    exact ⟨by rw [hv w' hu' hne]; exact h1, h2⟩
  · intro w e' he n x hd
    rw [hrec] at he
    have hne : w ≠ r := fun heq => hnr e' n x (heq ▸ he) hd
    obtain ⟨hu', h1, h2⟩ := h.record w e' he n x hd
    exact ⟨hu w hu', by rw [hv w hu' hne]; exact h1, h2⟩

/-- A fresh wire (unreserved in `s`) is neither a bound wire nor a recorded
wire with a meaning, given the invariant's reservation facts. -/
theorem fresh_not_bound {ctx ρ} {s : CircuitState} {r : String} (hl : BoundLookup ctx ρ s)
    (hfresh : s.usedNames.contains r = false) :
    ∀ id n (x : BitVec n), ρ id = some ⟨n, x⟩ → visible ctx s.sourceBindings id ≠ some r := by
  intro id n x hx hv
  obtain ⟨w, hw, hu⟩ := hl id n x hx
  rw [hv] at hw; cases hw
  rw [hfresh] at hu; cases hu

theorem fresh_not_recorded {ρ we} {s : CircuitState} {env : Env} {r : String}
    (hrec : RecordOk ρ we s env) (hfresh : s.usedNames.contains r = false) :
    ∀ e' n (x : BitVec n), s.translateRecord.get? r = some e' → ¬ Denotes ρ e' n x := by
  intro e' n x he hd
  have := (hrec r e' he n x hd).1
  rw [hfresh] at this; cases this

/-- The literal branch, in the invariant. A leaf: no recursion hypothesis.
Existing proofs used: `CircuitM.makeWire_spec`, `makeWire_sourceBindings`,
`makeWire_translateRecord`, `emitAssign_sound`. -/
theorem translateSignalPureLiteral_branch {ctx : CompilerState} {we : WEnv} {mems : MEnv}
    {initial : Env} {ρ : Valuation} {e : Lean.Expr} {us : List Level}
    {hint : String} {named : Bool}
    (hfn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us)
    {n : Nat} {x : BitVec n} {s0 : CircuitState} {r : Option String} {s1 : CircuitState}
    (hden : Denotes ρ e n x)
    (hrun : Returns (translateSignalPureLiteral? e.getAppArgs hint named) ctx s0 r s1) :
    ∃ w, r = some w ∧
      (Grows s0 s1 ∧ s1.sourceBindings = s0.sourceBindings ∧
        s1.translateRecord = s0.translateRecord ∧ s0.usedNames.contains w = false ∧
        Emits n s0 s1) ∧
      (∀ env0, Inv ctx ρ we mems initial s0 env0 → WidthsAgree we s1 →
        ∃ env1, Inv ctx ρ we mems initial s1 env1 ∧
          (∀ z, s0.usedNames.contains z = true → env1 z = env0 z) ∧
          s1.usedNames.contains w = true ∧ we w = n ∧ env1 w = x.toNat) := by
  cases hden with
  | fvar _ => simp [Lean.Expr.getAppFn] at hfn
  | binary hfn' hop' _ _ _ _ =>
    rw [hfn] at hfn'; cases hfn'
    rw [signalBinOpOf_pure] at hop'; cases hop'
  | @pureLit _ _ c _ v _ hback hlit =>
  have hlt := bitVecLitValue?_lt hlit
  unfold translateSignalPureLiteral? at hrun
  rw [hback] at hrun
  simp only [Option.bind_some, hlit] at hrun
  obtain ⟨res, sA, hmk, k1⟩ := Returns.bind hrun
  obtain ⟨hres, hsA⟩ := makeWire_returns hmk
  obtain ⟨u, sB, hem, k2⟩ := Returns.bind k1
  obtain ⟨hr, hs1⟩ := Returns.pure k2
  have hsB := emitAssign_returns hem
  obtain ⟨hfresh, hused, hbody, hwires⟩ := CircuitM.makeWire_spec hint (.bitVector n) named s0
  have hsbA := CircuitM.makeWire_sourceBindings hint (.bitVector n) named s0
  have hrecA := CircuitM.makeWire_translateRecord hint (.bitVector n) named s0
  rw [← hres] at hfresh hused hwires
  rw [← hsA] at hused hbody hwires hsbA hrecA
  rw [hs1]
  refine ⟨res, hr, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, hfresh, ?_⟩, ?_⟩
  · intro z hz; rw [hsB, emitAssign_usedNames, hused]; simp [Std.HashSet.contains_insert, hz]
  · intro p hp; rw [hsB, emitAssign_wires, hwires]; simp [hp]
  · intro hok
    exact (WiresOk.fresh hfresh hused hwires hok).congr
      (by rw [hsB, emitAssign_wires]) (by rw [hsB, emitAssign_usedNames])
  · intro p hp; rw [hsB, emitAssign_inputs, hsA, makeWire_inputs]; exact hp
  · rw [hsB, emitAssign_sourceBindings, hsbA]
  · rw [hsB, emitAssign_translateRecord, hrecA]
  · refine ⟨by rw [hsB, emitAssign_outputs, hsA, makeWire_outputs],
      by rw [hsB, emitAssign_inputs, hsA, makeWire_inputs],
      [.assign res _], by rw [hsB, emitAssign_body_cons, hbody]; rfl, ?_⟩
    intro st hst
    simp only [List.mem_singleton] at hst
    subst hst
    exact ⟨res, _, rfl, rfl, by rw [hsB, emitAssign_wires, hwires]; simp⟩
  · intro env0 hinv hw1
    have hsA0 : Runs we mems initial sA env0 := runs_of_body_eq hbody hinv.runs
    have hrunB := emitAssign_sound sA we mems initial env0 res _ _ hsA0
      (evalExpr_const_lt we env0 v n hlt)
    rw [← hsB] at hrunB
    have huse : ∀ z, s0.usedNames.contains z = true → sB.usedNames.contains z = true := by
      intro z hz; rw [hsB, emitAssign_usedNames, hused]; simp [Std.HashSet.contains_insert, hz]
    have hvals : ∀ z, s0.usedNames.contains z = true → z ≠ res →
        (fun m => if m = res then v else env0 m) z = env0 z := by
      intro z _ hne; simp [hne]
    refine ⟨_, hinv.transfer_except hrunB huse
      (by rw [hsB, emitAssign_sourceBindings, hsbA]) (by rw [hsB, emitAssign_translateRecord, hrecA])
      res hvals (fresh_not_bound hinv.lookup hfresh) (fresh_not_recorded hinv.record hfresh),
      ?_, ?_, ?_, ?_⟩
    · intro z hz
      have hne : z ≠ res := by intro h; subst h; rw [hfresh] at hz; cases hz
      simp [hne]
    · rw [hsB, emitAssign_usedNames, hused]; simp [Std.HashSet.contains_insert]
    · have hdecl : ({ name := res, ty := .bitVector n } : Port) ∈ sB.module.wires := by
        rw [hsB, emitAssign_wires, hwires]; simp
      exact hw1 _ hdecl n rfl
    · simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem RecordFresh.trans {a b c : CircuitState}
    (hab : RecordFresh a b) (hbc : RecordFresh b c)
    (hu : ∀ z, a.usedNames.contains z = true → b.usedNames.contains z = true) :
    RecordFresh a c := by
  intro w e' he
  rcases hbc w e' he with hb | hb
  · exact hab w e' hb
  · right
    cases h : a.usedNames.contains w with
    | false => rfl
    | true => have := hu w h; rw [hb] at this; cases this

/-- The operator branch, in the invariant, for any `translate` satisfying the
specification (the recursion hypothesis, discharged by `translateFuelFix_spec`).
Existing proofs used: `CircuitM.makeWire_spec`, `makeWire_sourceBindings`,
`makeWire_translateRecord`, `emitAssign_sound`, `Binary.rhs_correct`. -/
theorem translateCanonicalSignalBinary_branch
    {translate : TranslateFn} {ctx : CompilerState} {we : WEnv} {mems : MEnv}
    {initial : Env} {ρ : Valuation}
    (ih : Spec translate ctx we mems initial ρ)
    {e : Lean.Expr} {op : Operator} {hint : String} {named : Bool}
    {m : Name} {us : List Level}
    (hfn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    {n : Nat} {x : BitVec n} {s0 : CircuitState} {w : String} {s1 : CircuitState}
    (hden : Denotes ρ e n x)
    (hrun : Returns (translateCanonicalSignalBinary translate e op e.getAppArgs true true
      hint named) ctx s0 w s1)
    (hbl : BoundLookup ctx ρ s0) :
    (Grows s0 s1 ∧ s1.sourceBindings = s0.sourceBindings ∧ RecordFresh s0 s1 ∧
      s0.usedNames.contains w = false ∧ Emits n s0 s1) ∧
    (∀ env0, Inv ctx ρ we mems initial s0 env0 → WidthsAgree we s1 →
      ∃ env1, Inv ctx ρ we mems initial s1 env1 ∧
        (∀ z, s0.usedNames.contains z = true → env1 z = env0 z) ∧
        s1.usedNames.contains w = true ∧ we w = n ∧ env1 w = x.toNat) := by
  cases hden with
  | fvar _ => simp [Lean.Expr.getAppFn] at hfn
  | pureLit hfn' _ _ =>
    rw [hfn] at hfn'; cases hfn'
    rw [signalBinOpOf_pure] at hop; cases hop
  | @binary _ m' us' bop _ x1 x2 hfn' hop' _ hwid hd1 hd2 =>
  rw [hfn] at hfn'
  cases hfn'
  have hopeq : op = bop.operator := by rw [hop] at hop'; exact Option.some.inj hop'
  subst hopeq
  unfold translateCanonicalSignalBinary at hrun
  simp only [hwid] at hrun
  obtain ⟨hw, sA0, hwty, k1⟩ := Returns.bind hrun
  obtain ⟨hhw, hsA0⟩ := Returns.pure hwty
  rw [hhw] at k1
  obtain ⟨res, sA, hmk, k2⟩ := Returns.bind k1
  rw [hsA0] at hmk
  obtain ⟨hres, hsA⟩ := makeWire_returns hmk
  obtain ⟨wa, sB, htA, k3⟩ := Returns.bind k2
  obtain ⟨wb, sC, htB, k4⟩ := Returns.bind k3
  obtain ⟨u, sD, hem, k5⟩ := Returns.bind k4
  obtain ⟨hwres, hs1⟩ := Returns.pure k5
  have hsD := emitAssign_returns hem
  obtain ⟨hfresh, hused, hbody, hwires⟩ := CircuitM.makeWire_spec hint (.bitVector n) named s0
  have hsbA := CircuitM.makeWire_sourceBindings hint (.bitVector n) named s0
  have hrecA := CircuitM.makeWire_translateRecord hint (.bitVector n) named s0
  rw [← hres] at hfresh hused hwires
  rw [← hsA] at hused hbody hwires hsbA hrecA
  rw [hwres, hs1]
  -- structural facts, environment-free
  have huA : ∀ z, s0.usedNames.contains z = true → sA.usedNames.contains z = true := by
    intro z hz; rw [hused]; simp [Std.HashSet.contains_insert, hz]
  have hresA : sA.usedNames.contains res = true := by rw [hused]; simp [Std.HashSet.contains_insert]
  have hblA : BoundLookup ctx ρ sA := hbl.transfer huA hsbA
  obtain ⟨⟨gAu, gAw, gAk, gAi⟩, sbB, rfB, eA⟩ := ih.grows _ _ _ _ _ _ _ _ hd1 htA hblA
  have hblB : BoundLookup ctx ρ sB := hblA.transfer gAu sbB
  obtain ⟨⟨gBu, gBw, gBk, gBi⟩, sbC, rfC, eB⟩ := ih.grows _ _ _ _ _ _ _ _ hd2 htB hblB
  have wiresD : ∀ p ∈ sC.module.wires, p ∈ sD.module.wires := by
    intro p hp; rw [hsD, emitAssign_wires]; exact hp
  have huD : ∀ z, sC.usedNames.contains z = true → sD.usedNames.contains z = true := by
    intro z hz; rw [hsD, emitAssign_usedNames]; exact hz
  have rfA : RecordFresh s0 sA := by intro w e' he; left; rw [← hrecA]; exact he
  have rfAll : RecordFresh s0 sD := by
    have rf0C := (rfA.trans rfB huA).trans rfC (fun z hz => gAu z (huA z hz))
    intro w e' he
    rw [hsD, emitAssign_translateRecord] at he
    exact rf0C w e' he
  refine ⟨⟨⟨fun z hz => huD z (gBu z (gAu z (huA z hz))), fun p hp => wiresD p (gBw p (gAw p
      (by rw [hwires]; exact List.mem_cons_of_mem _ hp))),
      fun hok => (gBk (gAk (WiresOk.fresh hfresh hused hwires hok))).congr
        (by rw [hsD, emitAssign_wires]) (by rw [hsD, emitAssign_usedNames]),
      fun p hp => by
        rw [hsD, emitAssign_inputs]
        exact gBi p (gAi p (by rw [hsA, makeWire_inputs]; exact hp))⟩,
    by rw [hsD, emitAssign_sourceBindings, sbC, sbB, hsbA], rfAll, hfresh, ?_⟩, ?_⟩
  · obtain ⟨hoA, hiA, preA, hbA, hA⟩ := eA
    obtain ⟨hoB, hiB, preB, hbB, hB⟩ := eB
    refine ⟨?_, ?_, .assign res (.op bop.operator [.ref wa, .ref wb]) :: (preB ++ preA), ?_, ?_⟩
    · rw [hsD, emitAssign_outputs, hoB, hoA, hsA, makeWire_outputs]
    · rw [hsD, emitAssign_inputs, hiB, hiA, hsA, makeWire_inputs]
    · rw [hsD, emitAssign_body_cons, hbB, hbA, hbody]; simp
    · intro st hst
      rcases List.mem_cons.mp hst with rfl | hst
      · exact ⟨res, _, rfl, by cases bop <;> rfl, wiresD _ (gBw _ (gAw _ (by rw [hwires]; simp)))⟩
      · rcases List.mem_append.mp hst with h | h
        · obtain ⟨l, r, rfl, hr, hl⟩ := hB st h
          exact ⟨l, r, rfl, hr, wiresD _ hl⟩
        · obtain ⟨l, r, rfl, hr, hl⟩ := hA st h
          exact ⟨l, r, rfl, hr, wiresD _ (gBw _ hl)⟩
  -- semantics
  intro env0 hinv hw1
  have hwC : WidthsAgree we sC := hw1.mono wiresD
  have hwB : WidthsAgree we sB := hwC.mono gBw
  have hinvA : Inv ctx ρ we mems initial sA env0 :=
    hinv.transfer (runs_of_body_eq hbody hinv.runs) huA hsbA hrecA (fun _ _ => rfl)
  obtain ⟨envB, hinvB, frB, useA, wA, valA⟩ := ih.sem _ _ _ _ _ _ _ _ _ hd1 htA hinvA hwB
  obtain ⟨envC, hinvC, frC, useB, wB, valB⟩ := ih.sem _ _ _ _ _ _ _ _ _ hd2 htB hinvB hwC
  have valA' : envC wa = x1.toNat := by rw [frC wa useA]; exact valA
  have hrhs := Binary.rhs_correct bop we envC wa wb x1 x2 wA wB valA' valB
  have hrunD := emitAssign_sound sC we mems initial envC res _ _ hinvC.runs hrhs
  rw [← hsD] at hrunD
  -- `res` is neither bound nor recorded-with-meaning in sC
  have hnbC : ∀ id n' (x' : BitVec n'), ρ id = some ⟨n', x'⟩ →
      visible ctx sC.sourceBindings id ≠ some res := by
    rw [sbC, sbB, hsbA]; exact fresh_not_bound hbl hfresh
  have hnrC : ∀ e' n' (x' : BitVec n'), sC.translateRecord.get? res = some e' →
      ¬ Denotes ρ e' n' x' := by
    intro e' n' x' he hd'
    have resB : sB.usedNames.contains res = true := gAu res hresA
    rcases rfC res e' he with hB | hB
    · rcases rfB res e' hB with hA' | hA'
      · rw [hrecA] at hA'
        exact fresh_not_recorded hinv.record hfresh e' n' x' hA' hd'
      · rw [hresA] at hA'; cases hA'
    · rw [resB] at hB; cases hB
  have hvD : ∀ z, sC.usedNames.contains z = true → z ≠ res →
      (fun m => if m = res then (bop.apply x1 x2).toNat else envC m) z = envC z := by
    intro z _ hne; simp [hne]
  refine ⟨_, hinvC.transfer_except hrunD huD
      (by rw [hsD, emitAssign_sourceBindings]) (by rw [hsD, emitAssign_translateRecord])
      res hvD hnbC hnrC, ?_, huD res (gBu res (gAu res hresA)), ?_, by simp⟩
  · intro z hz
    have hzA := huA z hz
    have hne : z ≠ res := by intro h; subst h; rw [hfresh] at hz; cases hz
    simp only [hne, if_false]
    rw [frC z (gAu z hzA), frB z hzA]
  · have hdecl : ({ name := res, ty := .bitVector n } : Port) ∈ sD.module.wires := by
      apply wiresD; apply gBw; apply gAw; rw [hwires]; simp
    exact hw1 _ hdecl n rfl

/-! ## 8. The step of the SHIPPING knot, and the end-to-end theorem -/

theorem isFVar_false_of_const {e : Lean.Expr} {m : Name} {us : List Level}
    (h : e.getAppFn = .const m us) : e.isFVar = false := by
  cases e <;> simp_all [Lean.Expr.getAppFn, Lean.Expr.isFVar]

/-- Inserting into the record changes nothing the other invariant parts read. -/
theorem Inv.record_insert {ctx ρ we mems initial} {s : CircuitState} {env : Env}
    (h : Inv ctx ρ we mems initial s env) {e : Lean.Expr} {w : String} {n : Nat} {x : BitVec n}
    (hd : Denotes ρ e n x) (hused : s.usedNames.contains w = true)
    (hval : env w = x.toNat) (hwid : we w = n) :
    Inv ctx ρ we mems initial { s with translateRecord := s.translateRecord.insert w e } env :=
  ⟨h.runs, h.lookup, h.values, h.record.insert hd hused hval hwid⟩

/-- The core followed by the step's continuation (record, then return). -/
theorem translateStep_core {rec : TranslateFn} {ctx : CompilerState} {we : WEnv}
    {mems : MEnv} {initial : Env} {ρ : Valuation}
    (ih : Spec rec ctx we mems initial ρ)
    {e : Lean.Expr} {hint : String} {named : Bool} {c : Bool}
    {K : Option String → CompilerM String}
    (hK : ∀ w', K (some w') =
      if e.isFVar = true then pure w' else (recordTranslation e w' c >>= fun _ => pure w'))
    {n : Nat} {x : BitVec n} {s0 : CircuitState} {w : String} {s1 : CircuitState}
    (hden : Denotes ρ e n x)
    (hrun : Returns (translateCore rec e hint false named >>= K) ctx s0 w s1)
    (hbl : BoundLookup ctx ρ s0) :
    (Grows s0 s1 ∧ s1.sourceBindings = s0.sourceBindings ∧ RecordFresh s0 s1 ∧ Emits n s0 s1) ∧
    (∀ env0, Inv ctx ρ we mems initial s0 env0 → WidthsAgree we s1 →
      ∃ env1, Inv ctx ρ we mems initial s1 env1 ∧
        (∀ z, s0.usedNames.contains z = true → env1 z = env0 z) ∧
        s1.usedNames.contains w = true ∧ we w = n ∧ env1 w = x.toNat) := by
  obtain ⟨r, sc, hcore, k⟩ := Returns.bind hrun
  -- the record step after a core result `w'` produced at `sc`
  have after : ∀ w', r = some w' → e.isFVar = false →
      s1 = { sc with translateRecord := sc.translateRecord.insert w' e } ∧ w = w' := by
    intro w' hr hnf
    rw [hr, hK, hnf] at k
    simp only [Bool.false_eq_true, if_false] at k
    obtain ⟨u, s2, hrec, k2⟩ := Returns.bind k
    have hs2 := recordTranslation_returns hrec
    obtain ⟨hw, hs1⟩ := Returns.pure k2
    exact ⟨hs1.trans hs2, hw⟩
  cases hden with
  | @fvar id _ _ hρ =>
    obtain ⟨hr, hsc⟩ := lookupVar_returns (id := id) hcore
    obtain ⟨w', hw', hu'⟩ := hbl id _ _ hρ
    rw [hw'] at hr
    rw [hr, hK] at k
    simp only [Lean.Expr.isFVar, if_true] at k
    obtain ⟨hw, hs1⟩ := Returns.pure k
    rw [hsc] at hs1
    rw [hs1, hw]
    refine ⟨⟨⟨fun z hz => hz, fun p hp => hp, fun h => h, fun p hp => hp⟩, rfl, fun w e' he => Or.inl he,
      Emits.refl _ _⟩, ?_⟩
    intro env0 hinv _
    obtain ⟨hv, hwid⟩ := hinv.values id _ _ w' hρ hw'
    exact ⟨env0, hinv, fun _ _ => rfl, hu', hwid, hv⟩
  | @pureLit _ us cc _ v hfn hback hlit =>
    have hnf := isFVar_false_of_const hfn
    unfold translateCore at hcore
    split at hcore
    · simp [Lean.Expr.getAppFn] at hfn
    · rw [hfn] at hcore
      simp only [beq_self_eq_true, if_true] at hcore
      obtain ⟨w', hr, ⟨⟨gu, gw, gk, gi⟩, sb, hrec, hfr, em⟩, hsem⟩ :=
        translateSignalPureLiteral_branch (we := we) (mems := mems) (initial := initial) hfn
          (Denotes.pureLit hfn hback hlit) hcore
      obtain ⟨hs1, hw⟩ := after w' hr hnf
      rw [hs1, hw]
      refine ⟨⟨⟨gu, gw, gk, gi⟩, sb, ?_, em⟩, ?_⟩
      · intro w e' he
        simp only [Std.HashMap.get?_insert] at he
        split at he
        · right; rename_i heq; have : w' = w := by simpa using heq
          subst this; exact hfr
        · left; rw [← hrec]; exact he
      · intro env0 hinv hw1
        obtain ⟨env1, hinv1, fr, hu, hwid, hval⟩ := hsem env0 hinv hw1
        exact ⟨env1, hinv1.record_insert (Denotes.pureLit hfn hback hlit) hu hval hwid,
          fr, hu, hwid, hval⟩
  | @binary _ m us bop _ x1 x2 hfn hop hk hwid hd1 hd2 =>
    have hnf := isFVar_false_of_const hfn
    have hden := Denotes.binary hfn hop hk hwid hd1 hd2
    unfold translateCore at hcore
    split at hcore
    · simp [Lean.Expr.getAppFn] at hfn
    · rw [hfn] at hcore
      have hm : (m == ``Sparkle.Core.Signal.Signal.pure) = false := by
        cases h : (m == ``Sparkle.Core.Signal.Signal.pure) with
        | false => rfl
        | true =>
          have : m = ``Sparkle.Core.Signal.Signal.pure := by simpa using h
          rw [this, signalBinOpOf_pure] at hop; cases hop
      simp only [hm, Bool.false_eq_true, if_false, hop, hk, hwid] at hcore
      obtain ⟨w'', sd, htr, kk⟩ := Returns.bind hcore
      obtain ⟨hr, hsd⟩ := Returns.pure kk
      rw [← hsd] at htr
      obtain ⟨⟨⟨gu, gw, gk, gi⟩, sb, rf, hfr, em⟩, hsem⟩ :=
        translateCanonicalSignalBinary_branch ih hfn hop hden htr hbl
      obtain ⟨hs1, hw⟩ := after w'' hr hnf
      rw [hs1, hw]
      refine ⟨⟨⟨gu, gw, gk, gi⟩, sb, ?_, em⟩, ?_⟩
      · intro w e' he
        simp only [Std.HashMap.get?_insert] at he
        split at he
        · right; rename_i heq; have : w'' = w := by simpa using heq
          subst this; exact hfr
        · exact rf w e' he
      · intro env0 hinv hw1
        obtain ⟨env1, hinv1, fr, hu, hwid', hval⟩ := hsem env0 hinv hw1
        exact ⟨env1, hinv1.record_insert hden hu hval hwid', fr, hu, hwid', hval⟩

/-- One step of the SHIPPING knot: validated cache hit, or core then record.
The fallback is never reached for an expression with a meaning. -/
theorem translateStepWith_run {fallback : TranslateFn → TranslateFn} {rec : TranslateFn}
    {ctx : CompilerState} {we : WEnv} {mems : MEnv} {initial : Env} {ρ : Valuation}
    (ih : Spec rec ctx we mems initial ρ)
    {e : Lean.Expr} {hint : String} {named : Bool}
    {n : Nat} {x : BitVec n} {s0 : CircuitState} {w : String} {s1 : CircuitState}
    (hden : Denotes ρ e n x)
    (hrun : Returns (translateStepWith fallback rec e hint false named) ctx s0 w s1)
    (hbl : BoundLookup ctx ρ s0) :
    (Grows s0 s1 ∧ s1.sourceBindings = s0.sourceBindings ∧ RecordFresh s0 s1 ∧ Emits n s0 s1) ∧
    (∀ env0, Inv ctx ρ we mems initial s0 env0 → WidthsAgree we s1 →
      ∃ env1, Inv ctx ρ we mems initial s1 env1 ∧
        (∀ z, s0.usedNames.contains z = true → env1 z = env0 z) ∧
        s1.usedNames.contains w = true ∧ we w = n ∧ env1 w = x.toNat) := by
  unfold translateStepWith at hrun
  dsimp only at hrun
  by_cases hc0 : ((!named && !e.isFVar && !false) && translateCoreShape e) = true
  · rw [if_pos hc0] at hrun
    obtain ⟨r, s2, hc, k⟩ := Returns.bind hrun
    obtain ⟨hs2, hval⟩ := cacheLookupValidated_returns hc
    split at k
    · rename_i w'
      obtain ⟨hw, hs1⟩ := Returns.pure k
      have hrec := hval w' rfl
      rw [hs1, hs2, hw]
      refine ⟨⟨⟨fun z hz => hz, fun p hp => hp, fun h => h, fun p hp => hp⟩, rfl, fun w e' he => Or.inl he,
      Emits.refl _ _⟩, ?_⟩
      intro env0 hinv _
      obtain ⟨hu, hv, hwid⟩ := hinv.record w' e hrec n x hden
      exact ⟨env0, hinv, fun _ _ => rfl, hu, hwid, hv⟩
    · rw [hs2] at k
      exact translateStep_core ih (fun _ => rfl) hden k hbl
  · rw [if_neg hc0] at hrun
    exact translateStep_core ih (fun _ => rfl) hden hrun hbl

theorem translateStepWith_spec {fallback : TranslateFn → TranslateFn} {rec : TranslateFn}
    {ctx : CompilerState} {we : WEnv} {mems : MEnv} {initial : Env} {ρ : Valuation}
    (ih : Spec rec ctx we mems initial ρ) :
    Spec (translateStepWith fallback rec) ctx we mems initial ρ :=
  ⟨fun _ _ _ _ _ _ _ _ hd hr hbl => (translateStepWith_run ih hd hr hbl).1,
   fun _ _ _ _ _ _ env0 _ _ hd hr hinv hw =>
     (translateStepWith_run ih hd hr hinv.lookup).2 env0 hinv hw⟩

/-- **The general theorem for the fragment.** For the SHIPPING translator
`translateExprToWire` — the real entry, an ordinary definition — and for every
expression built from inputs, `BitVec` literals under `Signal.pure`, and the
canonical library operators `+ - * &&& ||| ^^^` in any combination and at any
literal width: if the expression has a meaning and the translation succeeds, the
returned wire carries that meaning, and the state invariant (statements
evaluate, bindings, record) is preserved. No recursion hypothesis remains: it is
discharged by induction on the shipping fuel. -/
theorem translateExprToWire_sound {ctx : CompilerState} {we : WEnv} {mems : MEnv}
    {initial : Env} {ρ : Valuation} {e : Lean.Expr} {hint : String} {named : Bool}
    {n : Nat} {x : BitVec n} {s0 : CircuitState} {env0 : Env} {w : String} {s1 : CircuitState}
    (hden : Denotes ρ e n x)
    (hrun : Returns (translateExprToWire e hint false named) ctx s0 w s1)
    (hinv : Inv ctx ρ we mems initial s0 env0) (hw : WidthsAgree we s1) :
    ∃ env1, Inv ctx ρ we mems initial s1 env1 ∧
      (∀ z, s0.usedNames.contains z = true → env1 z = env0 z) ∧
      s1.usedNames.contains w = true ∧ we w = n ∧ env1 w = x.toNat :=
  (translateFuelFix_spec (step := translateStep) (fun _ ih => translateStepWith_spec ih)
    translateFuelLimit).sem e hint named n x s0 env0 w s1 hden hrun hinv hw

end Tools.ShippingTranslateSoundness
