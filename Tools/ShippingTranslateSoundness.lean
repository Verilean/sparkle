import Tools.ShippingAllocationSoundness

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

/-! ## 4. The simulation relation and the specification of a translation -/

/-- The builder's statements evaluate, in one combinational cycle, to `env`. -/
def Runs (we : WEnv) (mems : MEnv) (initial : Env) (s : CircuitState) (env : Env) : Prop :=
  evalAssigns we mems s.module.finalize.body initial = some env

/-- Declared widths agree with the width environment of the final module. -/
def WidthsAgree (we : WEnv) (s : CircuitState) : Prop :=
  ∀ p ∈ s.module.wires, ∀ k, p.ty = .bitVector k → we p.name = k

theorem WidthsAgree.mono {we : WEnv} {s t : CircuitState}
    (h : WidthsAgree we t) (sub : ∀ p ∈ s.module.wires, p ∈ t.module.wires) :
    WidthsAgree we s := fun p hp k hk => h p (sub p hp) k hk

/-- Structural effect of a translation: names and declarations only grow. This
is stated separately from the semantic clause because the width argument needs
it before the semantic clause of a later call is available. -/
def Grows (s0 s1 : CircuitState) : Prop :=
  (∀ x, s0.usedNames.contains x = true → s1.usedNames.contains x = true) ∧
  (∀ p ∈ s0.module.wires, p ∈ s1.module.wires)

/-- What a successful translation of `e` guarantees. -/
structure Spec (translate : TranslateFn) (ctx : CompilerState) (we : WEnv)
    (mems : MEnv) (initial : Env) (ρ : Valuation) : Prop where
  grows : ∀ e hint s0 w s1, Returns (translate e hint false false) ctx s0 w s1 → Grows s0 s1
  sem : ∀ e hint (n : Nat) (x : BitVec n) s0 env0 w s1,
    Denotes ρ e n x →
    Returns (translate e hint false false) ctx s0 w s1 →
    Runs we mems initial s0 env0 →
    WidthsAgree we s1 →
    ∃ env1, Runs we mems initial s1 env1 ∧
      (∀ z, s0.usedNames.contains z = true → env1 z = env0 z) ∧
      s1.usedNames.contains w = true ∧ we w = n ∧ env1 w = x.toNat

/-! ## 5. The recursion: a fuel-bounded fixpoint and its induction -/

/-- The shape the shipping knot must take: a fuel-bounded fixpoint of a
non-recursive step. Fuel exhaustion is a compile error, like the existing
`SPARKLE_TRANSLATE_LIMIT` backstop. -/
def fuelFix (step : TranslateFn → TranslateFn) : Nat → TranslateFn
  | 0 => fun _ _ _ _ => throw (Exception.error .missing "translation fuel exhausted")
  | k + 1 => step (fuelFix step k)

/-- A translator that never succeeds satisfies the specification vacuously. -/
theorem spec_of_never {t : TranslateFn} {ctx we mems initial ρ}
    (never : ∀ e h a b s w s', ¬ Returns (t e h a b) ctx s w s') :
    Spec t ctx we mems initial ρ :=
  ⟨fun e h s0 w s1 hr => absurd hr (never e h false false s0 w s1),
   fun e h _ _ s0 _ w s1 _ hr => absurd hr (never e h false false s0 w s1)⟩

/-- The induction that discharges the recursive hypothesis: if one step
preserves the specification, every fuel-bounded iterate satisfies it. -/
theorem fuelFix_spec {step : TranslateFn → TranslateFn} {ctx we mems initial ρ}
    (hstep : ∀ t, Spec t ctx we mems initial ρ → Spec (step t) ctx we mems initial ρ) :
    ∀ k, Spec (fuelFix step k) ctx we mems initial ρ
  | 0 => spec_of_never fun _ _ _ _ _ _ _ hr => Returns.throw hr
  | k + 1 => hstep _ (fuelFix_spec hstep k)

/-! ## 6. One branch of the real translator: canonical Signal×Signal operators -/

theorem runs_of_body_eq {we : WEnv} {mems : MEnv} {initial : Env} {s t : CircuitState}
    {env : Env} (hb : t.module.body = s.module.body) (h : Runs we mems initial s env) :
    Runs we mems initial t env := by
  unfold Runs at *
  simpa [Module.finalize, hb] using h

/-- The Signal×Signal branch of the SHIPPING operator lowering preserves
meaning, for every canonical operator of `Binary`, at every width, for every
`translate` that satisfies the specification (the recursion hypothesis).

Existing proofs used: `CircuitM.makeWire_spec` (freshness of the result wire,
reservation, unchanged statements), `emitAssign_sound` (the emitted assignment
extends execution by exactly its RHS), `Binary.rhs_correct` (the IR operator
computes the `BitVec` operation), and the `library_*` lemmas above (the
`BitVec` operation is what the library instance computes). -/
theorem translateCanonicalSignalBinary_sound
    {translate : TranslateFn} {ctx : CompilerState} {we : WEnv} {mems : MEnv}
    {initial : Env} {ρ : Valuation}
    (ih : Spec translate ctx we mems initial ρ)
    {e : Lean.Expr} {op : Operator} {hint : String} {isNamed : Bool}
    {m : Name} {us : List Level}
    (hfn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    {n : Nat} {x : BitVec n} {s0 : CircuitState} {env0 : Env} {w : String}
    {s1 : CircuitState}
    (hden : Denotes ρ e n x)
    (hrun : Returns (translateCanonicalSignalBinary translate e op e.getAppArgs true true
      hint isNamed) ctx s0 w s1)
    (hs0 : Runs we mems initial s0 env0) (hw1 : WidthsAgree we s1) :
    ∃ env1, Runs we mems initial s1 env1 ∧
      (∀ z, s0.usedNames.contains z = true → env1 z = env0 z) ∧
      s1.usedNames.contains w = true ∧ we w = n ∧ env1 w = x.toNat := by
  -- the source term is a canonical binary application (the fvar clause is
  -- impossible: an fvar's head is not a constant)
  cases hden with
  | fvar _ => simp [Lean.Expr.getAppFn] at hfn
  | pureLit hfn' _ _ =>
    rw [hfn] at hfn'; cases hfn'
    have : signalBinOpOf ``Sparkle.Core.Signal.Signal.pure = none := rfl
    rw [this] at hop; cases hop
  | @binary _ m' us' bop _ x1 x2 hfn' hop' _ hwid hd1 hd2 =>
  rw [hfn] at hfn'
  cases hfn'
  have hopeq : op = bop.operator := by rw [hop] at hop'; exact Option.some.inj hop'
  subst hopeq
  -- run the shipping code, one bind at a time
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
  rw [hs1] at hw1
  rw [hwres, hs1]
  have hsD := emitAssign_returns hem
  -- facts about the allocation
  obtain ⟨hfresh, hused, hbody, hwires⟩ := CircuitM.makeWire_spec hint (.bitVector n) isNamed s0
  rw [← hres] at hfresh hused hwires
  rw [← hsA] at hused hbody hwires
  -- structural growth, needed for widths before the semantic facts
  obtain ⟨gAu, gAw⟩ := ih.grows _ _ _ _ _ htA
  obtain ⟨gBu, gBw⟩ := ih.grows _ _ _ _ _ htB
  have wiresD : ∀ p ∈ sC.module.wires, p ∈ sD.module.wires := by
    intro p hp; rw [hsD, emitAssign_wires]; exact hp
  have hwC : WidthsAgree we sC := hw1.mono wiresD
  have hwB : WidthsAgree we sB := hwC.mono gBw
  -- operands
  have hsA0 : Runs we mems initial sA env0 := runs_of_body_eq hbody hs0
  obtain ⟨envB, hrB, frB, useA, wA, valA⟩ := ih.sem _ _ _ _ _ _ _ _ hd1 htA hsA0 hwB
  obtain ⟨envC, hrC, frC, useB, wB, valB⟩ := ih.sem _ _ _ _ _ _ _ _ hd2 htB hrB hwC
  have valA' : envC wa = x1.toNat := by rw [frC wa useA]; exact valA
  -- the emitted assignment
  have hrhs := Binary.rhs_correct bop we envC wa wb x1 x2 wA wB valA' valB
  have hrunD := emitAssign_sound sC we mems initial envC res _ _ hrC hrhs
  rw [← hsD] at hrunD
  refine ⟨_, hrunD, ?_, ?_, ?_, ?_⟩
  · -- names reserved before the call keep their values
    intro z hz
    have hzA : sA.usedNames.contains z = true := by
      rw [hused]; simp [Std.HashSet.contains_insert, hz]
    have hne : z ≠ res := by
      intro h; subst h; rw [hfresh] at hz; exact absurd hz (by simp)
    simp only [hne, if_false]
    rw [frC z (gAu z hzA), frB z hzA]
  · rw [hsD, emitAssign_usedNames]
    apply gBu; apply gAu; rw [hused]; simp [Std.HashSet.contains_insert]
  · -- the result wire was declared at width n, and declarations only grow
    have hdecl : ({ name := res, ty := .bitVector n } : Port) ∈ sD.module.wires := by
      apply wiresD; apply gBw; apply gAw; rw [hwires]; simp
    exact hw1 _ hdecl n rfl
  · simp

/-! ## 7. A leaf branch of the real translator: `Signal.pure` of a literal -/

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

/-- The literal branch of the SHIPPING constant lowering preserves meaning. It
is a leaf: no recursion hypothesis. Existing proofs used:
`CircuitM.makeWire_spec`, `emitAssign_sound`; new: `evalExpr_const_lt`. -/
theorem translateSignalPureLiteral_sound {ctx : CompilerState} {we : WEnv} {mems : MEnv}
    {initial : Env} {ρ : Valuation} {e : Lean.Expr} {us : List Level}
    {hint : String} {isNamed : Bool}
    (hfn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us)
    {n : Nat} {x : BitVec n} {s0 : CircuitState} {env0 : Env} {w : String}
    {s1 : CircuitState}
    (hden : Denotes ρ e n x)
    (hrun : Returns (translateSignalPureLiteral? e.getAppArgs hint isNamed) ctx s0 (some w) s1)
    (hs0 : Runs we mems initial s0 env0) (hw1 : WidthsAgree we s1) :
    ∃ env1, Runs we mems initial s1 env1 ∧
      (∀ z, s0.usedNames.contains z = true → env1 z = env0 z) ∧
      s1.usedNames.contains w = true ∧ we w = n ∧ env1 w = x.toNat := by
  cases hden with
  | fvar _ => simp [Lean.Expr.getAppFn] at hfn
  | binary hfn' hop' _ _ _ _ =>
    rw [hfn] at hfn'; cases hfn'
    have : signalBinOpOf ``Sparkle.Core.Signal.Signal.pure = none := rfl
    rw [this] at hop'; cases hop'
  | @pureLit _ _ c _ v _ hback hlit =>
  have hlt := bitVecLitValue?_lt hlit
  unfold translateSignalPureLiteral? at hrun
  rw [hback] at hrun
  simp only [Option.bind_some, hlit] at hrun
  obtain ⟨res, sA, hmk, k1⟩ := Returns.bind hrun
  obtain ⟨hres, hsA⟩ := makeWire_returns hmk
  obtain ⟨u, sB, hem, k2⟩ := Returns.bind k1
  obtain ⟨hwres, hs1⟩ := Returns.pure k2
  have hsB := emitAssign_returns hem
  obtain ⟨hfresh, hused, hbody, hwires⟩ := CircuitM.makeWire_spec hint (.bitVector n) isNamed s0
  rw [← hres] at hfresh hused hwires
  rw [← hsA] at hused hbody hwires
  have hw : w = res := (Option.some.inj hwres)
  rw [hs1] at hw1
  rw [hw, hs1]
  have hsA0 : Runs we mems initial sA env0 := runs_of_body_eq hbody hs0
  have hrunB := emitAssign_sound sA we mems initial env0 res _ _ hsA0
    (evalExpr_const_lt we env0 v n hlt)
  rw [← hsB] at hrunB
  refine ⟨_, hrunB, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hne : z ≠ res := by
      intro h; subst h; rw [hfresh] at hz; exact absurd hz (by simp)
    simp [hne]
  · rw [hsB, emitAssign_usedNames, hused]; simp [Std.HashSet.contains_insert]
  · have hdecl : ({ name := res, ty := .bitVector n } : Port) ∈ sB.module.wires := by
      rw [hsB, emitAssign_wires, hwires]; simp
    exact hw1 _ hdecl n rfl
  · simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

end Tools.ShippingTranslateSoundness
