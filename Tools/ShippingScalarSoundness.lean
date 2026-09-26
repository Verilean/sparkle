import Sparkle.Compiler.Elab
import Tools.ShippingBuilderSoundness

/-! Local simulation rules for the SHIPPING scalar lowering path.
The finite primitive specification below refers to the existing registry and
the existing IR expressions/builder; it is not another source compiler.
These rules cover canonical BitVec functions. Recognizing overloaded Lean
operations, establishing widths, allocation freshness and cache validity
through MetaM remain obligations of the full compiler proof. -/

namespace Tools.ShippingScalarSoundness

open Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.Compiler.Elab Tools.ShippingBuilderSoundness

/-- Canonical same-width binary functions, independently of syntax/typeclass
recognition. Other registry entries are not covered by this theorem. -/
inductive Binary where
  | add | sub | mul | and | or | xor
  deriving DecidableEq, Repr

def Binary.name : Binary → Lean.Name
  | .add => ``BitVec.add
  | .sub => ``BitVec.sub
  | .mul => ``BitVec.mul
  | .and => ``BitVec.and
  | .or => ``BitVec.or
  | .xor => ``BitVec.xor

def Binary.operator : Binary → Operator
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .and => .and
  | .or => .or
  | .xor => .xor

def Binary.apply {w : Nat} : Binary → BitVec w → BitVec w → BitVec w
  | .add => BitVec.add
  | .sub => BitVec.sub
  | .mul => BitVec.mul
  | .and => BitVec.and
  | .or => BitVec.or
  | .xor => BitVec.xor

/-- Connect the specification to the ACTUAL shipping operator registry. -/
theorem Binary.registry (op : Binary) : getOperator op.name = some op.operator := by
  cases op <;> rfl

/-- No closed proposition or per-circuit decision procedure: arbitrary widths
(including zero), names, environments and operand values. -/
theorem Binary.rhs_correct (op : Binary) (we : WEnv) (env : Env)
    (a b : String) (x y : BitVec w)
    (hwa : we a = w) (hwb : we b = w)
    (ha : env a = x.toNat) (hb : env b = y.toNat) :
    evalExpr we env (.op op.operator [.ref a, .ref b]) = some (op.apply x y).toNat := by
  cases op <;>
    simp [Binary.operator, Binary.apply, evalExpr, evalList, evalOp, widthOf,
      hwa, hwb, ha, hb, mask, BitVec.toNat_add, BitVec.toNat_sub,
      BitVec.toNat_mul, ← BitVec.toNat_and, ← BitVec.toNat_or, ← BitVec.toNat_xor,
      Nat.add_comm]

/-- Semantic value-to-wire relation, reusable for local variables or cache
keys. It does not assume a denotation for arbitrary Lean.Expr: the source
valuation must be supplied by the surrounding compiler simulation. -/
def BindingsAgree {Key : Type} (lookup : Key → Option String)
    (values : Key → Nat) (env : Env) : Prop :=
  ∀ key wire, lookup key = some wire → env wire = values key

def Live {Key : Type} (lookup : Key → Option String) (wire : String) : Prop :=
  ∃ key, lookup key = some wire

def write (env : Env) (wire : String) (value : Nat) : Env :=
  fun n => if n = wire then value else env n

theorem BindingsAgree.write_fresh {Key : Type} {lookup : Key → Option String}
    {values : Key → Nat} {env : Env} (h : BindingsAgree lookup values env)
    (dest : String) (value : Nat) (fresh : ¬ Live lookup dest) :
    BindingsAgree lookup values (write env dest value) := by
  intro key wire hw
  have hn : wire ≠ dest := by
    intro he
    subst wire
    exact fresh ⟨key, hw⟩
  simpa [write, hn] using h key wire hw

/-- Scoped list extension, matching CompilerState.varMap's first-wins lookup.
The source valuation uses the same Boolean key comparison as list lookup. -/
theorem BindingsAgree.cons {Key : Type} [BEq Key]
    (bindings : List (Key × String)) (values : Key → Nat) (env : Env)
    (h : BindingsAgree (fun k => bindings.lookup k) values env)
    (key : Key) (wire : String) (value : Nat) (hv : env wire = value) :
    BindingsAgree (fun k => ((key, wire) :: bindings).lookup k)
      (fun k => if k == key then value else values k) env := by
  intro k n hn
  cases hk : (k == key) with
  | true =>
    have hn' : wire = n := by simpa [List.lookup_cons, hk] using hn
    subst n
    simpa [hk] using hv
  | false =>
    have hn' : bindings.lookup k = some n := by simpa [List.lookup_cons, hk] using hn
    simpa [hk] using h k n hn'

/-- The reader-scoped map used by the shipping compiler is an instance of the
relation. ShippingBindingsSoundness connects the persistent state-backed fallback. -/
def LocalBindingsAgree (state : CompilerState) (values : Lean.FVarId → Nat)
    (env : Env) : Prop := BindingsAgree (fun k => state.varMap.lookup k) values env

theorem LocalBindingsAgree.extend (state : CompilerState)
    (values : Lean.FVarId → Nat) (env : Env) (h : LocalBindingsAgree state values env)
    (key : Lean.FVarId) (wire : String) (value : Nat) (hv : env wire = value) :
    LocalBindingsAgree { state with varMap := (key, wire) :: state.varMap }
      (fun k => if k == key then value else values k) env :=
  BindingsAgree.cons state.varMap values env h key wire value hv

/-- Compose actual registry selection, operand semantics and actual builder
emission. The only semantic premises concern the already-built prefix and
the two operand wires; no RHS or whole-circuit replay proof is required. -/
theorem Binary.emit_correct {Key : Type} (op : Binary)
    (s : CircuitState) (we : WEnv) (mems : MEnv) (initial prior : Env)
    (a b dest : String) (x y : BitVec w)
    (lookup : Key → Option String) (values : Key → Nat)
    (hprefix : evalAssigns we mems s.module.finalize.body initial = some prior)
    (hwa : we a = w) (hwb : we b = w)
    (ha : prior a = x.toNat) (hb : prior b = y.toNat)
    (bindings : BindingsAgree lookup values prior) (fresh : ¬ Live lookup dest) :
    getOperator op.name = some op.operator ∧
    ∃ result,
      evalAssigns we mems
        (CircuitM.emitAssign dest (.op op.operator [.ref a, .ref b]) s).2.module.finalize.body
        initial = some result ∧
      result dest = (op.apply x y).toNat ∧ BindingsAgree lookup values result := by
  refine ⟨op.registry, write prior dest (op.apply x y).toNat, ?_, ?_, ?_⟩
  · exact emitAssign_sound s we mems initial prior dest _ _ hprefix
      (op.rhs_correct we prior a b x y hwa hwb ha hb)
  · simp [write]
  · exact bindings.write_fresh dest _ fresh

/-- The statement-producing step and scoped binding extension compose into
the local-variable invariant. Freshness is required for all currently visible
bindings; proving it for the allocator is still a separate obligation. -/
theorem Binary.emit_local (op : Binary) (state : CompilerState)
    (s : CircuitState) (we : WEnv) (mems : MEnv) (initial prior : Env)
    (a b dest : String) (x y : BitVec w) (key : Lean.FVarId)
    (values : Lean.FVarId → Nat)
    (hprefix : evalAssigns we mems s.module.finalize.body initial = some prior)
    (hwa : we a = w) (hwb : we b = w)
    (ha : prior a = x.toNat) (hb : prior b = y.toNat)
    (bindings : LocalBindingsAgree state values prior)
    (fresh : ¬ Live (fun k => state.varMap.lookup k) dest) :
    ∃ result,
      evalAssigns we mems
        (CircuitM.emitAssign dest (.op op.operator [.ref a, .ref b]) s).2.module.finalize.body
        initial = some result ∧
      result dest = (op.apply x y).toNat ∧
      LocalBindingsAgree { state with varMap := (key, dest) :: state.varMap }
        (fun k => if k == key then (op.apply x y).toNat else values k) result := by
  obtain ⟨_, result, hr, hv, hb⟩ := op.emit_correct s we mems initial prior a b dest x y
    (fun k => state.varMap.lookup k) values hprefix hwa hwb ha hb bindings fresh
  exact ⟨result, hr, hv, LocalBindingsAgree.extend state values result hb key dest _ hv⟩

end Tools.ShippingScalarSoundness
