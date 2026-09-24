import Tools.ShippingAllocationSoundness
import Std.Data.HashMap.Lemmas

/-! Scoped and persistent variable bindings of the shipping compiler.
The persistent table is the actual `Std.HashMap Lean.Name String` type.
These are transition rules, not a claim that every MetaM handler maintains them.
In particular, restoring a reader does not restore the mutable circuit state. -/
namespace Tools.ShippingBindingsSoundness

open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingScalarSoundness Tools.ShippingAllocationSoundness

abbrev Persistent := Std.HashMap Lean.Name String

def visible (state : CompilerState) (persistent : Persistent) (key : FVarId) : Option String :=
  match state.varMap.lookup key with
  | some wire => some wire
  | none => persistent.get? key.name

/-- Source values follow the same local-first rule as lookupVar. The two
valuations remain separate so shadowing cannot destroy the outer one. -/
def visibleValues (state : CompilerState) (localValues : FVarId → Nat)
    (persistentValues : Name → Nat) (key : FVarId) : Nat :=
  if (state.varMap.lookup key).isSome then localValues key else persistentValues key.name

/-- Both maps, including bindings hidden by local shadowing, must stay valid. -/
structure Valid (state : CompilerState) (persistent : Persistent)
    (localValues : FVarId → Nat) (persistentValues : Name → Nat)
    (env : Env) (used : Std.HashSet String) : Prop where
  locals : LocalBindingsAgree state localValues env
  persistentAgree : BindingsAgree (fun k => persistent.get? k) persistentValues env
  localReserved : Reserved (fun k => state.varMap.lookup k) used
  persistentReserved : Reserved (fun k => persistent.get? k) used

theorem Valid.visible_correct (h : Valid state persistent lv pv env used) :
    BindingsAgree (visible state persistent) (visibleValues state lv pv) env := by
  intro key wire hw
  cases hk : state.varMap.lookup key with
  | some w =>
    have he : w = wire := by simpa [visible, hk] using hw
    subst wire
    simpa [visibleValues, hk] using h.locals key w hk
  | none =>
    have hp : persistent.get? key.name = some wire := by simpa [visible, hk] using hw
    simpa [visibleValues, hk] using h.persistentAgree key.name wire hp

theorem Valid.visible_reserved (h : Valid state persistent lv pv env used) :
    Reserved (visible state persistent) used := by
  intro key wire hw
  cases hk : state.varMap.lookup key with
  | some w =>
    have he : w = wire := by simpa [visible, hk] using hw
    subst wire
    exact h.localReserved key w hk
  | none => exact h.persistentReserved key.name wire (by simpa [visible, hk] using hw)

/-- Local-hit rule for the local-first lookup model. Connecting the IO read
on a miss to a snapshot of the private persistent ref remains an obligation. -/
theorem visible_local (state : CompilerState) (persistent : Persistent)
    (key : FVarId) (wire : String)
    (hit : state.varMap.lookup key = some wire) :
    visible state persistent key = some wire := by
  simp [visible, hit]

/-- Exact execution equation for the shipping reader-scoped operation. -/
theorem withVarMapping_run {α : Type} (key : FVarId) (wire : String)
    (action : CompilerM α) (state : CompilerState) (circuit : CircuitState) :
    (CompilerM.withVarMapping key wire action state).run circuit =
      (action { state with varMap := (key, wire) :: state.varMap }).run circuit := rfl

theorem Valid.enter (h : Valid state persistent lv pv env used)
    (key : FVarId) (wire : String) (value : Nat) (hv : env wire = value)
    (hr : used.contains wire = true) :
    Valid { state with varMap := (key, wire) :: state.varMap } persistent
      (fun k => if k == key then value else lv k) pv env used := by
  refine ⟨LocalBindingsAgree.extend state lv env h.locals key wire value hv,
    h.persistentAgree, ?_, h.persistentReserved⟩
  intro k n hn
  cases hk : (k == key) with
  | true =>
    have he : wire = n := by simpa [List.lookup_cons, hk] using hn
    subst n
    exact hr
  | false => exact h.localReserved k n (by simpa [List.lookup_cons, hk] using hn)

/-- The exact HashMap insert used when handleLoop registers its binder.
Existing local values are unchanged; only the persistent valuation is updated. -/
theorem Valid.insert_persistent (h : Valid state persistent lv pv env used)
    (key : Name) (wire : String) (value : Nat) (hv : env wire = value)
    (hr : used.contains wire = true) :
    Valid state (persistent.insert key wire) lv
      (fun k => if key == k then value else pv k) env used := by
  refine ⟨h.locals, ?_, h.localReserved, ?_⟩
  · intro k n hn
    dsimp only at hn
    rw [Std.HashMap.get?_insert] at hn
    split at hn
    · rename_i hk
      have he := Option.some.inj hn
      subst n
      simpa [hk] using hv
    · rename_i hk
      simpa [hk] using h.persistentAgree k n hn
  · intro k n hn
    dsimp only at hn
    rw [Std.HashMap.get?_insert] at hn
    split at hn
    · have he := Option.some.inj hn
      subst n
      exact hr
    · exact h.persistentReserved k n hn

/-- A write to an actually allocated name preserves even hidden bindings.
This is the condition needed to restore an outer scope after emitted code. -/
theorem Valid.allocate_write (h : Valid state persistent lv pv env s.usedNames)
    (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) (value : Nat) :
    let a := CircuitM.makeWire hint ty named s
    Valid state persistent lv pv (write env a.1 value) a.2.usedNames := by
  dsimp only
  refine ⟨h.locals.write_fresh _ _ (makeWire_not_live _ s h.localReserved hint ty named),
    h.persistentAgree.write_fresh _ _ (makeWire_not_live _ s h.persistentReserved hint ty named),
    makeWire_reserved _ s h.localReserved hint ty named,
    makeWire_reserved _ s h.persistentReserved hint ty named⟩

/-- Enter a local scope, allocate/write in it, then leave it: both the inner
and the original outer invariant survive the SAME circuit-state transition.
This also protects an older local binding hidden by the new list head. -/
theorem Valid.scope_allocate_restore (h : Valid state persistent lv pv env s.usedNames)
    (key : FVarId) (wire : String) (value : Nat) (hv : env wire = value)
    (hr : s.usedNames.contains wire = true)
    (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) (written : Nat) :
    let a := CircuitM.makeWire hint ty named s
    let after := write env a.1 written
    Valid { state with varMap := (key, wire) :: state.varMap } persistent
      (fun k => if k == key then value else lv k) pv after a.2.usedNames ∧
    Valid state persistent lv pv after a.2.usedNames := by
  exact ⟨(h.enter key wire value hv hr).allocate_write hint ty named written,
    h.allocate_write hint ty named written⟩

/-- Compose the hidden-binding invariant with actual allocation and assignment
emission. The prefix and operand hypotheses are local simulation premises;
there is no whole-circuit replay premise or destination-freshness premise. -/
theorem Valid.allocate_emit (h : Valid state persistent lv pv prior s.usedNames)
    (op : Binary) (we : WEnv) (mems : MEnv) (initial : Env)
    (a b hint : String) (named : Bool) (x y : BitVec w)
    (hp : evalAssigns we mems s.module.finalize.body initial = some prior)
    (hwa : we a = w) (hwb : we b = w)
    (ha : prior a = x.toNat) (hb : prior b = y.toNat) :
    let allocation := CircuitM.makeWire hint (.bitVector w) named s
    let emitted := (CircuitM.emitAssign allocation.1
      (.op op.operator [.ref a, .ref b]) allocation.2).2
    ∃ result, evalAssigns we mems emitted.module.finalize.body initial = some result ∧
      result allocation.1 = (op.apply x y).toNat ∧
      Valid state persistent lv pv result emitted.usedNames := by
  dsimp only
  have hm := CircuitM.makeWire_spec hint (.bitVector w) named s
  have hp' : evalAssigns we mems
      (CircuitM.makeWire hint (.bitVector w) named s).2.module.finalize.body initial =
      some prior := by
    change evalAssigns we mems
      (CircuitM.makeWire hint (.bitVector w) named s).2.module.body.reverse initial = _
    rw [hm.2.2.1]
    exact hp
  refine ⟨write prior (CircuitM.makeWire hint (.bitVector w) named s).1
    (op.apply x y).toNat, ?_, ?_, ?_⟩
  · exact Tools.ShippingBuilderSoundness.emitAssign_sound _ we mems initial prior _ _ _ hp'
      (op.rhs_correct we prior a b x y hwa hwb ha hb)
  · simp [write]
  · exact h.allocate_write hint (.bitVector w) named _

/-- Scope restoration is sound when the body preserves every wire mentioned
by the OUTER maps. Validity of the inner visible map alone is insufficient. -/
theorem Valid.restore (h : Valid state persistent lv pv before used)
    (after : Env) (usedAfter : Std.HashSet String)
    (keepLocal : ∀ key wire, state.varMap.lookup key = some wire → after wire = before wire)
    (keepPersistent : ∀ key wire, persistent.get? key = some wire → after wire = before wire)
    (keepReserved : ∀ wire, used.contains wire = true → usedAfter.contains wire = true) :
    Valid state persistent lv pv after usedAfter := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro key wire hw
    rw [keepLocal key wire hw]
    exact h.locals key wire hw
  · intro key wire hw
    rw [keepPersistent key wire hw]
    exact h.persistentAgree key wire hw
  · intro key wire hw
    exact keepReserved wire (h.localReserved key wire hw)
  · intro key wire hw
    exact keepReserved wire (h.persistentReserved key wire hw)

end Tools.ShippingBindingsSoundness
