import Tools.ShippingScalarSoundness

/-! Discharge the scalar-emission freshness premise using the ACTUAL allocator.
The remaining invariant is that every live source/cache binding is reserved.
Theorems below propagate that invariant through allocation and binding extension;
they do not assert it for all MetaM/cache entry points without further proof. -/

namespace Tools.ShippingAllocationSoundness

open Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingScalarSoundness

def Reserved {Key : Type} (lookup : Key → Option String) (used : Std.HashSet String) : Prop :=
  ∀ key wire, lookup key = some wire → used.contains wire = true

theorem Reserved.not_live {Key : Type} {lookup : Key → Option String}
    {used : Std.HashSet String} (h : Reserved lookup used)
    (name : String) (fresh : used.contains name = false) : ¬ Live lookup name := by
  rintro ⟨key, hk⟩
  have := h key name hk
  simp [fresh] at this

theorem Reserved.insert {Key : Type} {lookup : Key → Option String}
    {used : Std.HashSet String} (h : Reserved lookup used) (name : String) :
    Reserved lookup (used.insert name) := by
  intro key wire hk
  simp [Std.HashSet.contains_insert, h key wire hk]

theorem Reserved.cons {Key : Type} [BEq Key] (bindings : List (Key × String))
    (used : Std.HashSet String) (h : Reserved (fun k => bindings.lookup k) used)
    (key : Key) (wire : String) :
    Reserved (fun k => ((key, wire) :: bindings).lookup k) (used.insert wire) := by
  intro k n hn
  cases hk : (k == key) with
  | true =>
    have hn' : wire = n := by simpa [List.lookup_cons, hk] using hn
    subst n
    simp
  | false =>
    have hn' : bindings.lookup k = some n := by simpa [List.lookup_cons, hk] using hn
    exact h.insert wire k n hn'

theorem makeWire_not_live {Key : Type} (lookup : Key → Option String)
    (s : CircuitState) (h : Reserved lookup s.usedNames)
    (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    ¬ Live lookup (CircuitM.makeWire hint ty named s).1 :=
  h.not_live _ (CircuitM.makeWire_spec hint ty named s).1

theorem makeWire_reserved {Key : Type} (lookup : Key → Option String)
    (s : CircuitState) (h : Reserved lookup s.usedNames)
    (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    Reserved lookup (CircuitM.makeWire hint ty named s).2.usedNames := by
  rw [(CircuitM.makeWire_spec hint ty named s).2.1]
  exact h.insert _

/-- Unlike Binary.emit_correct, this theorem takes no fresh-destination
hypothesis. The shipping allocator supplies it for any hint and naming mode.
The result still requires the source/wire relation and operand widths, plus
the reservation invariant on entry. -/
theorem allocate_emit_correct {Key : Type} (op : Binary)
    (s : CircuitState) (we : WEnv) (mems : MEnv) (initial prior : Env)
    (a b hint : String) (named : Bool) (x y : BitVec w)
    (lookup : Key → Option String) (values : Key → Nat)
    (hprefix : evalAssigns we mems s.module.finalize.body initial = some prior)
    (hwa : we a = w) (hwb : we b = w)
    (ha : prior a = x.toNat) (hb : prior b = y.toNat)
    (bindings : BindingsAgree lookup values prior) (reserved : Reserved lookup s.usedNames) :
    let allocation := CircuitM.makeWire hint (.bitVector w) named s
    let emitted := (CircuitM.emitAssign allocation.1
      (.op op.operator [.ref a, .ref b]) allocation.2).2
    ∃ result,
      evalAssigns we mems emitted.module.finalize.body initial = some result ∧
      result allocation.1 = (op.apply x y).toNat ∧
      BindingsAgree lookup values result ∧ Reserved lookup emitted.usedNames := by
  dsimp only
  have hm := CircuitM.makeWire_spec hint (.bitVector w) named s
  have hp : evalAssigns we mems
      (CircuitM.makeWire hint (.bitVector w) named s).2.module.finalize.body initial = some prior := by
    change evalAssigns we mems
      (CircuitM.makeWire hint (.bitVector w) named s).2.module.body.reverse initial = _
    rw [hm.2.2.1]
    exact hprefix
  obtain ⟨_, result, hr, hv, hc⟩ := op.emit_correct
    (CircuitM.makeWire hint (.bitVector w) named s).2 we mems initial prior a b
    (CircuitM.makeWire hint (.bitVector w) named s).1 x y lookup values hp hwa hwb ha hb
    bindings (makeWire_not_live lookup s reserved hint (.bitVector w) named)
  refine ⟨result, hr, hv, hc, ?_⟩
  exact makeWire_reserved lookup s reserved hint (.bitVector w) named

end Tools.ShippingAllocationSoundness
