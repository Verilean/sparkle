-- BUILT by the integrator: og1 exit 1 (a redundant tactic after `simp only` closed the goal), og2 exit 0 (308 jobs); axioms standard (ax6).
import Tools.ShippingChildInv

/-! # A concrete message outside `OkMsg` (makes probe case E precise)

`OkMsg` (`Tools/ShippingChildInv.lean`, the class of messages the diagnostic / exception laws allow)
contains two LAZY leaves, `ofExpr e` and `ofConstName n` (both `MessageData.ofLazy …`), so "the
escaped message is an `ofLazy` node" does NOT show that it is outside the class. Here a structural
test that the class cannot pass:

* `hasGoal m` — `m` contains an `ofGoal` node (through the structural constructors; lazy nodes,
  widgets and traces count as `false`);
* `okMsg_hasGoal : OkMsg m → hasGoal m = false` — every message of the class is goal-free;
* `not_okMsg_of_hasGoal : hasGoal m = true → ¬ OkMsg m`.

The probe (`Tests/Compiler/CanUnfoldProbe.lean`, case G) throws `ofGoal g` from a `canUnfold?`
callback and evaluates `hasGoal` of the message that escapes `whnf`: `true` there means the escaped
exception is not `OkExc` by this lemma. That is a statement about the escaped VALUE (observed at
runtime) plus a kernel lemma; it is NOT by itself a counterexample to `excOk`, whose premise also
asks the start world to be `quiet` (not checked by the probe). -/

namespace Tools.ShippingOkMsgGoal
open Lean
open Tools.ShippingChildInv

/-- The message contains an `ofGoal` node (structurally). -/
def hasGoal : MessageData → Bool
  | .ofGoal _ => true
  | .compose a b => hasGoal a || hasGoal b
  | .nest _ a => hasGoal a
  | .group a => hasGoal a
  | .tagged _ a => hasGoal a
  | .withContext _ a => hasGoal a
  | .withNamingContext _ a => hasGoal a
  | .ofOriginatingSyntax _ a => hasGoal a
  | _ => false

theorem hasGoal_joinSep (sep : MessageData) (hs : hasGoal sep = false) :
    ∀ l : List MessageData, (∀ m ∈ l, hasGoal m = false) → hasGoal (MessageData.joinSep l sep) = false
  | [], _ => rfl
  | [a], h => by
    simp only [MessageData.joinSep]
    exact h a (List.mem_singleton.mpr rfl)
  | a :: b :: rest, h => by
    simp only [MessageData.joinSep]
    have ha := h a (List.mem_cons_self ..)
    have hr := hasGoal_joinSep sep hs (b :: rest) (fun m hm => h m (List.mem_cons_of_mem _ hm))
    show (hasGoal (a ++ sep ++ MessageData.joinSep (b :: rest) sep)) = false
    simp only [HAppend.hAppend, Append.append, hasGoal, ha, hs, hr, Bool.or_false]

theorem hasGoal_string (s : String) : hasGoal (stringToMessageData s) = false := by
  unfold stringToMessageData
  apply hasGoal_joinSep _ rfl
  intro m hm
  first
    | (simp only [Std.Iter.toList_map, List.mem_map] at hm
       obtain ⟨x, -, rfl⟩ := hm
       rfl)
    | (simp at hm
       obtain ⟨x, -, rfl⟩ := hm
       rfl)

theorem okMsg_hasGoal {m : MessageData} (h : OkMsg m) : hasGoal m = false := by
  induction h with
  | str s => exact hasGoal_string s
  | fmt f => rfl
  | compose _ _ iha ihb => simp [hasGoal, iha, ihb]
  | nest _ _ ih => simpa [hasGoal] using ih
  | group _ ih => simpa [hasGoal] using ih
  | tagged _ _ ih => simpa [hasGoal] using ih
  | withContext _ _ _ ih => simpa [hasGoal] using ih
  | withNamingContext _ _ ih => simpa [hasGoal] using ih
  | ofSyntax _ _ ih => simpa [hasGoal] using ih
  | ofExpr e => rfl
  | ofConstName n full => rfl

theorem not_okMsg_of_hasGoal {m : MessageData} (h : hasGoal m = true) : ¬ OkMsg m := by
  intro hm
  rw [okMsg_hasGoal hm] at h
  cases h

/-- In particular a bare goal message is outside the class. -/
theorem not_okMsg_ofGoal (g : MVarId) : ¬ OkMsg (.ofGoal g) :=
  not_okMsg_of_hasGoal rfl

end Tools.ShippingOkMsgGoal
