import Tools.ShippingEntrySoundness
import Tools.ConeFoldSlices
import Tools.ShippingOptSoundness

/-! # Post-processing: `dropZeroWidthModule` and `mergeDuplicates`

`synthesizeCombinational` (what `#synthesizeVerilog` calls) runs the entry,
then `dropZeroWidthModule`, then `mergeDuplicates` (skipped when
`SPARKLE_NO_REGDEDUP` is set). This file proves both passes preserve the IR
semantics on the modules the certified entry returns, and extends the entry
theorems to the IR `synthesizeCombinational` returns. -/

namespace Tools.ShippingPostSoundness

open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.IR.Type Tools.ShippingTranslateSoundness Tools.ShippingEntrySoundness
open Sparkle.IR.RegDedup Sparkle.IR.ZeroWidth
open Tools.ConeFold (WidthMatch evalOp_congr widthOf_op_shape evalGo_congr widthOfGo_congr)

/-! ## 1. Renaming references -/

mutual
/-- Renaming each reference `x` to `σ x`, where `σ x` carries the same value
and has the same width, changes neither width nor value. -/
theorem renameE_sound (we : WEnv) (env : Env) (σ : String → String)
    (hσ : ∀ x, env (σ x) = env x ∧ we (σ x) = we x) :
    ∀ e, widthOf we (renameE σ e) = widthOf we e ∧
      evalExpr we env (renameE σ e) = evalExpr we env e
  | .const _ _ => ⟨rfl, rfl⟩
  | .ref n => ⟨(hσ n).2, by simp [renameE, evalExpr, (hσ n).1]⟩
  | .op o args => by
    obtain ⟨hm, hl⟩ := renameL_sound we env σ hσ args
    have hw : widthOf we (renameE σ (.op o args)) = widthOf we (.op o args) :=
      widthOf_op_shape we o hm
    refine ⟨hw, ?_⟩
    show evalExpr we env (.op o (renameE.renameL σ args)) = _
    simp only [evalExpr, hl]
    cases evalList we env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [show widthOf we (.op o (renameE.renameL σ args)) = widthOf we (.op o args) from hw]
      exact evalOp_congr we hm o vals _
  | .concat args => by
    obtain ⟨hm, hl⟩ := renameL_sound we env σ hσ args
    refine ⟨?_, ?_⟩
    · show widthOf.go we (renameE.renameL σ args) = widthOf.go we args
      exact widthOfGo_congr we hm
    · show evalExpr we env (.concat (renameE.renameL σ args)) = _
      simp only [evalExpr, hl]
      cases evalList we env args with
      | none => rfl
      | some vals =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        rw [evalGo_congr we hm vals]
  | .slice e hi lo => by
    obtain ⟨-, he⟩ := renameE_sound we env σ hσ e
    exact ⟨rfl, by simp only [renameE, evalExpr, he]⟩
  | .sliceDim _ _ _ => ⟨rfl, rfl⟩
  | .index _ _ => ⟨rfl, rfl⟩

theorem renameL_sound (we : WEnv) (env : Env) (σ : String → String)
    (hσ : ∀ x, env (σ x) = env x ∧ we (σ x) = we x) :
    ∀ args, WidthMatch we args (renameE.renameL σ args) ∧
      evalList we env (renameE.renameL σ args) = evalList we env args
  | [] => ⟨.nil, rfl⟩
  | a :: rest => by
    obtain ⟨hwa, hea⟩ := renameE_sound we env σ hσ a
    obtain ⟨hm, hl⟩ := renameL_sound we env σ hσ rest
    refine ⟨.cons hwa hm, ?_⟩
    show evalList we env (renameE σ a :: renameE.renameL σ rest) = _
    simp only [evalList, hea, hl]
end

mutual
theorem refs_renameE (σ : String → String) :
    ∀ e z, z ∈ Sparkle.IR.Reorder.refsOf (renameE σ e) →
      ∃ x ∈ Sparkle.IR.Reorder.refsOf e, z = σ x
  | .const _ _, z, h => by simp [renameE, Sparkle.IR.Reorder.refsOf] at h
  | .ref n, z, h => by
    simp [renameE, Sparkle.IR.Reorder.refsOf] at h
    exact ⟨n, by simp [Sparkle.IR.Reorder.refsOf], h⟩
  | .op o args, z, h => by
    obtain ⟨x, hx, hz⟩ := refs_renameL σ args z h
    exact ⟨x, hx, hz⟩
  | .concat args, z, h => by
    obtain ⟨x, hx, hz⟩ := refs_renameL σ args z h
    exact ⟨x, hx, hz⟩
  | .slice e _ _, z, h => refs_renameE σ e z h
  | .sliceDim e _ _, z, h => refs_renameE σ e z h
  | .index a i, z, h => by
    simp only [renameE, Sparkle.IR.Reorder.refsOf, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x, hx, hz⟩ := refs_renameE σ a z h
      exact ⟨x, by simp [Sparkle.IR.Reorder.refsOf, hx], hz⟩
    · obtain ⟨x, hx, hz⟩ := refs_renameE σ i z h
      exact ⟨x, by simp [Sparkle.IR.Reorder.refsOf, hx], hz⟩

theorem refs_renameL (σ : String → String) :
    ∀ args z, z ∈ Sparkle.IR.Reorder.refsOf.refsList (renameE.renameL σ args) →
      ∃ x ∈ Sparkle.IR.Reorder.refsOf.refsList args, z = σ x
  | [], z, h => by simp [renameE.renameL, Sparkle.IR.Reorder.refsOf.refsList] at h
  | a :: rest, z, h => by
    simp only [renameE.renameL, Sparkle.IR.Reorder.refsOf.refsList, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x, hx, hz⟩ := refs_renameE σ a z h
      exact ⟨x, by simp [Sparkle.IR.Reorder.refsOf.refsList, hx], hz⟩
    · obtain ⟨x, hx, hz⟩ := refs_renameL σ rest z h
      exact ⟨x, by simp [Sparkle.IR.Reorder.refsOf.refsList, hx], hz⟩
end

/-! ## 2. The merge checker is sound -/

open Sparkle.IR.Reorder (refsOf evalExpr_congr)

/-- A name no later statement of the body can reassign. -/
def Settled (allLhs defined : List String) (z : String) : Prop := z ∈ defined ∨ z ∉ allLhs

/-- What `validateMerge` knows after a prefix, in the environment that prefix
produced. -/
structure CheckInv (we : WEnv) (allLhs : List String) (st : MergeCheck) (env : Env) : Prop where
  S : ∀ x, env (aliasOf st.S x) = env x ∧ we (aliasOf st.S x) = we x
  V : ∀ x, env (aliasOf st.V x) = env x ∧ we (aliasOf st.V x) = we x
  R : ∀ y c, st.R.lookup y = some c → evalExpr we env c = some (env y)
  domS : ∀ x y, st.S.lookup x = some y → x ∈ st.defined ∧ y ∈ st.defined
  domV : ∀ x y, st.V.lookup x = some y → x ∈ st.defined ∧ Settled allLhs st.defined y
  domR : ∀ y c, st.R.lookup y = some c →
    y ∈ st.defined ∧ ∀ z ∈ refsOf c, Settled allLhs st.defined z

theorem aliasOf_cons (l t : String) (A : List (String × String)) (z : String) :
    aliasOf ((l, t) :: A) z = if z = l then t else aliasOf A z := by
  unfold aliasOf
  by_cases h : z = l
  · subst h; simp [List.lookup_cons]
  · have hb : (z == l) = false := beq_false_of_ne h
    simp [List.lookup, hb, h]

theorem aliasOf_of_none {A : List (String × String)} {z : String} (h : A.lookup z = none) :
    aliasOf A z = z := by
  simp [aliasOf, h]

theorem lookup_cons_eq {α : Type} (l : String) (t : α) (A : List (String × α)) (z : String) :
    ((l, t) :: A).lookup z = if z = l then some t else A.lookup z := by
  by_cases h : z = l
  · subst h; simp [List.lookup_cons]
  · have hb : (z == l) = false := beq_false_of_ne h
    simp [List.lookup, hb, h]

/-- A settled name stays settled through the value aliases. -/
theorem settled_aliasOf {allLhs defined : List String} {V : List (String × String)}
    (hV : ∀ x y, V.lookup x = some y → x ∈ defined ∧ Settled allLhs defined y)
    {x : String} (hx : Settled allLhs defined x) : Settled allLhs defined (aliasOf V x) := by
  cases h : V.lookup x with
  | none => rw [aliasOf_of_none h]; exact hx
  | some y => simp only [aliasOf, h, Option.getD_some]; exact (hV x y h).2

theorem settled_ne {allLhs defined : List String} {l z : String} (hl : l ∈ allLhs)
    (hnd : l ∉ defined) (hz : Settled allLhs defined z) : z ≠ l := by
  rintro rfl
  rcases hz with h | h
  · exact hnd h
  · exact h hl

theorem settled_mono {allLhs defined : List String} {l z : String}
    (hz : Settled allLhs defined z) : Settled allLhs (l :: defined) z := by
  rcases hz with h | h
  · exact Or.inl (List.mem_cons_of_mem _ h)
  · exact Or.inr h

/-- The frame: assigning a name that is not yet defined but is assigned by the
body keeps everything the checker knows. -/
theorem CheckInv.update {we : WEnv} {allLhs : List String} {st : MergeCheck} {env : Env}
    (h : CheckInv we allLhs st env) {l : String} (hl : l ∈ allLhs) (hnd : l ∉ st.defined)
    (v : Nat) :
    CheckInv we allLhs { st with defined := l :: st.defined }
      (fun n => if n = l then v else env n) := by
  have hS : ∀ x, aliasOf st.S x = x ∨ aliasOf st.S x ∈ st.defined := by
    intro x
    cases hx : st.S.lookup x with
    | none => left; exact aliasOf_of_none hx
    | some y => right; simp only [aliasOf, hx, Option.getD_some]; exact (h.domS x y hx).2
  have hSl : aliasOf st.S l = l := by
    cases hx : st.S.lookup l with
    | none => exact aliasOf_of_none hx
    | some y => exact absurd (h.domS l y hx).1 hnd
  have hVl : aliasOf st.V l = l := by
    cases hx : st.V.lookup l with
    | none => exact aliasOf_of_none hx
    | some y => exact absurd (h.domV l y hx).1 hnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = l
    · subst hx; rw [hSl]; exact ⟨rfl, rfl⟩
    · have hne : aliasOf st.S x ≠ l := by
        rcases hS x with e | e
        · rw [e]; exact hx
        · intro e'; rw [e'] at e; exact hnd e
      simp only [hne, hx, if_false]
      exact h.S x
  · intro x
    by_cases hx : x = l
    · subst hx; rw [hVl]; exact ⟨rfl, rfl⟩
    · have hne : aliasOf st.V x ≠ l := by
        cases hy : st.V.lookup x with
        | none => rw [aliasOf_of_none hy]; exact hx
        | some y =>
          simp only [aliasOf, hy, Option.getD_some]
          exact settled_ne hl hnd (h.domV x y hy).2
      simp only [hne, hx, if_false]
      exact h.V x
  · intro y c hc
    obtain ⟨hy, hrefs⟩ := h.domR y c hc
    have hyl : y ≠ l := fun e => hnd (e ▸ hy)
    rw [evalExpr_congr we _ env c (fun z hz => by
      simp [settled_ne hl hnd (hrefs z hz)])]
    simp only [hyl, if_false]
    exact h.R y c hc
  · intro x y hxy
    obtain ⟨a, b⟩ := h.domS x y hxy
    exact ⟨List.mem_cons_of_mem _ a, List.mem_cons_of_mem _ b⟩
  · intro x y hxy
    obtain ⟨a, b⟩ := h.domV x y hxy
    exact ⟨List.mem_cons_of_mem _ a, settled_mono b⟩
  · intro y c hc
    obtain ⟨a, b⟩ := h.domR y c hc
    exact ⟨List.mem_cons_of_mem _ a, fun z hz => settled_mono (b z hz)⟩

theorem CheckInv.addR {we : WEnv} {allLhs : List String} {st : MergeCheck} {env : Env}
    (h : CheckInv we allLhs st env) {l : String} {c : Sparkle.IR.AST.Expr}
    (hc : evalExpr we env c = some (env l)) (hl : l ∈ st.defined)
    (hrefs : ∀ z ∈ refsOf c, Settled allLhs st.defined z) :
    CheckInv we allLhs { st with R := (l, c) :: st.R } env := by
  refine ⟨h.S, h.V, ?_, h.domS, h.domV, ?_⟩
  · intro y c' hy
    simp only [lookup_cons_eq] at hy
    split at hy
    · rename_i e; cases hy; subst e; exact hc
    · exact h.R y c' hy
  · intro y c' hy
    simp only [lookup_cons_eq] at hy
    split at hy
    · rename_i e; cases hy; subst e; exact ⟨hl, hrefs⟩
    · exact h.domR y c' hy

theorem CheckInv.addV {we : WEnv} {allLhs : List String} {st : MergeCheck} {env : Env}
    (h : CheckInv we allLhs st env) {l t : String}
    (ht : env t = env l ∧ we t = we l) (hl : l ∈ st.defined) (hts : Settled allLhs st.defined t) :
    CheckInv we allLhs { st with V := (l, t) :: st.V } env := by
  refine ⟨h.S, ?_, h.R, h.domS, ?_, h.domR⟩
  · intro x
    rw [aliasOf_cons]
    split
    · rename_i e; subst e; exact ht
    · exact h.V x
  · intro x y hy
    simp only [lookup_cons_eq] at hy
    split at hy
    · rename_i e; cases hy; subst e; exact ⟨hl, hts⟩
    · exact h.domV x y hy

theorem CheckInv.addS {we : WEnv} {allLhs : List String} {st : MergeCheck} {env : Env}
    (h : CheckInv we allLhs st env) {l y : String}
    (hy : env y = env l ∧ we y = we l) (hl : l ∈ st.defined) (hyd : y ∈ st.defined) :
    CheckInv we allLhs { st with S := (l, y) :: st.S } env := by
  refine ⟨?_, h.V, h.R, ?_, h.domV, h.domR⟩
  · intro x
    rw [aliasOf_cons]
    split
    · rename_i e; subst e; exact hy
    · exact h.S x
  · intro x y' hy'
    simp only [lookup_cons_eq] at hy'
    split at hy'
    · rename_i e; cases hy'; subst e; exact ⟨hl, hyd⟩
    · exact h.domS x y' hy'

/-- One statement: the new statement assigns the same name the same value, and
the invariant moves to the next environment. -/
theorem validateStep_sound {wOf : String → Nat} {we : WEnv} {allLhs : List String}
    {st st' : MergeCheck} {env : Env} {l : String} {e : Sparkle.IR.AST.Expr}
    {new : Stmt} {v : Nat}
    (hwe : ∀ x, we x = wOf x) (hstep : validateStep wOf allLhs st (.assign l e) new = some st')
    (hinv : CheckInv we allLhs st env) (hl : l ∈ allLhs) (hev : evalExpr we env e = some v) :
    ∃ e', new = .assign l e' ∧ evalExpr we env e' = some v ∧
      CheckInv we allLhs st' (fun n => if n = l then v else env n) := by
  cases new with
  | assign l' e' =>
    simp only [validateStep] at hstep
    by_cases h1 : (l' ≠ l ∨ l ∈ st.defined)
    · rw [if_pos h1] at hstep; cases hstep
    rw [if_neg h1] at hstep
    have hl' : l = l' := Classical.byContradiction fun hne => h1 (Or.inl (Ne.symm hne))
    have hnd : l ∉ st.defined := fun hm => h1 (Or.inr hm)
    subst hl'
    by_cases h2 : (!(refsOf e).all (fun x => !allLhs.contains x || st.defined.contains x)) = true
    · rw [if_pos h2] at hstep; cases hstep
    rw [if_neg h2] at hstep
    have hall : ∀ x ∈ refsOf e, x ∈ allLhs → x ∈ st.defined := by simpa using h2
    have htopo : ∀ x ∈ refsOf e, Settled allLhs st.defined x := by
      intro x hx
      by_cases hxa : x ∈ allLhs
      · exact Or.inl (hall x hx hxa)
      · exact Or.inr hxa
    have base := hinv.update hl hnd v
    have hvl : (fun n => if n = l then v else env n) l = v := by simp
    -- the canonical right-hand side under the value aliases evaluates like `e`
    have hcV : evalExpr we env (renameE (aliasOf st.V) e) = some v := by
      rw [(renameE_sound we env _ hinv.V e).2]; exact hev
    have hcVrefs : ∀ z ∈ refsOf (renameE (aliasOf st.V) e), Settled allLhs st.defined z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := refs_renameE _ e z hz
      exact settled_aliasOf hinv.domV (htopo x hx)
    have hcV' : evalExpr we (fun n => if n = l then v else env n) (renameE (aliasOf st.V) e) =
        some v := by
      rw [evalExpr_congr we _ env _ (fun z hz => by
        simp [settled_ne hl hnd (hcVrefs z hz)])]
      exact hcV
    by_cases h3 : e' = renameE (aliasOf st.S) e
    · rw [if_pos h3] at hstep
      cases hstep
      refine ⟨_, rfl, by rw [h3, (renameE_sound we env _ hinv.S e).2]; exact hev, ?_⟩
      have withR := base.addR (l := l) (c := renameE (aliasOf st.V) e) (by simp only [if_true]; exact hcV')
        (List.mem_cons_self) (fun z hz => settled_mono (hcVrefs z hz))
      cases e with
      | ref x =>
        simp only
        by_cases h4 : (x ≠ l ∧ wOf l = wOf x)
        · rw [if_pos h4]
          have hxs : Settled allLhs st.defined x := htopo x (by simp [refsOf])
          have hts := settled_aliasOf hinv.domV hxs
          have htl : aliasOf st.V x ≠ l := settled_ne hl hnd hts
          have hvx : v = env x := by simp [evalExpr] at hev; exact hev.symm
          refine withR.addV ⟨?_, ?_⟩ List.mem_cons_self (settled_mono hts)
          · simp only [htl, if_false, if_true, hvx]; exact (hinv.V x).1
          · rw [(hinv.V x).2, hwe, hwe, h4.2]
        · rw [if_neg h4]; exact withR
      | _ => exact withR
    · rw [if_neg h3] at hstep
      cases e' with
      | ref y =>
        simp only at hstep
        split at hstep
        · rename_i hc
          obtain ⟨hyl, hyd, -, hR, hw⟩ := hc
          cases hstep
          have hyd' : y ∈ st.defined := by simpa using hyd
          have hy := hinv.R y _ hR
          rw [hcV] at hy
          have hvy : v = env y := Option.some.inj hy
          refine ⟨_, rfl, by simp [evalExpr, hvy], ?_⟩
          have hys : Settled allLhs st.defined y := Or.inl hyd'
          have hts := settled_aliasOf hinv.domV hys
          have htl : aliasOf st.V y ≠ l := settled_ne hl hnd hts
          have withS := base.addS (l := l) (y := y)
            ⟨by simp [hyl, hvy], by rw [hwe, hwe, hw]⟩ List.mem_cons_self
            (List.mem_cons_of_mem _ hyd')
          exact withS.addV ⟨by simp [htl, hvy, (hinv.V y).1], by rw [(hinv.V y).2, hwe, hwe, hw]⟩
            List.mem_cons_self (settled_mono hts)
        · cases hstep
      | _ => simp at hstep
  | _ => simp [validateStep] at hstep

theorem validateMerge_go_sound {wOf : String → Nat} {we : WEnv} {mems : MEnv}
    {allLhs : List String} (hwe : ∀ x, we x = wOf x) :
    ∀ (old new : List Stmt) (st : MergeCheck) (env envF : Env),
      validateMerge.go wOf allLhs st old new = true → CheckInv we allLhs st env →
      (∀ s ∈ old, ∃ l e, s = .assign l e ∧ l ∈ allLhs) →
      evalAssigns we mems old env = some envF → evalAssigns we mems new env = some envF
  | [], [], _, _, _, _, _, _, h => h
  | [], _ :: _, _, _, _, hgo, _, _, _ => by simp [validateMerge.go] at hgo
  | _ :: _, [], _, _, _, hgo, _, _, _ => by simp [validateMerge.go] at hgo
  | a :: as, b :: bs, st, env, envF, hgo, hinv, hass, hev => by
    obtain ⟨l, e, rfl, hl⟩ := hass a List.mem_cons_self
    simp only [validateMerge.go] at hgo
    split at hgo
    · rename_i st' hstep
      simp only [evalAssigns] at hev
      cases hv : evalExpr we env e with
      | none => rw [hv] at hev; cases hev
      | some v =>
        rw [hv] at hev
        simp only [Option.bind_eq_bind, Option.bind_some] at hev
        obtain ⟨e', rfl, he', hinv'⟩ := validateStep_sound hwe hstep hinv hl hv
        simp only [evalAssigns, he', Option.bind_eq_bind, Option.bind_some]
        exact validateMerge_go_sound hwe as bs st' _ envF hgo hinv'
          (fun s hs => hass s (List.mem_cons_of_mem _ hs)) hev
    · cases hgo

/-- **The merge checker is sound.** If `validateMerge` accepts `new` for the
combinational body `old` under declared widths `wOf`, `new` evaluates to the
SAME environment as `old`. -/
theorem validateMerge_sound {wOf : String → Nat} {we : WEnv} {mems : MEnv}
    {old new : List Stmt} {init env : Env} (hwe : ∀ x, we x = wOf x)
    (hall : old.all isAssign = true) (hv : validateMerge wOf old new = true)
    (hev : evalAssigns we mems old init = some env) :
    evalAssigns we mems new init = some env := by
  unfold validateMerge at hv
  refine validateMerge_go_sound hwe old new {} init env hv ?_ ?_ hev
  · refine ⟨fun x => ?_, fun x => ?_, fun y c h => ?_, fun x y h => ?_, fun x y h => ?_,
      fun y c h => ?_⟩ <;> simp_all [aliasOf]
  · intro s hs
    have := List.all_eq_true.mp hall s hs
    cases s with
    | assign l e =>
      exact ⟨l, e, rfl, List.mem_filterMap.mpr ⟨.assign l e, hs, rfl⟩⟩
    | _ => simp [isAssign] at this

/-- **`mergeDuplicates` on a combinational module:** its statement list
evaluates to the SAME environment under the declared widths, and the wires and
ports are unchanged. The `assertions` it rewrites are not covered. -/
theorem mergeDuplicates_sound (m : Sparkle.IR.AST.Module) (mems : MEnv) (init env : Env)
    (hall : m.body.all isAssign = true)
    (hev : evalAssigns (weOf m) mems m.body init = some env) :
    evalAssigns (weOf (mergeDuplicates m)) mems (mergeDuplicates m).body init = some env ∧
    (mergeDuplicates m).wires = m.wires ∧ (mergeDuplicates m).inputs = m.inputs ∧
    (mergeDuplicates m).outputs = m.outputs := by
  unfold mergeDuplicates
  simp only [hall, if_true]
  split
  · rename_i hv
    refine ⟨?_, rfl, rfl, rfl⟩
    exact validateMerge_sound (wOf := declWidth m) (fun _ => rfl) hall hv hev
  · exact ⟨hev, rfl, rfl, rfl⟩

/-! ## 3. `dropZeroWidthModule` on the entry's modules -/

/-- The width-map fold misses names it never saw. -/
theorem wmFold_notin (ports : List Port) :
    ∀ (acc : Sparkle.IR.Optimize.WidthMap) (x : String), x ∉ ports.map (·.name) →
      (ports.foldl (fun acc p => acc.insert p.name p.ty.bitWidth) acc).get? x = acc.get? x := by
  induction ports with
  | nil => intro acc x _; rfl
  | cons q rest ih =>
    intro acc x hx
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    simp only [List.foldl_cons]
    rw [ih _ x hx.2, Std.HashMap.get?_insert]
    simp [Ne.symm hx.1]

/-- ... and finds a name that occurs once. -/
theorem wmFold_mem (ports : List Port) :
    ∀ (acc : Sparkle.IR.Optimize.WidthMap) (p : Port), (ports.map (·.name)).Nodup → p ∈ ports →
      (ports.foldl (fun acc p => acc.insert p.name p.ty.bitWidth) acc).get? p.name =
        some p.ty.bitWidth := by
  induction ports with
  | nil => intro acc p _ hp; cases hp
  | cons q rest ih =>
    intro acc p hnd hp
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · rw [wmFold_notin rest _ _ hnd.1, Std.HashMap.get?_insert]; simp
    · exact ih _ p hnd.2 hp'

theorem filterMap_eq_self {α : Type} {f : α → Option α} :
    ∀ (l : List α), (∀ a ∈ l, f a = some a) → l.filterMap f = l
  | [], _ => rfl
  | a :: rest, h => by
    simp only [List.filterMap_cons, h a List.mem_cons_self]
    rw [filterMap_eq_self rest (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem find?_filter_nodup (Q : Port → Bool) :
    ∀ (l : List Port), (l.map (·.name)).Nodup → ∀ x,
      (l.filter Q).find? (fun p => p.name == x) =
        match l.find? (fun p => p.name == x) with
        | some p => if Q p then some p else none
        | none => none
  | [], _, _ => rfl
  | q :: rest, hnd, x => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases hq : q.name = x
    · have hnone : (rest.filter Q).find? (fun p => p.name == x) = none := by
        rw [List.find?_eq_none]
        intro a ha
        have ha' := (List.mem_filter.mp ha).1
        intro hax
        have : a.name = x := by simpa using hax
        exact hnd.1 (hq ▸ this ▸ List.mem_map_of_mem ha')
      simp only [List.find?_cons, hq, beq_self_eq_true, List.filter_cons]
      by_cases hQ : Q q = true
      · simp [hQ, hq]
      · simp [hQ, hnone]
    · have hb : (q.name == x) = false := beq_false_of_ne hq
      simp only [List.filter_cons, List.find?_cons, hb]
      rw [← find?_filter_nodup Q rest hnd.2 x]
      by_cases hQ : Q q = true <;> simp [hQ, List.find?_cons, hb]

/-- Dropping width-0 wire declarations does not change the widths read off. -/
theorem weOf_dropWires (M : Sparkle.IR.AST.Module) (hnd : (M.wires.map (·.name)).Nodup) :
    weOf { M with wires := M.wires.filter (fun p => p.ty.bitWidth != 0) } = weOf M := by
  funext x
  simp only [weOf]
  rw [find?_filter_nodup _ M.wires hnd x]
  cases hf : M.wires.find? (fun p => p.name == x) with
  | none => rfl
  | some p =>
    simp only
    by_cases hQ : (p.ty.bitWidth != 0) = true
    · simp [hQ]
    · simp only [hQ, if_false]
      have h0 : p.ty.bitWidth = 0 := by simpa using hQ
      obtain ⟨pn, pty⟩ := p
      cases pty <;> simp_all [HWType.bitWidth]

theorem dzExpr_shaped (wm : Sparkle.IR.Optimize.WidthMap) (r : Sparkle.IR.AST.Expr)
    (hr : ShapedRhs r ∨ ∃ w, r = .ref w) : dzExpr wm r = r := by
  rcases hr with hr | ⟨w, rfl⟩
  · unfold ShapedRhs at hr
    match r, hr with
    | .const _ _, _ => simp [dzExpr]
    | .ref _, _ => simp [dzExpr]
    | .op _ [.ref _, .ref _], _ => simp [dzExpr, dzList]
  · simp [dzExpr]

/-- **`dropZeroWidthModule` on the entry's modules.** For a module with the
entry's shape (`PostReady`, read off its construction) at a nonzero width, the
pass changes no statement and no width it can read. -/
theorem dropZeroWidth_entry (M : Sparkle.IR.AST.Module) (n : Nat) (hn : 0 < n)
    (hpr : PostReady M n) :
    (dropZeroWidthModule M).body = M.body ∧ weOf (dropZeroWidthModule M) = weOf M ∧
    (dropZeroWidthModule M).inputs = M.inputs ∧ (dropZeroWidthModule M).outputs = M.outputs ∧
    ((dropZeroWidthModule M).wires.map (·.name)).Nodup := by
  obtain ⟨hnd, hout, hbody, houts, _⟩ := hpr
  unfold dropZeroWidthModule
  split
  · exact ⟨rfl, rfl, rfl, rfl, hnd⟩
  · refine ⟨?_, weOf_dropWires M hnd, rfl, rfl, ?_⟩
    · apply filterMap_eq_self
      intro st hst
      obtain ⟨l, r, rfl, hlr⟩ := hbody st hst
      have hwm : (Sparkle.IR.Optimize.buildWidthMap M).get? l = some n := by
        simp only [Sparkle.IR.Optimize.buildWidthMap]
        rcases hlr with ⟨_, hl⟩ | ⟨rfl, _⟩
        · exact wmFold_mem M.wires _ ⟨l, .bitVector n⟩ hnd hl
        · rw [wmFold_notin M.wires _ _ hout, houts hn]
          simp [Std.HashMap.get?_insert, HWType.bitWidth]
      have hdz : dzExpr (Sparkle.IR.Optimize.buildWidthMap M) r = r :=
        dzExpr_shaped _ r (by rcases hlr with ⟨h, _⟩ | ⟨_, h⟩ <;> simp_all)
      simp only [dzStmt, hwm]
      split
      · rename_i h; cases h; omega
      · rw [hdz]
    · exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) hnd

/-! ## 4. Both passes, in the order `synthesizeCombinational` runs them -/

/-- After `dropZeroWidthModule`, then optionally `mergeDuplicates` (skipped when
`SPARKLE_NO_REGDEDUP` is set), the module evaluates to the SAME environment
under its own declared widths, with the same ports. -/
theorem postprocess_sound {M M' : Sparkle.IR.AST.Module} {n : Nat} (hn : 0 < n)
    (hpr : PostReady M n)
    (hM' : M' = dropZeroWidthModule M ∨ M' = mergeDuplicates (dropZeroWidthModule M))
    {mems : MEnv} {init env : Env}
    (hev : evalAssigns (weOf M) mems M.body init = some env) :
    evalAssigns (weOf M') mems M'.body init = some env ∧ M'.inputs = M.inputs ∧
      M'.outputs = M.outputs := by
  obtain ⟨hb, hw, hi, ho, -⟩ := dropZeroWidth_entry M n hn hpr
  have hdz : evalAssigns (weOf (dropZeroWidthModule M)) mems (dropZeroWidthModule M).body init =
      some env := by rw [hb, hw]; exact hev
  rcases hM' with rfl | rfl
  · exact ⟨hdz, hi, ho⟩
  · have hall : (dropZeroWidthModule M).body.all isAssign = true := by
      rw [hb, List.all_eq_true]
      intro st hst
      obtain ⟨l, r, rfl, -⟩ := hpr.2.2.1 st hst
      rfl
    obtain ⟨hev', -, hi', ho'⟩ := mergeDuplicates_sound _ mems init env hall hdz
    exact ⟨hev', hi'.trans hi, ho'.trans ho⟩

theorem RunsTo.pure {α : Type} {a b : α} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') : b = a := by
  unfold RunsTo at h
  change EST.Out.ok a w = _ at h
  cases h; rfl

/-- `synthesizeCombinational` runs the entry in the SAME contexts and state
references, then the two passes (the second only when the environment variable
is unset). -/
theorem synthesizeCombinational_reads {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      (M' = dropZeroWidthModule M ∨ M' = mergeDuplicates (dropZeroWidthModule M)) := by
  unfold synthesizeCombinational synthesizeCombinationalWith at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  rcases RunsTo.ite h with h | h
  · have := RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inl this.1
  · have := RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inr this.1

/-- **`#synthesizeVerilog`'s IR, for the fragment.** A successful run of
`synthesizeCombinational` (entry, zero-width cleanup, merge) for a declaration
that the run's environment defines as `quoteDecl dn names n fe` (`n > 0`):
distinct input ports, and for every domain, all input signals and every cycle,
the RETURNED module drives `out` with the Lean meaning. -/
theorem synthesizeCombinational_fragment {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    ∃ port : Nat → Option String,
      (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
      (∀ j, j < names.length → ∃ w, port j = some w) ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) (mems : MEnv)
        (initial : Env),
        (∀ j w, j < names.length → port j = some w → initial w = ((sigs j).val t).toNat) →
        ∃ env, evalAssigns (weOf M') mems M'.body initial = some env ∧
          env "out" = ((denoteFE n sigs fe).val t).toNat := by
  obtain ⟨M, D, w1, hcore, hM'⟩ := synthesizeCombinational_reads h
  obtain ⟨port, hdist, hex, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  refine ⟨port, hdist, hex, fun sigs t mems initial hinit => ?_⟩
  obtain ⟨env, hev, hout, hpr, -, -, -⟩ := hsem sigs t mems initial hinit
  obtain ⟨hev', -, -⟩ := postprocess_sound hn hpr hM' hev
  exact ⟨env, hev', hout⟩

/-! ## 5. Through the optimizer: the module `toVerilog` prints

`#synthesizeVerilog` prints `verilogOf M' = toVerilog (checkedOptimize M')`.
`checkedOptimize` keeps `optimizeModule`'s result only if the proved checker
accepts it; its precondition is that the body has the simple shape, which is
carried from the translator through both passes. -/

open Sparkle.IR.OptCheck (simpleRhs simpleBody checkedOptimize)

theorem simpleRhs_renameE (σ : String → String) :
    ∀ e, simpleRhs e = true → simpleRhs (renameE σ e) = true
  | .const _ _, _ => rfl
  | .ref _, _ => rfl
  | .op _ [.ref _, .ref _], h => by simpa [renameE, renameE.renameL, simpleRhs] using h

theorem validateStep_shape {wOf : String → Nat} {allLhs : List String} {st st' : MergeCheck}
    {l : String} {e : Sparkle.IR.AST.Expr} {new : Stmt}
    (h : validateStep wOf allLhs st (.assign l e) new = some st') :
    ∃ e', new = .assign l e' ∧ (e' = renameE (aliasOf st.S) e ∨ ∃ y, e' = .ref y) := by
  cases new with
  | assign l' e' =>
    simp only [validateStep] at h
    by_cases h1 : (l' ≠ l ∨ l ∈ st.defined)
    · rw [if_pos h1] at h; cases h
    rw [if_neg h1] at h
    have hl' : l = l' := Classical.byContradiction fun hne => h1 (Or.inl (Ne.symm hne))
    subst hl'
    by_cases h2 : (!(refsOf e).all (fun x => !allLhs.contains x || st.defined.contains x)) = true
    · rw [if_pos h2] at h; cases h
    rw [if_neg h2] at h
    by_cases h3 : e' = renameE (aliasOf st.S) e
    · exact ⟨e', rfl, Or.inl h3⟩
    · rw [if_neg h3] at h
      cases e' with
      | ref y => exact ⟨_, rfl, Or.inr ⟨y, rfl⟩⟩
      | _ => simp at h
  | _ => simp [validateStep] at h

/-- All statements are assigns of the simple shapes. -/
def SimpleStmts (body : List Stmt) : Prop :=
  ∀ st ∈ body, ∃ l r, st = .assign l r ∧ simpleRhs r = true

theorem simpleBody_of (m : Sparkle.IR.AST.Module) (h : SimpleStmts m.body) :
    simpleBody m = true := by
  unfold simpleBody
  rw [List.all_eq_true]
  intro st hst
  obtain ⟨l, r, rfl, hr⟩ := h st hst
  exact hr

theorem validateMerge_go_simple {wOf : String → Nat} {allLhs : List String} :
    ∀ (old new : List Stmt) (st : MergeCheck),
      validateMerge.go wOf allLhs st old new = true → SimpleStmts old → SimpleStmts new
  | [], [], _, _, _ => fun _ h => by cases h
  | [], _ :: _, _, hgo, _ => by simp [validateMerge.go] at hgo
  | _ :: _, [], _, hgo, _ => by simp [validateMerge.go] at hgo
  | a :: as, b :: bs, st, hgo, hs => by
    obtain ⟨l, e, rfl, he⟩ := hs a List.mem_cons_self
    simp only [validateMerge.go] at hgo
    split at hgo
    · rename_i st' hstep
      obtain ⟨e', rfl, h'⟩ := validateStep_shape hstep
      have hrest := validateMerge_go_simple as bs st' hgo
        (fun s hs' => hs s (List.mem_cons_of_mem _ hs'))
      intro s hs'
      rcases List.mem_cons.mp hs' with rfl | hs'
      · refine ⟨l, e', rfl, ?_⟩
        rcases h' with rfl | ⟨y, rfl⟩
        · exact simpleRhs_renameE _ e he
        · rfl
      · exact hrest s hs'
    · cases hgo

theorem mergeDuplicates_simple (m : Sparkle.IR.AST.Module) (h : SimpleStmts m.body) :
    SimpleStmts (mergeDuplicates m).body := by
  have hall : m.body.all isAssign = true := by
    rw [List.all_eq_true]; intro st hst
    obtain ⟨l, r, rfl, -⟩ := h st hst; rfl
  unfold mergeDuplicates
  simp only [hall, if_true]
  split
  · rename_i hv
    exact validateMerge_go_simple m.body _ {} hv h
  · exact h

/-- A name declared once at width `k` has declared width `k`. -/
theorem declWidth_of_mem {m : Sparkle.IR.AST.Module} (hnd : (m.wires.map (·.name)).Nodup)
    {x : String} {k : Nat} (hx : ({ name := x, ty := .bitVector k } : Port) ∈ m.wires) :
    Sparkle.IR.RegDedup.declWidth m x = k := by
  unfold Sparkle.IR.RegDedup.declWidth
  rw [find?_of_nodup hnd hx]

/-- The post-processed module keeps the simple shape, the ports, the width-`n`
declarations and distinct wire names. -/
theorem postprocess_facts {M M' : Sparkle.IR.AST.Module} {n : Nat} (hn : 0 < n)
    (hpr : PostReady M n)
    (hM' : M' = dropZeroWidthModule M ∨ M' = mergeDuplicates (dropZeroWidthModule M)) :
    SimpleStmts M'.body ∧ M'.inputs = M.inputs ∧ (M'.wires.map (·.name)).Nodup ∧
      ∀ x, ({ name := x, ty := .bitVector n } : Port) ∈ M.wires →
        ({ name := x, ty := .bitVector n } : Port) ∈ M'.wires := by
  obtain ⟨hb, -, hi, -, hnd⟩ := dropZeroWidth_entry M n hn hpr
  have hsM : SimpleStmts (dropZeroWidthModule M).body := by
    rw [hb]
    intro st hst
    obtain ⟨l, r, rfl, hlr⟩ := hpr.2.2.1 st hst
    rcases hlr with ⟨hr, -⟩ | ⟨-, w, rfl⟩
    · exact ⟨l, r, rfl, hr⟩
    · exact ⟨l, _, rfl, rfl⟩
  have hwdz : ∀ x, ({ name := x, ty := .bitVector n } : Port) ∈ M.wires →
      ({ name := x, ty := .bitVector n } : Port) ∈ (dropZeroWidthModule M).wires := by
    intro x hx
    unfold dropZeroWidthModule
    split
    · exact hx
    · exact List.mem_filter.mpr ⟨hx, by simp [HWType.bitWidth]; omega⟩
  rcases hM' with rfl | rfl
  · exact ⟨hsM, hi, hnd, hwdz⟩
  · have hall : (dropZeroWidthModule M).body.all isAssign = true := by
      rw [List.all_eq_true]; intro st hst
      obtain ⟨l, r, rfl, -⟩ := hsM st hst; rfl
    have hwi : (mergeDuplicates (dropZeroWidthModule M)).wires = (dropZeroWidthModule M).wires ∧
        (mergeDuplicates (dropZeroWidthModule M)).inputs = (dropZeroWidthModule M).inputs := by
      unfold mergeDuplicates
      simp only [hall, if_true]
      split <;> exact ⟨rfl, rfl⟩
    refine ⟨mergeDuplicates_simple _ hsM, hwi.2.trans hi, by rw [hwi.1]; exact hnd,
      fun x hx => by rw [hwi.1]; exact hwdz x hx⟩

/-- **The module `#synthesizeVerilog` prints, for the fragment.** For a
successful run of `synthesizeCombinational` on a declaration that the run's
environment defines as `quoteDecl dn names n fe` (`n > 0`), the module
`checkedOptimize M'` — the one `verilogOf M' = toVerilog (checkedOptimize M')`
prints — has a distinct input port per input and, for every domain, all input
signals and every cycle, its statements under its declared widths drive `out`
with the Lean meaning. -/
theorem printedModule_fragment {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    ∃ port : Nat → Option String,
      (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
      (∀ j, j < names.length → ∃ w, port j = some w ∧
        w ∈ (checkedOptimize M').inputs.map (·.name)) ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) (mems : MEnv)
        (initial : Env),
        (∀ j w, j < names.length → port j = some w → initial w = ((sigs j).val t).toNat) →
        ∃ env, evalAssigns (Sparkle.IR.RegDedup.declWidth (checkedOptimize M')) mems
            (checkedOptimize M').body initial = some env ∧
          env "out" = ((denoteFE n sigs fe).val t).toNat := by
  obtain ⟨M, D, w1, hcore, hM'⟩ := synthesizeCombinational_reads h
  obtain ⟨port, hdist, hex, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  -- the module's structure does not depend on the values: read it at one valuation
  obtain ⟨env0, hev0, -, hpr, -, hmo, hinM⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun j w _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  obtain ⟨-, hin', ho'⟩ := postprocess_sound hn hpr hM' hev0
  obtain ⟨hsimp, -, hnd', hdecl'⟩ := postprocess_facts hn hpr hM'
  have hgate : simpleBody M' = true := simpleBody_of M' hsimp
  obtain ⟨hinO, houtO'⟩ := Tools.ShippingOptSoundness.checkedOptimize_ports hgate
  refine ⟨port, hdist, ?_, fun sigs t mems initial hinit => ?_⟩
  · intro j hj
    obtain ⟨wj, hwj⟩ := hex j hj
    refine ⟨wj, hwj, ?_⟩
    rw [hinO, hin']
    exact List.mem_map.mpr ⟨_, hinM j wj hj hwj, rfl⟩
  · obtain ⟨env, hev, hout, hpr, hins, -, -⟩ := hsem sigs t mems initial hinit
    obtain ⟨hev', -, -⟩ := postprocess_sound hn hpr hM' hev
    have hinsM' : ∀ x ∈ M'.inputs.map (·.name),
        initial x < 2 ^ Sparkle.IR.RegDedup.declWidth M' x := by
      intro x hx
      rw [hin'] at hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, hj, hpj, hty, hdecl⟩ := hins p hp
      rw [declWidth_of_mem hnd' (hdecl' _ hdecl), hinit j p.name hj hpj]
      exact BitVec.isLt _
    obtain ⟨envO, hevO, houtO, -, -⟩ :=
      Tools.ShippingOptSoundness.checkedOptimize_sound hgate hinsM' hev'
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (ho' ▸ hmo)
    refine ⟨envO, hevO, ?_⟩
    rw [← hpn, houtO p hp, hpn, hout]

/-! ## 6. Uniform expression widths survive the checked merge

`out` is a port, not an internal wire, so `weOf M "out"` is zero.
The exceptional target must therefore remain explicit: an accepted alias has
equal target widths and names an earlier, different target. Two exceptional
targets cannot be different, which rules out losing the RHS width at `out`. -/

theorem sized_rename {we : WEnv} {e : Sparkle.IR.AST.Expr} {n : Nat}
    (h : SizedExpr we e n) (σ : String → String) (hw : ∀ x, we (σ x) = we x) :
    SizedExpr we (renameE σ e) n := by
  induction h with
  | ref x => simpa only [renameE, ← hw x] using SizedExpr.ref (we := we) (σ x)
  | const v n => exact .const v n
  | bin op _ _ ih₁ ih₂ =>
    simpa only [renameE, renameE.renameL] using SizedExpr.bin op ih₁ ih₂

/-- Uniform RHS widths, allowing the single output port as an exceptional
target in the wire-only width environment. -/
def UniformStmts (we : WEnv) (n : Nat) (body : List Stmt) : Prop :=
  ∀ s ∈ body, ∃ l e, s = .assign l e ∧ SizedExpr we e n ∧ (we l = n ∨ l = "out")

theorem validateStep_sized {we : WEnv} {n : Nat} {allLhs : List String}
    {st st' : MergeCheck} {l : String} {e : Sparkle.IR.AST.Expr} {new : Stmt}
    (h : validateStep we allLhs st (.assign l e) new = some st')
    (hs : SizedExpr we e n) (hl : we l = n ∨ l = "out")
    (hS : ∀ x, we (aliasOf st.S x) = we x)
    (hd : ∀ x ∈ st.defined, we x = n ∨ x = "out") :
    (∃ e', new = .assign l e' ∧ SizedExpr we e' n) ∧
    (∀ x, we (aliasOf st'.S x) = we x) ∧
    (∀ x ∈ st'.defined, we x = n ∨ x = "out") := by
  cases new with
  | assign l' e' =>
    simp only [validateStep] at h
    by_cases h1 : l' ≠ l ∨ l ∈ st.defined
    · rw [if_pos h1] at h; cases h
    rw [if_neg h1] at h
    have heq : l = l' := Classical.byContradiction fun hne => h1 (Or.inl (Ne.symm hne))
    subst heq
    by_cases h2 : (!(refsOf e).all (fun x => !allLhs.contains x || st.defined.contains x)) = true
    · rw [if_pos h2] at h; cases h
    rw [if_neg h2] at h
    have hd' : ∀ x ∈ l :: st.defined, we x = n ∨ x = "out" := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hl
      · exact hd x hx
    by_cases h3 : e' = renameE (aliasOf st.S) e
    · rw [if_pos h3] at h
      cases h
      exact ⟨⟨_, rfl, h3 ▸ sized_rename hs _ hS⟩, hS, hd'⟩
    · rw [if_neg h3] at h
      cases e' with
      | ref y =>
        simp only at h
        split at h
        · rename_i hc
          obtain ⟨hne, hyd, _, _, hwy⟩ := hc
          cases h
          have hyd' : y ∈ st.defined := by simpa using hyd
          have hyn : we y = n := by
            rcases hl with hl | hl
            · exact hwy.symm.trans hl
            · rcases hd y hyd' with hy | hy
              · exact hy
              · exact False.elim (hne (hy.trans hl.symm))
          refine ⟨⟨_, rfl, ?_⟩, ?_, hd'⟩
          · simpa only [hyn] using SizedExpr.ref (we := we) y
          · intro x
            rw [aliasOf_cons]
            split
            · rename_i hx; subst x; exact hwy.symm
            · exact hS x
        · cases h
      | _ => simp at h
  | _ => simp [validateStep] at h

theorem validateMerge_go_sized {we : WEnv} {n : Nat} {allLhs : List String} :
    ∀ (old new : List Stmt) (st : MergeCheck),
      validateMerge.go we allLhs st old new = true → UniformStmts we n old →
      (∀ x, we (aliasOf st.S x) = we x) →
      (∀ x ∈ st.defined, we x = n ∨ x = "out") → UniformStmts we n new
  | [], [], _, _, _, _, _ => fun _ h => by cases h
  | [], _ :: _, _, h, _, _, _ => by simp [validateMerge.go] at h
  | _ :: _, [], _, h, _, _, _ => by simp [validateMerge.go] at h
  | a :: as, b :: bs, st, h, hs, hS, hd => by
    obtain ⟨l, e, rfl, he, hl⟩ := hs a List.mem_cons_self
    simp only [validateMerge.go] at h
    split at h
    · rename_i st' hstep
      obtain ⟨⟨e', rfl, he'⟩, hS', hd'⟩ := validateStep_sized hstep he hl hS hd
      have ht := validateMerge_go_sized as bs st' h
        (fun s hm => hs s (List.mem_cons_of_mem _ hm)) hS' hd'
      intro s hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨l, e', rfl, he', hl⟩
      · exact ht s hm
    · cases h

theorem validateMerge_sized {we : WEnv} {n : Nat} {old new : List Stmt}
    (h : validateMerge we old new = true) (hs : UniformStmts we n old) :
    UniformStmts we n new :=
  validateMerge_go_sized old new {} h hs (fun _ => rfl) (fun _ hm => by cases hm)

theorem mergeDuplicates_sized {m : Sparkle.IR.AST.Module} {n : Nat}
    (hs : UniformStmts (weOf m) n m.body) :
    UniformStmts (weOf (mergeDuplicates m)) n (mergeDuplicates m).body := by
  have hall : m.body.all isAssign = true := by
    rw [List.all_eq_true]
    intro s hm
    obtain ⟨l, e, rfl, _, _⟩ := hs s hm
    rfl
  unfold mergeDuplicates
  simp only [hall, if_true]
  split
  · rename_i hv
    exact validateMerge_sized hv hs
  · exact hs

theorem postprocess_sized {m m' : Sparkle.IR.AST.Module} {n : Nat}
    (hn : 0 < n) (hpr : PostReady m n)
    (hm : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    UniformStmts (weOf m') n m'.body := by
  obtain ⟨hb, hw, _, _, _⟩ := dropZeroWidth_entry m n hn hpr
  have hs : UniformStmts (weOf (dropZeroWidthModule m)) n (dropZeroWidthModule m).body := by
    rw [hb, hw]
    intro s hm
    obtain ⟨l, e, rfl, hshape⟩ := hpr.2.2.1 s hm
    refine ⟨l, e, rfl, hpr.2.2.2.2.2 l e hm, ?_⟩
    rcases hshape with ⟨_, hl⟩ | ⟨hl, _⟩
    · exact Or.inl (declWidth_of_mem hpr.1 hl)
    · exact Or.inr hl
  rcases hm with rfl | rfl
  · exact hs
  · exact mergeDuplicates_sized hs

theorem postprocess_wires_subset {m m' : Sparkle.IR.AST.Module} {n : Nat}
    (hn : 0 < n) (hpr : PostReady m n)
    (hm : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    ∀ p ∈ m'.wires, p ∈ m.wires := by
  have hdz : ∀ p ∈ (dropZeroWidthModule m).wires, p ∈ m.wires := by
    unfold dropZeroWidthModule
    split
    · exact fun _ hp => hp
    · exact fun _ hp => (List.mem_filter.mp hp).1
  rcases hm with rfl | rfl
  · exact hdz
  · have hu := postprocess_sized hn hpr (Or.inl rfl)
    have hall : (dropZeroWidthModule m).body.all isAssign = true := by
      rw [List.all_eq_true]
      intro s hs
      obtain ⟨l, e, rfl, _, _⟩ := hu s hs
      rfl
    unfold mergeDuplicates
    simp only [hall, if_true]
    split <;> exact hdz

/-- Widths of every RHS at the actual synthesis entry, after both cleanup
passes. No checker or sizing hypothesis is supplied by the caller. This is
before `checkedOptimize`, which may introduce mixed-width expressions. -/
theorem synthesizeCombinational_sized {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    UniformStmts (weOf m) n m.body := by
  obtain ⟨m0, d0, w1, hcore, hm⟩ := synthesizeCombinational_reads h
  obtain ⟨_, _, _, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  obtain ⟨_, _, _, hpr, _, _, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  exact postprocess_sized hn hpr hm

end Tools.ShippingPostSoundness
