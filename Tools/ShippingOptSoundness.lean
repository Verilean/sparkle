import Sparkle.IR.OptCheck
import Tools.ConeFoldSlices

/-! # The optimizer result check is sound

`Sparkle.IR.OptCheck.checkedOptimize` keeps `optimizeModule`'s result on a
module the check understands only if `optCheck` accepts it. This file proves
that an accepted result computes the same outputs, under the widths each module
declares, for every input assignment whose values fit their declared widths. -/

namespace Tools.ShippingOptSoundness

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck
open Sparkle.IR.Reorder (refsOf evalExpr_congr)

/-! ## 1. The normal-form grammar -/

inductive Shape : Expr → Prop
  | const {v : Int} {w : Nat} : 0 ≤ v → v < ((2 ^ w : Nat) : Int) → Shape (.const v w)
  | ref (x : String) : Shape (.ref x)
  | bin {o : Operator} {a b : Expr} : isBinOp o = true → Shape a → Shape b →
      Shape (.op o [a, b])

theorem widthOf_bin (we : WEnv) {o : Operator} (a b : Expr) (h : isBinOp o = true) :
    widthOf we (.op o [a, b]) = max (widthOf we a) (widthOf we b) := by
  cases o <;> simp_all [isBinOp, widthOf]

theorem evalOp_bin_args (we : WEnv) {o : Operator} (h : isBinOp o = true)
    (args args' : List Expr) (vals : List Nat) (w : Nat) :
    evalOp we o args vals w = evalOp we o args' vals w := by
  rcases vals with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> cases o <;> simp_all [isBinOp, evalOp]

theorem evalOp_bin_lt (we : WEnv) {o : Operator} (h : isBinOp o = true)
    (args : List Expr) (va vb w r : Nat) (hr : evalOp we o args [va, vb] w = some r) :
    r < 2 ^ w := by
  cases o <;> simp_all [isBinOp, evalOp] <;> (subst hr; exact Nat.mod_lt _ (Nat.two_pow_pos w))

theorem evalConst_fit (we : WEnv) (env : Env) {v : Int} {w : Nat} (h0 : 0 ≤ v)
    (hlt : v < ((2 ^ w : Nat) : Int)) : evalExpr we env (.const v w) = some v.toNat := by
  have hv : v % ((2 ^ w : Nat) : Int) = v := Int.emod_eq_of_lt h0 hlt
  simp only [evalExpr, hv, Int.add_emod_right, mask]
  have : (v.toNat) < 2 ^ w := by omega
  simp [Int.emod_eq_of_lt h0 hlt, Nat.mod_eq_of_lt this]

theorem shape_eval (we : WEnv) (env : Env) :
    ∀ {e : Expr}, Shape e → ∃ v, evalExpr we env e = some v
  | _, .const h0 hlt => ⟨_, evalConst_fit we env h0 hlt⟩
  | _, .ref x => ⟨env x, rfl⟩
  | .op o [a, b], .bin ho ha hb => by
    obtain ⟨va, hva⟩ := shape_eval we env ha
    obtain ⟨vb, hvb⟩ := shape_eval we env hb
    simp only [evalExpr, evalList, hva, hvb, Option.bind_eq_bind, Option.bind_some]
    cases o <;> simp_all [isBinOp, evalOp]

/-- Values of normal forms fit their width when the references do. -/
theorem shape_bound (we : WEnv) (env : Env) :
    ∀ {e : Expr}, Shape e → (∀ x ∈ refsOf e, env x < 2 ^ we x) →
      ∀ v, evalExpr we env e = some v → v < 2 ^ widthOf we e
  | _, .const h0 hlt, _, v, hv => by
    rw [evalConst_fit we env h0 hlt] at hv
    cases hv; simp only [widthOf]; omega
  | _, .ref x, hr, v, hv => by
    simp only [evalExpr, Option.some.injEq] at hv
    subst hv; exact hr x (by simp [refsOf])
  | .op o [a, b], .bin ho ha hb, _, v, hv => by
    obtain ⟨va, hva⟩ := shape_eval we env ha
    obtain ⟨vb, hvb⟩ := shape_eval we env hb
    simp only [evalExpr, evalList, hva, hvb, Option.bind_eq_bind, Option.bind_some] at hv
    exact evalOp_bin_lt we ho _ va vb _ v hv

/-! ## 2. Normalisation preserves width and value -/

/-- What the definitions seen so far guarantee, in the current environment. -/
def DefsOk (we : WEnv) (init env : Env) (defs : List (String × Expr)) : Prop :=
  (∀ x d, defs.lookup x = some d → Shape d ∧ evalExpr we init d = some (env x)) ∧
  (∀ x, defs.lookup x = none → env x = init x)

theorem and_mask (va w : Nat) (h : va < 2 ^ w) : mask w (va &&& (2 ^ w - 1)) = va := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]
  simp [mask, Nat.mod_eq_of_lt h]

/-- The two outcomes of `normE`'s operator case. -/
theorem mask_match {we : WEnv} {ins : List String} {o : Operator} {a' b' e' : Expr}
    (h : (match o, b' with
      | .and, .const m w =>
        if m = ((2 ^ w - 1 : Nat) : Int) ∧ widthOf we a' = w ∧
            (refsOf a').all (fun x => ins.contains x) then some a'
        else some (.op o [a', b'])
      | _, _ => some (.op o [a', b'])) = some e') :
    e' = .op o [a', b'] ∨
      (o = .and ∧ ∃ w : Nat, b' = .const ((2 ^ w - 1 : Nat) : Int) w ∧ widthOf we a' = w ∧
        (refsOf a').all (fun x => ins.contains x) = true ∧ e' = a') := by
  revert h
  cases o <;> cases b' <;> simp only [Option.some.injEq] <;> (try (intro h; left; exact h.symm))
  rename_i m w
  split
  · rename_i hc
    intro h
    right
    exact ⟨trivial, w, by rw [hc.1], hc.2.1, hc.2.2, (Option.some.inj h).symm⟩
  · intro h; left; exact (Option.some.inj h).symm

theorem normE_sound {we : WEnv} {ins : List String} {defs : List (String × Expr)}
    {init env : Env} (hd : DefsOk we init env defs)
    (hins : ∀ x ∈ ins, init x < 2 ^ we x) :
    ∀ (r e' : Expr), normE we ins defs r = some e' →
      Shape e' ∧ widthOf we e' = widthOf we r ∧
      ∃ v, evalExpr we env r = some v ∧ evalExpr we init e' = some v
  | .const v w, e', h => by
    simp only [normE] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨.const hc.1 hc.2, rfl, _, evalConst_fit we env hc.1 hc.2,
        evalConst_fit we init hc.1 hc.2⟩
    · cases h
  | .ref x, e', h => by
    simp only [normE] at h
    cases hl : defs.lookup x with
    | some d =>
      rw [hl] at h
      simp only at h
      by_cases hw : we x = widthOf we d
      · rw [if_pos hw] at h
        cases h
        obtain ⟨hs, he⟩ := hd.1 x _ hl
        exact ⟨hs, by simp [widthOf, hw], env x, rfl, he⟩
      · rw [if_neg hw] at h; cases h
    | none =>
      rw [hl] at h
      cases h
      exact ⟨.ref x, rfl, env x, rfl, by simp [evalExpr, hd.2 x hl]⟩
  | .op o [a, b], e', h => by
    simp only [normE] at h
    split at h
    · rename_i ho
      cases ha : normE we ins defs a with
      | none => simp [ha] at h
      | some a' =>
        cases hb : normE we ins defs b with
        | none => simp [ha, hb] at h
        | some b' =>
          simp only [ha, hb, Option.bind_eq_bind, Option.bind_some] at h
          obtain ⟨sa, wa, va, hva, hva'⟩ := normE_sound hd hins a a' ha
          obtain ⟨sb, wb, vb, hvb, hvb'⟩ := normE_sound hd hins b b' hb
          have hw0 : widthOf we (.op o [a, b]) = max (widthOf we a) (widthOf we b) :=
            widthOf_bin we a b ho
          have hev : evalExpr we env (.op o [a, b]) =
              evalOp we o [a, b] [va, vb] (max (widthOf we a) (widthOf we b)) := by
            simp only [evalExpr, evalList, hva, hvb, Option.bind_eq_bind, Option.bind_some, hw0]
          -- the generic result: the same operator on the normalised operands
          have generic : Shape (.op o [a', b']) ∧
              widthOf we (.op o [a', b']) = widthOf we (.op o [a, b]) ∧
              ∃ v, evalExpr we env (.op o [a, b]) = some v ∧
                evalExpr we init (.op o [a', b']) = some v := by
            refine ⟨.bin ho sa sb, by rw [widthOf_bin we _ _ ho, hw0, wa, wb], ?_⟩
            obtain ⟨v, hv⟩ := shape_eval we env (Shape.bin ho (Shape.ref "a") (Shape.ref "b"))
            have hv2 : ∃ v, evalOp we o [a, b] [va, vb]
                (max (widthOf we a) (widthOf we b)) = some v := by
              cases o <;> simp_all [isBinOp, evalOp]
            obtain ⟨v', hv'⟩ := hv2
            refine ⟨v', by rw [hev]; exact hv', ?_⟩
            simp only [evalExpr, evalList, hva', hvb', Option.bind_eq_bind, Option.bind_some,
              widthOf_bin we a' b' ho, wa, wb]
            rw [evalOp_bin_args we ho [a', b'] [a, b]]
            exact hv'
          rcases mask_match h with rfl | ⟨rfl, w, rfl, hwa, hrefs, rfl⟩
          · exact generic
          · -- mask elimination: `a' & (2^w - 1)` with `a'` of width `w`
            have hvb2 : vb = 2 ^ w - 1 := by
              rw [evalConst_fit we init (by omega) (by
                have := Nat.two_pow_pos w; omega)] at hvb'
              simp at hvb'; omega
            have hbound : va < 2 ^ w := by
              rw [← hwa]
              refine shape_bound we init sa (fun x hx => ?_) va hva'
              have hx' : x ∈ ins := by
                have := List.all_eq_true.mp hrefs x hx
                simpa using this
              exact hins x hx'
            have hwb : widthOf we b = w := by rw [← wb]; rfl
            refine ⟨sa, ?_, va, ?_, hva'⟩
            · rw [hwa, hw0, ← wa, hwa, hwb, Nat.max_self]
            · rw [hev, ← wa, hwa, hwb, Nat.max_self, hvb2]
              simp only [evalOp, and_mask va w hbound]
    · cases h
  | .op _ [], _, h => by simp [normE] at h
  | .op _ [_], _, h => by simp [normE] at h
  | .op _ (_ :: _ :: _ :: _), _, h => by simp [normE] at h
  | .concat _, _, h => by simp [normE] at h
  | .slice _ _ _, _, h => by simp [normE] at h
  | .sliceDim _ _ _, _, h => by simp [normE] at h
  | .index _ _, _, h => by simp [normE] at h

theorem lookup_cons_eq' {α : Type} (l : String) (t : α) (A : List (String × α)) (z : String) :
    ((l, t) :: A).lookup z = if z = l then some t else A.lookup z := by
  by_cases h : z = l
  · subst h; simp [List.lookup_cons]
  · have hb : (z == l) = false := beq_false_of_ne h
    simp [List.lookup, hb, h]

/-- A body `normBody` accepts evaluates, and every name's normal form carries
its value. -/
theorem normBody_sound {we : WEnv} {ins : List String} {mems : MEnv} {init : Env}
    (hins : ∀ x ∈ ins, init x < 2 ^ we x) :
    ∀ (body : List Stmt) (defs D : List (String × Expr)) (env : Env),
      DefsOk we init env defs → normBody we ins defs body = some D →
      ∃ envF, evalAssigns we mems body env = some envF ∧ DefsOk we init envF D
  | [], defs, D, env, hd, h => by
    simp only [normBody, Option.some.injEq] at h
    subst h; exact ⟨env, rfl, hd⟩
  | .assign l r :: rest, defs, D, env, hd, h => by
    simp only [normBody] at h
    cases he : normE we ins defs r with
    | none => simp [he] at h
    | some e =>
      simp only [he, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨hs, -, v, hv, hv'⟩ := normE_sound hd hins r e he
      have hd' : DefsOk we init (fun n => if n = l then v else env n) ((l, e) :: defs) := by
        refine ⟨fun x d hx => ?_, fun x hx => ?_⟩
        · rw [lookup_cons_eq'] at hx
          split at hx
          · rename_i hxl; cases hx; subst hxl; simp [hs, hv']
          · rename_i hxl
            obtain ⟨a, b⟩ := hd.1 x d hx
            exact ⟨a, by simp [hxl, b]⟩
        · rw [lookup_cons_eq'] at hx
          split at hx
          · cases hx
          · rename_i hxl; simp [hxl, hd.2 x hx]
      obtain ⟨envF, hev, hdF⟩ := normBody_sound (mems := mems) hins rest _ D _ hd' h
      exact ⟨envF, by simp [evalAssigns, hv, hev], hdF⟩
  | .register .. :: _, _, _, _, _, h => by simp [normBody] at h
  | .memory .. :: _, _, _, _, _, h => by simp [normBody] at h
  | .inst .. :: _, _, _, _, _, h => by simp [normBody] at h

/-! ## 3. The check -/

/-- **`optCheck` is sound.** If it accepts `o` for `m`, then for every input
assignment whose values fit `m`'s declared input widths, whenever `m`'s
statements evaluate, so do `o`'s, and every output has the same value; the
ports are the same. -/
theorem optCheck_sound {m o : Sparkle.IR.AST.Module} (hchk : optCheck m o = true)
    {mems : MEnv} {init envM : Env}
    (hins : ∀ x ∈ m.inputs.map (·.name), init x < 2 ^ Sparkle.IR.RegDedup.declWidth m x)
    (hevM : evalAssigns (Sparkle.IR.RegDedup.declWidth m) mems m.body init = some envM) :
    ∃ envO, evalAssigns (Sparkle.IR.RegDedup.declWidth o) mems o.body init = some envO ∧
      (∀ p ∈ m.outputs, envO p.name = envM p.name) ∧
      o.inputs = m.inputs ∧ o.outputs = m.outputs := by
  unfold optCheck at hchk
  simp only at hchk
  split at hchk
  · rename_i dm dO hm ho
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨hin, hout⟩, houts⟩ := hchk
    have hd0 : ∀ (we : WEnv) (env : Env), DefsOk we env env [] :=
      fun _ _ => ⟨fun x d h => by simp at h, fun _ _ => rfl⟩
    obtain ⟨envM', hevM', hdM⟩ := normBody_sound hins m.body [] dm init (hd0 _ init) hm
    rw [hevM] at hevM'
    cases hevM'
    have hmemO : ∀ x, x ∈ (m.inputs.map (·.name)).filter
        (fun x => Sparkle.IR.RegDedup.declWidth m x == Sparkle.IR.RegDedup.declWidth o x) →
        x ∈ m.inputs.map (·.name) ∧
          Sparkle.IR.RegDedup.declWidth m x = Sparkle.IR.RegDedup.declWidth o x := by
      intro x hx
      obtain ⟨h1, h2⟩ := List.mem_filter.mp hx
      exact ⟨h1, beq_iff_eq.mp h2⟩
    have hinsO : ∀ x ∈ (m.inputs.map (·.name)).filter
        (fun x => Sparkle.IR.RegDedup.declWidth m x == Sparkle.IR.RegDedup.declWidth o x),
        init x < 2 ^ Sparkle.IR.RegDedup.declWidth o x := by
      intro x hx
      obtain ⟨h1, h2⟩ := hmemO x hx
      rw [← h2]; exact hins x h1
    obtain ⟨envO, hevO, hdO⟩ := normBody_sound hinsO o.body [] dO init (hd0 _ init) ho
    refine ⟨envO, hevO, fun p hp => ?_, hin, hout⟩
    have := List.all_eq_true.mp houts p hp
    split at this
    · rename_i em eo hem heo
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨rfl, hrefs⟩ := this
      obtain ⟨-, h1⟩ := hdM.1 p.name em hem
      obtain ⟨-, h2⟩ := hdO.1 p.name em heo
      have hcongr := Tools.ConeFold.evalExpr_we_congr (Sparkle.IR.RegDedup.declWidth m)
        (Sparkle.IR.RegDedup.declWidth o) init em (fun x hx => by
          have hx' := List.all_eq_true.mp hrefs x hx
          exact (hmemO x (by simpa using hx')).2)
      rw [hcongr, h2] at h1
      exact Option.some.inj h1
    · cases this
  · cases hchk

/-- **`checkedOptimize` preserves outputs on modules of simple shape.**
Whether the optimised module is accepted or the input module is kept, the
module returned computes the same outputs, with the same ports. -/
theorem checkedOptimize_sound {m : Sparkle.IR.AST.Module} (hgate : simpleBody m = true)
    {mems : MEnv} {init envM : Env}
    (hins : ∀ x ∈ m.inputs.map (·.name), init x < 2 ^ Sparkle.IR.RegDedup.declWidth m x)
    (hevM : evalAssigns (Sparkle.IR.RegDedup.declWidth m) mems m.body init = some envM) :
    ∃ envO, evalAssigns (Sparkle.IR.RegDedup.declWidth (checkedOptimize m)) mems
        (checkedOptimize m).body init = some envO ∧
      (∀ p ∈ m.outputs, envO p.name = envM p.name) ∧
      (checkedOptimize m).inputs = m.inputs ∧ (checkedOptimize m).outputs = m.outputs := by
  unfold checkedOptimize
  simp only [hgate, if_true]
  split
  · rename_i hchk
    exact optCheck_sound hchk hins hevM
  · exact ⟨envM, hevM, fun _ _ => rfl, rfl, rfl⟩

theorem optCheck_ports {m o : Sparkle.IR.AST.Module} (h : optCheck m o = true) :
    o.inputs = m.inputs ∧ o.outputs = m.outputs := by
  unfold optCheck at h
  simp only at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  · cases h

theorem checkedOptimize_ports {m : Sparkle.IR.AST.Module} (hgate : simpleBody m = true) :
    (checkedOptimize m).inputs = m.inputs ∧ (checkedOptimize m).outputs = m.outputs := by
  unfold checkedOptimize
  simp only [hgate, if_true]
  split
  · rename_i hc; exact optCheck_ports hc
  · exact ⟨rfl, rfl⟩

end Tools.ShippingOptSoundness
