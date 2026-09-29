import Tools.ShippingOptSoundness

/-! # The sequential rename-equivalence normal forms are sound

`Sparkle.IR.OptCheck.seqOptCheck` compares two sequential modules through
mux-aware normal forms under a register renaming. This file gives the
normal-form layer: the extended shape grammar, its evaluation and width
bounds, soundness of `seqNormE`/`seqNormBody` (mirroring the combinational
`normE_sound`/`normBody_sound`), and evaluation-commutation for the total
reference renaming `renameRefsT`. -/

namespace Tools.ShippingSeqOptSoundness

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck
open Sparkle.IR.Reorder (refsOf)
open Tools.ShippingOptSoundness

/-- Normal forms of the sequential checker: the combinational grammar plus
the mux node at equal branch widths (its value is a branch value, so the
width bound carries through). -/
inductive SeqShape (we : WEnv) : Expr → Prop
  | const {v : Int} {w : Nat} : 0 ≤ v → v < ((2 ^ w : Nat) : Int) →
      SeqShape we (.const v w)
  | ref (x : String) : SeqShape we (.ref x)
  | bin {o : Operator} {a b : Expr} : isBinOp o = true → SeqShape we a →
      SeqShape we b → SeqShape we (.op o [a, b])
  | mux {c a b : Expr} : SeqShape we c → SeqShape we a → SeqShape we b →
      widthOf we a = widthOf we b → SeqShape we (.op .mux [c, a, b])

theorem refs_mux_mem {op : Operator} {c a b : Expr} {x : String} :
    x ∈ refsOf (.op op [c, a, b]) ↔ x ∈ refsOf c ∨ x ∈ refsOf a ∨ x ∈ refsOf b := by
  simp [refsOf, Sparkle.IR.Reorder.refsOf.refsList]

theorem refs_bin_mem {op : Operator} {a b : Expr} {x : String} :
    x ∈ refsOf (.op op [a, b]) ↔ x ∈ refsOf a ∨ x ∈ refsOf b := by
  simp [refsOf, Sparkle.IR.Reorder.refsOf.refsList]

theorem seqShape_eval (we : WEnv) (env : Env) :
    ∀ {e : Expr}, SeqShape we e → ∃ v, evalExpr we env e = some v
  | _, .const h0 hlt => ⟨_, evalConst_fit we env h0 hlt⟩
  | _, .ref x => ⟨env x, rfl⟩
  | .op o [a, b], .bin ho ha hb => by
    obtain ⟨va, hva⟩ := seqShape_eval we env ha
    obtain ⟨vb, hvb⟩ := seqShape_eval we env hb
    simp only [evalExpr, evalList, hva, hvb, Option.bind_eq_bind, Option.bind_some]
    cases o <;> simp_all [isBinOp, evalOp]
  | .op .mux [c, a, b], .mux hc ha hb hw => by
    obtain ⟨vc, hvc⟩ := seqShape_eval we env hc
    obtain ⟨va, hva⟩ := seqShape_eval we env ha
    obtain ⟨vb, hvb⟩ := seqShape_eval we env hb
    simp only [evalExpr, evalList, hvc, hva, hvb, Option.bind_eq_bind, Option.bind_some]
    simp [evalOp]

theorem seqShape_bound (we : WEnv) (env : Env) :
    ∀ {e : Expr}, SeqShape we e → (∀ x ∈ refsOf e, env x < 2 ^ we x) →
      ∀ v, evalExpr we env e = some v → v < 2 ^ widthOf we e
  | _, .const h0 hlt, _, v, hv => by
    rw [evalConst_fit we env h0 hlt] at hv
    cases hv; simp only [widthOf]; omega
  | _, .ref x, hr, v, hv => by
    simp only [evalExpr, Option.some.injEq] at hv
    subst hv; exact hr x (by simp [refsOf])
  | .op o [a, b], .bin ho ha hb, _, v, hv => by
    obtain ⟨va, hva⟩ := seqShape_eval we env ha
    obtain ⟨vb, hvb⟩ := seqShape_eval we env hb
    simp only [evalExpr, evalList, hva, hvb, Option.bind_eq_bind, Option.bind_some] at hv
    exact evalOp_bin_lt we ho _ va vb _ v hv
  | .op .mux [c, a, b], .mux hc ha hb hw, hr, v, hv => by
    obtain ⟨vc, hvc⟩ := seqShape_eval we env hc
    obtain ⟨va, hva⟩ := seqShape_eval we env ha
    obtain ⟨vb, hvb⟩ := seqShape_eval we env hb
    have hra : ∀ x ∈ refsOf a, env x < 2 ^ we x :=
      fun x hx => hr x (refs_mux_mem.mpr (Or.inr (Or.inl hx)))
    have hrb : ∀ x ∈ refsOf b, env x < 2 ^ we x :=
      fun x hx => hr x (refs_mux_mem.mpr (Or.inr (Or.inr hx)))
    have hba := seqShape_bound we env ha hra va hva
    have hbb := seqShape_bound we env hb hrb vb hvb
    simp only [evalExpr, evalList, hvc, hva, hvb, Option.bind_eq_bind, Option.bind_some,
      evalOp, Option.some.injEq] at hv
    subst hv
    have hwm : widthOf we (.op .mux [c, a, b]) = widthOf we a := by
      simp [widthOf]
    rw [hwm]
    by_cases h0 : vc ≠ 0
    · simp [h0, hba]
    · have h0' : vc = 0 := by omega
      simp [h0', hw, hbb]

/-- What the definitions seen so far guarantee, in the current environment. -/
def SeqDefsOk (we : WEnv) (init env : Env) (defs : List (String × Expr)) : Prop :=
  (∀ x d, defs.lookup x = some d → SeqShape we d ∧ evalExpr we init d = some (env x)) ∧
  (∀ x, defs.lookup x = none → env x = init x)

theorem seqNormE_sound {we : WEnv} {ins : List String} {defs : List (String × Expr)}
    {init env : Env} (hd : SeqDefsOk we init env defs)
    (hins : ∀ x ∈ ins, init x < 2 ^ we x) :
    ∀ (r e' : Expr), seqNormE we ins defs r = some e' →
      SeqShape we e' ∧ widthOf we e' = widthOf we r ∧
      ∃ v, evalExpr we env r = some v ∧ evalExpr we init e' = some v
  | .const v w, e', h => by
    simp only [seqNormE] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨.const hc.1 hc.2, rfl, _, evalConst_fit we env hc.1 hc.2,
        evalConst_fit we init hc.1 hc.2⟩
    · cases h
  | .ref x, e', h => by
    simp only [seqNormE] at h
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
  | .op .mux [c, a, b], e', h => by
    simp only [seqNormE] at h
    cases hcn : seqNormE we ins defs c with
    | none => simp [hcn] at h
    | some c' =>
      cases han : seqNormE we ins defs a with
      | none => simp [hcn, han] at h
      | some a' =>
        cases hbn : seqNormE we ins defs b with
        | none => simp [hcn, han, hbn] at h
        | some b' =>
          simp only [hcn, han, hbn, Option.bind_eq_bind, Option.bind_some] at h
          obtain ⟨sc, wc, vc, hvc, hvc'⟩ := seqNormE_sound hd hins c c' hcn
          obtain ⟨sa, wa, va, hva, hva'⟩ := seqNormE_sound hd hins a a' han
          obtain ⟨sb, wb, vb, hvb, hvb'⟩ := seqNormE_sound hd hins b b' hbn
          by_cases hww : widthOf we a' = widthOf we b'
          · rw [if_pos hww] at h
            cases h
            refine ⟨.mux sc sa sb hww, by simp [widthOf, wa], ?_⟩
            refine ⟨if vc ≠ 0 then va else vb, ?_, ?_⟩
            · simp only [evalExpr, evalList, hvc, hva, hvb, Option.bind_eq_bind,
                Option.bind_some]
              simp [evalOp]
            · simp only [evalExpr, evalList, hvc', hva', hvb', Option.bind_eq_bind,
                Option.bind_some]
              simp [evalOp]
          · rw [if_neg hww] at h; cases h
  | .op o [a, b], e', h => by
    simp only [seqNormE] at h
    split at h
    · rename_i ho
      cases ha : seqNormE we ins defs a with
      | none => simp [ha] at h
      | some a' =>
        cases hb : seqNormE we ins defs b with
        | none => simp [ha, hb] at h
        | some b' =>
          simp only [ha, hb, Option.bind_eq_bind, Option.bind_some] at h
          obtain ⟨sa, wa, va, hva, hva'⟩ := seqNormE_sound hd hins a a' ha
          obtain ⟨sb, wb, vb, hvb, hvb'⟩ := seqNormE_sound hd hins b b' hb
          have hw0 : widthOf we (.op o [a, b]) = max (widthOf we a) (widthOf we b) :=
            widthOf_bin we a b ho
          have hev : evalExpr we env (.op o [a, b]) =
              evalOp we o [a, b] [va, vb] (max (widthOf we a) (widthOf we b)) := by
            simp only [evalExpr, evalList, hva, hvb, Option.bind_eq_bind, Option.bind_some, hw0]
          have generic : SeqShape we (.op o [a', b']) ∧
              widthOf we (.op o [a', b']) = widthOf we (.op o [a, b]) ∧
              ∃ v, evalExpr we env (.op o [a, b]) = some v ∧
                evalExpr we init (.op o [a', b']) = some v := by
            refine ⟨.bin ho sa sb, by rw [widthOf_bin we _ _ ho, hw0, wa, wb], ?_⟩
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
          · have hvb2 : vb = 2 ^ w - 1 := by
              rw [evalConst_fit we init (by omega) (by
                have := Nat.two_pow_pos w; omega)] at hvb'
              simp at hvb'; omega
            have hbound : va < 2 ^ w := by
              rw [← hwa]
              refine seqShape_bound we init sa (fun x hx => ?_) va hva'
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
  | .op _ [], _, h => by simp [seqNormE] at h
  | .op _ [_], _, h => by simp [seqNormE] at h
  | .op .mux (_ :: _ :: _ :: _ :: _), _, h => by simp [seqNormE] at h
  | .concat _, _, h => by simp [seqNormE] at h
  | .slice _ _ _, _, h => by simp [seqNormE] at h
  | .sliceDim _ _ _, _, h => by simp [seqNormE] at h
  | .index _ _, _, h => by simp [seqNormE] at h

/-- A body `seqNormBody` accepts evaluates, and every name's normal form
carries its value. -/
theorem seqNormBody_sound {we : WEnv} {ins : List String} {mems : MEnv} {init : Env}
    (hins : ∀ x ∈ ins, init x < 2 ^ we x) :
    ∀ (body : List Stmt) (defs D : List (String × Expr)) (env : Env),
      SeqDefsOk we init env defs → seqNormBody we ins defs body = some D →
      ∃ envF, evalAssigns we mems body env = some envF ∧ SeqDefsOk we init envF D
  | [], defs, D, env, hd, h => by
    simp only [seqNormBody, Option.some.injEq] at h
    subst h; exact ⟨env, rfl, hd⟩
  | .assign l r :: rest, defs, D, env, hd, h => by
    simp only [seqNormBody] at h
    cases he : seqNormE we ins defs r with
    | none => simp [he] at h
    | some e =>
      simp only [he, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨hs, -, v, hv, hv'⟩ := seqNormE_sound hd hins r e he
      have hd' : SeqDefsOk we init (fun n => if n = l then v else env n) ((l, e) :: defs) := by
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
      obtain ⟨envF, hev, hdF⟩ := seqNormBody_sound (mems := mems) hins rest _ D _ hd' h
      exact ⟨envF, by simp [evalAssigns, hv, hev], hdF⟩
  | .register .. :: _, _, _, _, _, h => by simp [seqNormBody] at h
  | .memory .. :: _, _, _, _, _, h => by simp [seqNormBody] at h
  | .inst .. :: _, _, _, _, _, h => by simp [seqNormBody] at h

/-! ## Renaming commutes with evaluation on normal forms -/

theorem widthOf_renameT {subst : Std.HashMap String String} {weO weM : WEnv} :
    ∀ {e : Expr}, SeqShape weO e →
      (∀ x ∈ refsOf e, weO x = weM (renameT subst x)) →
      widthOf weM (renameRefsT subst e) = widthOf weO e
  | _, .const _ _, _ => rfl
  | _, .ref x, hw => by
    simp only [renameRefsT, widthOf]
    exact (hw x (by simp [refsOf])).symm
  | .op o [a, b], .bin ho ha hb, hw => by
    have iha := widthOf_renameT ha (fun x hx => hw x (refs_bin_mem.mpr (Or.inl hx)))
    have ihb := widthOf_renameT hb (fun x hx => hw x (refs_bin_mem.mpr (Or.inr hx)))
    show widthOf weM (.op o [renameRefsT subst a, renameRefsT subst b]) = _
    rw [widthOf_bin weM _ _ ho, widthOf_bin weO a b ho, iha, ihb]
  | .op .mux [c, a, b], .mux hc ha hb hwab, hw => by
    have iha := widthOf_renameT ha (fun x hx => hw x (refs_mux_mem.mpr (Or.inr (Or.inl hx))))
    show widthOf weM (.op .mux [renameRefsT subst c, renameRefsT subst a,
      renameRefsT subst b]) = _
    simp only [widthOf]
    exact iha

/-- Evaluating a normal form in the renamed environment agrees with
evaluating its renaming in the original environment. -/
theorem evalExpr_renameT {subst : Std.HashMap String String} {weO weM : WEnv} {init : Env} :
    ∀ {e : Expr}, SeqShape weO e →
      (∀ x ∈ refsOf e, weO x = weM (renameT subst x)) →
      evalExpr weM init (renameRefsT subst e) =
        evalExpr weO (fun x => init (renameT subst x)) e
  | _, .const _ _, _ => rfl
  | _, .ref x, _ => rfl
  | .op o [a, b], .bin ho ha hb, hw => by
    have iha := evalExpr_renameT (init := init) ha (fun x hx => hw x (refs_bin_mem.mpr (Or.inl hx)))
    have ihb := evalExpr_renameT (init := init) hb (fun x hx => hw x (refs_bin_mem.mpr (Or.inr hx)))
    have wa := widthOf_renameT ha (fun x hx => hw x (refs_bin_mem.mpr (Or.inl hx)))
    have wb := widthOf_renameT hb (fun x hx => hw x (refs_bin_mem.mpr (Or.inr hx)))
    obtain ⟨va, hva⟩ := seqShape_eval weO (fun x => init (renameT subst x)) ha
    obtain ⟨vb, hvb⟩ := seqShape_eval weO (fun x => init (renameT subst x)) hb
    show evalExpr weM init (.op o [renameRefsT subst a, renameRefsT subst b]) = _
    simp only [evalExpr, evalList, iha, ihb, hva, hvb, Option.bind_eq_bind, Option.bind_some,
      widthOf_bin weM _ _ ho, widthOf_bin weO a b ho, wa, wb]
    rw [evalOp_bin_args weM ho _ [a, b]]
    rw [show evalOp weM o [a, b] [va, vb] (max (widthOf weO a) (widthOf weO b)) =
      evalOp weO o [a, b] [va, vb] (max (widthOf weO a) (widthOf weO b)) from by
        cases o <;> simp_all [isBinOp, evalOp]]
  | .op .mux [c, a, b], .mux hc ha hb hwab, hw => by
    have ihc := evalExpr_renameT (init := init) hc (fun x hx => hw x (refs_mux_mem.mpr (Or.inl hx)))
    have iha := evalExpr_renameT (init := init) ha (fun x hx => hw x (refs_mux_mem.mpr (Or.inr (Or.inl hx))))
    have ihb := evalExpr_renameT (init := init) hb (fun x hx => hw x (refs_mux_mem.mpr (Or.inr (Or.inr hx))))
    obtain ⟨vc, hvc⟩ := seqShape_eval weO (fun x => init (renameT subst x)) hc
    obtain ⟨va, hva⟩ := seqShape_eval weO (fun x => init (renameT subst x)) ha
    obtain ⟨vb, hvb⟩ := seqShape_eval weO (fun x => init (renameT subst x)) hb
    show evalExpr weM init (.op .mux [renameRefsT subst c, renameRefsT subst a,
      renameRefsT subst b]) = _
    simp only [evalExpr, evalList, ihc, iha, ihb, hvc, hva, hvb, Option.bind_eq_bind,
      Option.bind_some]
    simp [evalOp]

/-! ## The register pairing substitution -/

theorem foldl_insert_lookup_notmem {β : Type} :
    ∀ (l : List (String × β)) (h : Std.HashMap String β) (x : String),
      x ∉ l.map (·.1) →
      (l.foldl (fun acc p => acc.insert p.1 p.2) h)[x]? = h[x]?
  | [], _, _, _ => rfl
  | (k, v) :: rest, h, x, hnm => by
    have hxk : x ≠ k := fun heq => hnm (by simp [heq])
    have hrest : x ∉ rest.map (·.1) := fun hm => hnm (by simp [hm])
    show (rest.foldl (fun acc p => acc.insert p.1 p.2) (h.insert k v))[x]? = h[x]?
    rw [foldl_insert_lookup_notmem rest _ x hrest]
    have hkx : (k == x) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun heq => hxk heq.symm
    simp [Std.HashMap.getElem?_insert, hkx]

theorem foldl_insert_lookup {β : Type} :
    ∀ (l : List (String × β)) (h : Std.HashMap String β),
      (l.map (·.1)).Nodup →
      ∀ (k : String) (v : β), (k, v) ∈ l →
        (l.foldl (fun acc p => acc.insert p.1 p.2) h)[k]? = some v
  | [], _, _, _, _, hm => absurd hm (List.not_mem_nil)
  | (k0, v0) :: rest, h, hnd, k, v, hm => by
    have hnd' : (rest.map (·.1)).Nodup := by
      simp only [List.map_cons, List.nodup_cons] at hnd
      exact hnd.2
    rcases List.mem_cons.mp hm with heq | hmem
    · cases heq
      have hknm : k0 ∉ rest.map (·.1) := by
        simp only [List.map_cons, List.nodup_cons] at hnd
        exact hnd.1
      show (rest.foldl (fun acc p => acc.insert p.1 p.2) (h.insert k0 v0))[k0]? = some v0
      rw [foldl_insert_lookup_notmem rest _ k0 hknm]
      simp [Std.HashMap.getElem?_insert]
    · show (rest.foldl (fun acc p => acc.insert p.1 p.2) (h.insert k0 v0))[k]? = some v
      exact foldl_insert_lookup rest (h.insert k0 v0) hnd' k v hmem

/-! ## Renaming and reference sets -/

mutual
theorem refsOf_renameRefsT (subst : Std.HashMap String String) :
    ∀ (e : Expr), refsOf (renameRefsT subst e) = (refsOf e).map (renameT subst)
  | .const _ _ => rfl
  | .ref _ => rfl
  | .op o args => by
    show Sparkle.IR.Reorder.refsOf.refsList (renameRefsTList subst args) = _
    rw [refsList_renameRefsTList subst args]
    rfl
  | .concat args => by
    show Sparkle.IR.Reorder.refsOf.refsList (renameRefsTList subst args) = _
    rw [refsList_renameRefsTList subst args]
    rfl
  | .slice e _ _ => refsOf_renameRefsT subst e
  | .sliceDim e _ _ => refsOf_renameRefsT subst e
  | .index a i => by
    show refsOf (renameRefsT subst a) ++ refsOf (renameRefsT subst i) =
      (refsOf a ++ refsOf i).map (renameT subst)
    rw [refsOf_renameRefsT subst a, refsOf_renameRefsT subst i, List.map_append]

theorem refsList_renameRefsTList (subst : Std.HashMap String String) :
    ∀ (args : List Expr),
      Sparkle.IR.Reorder.refsOf.refsList (renameRefsTList subst args) =
        (Sparkle.IR.Reorder.refsOf.refsList args).map (renameT subst)
  | [] => rfl
  | a :: rest => by
    show refsOf (renameRefsT subst a) ++
        Sparkle.IR.Reorder.refsOf.refsList (renameRefsTList subst rest) =
      (refsOf a ++ Sparkle.IR.Reorder.refsOf.refsList rest).map (renameT subst)
    rw [refsOf_renameRefsT subst a, refsList_renameRefsTList subst rest, List.map_append]
end

/-! ## Sequential body projections -/

def seqRegsL (body : List Stmt) :
    List (String × String × (String × Sparkle.IR.Type.ResetKind) × Expr × Int) :=
  body.filterMap fun st => match st with
    | .register o c rk i iv => some (o, c, rk, i, iv)
    | _ => none

theorem seqRegs_eq (m : Module) : seqRegs m = seqRegsL m.body := rfl

theorem evalAssigns_seq_skip {we : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOk = true → ∀ (env : Env),
      evalAssigns we mems body env =
        evalAssigns we mems (body.filter (fun st => match st with
          | .assign .. => true
          | _ => false)) env
  | [], _, env => rfl
  | .assign l r :: rest, hok, env => by
    have hrest : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok
      exact hok.2
    show (evalExpr we env r).bind _ = (evalExpr we env r).bind _
    cases evalExpr we env r with
    | none => rfl
    | some v =>
      simp only [Option.bind_some]
      exact evalAssigns_seq_skip hrest _
  | .register o c rk i iv :: rest, hok, env => by
    have hrest : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok
      exact hok.2
    show evalAssigns we mems rest env = _
    exact evalAssigns_seq_skip hrest env
  | .memory .. :: rest, hok, env => by
    simp [seqStmtOk] at hok
  | .inst .. :: rest, hok, env => by
    simp [seqStmtOk] at hok

theorem regNexts_seq_map {we : WEnv} {mems : MEnv} {envF : Env} {f : Expr → Nat} :
    ∀ {body : List Stmt}, body.all seqStmtOk = true →
      (∀ r ∈ seqRegsL body, evalExpr we envF r.2.2.2.1 = some (f r.2.2.2.1)) →
      regNexts we mems body envF = some ((seqRegsL body).map fun r =>
        (r.1, if envF r.2.2.1.1 ≠ 0 then encodeInit r.2.2.2.2 (we r.1)
          else mask (we r.1) (f r.2.2.2.1)))
  | [], _, _ => rfl
  | .assign l r :: rest, hok, hv => by
    have hrest : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok
      exact hok.2
    show regNexts we mems rest envF = _
    exact regNexts_seq_map hrest hv
  | .register o c rk i iv :: rest, hok, hv => by
    have hrest : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok
      exact hok.2
    have hhead : evalExpr we envF i = some (f i) :=
      hv (o, c, rk, i, iv)
        (List.mem_filterMap.mpr ⟨.register o c rk i iv, List.mem_cons_self, rfl⟩)
    have htail := regNexts_seq_map (mems := mems) (envF := envF) (f := f) hrest
      (fun r hr => hv r (by
        obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp hr
        exact List.mem_filterMap.mpr ⟨a, List.mem_cons_of_mem _ ha, he⟩))
    simp only [regNexts, hhead, htail, Option.bind_eq_bind, Option.bind_some,
      seqRegsL, List.filterMap_cons, List.map_cons, Option.some.injEq]
  | .memory .. :: rest, hok, hv => by simp [seqStmtOk] at hok
  | .inst .. :: rest, hok, hv => by simp [seqStmtOk] at hok

/-! ## One-cycle soundness of the sequential rename-equivalence checker -/

/-- An accepted body's assign segment never writes a name `z` that no
assign targets. -/
theorem evalAssigns_keeps {we : WEnv} {mems : MEnv} (z : String) :
    ∀ {body : List Stmt} {env envF : Env},
      body.all seqStmtOk = true →
      body.all (fun st => match st with
        | .assign l _ => l != z
        | _ => true) = true →
      evalAssigns we mems body env = some envF → envF z = env z
  | [], env, envF, _, _, h => by cases h; rfl
  | .assign l r :: rest, env, envF, hok, hz, h => by
    have hok' : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    have hz' : (rest.all fun st => match st with
        | .assign l _ => l != z
        | _ => true) = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hz; exact hz.2
    have hlz : l ≠ z := by
      simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hz
      exact hz.1
    simp only [evalAssigns, Option.bind_eq_bind] at h
    cases hv : evalExpr we env r with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h
      simp only [Option.bind_some] at h
      have := evalAssigns_keeps z hok' hz' h
      have hzl : ¬(z = l) := fun heq => hlz heq.symm
      rw [this, if_neg hzl]
  | .register .. :: rest, env, envF, hok, hz, h => by
    have hok' : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    have hz' : (rest.all fun st => match st with
        | .assign l _ => l != z
        | _ => true) = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hz; exact hz.2
    exact evalAssigns_keeps z hok' hz' h
  | .memory .. :: rest, env, envF, hok, _, h => by simp [seqStmtOk] at hok
  | .inst .. :: rest, env, envF, hok, _, h => by simp [seqStmtOk] at hok

/-- Accepted bodies carry no memories, so the memory state is unchanged. -/
theorem memNexts_seqStmtOk {we : WEnv} {mems : MEnv} {envF : Env} :
    ∀ {body : List Stmt}, body.all seqStmtOk = true →
      memNexts we body mems envF = some mems
  | [], _ => rfl
  | .assign _ _ :: rest, hok => by
    have hok' : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show memNexts we rest mems envF = some mems
    exact memNexts_seqStmtOk hok'
  | .register .. :: rest, hok => by
    have hok' : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show memNexts we rest mems envF = some mems
    exact memNexts_seqStmtOk hok'
  | .memory .. :: rest, hok => by simp [seqStmtOk] at hok
  | .inst .. :: rest, hok => by simp [seqStmtOk] at hok

/-- Off the register pairing, the checker's substitution is the identity. -/
theorem seqSubst_off {m o : Module}
    (hlen : (seqRegs m).length = (seqRegs o).length) :
    ∀ x, x ∉ (seqRegs o).map (·.1) → renameT (seqSubst m o) x = x := by
  have hsubst : seqSubst m o = ((List.zip (seqRegs o) (seqRegs m)).map
      (fun pr => (pr.1.1, pr.2.1))).foldl (fun acc p => acc.insert p.1 p.2) {} := by
    rw [List.foldl_map]
    rfl
  have hkeys : (((List.zip (seqRegs o) (seqRegs m)).map (fun pr => (pr.1.1, pr.2.1))).map (·.1)) =
      (seqRegs o).map (·.1) := by
    have h1 : (((List.zip (seqRegs o) (seqRegs m)).map (fun pr => (pr.1.1, pr.2.1))).map (·.1)) =
        ((List.zip (seqRegs o) (seqRegs m)).map Prod.fst).map (·.1) := by
      rw [List.map_map, List.map_map]
      rfl
    rw [h1, List.map_fst_zip
      (by omega : (seqRegs o).length ≤ (seqRegs m).length)]
  intro x hx
  have hnm : x ∉ ((List.zip (seqRegs o) (seqRegs m)).map (fun pr => (pr.1.1, pr.2.1))).map (·.1) := by
    rw [hkeys]; exact hx
  have := foldl_insert_lookup_notmem _ ({} : Std.HashMap String String) x hnm
  rw [← hsubst] at this
  simp [renameT, this]

/-- The checker's substitution sends the i-th `o` register name to the
i-th `m` register name. -/
theorem seqSubst_pair {m o : Module}
    (hlen : (seqRegs m).length = (seqRegs o).length)
    (hndO : ((seqRegs o).map (·.1)).Nodup) :
    ∀ i (hi : i < (seqRegs o).length),
      renameT (seqSubst m o) (((seqRegs o)[i]'hi).1) =
        (((seqRegs m)[i]'(by omega)).1) := by
  have hsubst : seqSubst m o = ((List.zip (seqRegs o) (seqRegs m)).map
      (fun pr => (pr.1.1, pr.2.1))).foldl (fun acc p => acc.insert p.1 p.2) {} := by
    rw [List.foldl_map]
    rfl
  have hkeys : (((List.zip (seqRegs o) (seqRegs m)).map (fun pr => (pr.1.1, pr.2.1))).map (·.1)) =
      (seqRegs o).map (·.1) := by
    have h1 : (((List.zip (seqRegs o) (seqRegs m)).map (fun pr => (pr.1.1, pr.2.1))).map (·.1)) =
        ((List.zip (seqRegs o) (seqRegs m)).map Prod.fst).map (·.1) := by
      rw [List.map_map, List.map_map]
      rfl
    rw [h1, List.map_fst_zip
      (by omega : (seqRegs o).length ≤ (seqRegs m).length)]
  have hndKeys : (((List.zip (seqRegs o) (seqRegs m)).map (fun pr => (pr.1.1, pr.2.1))).map (·.1)).Nodup := by
    rw [hkeys]; exact hndO
  intro i hi
  have hmem : ((((seqRegs o)[i]'hi).1), (((seqRegs m)[i]'(by omega : i < (seqRegs m).length)).1)) ∈
      (List.zip (seqRegs o) (seqRegs m)).map (fun pr => (pr.1.1, pr.2.1)) := by
    refine List.mem_map.mpr ⟨(((seqRegs o)[i]'hi), ((seqRegs m)[i]'(by omega))), ?_, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by rw [List.length_zip]; omega, by rw [List.getElem_zip]⟩
  have := foldl_insert_lookup _ ({} : Std.HashMap String String) hndKeys _ _ hmem
  rw [← hsubst] at this
  simp [renameT, this]

open Sparkle.IR.RegDedup (declWidth) in
set_option maxHeartbeats 4000000 in
/-- **The sequential rename-equivalence check is sound for one cycle.**
With reset low and fitting inputs and register states, both modules step:
the outputs agree, the register updates pair up name-for-name with equal
values, and the updated values stay width-bounded. -/
theorem seqOptCheck_step_sound {m o : Sparkle.IR.AST.Module}
    (hchk : seqOptCheck m o = true) {mems : MEnv} {init : Env}
    (hins : ∀ x ∈ m.inputs.map (·.name),
      init x < 2 ^ Sparkle.IR.RegDedup.declWidth m x)
    (hregs : ∀ r ∈ seqRegs m, init r.1 < 2 ^ Sparkle.IR.RegDedup.declWidth m r.1)
    (hrst : init "rst" = 0) {initO : Env}
    (hagree : ∀ x ∈ ((m.inputs.map (·.name)).filter
        (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)),
      initO x = init (renameT (seqSubst m o) x))
    (hrstO : initO "rst" = 0) :
    ∃ envM envO nextsM nextsO,
      stepModule (Sparkle.IR.RegDedup.declWidth m) m.body init mems
        = some (envM, nextsM, mems) ∧
      stepModule (Sparkle.IR.RegDedup.declWidth o) o.body initO mems
        = some (envO, nextsO, mems) ∧
      (∀ p ∈ m.outputs, envO p.name = envM p.name) ∧
      nextsM.map (·.1) = (seqRegs m).map (·.1) ∧
      nextsO.map (·.1) = (seqRegs o).map (·.1) ∧
      nextsM.map (·.2) = nextsO.map (·.2) ∧
      (∀ pr ∈ nextsM, pr.2 < 2 ^ Sparkle.IR.RegDedup.declWidth m pr.1) := by
  simp only [seqOptCheck] at hchk
  rw [Bool.and_eq_true] at hchk
  obtain ⟨h1, h2⟩ := hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hinEq⟩, houtEq⟩, hokM⟩, hokO⟩, hndM⟩, hndO⟩, hdisjM⟩,
    hdisjO⟩, hzM⟩, hzO⟩, hpairs⟩ := h1
  have renPair := seqSubst_pair (m := m) (o := o) hlen hndO
  have renOff := seqSubst_off (m := m) (o := o) hlen
  -- The paired static facts, index-wise.
  have hpairAt : ∀ i (hi : i < (seqRegs m).length),
      ((seqRegs m)[i]'hi).2.1 = ((seqRegs o)[i]'(by omega)).2.1 ∧
      ((seqRegs m)[i]'hi).2.2.1.1 = "rst" ∧ ((seqRegs o)[i]'(by omega)).2.2.1.1 = "rst" ∧
      ((seqRegs m)[i]'hi).2.2.1.2 = ((seqRegs o)[i]'(by omega)).2.2.1.2 ∧
      ((seqRegs m)[i]'hi).2.2.2.2 = ((seqRegs o)[i]'(by omega)).2.2.2.2 ∧
      (declWidth m) ((seqRegs m)[i]'hi).1 = (declWidth o) ((seqRegs o)[i]'(by omega)).1 ∧
      0 < (declWidth m) ((seqRegs m)[i]'hi).1 := by
    intro i hi
    have hp := List.all_eq_true.mp hpairs (((seqRegs m)[i]'hi), ((seqRegs o)[i]'(by omega))) (by
      rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_zip]; omega, by rw [List.getElem_zip]⟩)
    have hp' : ((((seqRegs m)[i]'hi).2.1 == ((seqRegs o)[i]'(by omega : i < (seqRegs o).length)).2.1) &&
        (((seqRegs m)[i]'hi).2.2.1.1 == "rst") &&
        (((seqRegs o)[i]'(by omega : i < (seqRegs o).length)).2.2.1.1 == "rst") &&
        decide (((seqRegs m)[i]'hi).2.2.1.2 = ((seqRegs o)[i]'(by omega : i < (seqRegs o).length)).2.2.1.2) &&
        (((seqRegs m)[i]'hi).2.2.2.2 == ((seqRegs o)[i]'(by omega : i < (seqRegs o).length)).2.2.2.2) &&
        ((declWidth m) ((seqRegs m)[i]'hi).1 == (declWidth o) ((seqRegs o)[i]'(by omega : i < (seqRegs o).length)).1) &&
        decide (0 < (declWidth m) ((seqRegs m)[i]'hi).1)) = true := hp
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp'
    exact ⟨hp'.1.1.1.1.1.1, hp'.1.1.1.1.1.2, hp'.1.1.1.1.2, hp'.1.1.1.2, hp'.1.1.2,
      hp'.1.2, hp'.2⟩
  -- Fitting environments over both reference domains.
  have hinsMfit : ∀ x ∈ (m.inputs.map (·.name) ++ (seqRegs m).map (·.1)), init x < 2 ^ (declWidth m) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hins x hx
    · obtain ⟨r, hr, he⟩ := List.mem_map.mp hx
      exact he ▸ hregs r hr
  have hinNotReg : ∀ x ∈ (m.inputs.map (·.name)), x ∉ (seqRegs o).map (·.1) := by
    intro x hxin hm
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
    have := List.all_eq_true.mp hdisjO r hr
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    have hcon := this.1
    rw [he] at hcon
    rw [List.contains_eq_mem] at hcon
    simp only [decide_eq_false_iff_not] at hcon
    exact hcon hxin
  have hinsOfit : ∀ x ∈ ((m.inputs.map (·.name)).filter (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)), initO x < 2 ^ (declWidth o) x := by
    intro x hx
    rw [hagree x hx]
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨hxin, hwx⟩ := List.mem_filter.mp hx
      have hwx' : (declWidth m) x = (declWidth o) x := by simpa using hwx
      simp only [renOff x (hinNotReg x hxin)]
      rw [← hwx']
      exact hins x hxin
    · obtain ⟨r, hr, he⟩ := List.mem_map.mp hx
      obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
      subst he
      have hrw := renPair i hi
      rw [hri] at hrw
      rw [hrw]
      have hwEq := (hpairAt i (by omega)).2.2.2.2.2.1
      rw [hri] at hwEq
      rw [← hwEq]
      exact hregs _ (List.mem_iff_getElem.mpr ⟨i, by omega, rfl⟩)
  -- Width compatibility of the renaming on the o-side reference domain.
  have hwren : ∀ x ∈ ((m.inputs.map (·.name)).filter (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)), (declWidth o) x = (declWidth m) (renameT (seqSubst m o) x) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨hxin, hwx⟩ := List.mem_filter.mp hx
      rw [renOff x (hinNotReg x hxin)]
      have h1 : (declWidth m) x = (declWidth o) x := by simpa using hwx
      omega
    · obtain ⟨r, hr, he⟩ := List.mem_map.mp hx
      obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
      subst he
      rw [← hri, renPair i hi]
      exact ((hpairAt i (by omega)).2.2.2.2.2.1).symm
  -- Decompose the normal-form half of the check.
  split at h2
  case h_2 => cases h2
  rename_i dm dO hnm hno
  rw [Bool.and_eq_true] at h2
  obtain ⟨houts, hnexts⟩ := h2
  have houtsE := List.all_eq_true.mp houts
  have hnextsE := List.all_eq_true.mp hnexts
  -- Run both normalizations from the fitting initial environments.
  have hd0M : SeqDefsOk (declWidth m) init init [] :=
    ⟨fun x d hx => by simp [List.lookup] at hx, fun _ _ => rfl⟩
  have hd0O : SeqDefsOk (declWidth o) initO initO [] :=
    ⟨fun x d hx => by simp [List.lookup] at hx, fun _ _ => rfl⟩
  obtain ⟨envM, hevM, hdM⟩ :=
    seqNormBody_sound (mems := mems) hinsMfit (seqAssigns m) [] dm init hd0M hnm
  obtain ⟨envO, hevO, hdO⟩ :=
    seqNormBody_sound (mems := mems) hinsOfit (seqAssigns o) [] dO initO hd0O hno
  have hevMfull : evalAssigns (declWidth m) mems m.body init = some envM := by
    rw [evalAssigns_seq_skip hokM]
    exact hevM
  have hevOfull : evalAssigns (declWidth o) mems o.body initO = some envO := by
    rw [evalAssigns_seq_skip hokO]
    exact hevO
  -- Reset stays low through the assign segments.
  have hzMfull : m.body.all (fun st => match st with
      | .assign l _ => l != "rst"
      | _ => true) = true := by
    rw [List.all_eq_true]
    intro st hst
    cases st with
    | assign l r => exact List.all_eq_true.mp hzM _ (List.mem_filter.mpr ⟨hst, rfl⟩)
    | register o c rk i iv => rfl
    | memory n aw dw md wa wd wen ra rd ep ew rp => rfl
    | inst n mn conns => rfl
  have hzOfull : o.body.all (fun st => match st with
      | .assign l _ => l != "rst"
      | _ => true) = true := by
    rw [List.all_eq_true]
    intro st hst
    cases st with
    | assign l r => exact List.all_eq_true.mp hzO _ (List.mem_filter.mpr ⟨hst, rfl⟩)
    | register o c rk i iv => rfl
    | memory n aw dw md wa wd wen ra rd ep ew rp => rfl
    | inst n mn conns => rfl
  have hrstM : envM "rst" = 0 := by
    rw [evalAssigns_keeps "rst" hokM hzMfull hevMfull]
    exact hrst
  have hrstOF : envO "rst" = 0 := by
    rw [evalAssigns_keeps "rst" hokO hzOfull hevOfull]
    exact hrstO
  have hif : ¬((0 : Nat) ≠ 0) := fun h => h rfl
  -- Output correspondence.
  have houtCorr : ∀ p ∈ m.outputs, envO p.name = envM p.name := by
    intro p hp
    have h := houtsE p hp
    have h' : (match dm.lookup p.name, dO.lookup p.name with
        | some em, some eo =>
          decide (em = renameRefsT (seqSubst m o) eo) &&
            (refsOf em).all (fun x => (m.inputs.map (·.name) ++ (seqRegs m).map (·.1)).contains x) &&
            (refsOf eo).all (fun x => ((m.inputs.map (·.name)).filter (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)).contains x)
        | _, _ => false) = true := h
    split at h'
    case h_2 => cases h'
    rename_i em eo hem heo
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨hren, hrefsM⟩, hrefsO⟩ := h'
    obtain ⟨hsM, hvM⟩ := hdM.1 p.name em hem
    obtain ⟨hsO, hvO⟩ := hdO.1 p.name eo heo
    have hcompat : ∀ x ∈ refsOf eo, (declWidth o) x = (declWidth m) (renameT (seqSubst m o) x) := by
      intro x hx
      apply hwren
      have := List.all_eq_true.mp hrefsO x hx
      simpa [List.contains_eq_mem] using this
    have hbr := evalExpr_renameT (subst := seqSubst m o) (weM := (declWidth m)) (init := init)
      hsO hcompat
    rw [hren, hbr] at hvM
    have hcongr : evalExpr (declWidth o) initO eo =
        evalExpr (declWidth o) (fun x => init (renameT (seqSubst m o) x)) eo := by
      apply Sparkle.IR.Reorder.evalExpr_congr
      intro n hn
      apply hagree
      have := List.all_eq_true.mp hrefsO n hn
      simpa [List.contains_eq_mem] using this
    rw [← hcongr, hvO] at hvM
    exact Option.some.inj hvM
  -- Paired register next-values agree.
  have hregNext : ∀ i (hi : i < (seqRegs m).length),
      evalExpr (declWidth m) envM (((seqRegs m)[i]'hi).2.2.2.1) =
        some ((evalExpr (declWidth m) envM (((seqRegs m)[i]'hi).2.2.2.1)).getD 0) ∧
      evalExpr (declWidth o) envO (((seqRegs o)[i]'(by omega)).2.2.2.1) =
        some ((evalExpr (declWidth o) envO (((seqRegs o)[i]'(by omega)).2.2.2.1)).getD 0) ∧
      (evalExpr (declWidth m) envM (((seqRegs m)[i]'hi).2.2.2.1)).getD 0 =
        (evalExpr (declWidth o) envO (((seqRegs o)[i]'(by omega)).2.2.2.1)).getD 0 := by
    intro i hi
    have hn := hnextsE (((seqRegs m)[i]'hi), ((seqRegs o)[i]'(by omega))) (by
      rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_zip]; omega, by rw [List.getElem_zip]⟩)
    have hn' : (match seqNormE (declWidth m) (m.inputs.map (·.name) ++ (seqRegs m).map (·.1)) dm (((seqRegs m)[i]'hi).2.2.2.1),
        seqNormE (declWidth o) ((m.inputs.map (·.name)).filter (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)) dO (((seqRegs o)[i]'(by omega : i < (seqRegs o).length)).2.2.2.1) with
        | some fm, some fo =>
          decide (fm = renameRefsT (seqSubst m o) fo) &&
            (refsOf fm).all (fun x => (m.inputs.map (·.name) ++ (seqRegs m).map (·.1)).contains x) &&
            (refsOf fo).all (fun x => ((m.inputs.map (·.name)).filter (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)).contains x)
        | _, _ => false) = true := hn
    split at hn'
    case h_2 => cases hn'
    rename_i fm fo hfm hfo
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hn'
    obtain ⟨⟨hrenf, hrefsM⟩, hrefsO⟩ := hn'
    obtain ⟨hsFm, hwFm, vM, hevalMr, hevalMf⟩ :=
      seqNormE_sound hdM hinsMfit (((seqRegs m)[i]'hi).2.2.2.1) fm hfm
    obtain ⟨hsFo, hwFo, vO, hevalOr, hevalOf⟩ :=
      seqNormE_sound hdO hinsOfit (((seqRegs o)[i]'(by omega : i < (seqRegs o).length)).2.2.2.1) fo hfo
    have hcompat : ∀ x ∈ refsOf fo, (declWidth o) x = (declWidth m) (renameT (seqSubst m o) x) := by
      intro x hx
      apply hwren
      have := List.all_eq_true.mp hrefsO x hx
      simpa [List.contains_eq_mem] using this
    have hbr := evalExpr_renameT (subst := seqSubst m o) (weM := (declWidth m)) (init := init)
      hsFo hcompat
    rw [hrenf, hbr] at hevalMf
    have hcongrF : evalExpr (declWidth o) initO fo =
        evalExpr (declWidth o) (fun x => init (renameT (seqSubst m o) x)) fo := by
      apply Sparkle.IR.Reorder.evalExpr_congr
      intro n hn
      apply hagree
      have := List.all_eq_true.mp hrefsO n hn
      simpa [List.contains_eq_mem] using this
    rw [← hcongrF, hevalOf] at hevalMf
    have hvals : vM = vO := (Option.some.inj hevalMf).symm
    refine ⟨?_, ?_, ?_⟩
    · rw [hevalMr]
      rfl
    · rw [hevalOr]
      rfl
    · rw [hevalMr, hevalOr]
      simpa using hvals
  -- The register nexts, as explicit maps.
  have hfoldM : seqRegsL m.body = seqRegs m := (seqRegs_eq m).symm
  have hfoldO : seqRegsL o.body = seqRegs o := (seqRegs_eq o).symm
  have hvMall : ∀ r ∈ seqRegsL m.body, evalExpr (declWidth m) envM r.2.2.2.1 =
      some ((evalExpr (declWidth m) envM r.2.2.2.1).getD 0) := by
    intro r hr
    have hr' : r ∈ (seqRegs m) := hfoldM ▸ hr
    obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr'
    rw [← hri]
    exact (hregNext i hi).1
  have hvOall : ∀ r ∈ seqRegsL o.body, evalExpr (declWidth o) envO r.2.2.2.1 =
      some ((evalExpr (declWidth o) envO r.2.2.2.1).getD 0) := by
    intro r hr
    have hr' : r ∈ (seqRegs o) := hfoldO ▸ hr
    obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr'
    rw [← hri]
    exact (hregNext i (by omega)).2.1
  have hnM := regNexts_seq_map (we := (declWidth m)) (mems := mems) (envF := envM)
    (f := fun e => (evalExpr (declWidth m) envM e).getD 0) hokM hvMall
  have hnO := regNexts_seq_map (we := (declWidth o)) (mems := mems) (envF := envO)
    (f := fun e => (evalExpr (declWidth o) envO e).getD 0) hokO hvOall
  rw [hfoldM] at hnM
  rw [hfoldO] at hnO
  have hmemM := memNexts_seqStmtOk (we := (declWidth m)) (mems := mems) (envF := envM) hokM
  have hmemO := memNexts_seqStmtOk (we := (declWidth o)) (mems := mems) (envF := envO) hokO
  refine ⟨envM, envO,
    (seqRegs m).map (fun r => (r.1, if envM r.2.2.1.1 ≠ 0 then encodeInit r.2.2.2.2 ((declWidth m) r.1)
      else mask ((declWidth m) r.1) ((evalExpr (declWidth m) envM r.2.2.2.1).getD 0))),
    (seqRegs o).map (fun r => (r.1, if envO r.2.2.1.1 ≠ 0 then encodeInit r.2.2.2.2 ((declWidth o) r.1)
      else mask ((declWidth o) r.1) ((evalExpr (declWidth o) envO r.2.2.2.1).getD 0))),
    ?_, ?_, houtCorr, ?_, ?_, ?_, ?_⟩
  · simp only [stepModule, hevMfull, hnM, hmemM, Option.bind_eq_bind, Option.bind_some]
  · simp only [stepModule, hevOfull, hnO, hmemO, Option.bind_eq_bind, Option.bind_some]
  · rw [List.map_map]
    rfl
  · rw [List.map_map]
    rfl
  · apply List.ext_getElem
    · simp only [List.length_map]
      omega
    · intro i h1i h2i
      have hi : i < (seqRegs m).length := by
        simp only [List.length_map] at h1i
        exact h1i
      simp only [List.getElem_map]
      obtain ⟨hcEq, hkM1, hkO1, hkind, hinit, hwEq, hwPos⟩ := hpairAt i hi
      rw [hkM1, hkO1, hrstM, hrstOF, if_neg hif, if_neg hif]
      rw [← hwEq, (hregNext i hi).2.2]
  · intro pr hpr
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hpr
    obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
    subst he
    obtain ⟨hcEq, hkM1, hkO1, hkind, hinit, hwEq, hwPos⟩ := hpairAt i hi
    show (if envM r.2.2.1.1 ≠ 0 then encodeInit r.2.2.2.2 ((declWidth m) r.1)
      else mask ((declWidth m) r.1) ((evalExpr (declWidth m) envM r.2.2.2.1).getD 0)) < 2 ^ (declWidth m) r.1
    rw [← hri, hkM1, hrstM, if_neg hif]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-! ## Trace equivalence -/

/-- With nodup names, `find?` at the i-th name returns the i-th entry. -/
theorem find?_nodup_at :
    ∀ (nexts : List (String × Nat)), ((nexts.map (·.1)).Nodup) →
      ∀ (i : Nat) (hi : i < nexts.length),
        nexts.find? (fun p => p.1 == (nexts[i]'hi).1) = some (nexts[i]'hi)
  | (k, v) :: rest, _, 0, hi => by
    rw [List.find?_cons_of_pos (by simp)]
    rfl
  | (k, v) :: rest, hnd, i + 1, hi => by
    have hnd' : (rest.map (·.1)).Nodup := by
      simp only [List.map_cons, List.nodup_cons] at hnd
      exact hnd.2
    have hk : k ∉ rest.map (·.1) := by
      simp only [List.map_cons, List.nodup_cons] at hnd
      exact hnd.1
    have hi' : i < rest.length := by simpa using hi
    have hne : (k == ((rest[i]'hi').1)) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      exact hk (by
        rw [he]
        exact List.mem_map.mpr ⟨rest[i]'hi', List.getElem_mem hi', rfl⟩)
    rw [List.find?_cons_of_neg (by simp [hne])]
    exact find?_nodup_at rest hnd' i hi'

/-- Applying a nodup update list at its i-th name yields the i-th value. -/
theorem applyNexts_at {st : String → Nat} {nexts : List (String × Nat)}
    (hnd : (nexts.map (·.1)).Nodup) (i : Nat) (hi : i < nexts.length) :
    applyNexts st nexts ((nexts[i]'hi).1) = (nexts[i]'hi).2 := by
  simp only [applyNexts, find?_nodup_at nexts hnd i hi]

/-- The canonical seeding discipline: inputs from a stream, everything
else read from the register state. -/
def seedIn (m : Module) (ins : Nat → String → Nat) :
    Nat → (String → Nat) → Env :=
  fun t st n => if (m.inputs.map (·.name)).contains n then ins t n else st n

open Sparkle.IR.RegDedup (declWidth) in
set_option maxHeartbeats 2000000 in
/-- **Accepted pairs are trace-equivalent.** Under the canonical seeding
from any fitting input stream that holds reset low, and from any pair of
register states equal across the pairing (with the `m` state
width-bounded), both modules run for `k` cycles and their output streams
coincide, cycle for cycle. -/
theorem seqOptCheck_run_sound {m o : Sparkle.IR.AST.Module}
    (hchk : seqOptCheck m o = true) (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    (hrstIn : "rst" ∈ m.inputs.map (·.name))
    (hrstZ : ∀ t, ins t "rst" = 0) :
    ∀ (k : Nat) (stM stO : String → Nat) (mems : MEnv),
      (∀ pr ∈ (seqRegs m).zip (seqRegs o), stO pr.2.1 = stM pr.1.1) →
      (∀ r ∈ seqRegs m, stM r.1 < 2 ^ declWidth m r.1) →
      ∃ trM trO,
        runModule (declWidth m) m.body (seedIn m ins) k stM mems = some trM ∧
        runModule (declWidth o) o.body (seedIn m ins) k stO mems = some trO ∧
        ∀ p ∈ m.outputs, trO.map (fun e => e p.name) = trM.map (fun e => e p.name) := by
  intro k
  induction k with
  | zero =>
    intro stM stO mems hcpl hfit
    exact ⟨[], [], rfl, rfl, fun p _ => rfl⟩
  | succ k ih =>
    intro stM stO mems hcpl hfit
    have hstat := hchk
    simp only [seqOptCheck] at hstat
    rw [Bool.and_eq_true] at hstat
    obtain ⟨h1, -⟩ := hstat
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hinEq⟩, houtEq⟩, hokM⟩, hokO⟩, hndM⟩, hndO⟩, hdisjM⟩,
      hdisjO⟩, hzM⟩, hzO⟩, hpairs⟩ := h1
    have hcontains : ∀ x ∈ m.inputs.map (·.name),
        ((m.inputs.map (·.name)).contains x) = true := by
      intro x hx
      simpa [List.contains_eq_mem] using hx
    have hnotInM : ∀ r ∈ seqRegs m,
        ((m.inputs.map (·.name)).contains r.1) = false := by
      intro r hr
      have hd := List.all_eq_true.mp hdisjM r hr
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
      exact hd.1
    have hnotInO : ∀ r ∈ seqRegs o,
        ((m.inputs.map (·.name)).contains r.1) = false := by
      intro r hr
      have hd := List.all_eq_true.mp hdisjO r hr
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
      exact hd.1
    have hinsE : ∀ x ∈ m.inputs.map (·.name),
        seedIn m ins k stM x < 2 ^ declWidth m x := by
      intro x hx
      simp only [seedIn]
      rw [if_pos (hcontains x hx)]
      exact hinsFit k x hx
    have hregsE : ∀ r ∈ seqRegs m,
        seedIn m ins k stM r.1 < 2 ^ declWidth m r.1 := by
      intro r hr
      simp only [seedIn]
      rw [if_neg (by rw [hnotInM r hr]; exact Bool.false_ne_true)]
      exact hfit r hr
    have hrstE : seedIn m ins k stM "rst" = 0 := by
      simp only [seedIn]
      rw [if_pos (hcontains _ hrstIn)]
      exact hrstZ k
    have hrstOE : seedIn m ins k stO "rst" = 0 := by
      simp only [seedIn]
      rw [if_pos (hcontains _ hrstIn)]
      exact hrstZ k
    have hagreeE : ∀ x ∈ ((m.inputs.map (·.name)).filter
        (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)),
        seedIn m ins k stO x = seedIn m ins k stM (renameT (seqSubst m o) x) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨hxin, -⟩ := List.mem_filter.mp hx
        have hxO : x ∉ (seqRegs o).map (·.1) := by
          intro hm
          obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
          have hc := hnotInO r hr
          rw [he] at hc
          rw [List.contains_eq_mem] at hc
          simp only [decide_eq_false_iff_not] at hc
          exact hc hxin
        rw [seqSubst_off hlen x hxO]
        simp only [seedIn]
        rw [if_pos (hcontains x hxin), if_pos (hcontains x hxin)]
      · obtain ⟨r, hr, he⟩ := List.mem_map.mp hx
        obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
        subst he
        rw [← hri, seqSubst_pair hlen hndO i hi]
        simp only [seedIn]
        rw [if_neg (by rw [hnotInO _ (List.getElem_mem hi)]; exact Bool.false_ne_true),
          if_neg (by
            rw [hnotInM _ (List.getElem_mem (by omega : i < (seqRegs m).length))]
            exact Bool.false_ne_true)]
        exact hcpl (((seqRegs m)[i]'(by omega)), ((seqRegs o)[i]'hi)) (by
          rw [List.mem_iff_getElem]
          exact ⟨i, by rw [List.length_zip]; omega, by rw [List.getElem_zip]⟩)
    obtain ⟨envM, envO, nextsM, nextsO, hstepM, hstepO, hout, hnmM, hnmO, hvals, hbnd⟩ :=
      seqOptCheck_step_sound hchk (mems := mems) hinsE hregsE hrstE hagreeE hrstOE
    have hlenM : nextsM.length = (seqRegs m).length := by
      have := congrArg List.length hnmM
      simpa using this
    have hlenO : nextsO.length = (seqRegs o).length := by
      have := congrArg List.length hnmO
      simpa using this
    have hndM' : (nextsM.map (·.1)).Nodup := by rw [hnmM]; exact hndM
    have hndO' : (nextsO.map (·.1)).Nodup := by rw [hnmO]; exact hndO
    have hnameM : ∀ i (hi : i < (seqRegs m).length),
        ((nextsM[i]'(by omega)).1) = (((seqRegs m)[i]'hi).1) := by
      intro i hi
      have h1 := List.getElem_of_eq hnmM
        (by simp only [List.length_map]; omega : i < (nextsM.map (·.1)).length)
      simpa using h1
    have hnameO : ∀ i (hi : i < (seqRegs o).length),
        ((nextsO[i]'(by omega)).1) = (((seqRegs o)[i]'hi).1) := by
      intro i hi
      have h1 := List.getElem_of_eq hnmO
        (by simp only [List.length_map]; omega : i < (nextsO.map (·.1)).length)
      simpa using h1
    have hvalEq : ∀ i (hi : i < nextsM.length),
        (nextsM[i]'hi).2 = (nextsO[i]'(by omega)).2 := by
      intro i hi
      have h1 := List.getElem_of_eq hvals
        (by simp only [List.length_map]; omega : i < (nextsM.map (·.2)).length)
      simpa using h1
    have hcpl' : ∀ pr ∈ (seqRegs m).zip (seqRegs o),
        applyNexts stO nextsO pr.2.1 = applyNexts stM nextsM pr.1.1 := by
      intro pr hpr
      obtain ⟨i, hzi, hzri⟩ := List.mem_iff_getElem.mp hpr
      rw [List.getElem_zip] at hzri
      subst hzri
      have hi : i < (seqRegs m).length := by rw [List.length_zip] at hzi; omega
      have hiO : i < (seqRegs o).length := by omega
      show applyNexts stO nextsO (((seqRegs o)[i]'hiO).1) =
        applyNexts stM nextsM (((seqRegs m)[i]'hi).1)
      rw [← hnameO i hiO, ← hnameM i hi]
      rw [applyNexts_at hndO' i (by omega), applyNexts_at hndM' i (by omega)]
      rw [hvalEq i (by omega)]
    have hfit' : ∀ r ∈ seqRegs m,
        applyNexts stM nextsM r.1 < 2 ^ declWidth m r.1 := by
      intro r hr
      obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
      rw [← hri, ← hnameM i hi, applyNexts_at hndM' i (by omega)]
      exact hbnd _ (List.getElem_mem _)
    obtain ⟨trM', trO', hrunM', hrunO', houts'⟩ :=
      ih (applyNexts stM nextsM) (applyNexts stO nextsO) mems hcpl' hfit'
    refine ⟨envM :: trM', envO :: trO', ?_, ?_, ?_⟩
    · simp only [runModule, hstepM, Option.bind_eq_bind, Option.bind_some, hrunM']
    · simp only [runModule, hstepO, Option.bind_eq_bind, Option.bind_some, hrunO']
    · intro p hp
      simp only [List.map_cons]
      rw [hout p hp, houts' p hp]

end Tools.ShippingSeqOptSoundness
