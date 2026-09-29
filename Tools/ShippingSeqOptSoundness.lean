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

end Tools.ShippingSeqOptSoundness
