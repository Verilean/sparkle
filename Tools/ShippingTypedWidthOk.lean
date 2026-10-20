import Tools.ShippingHierTyped
import Tools.ShippingTextTyped

/-! # `TypedExpr → widthOk`, and the typed assignment of the IR-side width typing (G1, round par/a-7; T1, T2 of docs/parallel/A-oneout.md)

`hierTyped` (`Tools/ShippingHierTyped.lean`) asks of every assignment
`l := r` of a module `assignTyped W X l r`:

    avoids X r && Tools.ConeFold.widthOk W r && (X.contains l || widthOf W r == W l)

(`X` the output ports' names, `W` the declared widths). The typing the
compiler's proofs carry is `TypedExpr we r n`
(`Tools/ShippingTypedExprSoundness.lean`). This file relates the two — pure,
no run:

* `typed_widthOk` (T1): `TypedExpr we e n → widthOk we e = true`, for EVERY
  constructor of `TypedExpr`. `widthOk`'s only refusal is a `mux` whose false
  arm is wider than its true arm; `TypedExpr.mux` has both arms at one width.
  FINDING: none — no constructor of `TypedExpr` is refused by `widthOk`.
* `assignTyped_of_typed` (T2 and the rest of `assignTyped`): a typed
  right-hand side, a table that is `0` on `X`, and a target of the typed
  width or in `X`.
* `weOf_not_wire`: a name no wire has is `0` in the wire table.
* `typedIn_assignTyped`: every assignment of a module typed in its own wire
  table (`TypedIn`, what `core_closed_typedIn` gives of a parent) is
  `assignTyped (declWidth m) (outputs' names)`.
* `lookup_of_forall`, `kidsTyped_of`, `connsTyped_call`: `kidsTyped` and
  `connsTyped` from statement-wise facts, the second for the connection list
  of a one-output call (`callStmt_parts`' description of it).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingTypedWidthOk
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingTypedExprSoundness (TypedExpr)
open Tools.ConeFold (widthOk widthOkL muxArmOk)
open Tools.ShippingHierTyped (assignTyped avoids childTyped connsTyped kidsTyped)

/-- A two-operand node passes the mux arm test whatever its operator. -/
theorem muxArmOk_two (we : WEnv) (o : Operator) (a b : Sparkle.IR.AST.Expr) :
    muxArmOk we o [a, b] = true := by
  cases o <;> rfl

/-- A one-operand node passes the mux arm test whatever its operator. -/
theorem muxArmOk_one (we : WEnv) (o : Operator) (a : Sparkle.IR.AST.Expr) :
    muxArmOk we o [a] = true := by
  cases o <;> rfl

/-- **A typed expression is width-consistent** (T1). -/
theorem typed_widthOk {we : WEnv} {e : Sparkle.IR.AST.Expr} {n : Nat}
    (h : TypedExpr we e n) : widthOk we e = true := by
  induction h with
  | ref x hn => simp [widthOk]
  | const v n hn => simp [widthOk]
  | bin op _ _ _ iha ihb => simp [widthOk, widthOkL, muxArmOk_two, iha, ihb]
  | compare _ _ _ iha ihb => simp [widthOk, widthOkL, muxArmOk_two, iha, ihb]
  | signedCompare a b _ _ _ => simp [widthOk, widthOkL, muxArmOk_two]
  | mux hc ht hf ihc iht ihf =>
    simp [widthOk, widthOkL, muxArmOk, ihc, iht, ihf, ht.width, hf.width]
  | zext x k hk hx => simp [widthOk, widthOkL]
  | trunc x w hw hwx => simp [widthOk, widthOkL]
  | slice x hi lo hle hhi => simp [widthOk]
  | cat a b ha hb => simp [widthOk, widthOkL]
  | not1 x hx => simp [widthOk, widthOkL, muxArmOk_one]

/-- A name not in a list fails `contains`. -/
theorem not_contains {X : List String} {x : String} (h : x ∉ X) : (!X.contains x) = true := by
  first
    | exact Bool.not_eq_true'.mpr
        (Bool.eq_false_iff.mpr (fun hc => h (List.contains_iff_mem.mp hc)))
    | simpa using h

/-- **A typed assignment is `assignTyped`** (T2 with the other two
conjuncts): the right-hand side reads no name of `X` (a typed reference has
a positive table width, the table is `0` on `X`), is width-consistent
(`typed_widthOk`), and has its target's width unless the target is in `X`. -/
theorem assignTyped_of_typed {we : WEnv} {X : List String} {l : String}
    {r : Sparkle.IR.AST.Expr} {n : Nat}
    (ht : TypedExpr we r n) (hX : ∀ x ∈ X, we x = 0) (hl : we l = n ∨ l ∈ X) :
    assignTyped we X l r = true := by
  unfold Tools.ShippingHierTyped.assignTyped
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, typed_widthOk ht⟩, ?_⟩
  · unfold Tools.ShippingHierTyped.avoids
    rw [List.all_eq_true]
    intro x hx
    have hp := ht.refs_positive x hx
    have hnx : x ∉ X := by
      intro hxX
      rw [hX x hxX] at hp
      exact Nat.lt_irrefl 0 hp
    exact not_contains hnx
  · rw [Bool.or_eq_true]
    rcases hl with h1 | h1
    · right
      rw [ht.width, h1]
      exact beq_self_eq_true n
    · left
      exact List.contains_iff_mem.mpr h1

/-- A name no wire has is `0` in the wire table. -/
theorem weOf_not_wire {m : Sparkle.IR.AST.Module} {x : String}
    (h : ∀ p ∈ m.wires, p.name ≠ x) : Tools.ShippingEntrySoundness.weOf m x = 0 := by
  have hf : m.wires.find? (fun p => p.name == x) = none :=
    List.find?_eq_none.mpr (fun p hp hb => h p hp (beq_iff_eq.mp hb))
  first
    | (unfold Tools.ShippingEntrySoundness.weOf
       rw [hf])
    | simp [Tools.ShippingEntrySoundness.weOf, hf]

/-- **Every assignment of a module typed in its own wire table is
`assignTyped`** in the IR's declared widths, off its output ports. -/
theorem typedIn_assignTyped {m : Sparkle.IR.AST.Module}
    (h : Tools.ShippingTextTyped.TypedIn m) {l : String} {r : Sparkle.IR.AST.Expr}
    (hm : Stmt.assign l r ∈ m.body) :
    assignTyped (Sparkle.IR.RegDedup.declWidth m) (m.outputs.map (·.name)) l r = true := by
  have hW : Sparkle.IR.RegDedup.declWidth m = Tools.ShippingEntrySoundness.weOf m := rfl
  rw [hW]
  obtain ⟨n, ht, hl⟩ := h.asg l r hm
  refine assignTyped_of_typed ht ?_ ?_
  · intro x hx
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hx
    have hqn' : q.name = x := hqn
    exact weOf_not_wire (fun p hp e => h.ow q hq p hp (e.trans hqn'.symm))
  · rcases hl with h1 | ⟨q, hq, hqn, -⟩
    · exact Or.inl h1
    · exact Or.inr (List.mem_map.mpr ⟨q, hq, hqn⟩)

/-- The first entry of a key whose every entry has one value. -/
theorem lookup_of_forall {k : String} {v : Sparkle.IR.AST.Expr} :
    ∀ (l : List (String × Sparkle.IR.AST.Expr)), (k, v) ∈ l →
      (∀ c ∈ l, c.1 = k → c.2 = v) → l.lookup k = some v
  | [], hmem, _ => by cases hmem
  | (k', v') :: rest, hmem, hu => by
    rw [List.lookup_cons]
    by_cases hk : k = k'
    · have hv : v' = v := hu (k', v') (List.mem_cons_self ..) hk.symm
      have hb : (k == k') = true := by
        rw [hk]
        exact beq_self_eq_true k'
      rw [hb, hv]
    · have hb : (k == k') = false := by
        first
          | exact beq_eq_false_iff_ne.mpr hk
          | simpa using hk
      rw [hb]
      show rest.lookup k = some v
      refine lookup_of_forall rest ?_ (fun c hc => hu c (List.mem_cons_of_mem _ hc))
      rcases List.mem_cons.mp hmem with h | h
      · exact absurd (congrArg Prod.fst h) hk
      · exact h

/-- `false = true` proves anything. -/
theorem ff_absurd' {Q : Prop} (h : false = true) : Q := by
  cases h

/-- **`kidsTyped` from statement-wise facts.** -/
theorem kidsTyped_of {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {W : WEnv}
    {Xp : List String} {body : List Stmt}
    (ha : ∀ l r, Stmt.assign l r ∈ body → assignTyped W Xp l r = true)
    (hi : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
      ∃ child cwe, C mn = some (child, cwe) ∧ childTyped cwe child = true ∧
        connsTyped W Xp child cwe conns = true)
    (hk : ∀ st ∈ body, Tools.ShippingHierSVSoundness.seqStmtOkI st = true) :
    kidsTyped C W Xp body = true := by
  unfold Tools.ShippingHierTyped.kidsTyped
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | assign l r => exact ha l r hst
  | inst mn iname conns =>
    obtain ⟨child, cwe, hc, h1, h2⟩ := hi mn iname conns hst
    simp [hc, h1, h2]
  | register => rfl
  | memory => exact ff_absurd' (hk _ hst)

/-- **`connsTyped` of a one-output call's connection list**: the list is the
output connection and input connections whose port is not the output's
(`Tools.ShippingOneOutClose.callStmt_parts`); each input connection reads a
parent wire off `Xp` no wider than the child's port; the output connection
drives a wire of `Xp` or one at least as wide as the port. -/
theorem connsTyped_call {W : WEnv} {Xp : List String} {mc : Sparkle.IR.AST.Module}
    {cwe : WEnv} {conns : List (String × Sparkle.IR.AST.Expr)} {outW : String}
    {argWs : List String} {outP : Port}
    (houts : mc.outputs = [outP])
    (hall : ∀ c ∈ conns, c = (outP.name, Sparkle.IR.AST.Expr.ref outW) ∨
      ∃ q ∈ mc.inputs, ∃ aw ∈ argWs,
        c = (q.name, Sparkle.IR.AST.Expr.ref aw) ∧ q.name ≠ outP.name)
    (hmem : (outP.name, Sparkle.IR.AST.Expr.ref outW) ∈ conns)
    (hin : ∀ pn aw, (pn, Sparkle.IR.AST.Expr.ref aw) ∈ conns → pn ≠ outP.name →
      aw ∉ Xp ∧ W aw ≤ cwe pn)
    (hout : outW ∈ Xp ∨ outP.ty.bitWidth ≤ W outW) :
    connsTyped W Xp mc cwe conns = true := by
  unfold Tools.ShippingHierTyped.connsTyped
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro c hc
    rw [Bool.or_eq_true]
    rcases hall c hc with e | ⟨q, hq, aw, haw, e, hne⟩
    · left
      rw [e, houts]
      exact List.contains_iff_mem.mpr (List.mem_singleton.mpr rfl)
    · right
      have hc' : (q.name, Sparkle.IR.AST.Expr.ref aw) ∈ conns := by
        rw [← e]
        exact hc
      obtain ⟨hx, hle⟩ := hin q.name aw hc' hne
      rw [e]
      show (!Xp.contains aw && decide (W aw ≤ cwe q.name)) = true
      rw [Bool.and_eq_true]
      exact ⟨not_contains hx, decide_eq_true hle⟩
  · rw [houts, List.all_eq_true]
    intro p hp
    have hpe : p = outP := List.mem_singleton.mp hp
    rw [hpe]
    have hl : conns.lookup outP.name = some (Sparkle.IR.AST.Expr.ref outW) := by
      refine lookup_of_forall conns hmem ?_
      intro c hc hck
      rcases hall c hc with e | ⟨q, -, aw, -, e, hne⟩
      · rw [e]
      · exact absurd ((congrArg Prod.fst e).symm.trans hck) hne
    rw [hl]
    show (Xp.contains outW || decide (outP.ty.bitWidth ≤ W outW)) = true
    rw [Bool.or_eq_true]
    rcases hout with h | h
    · left
      exact List.contains_iff_mem.mpr h
    · right
      exact decide_eq_true h

end Tools.ShippingTypedWidthOk
