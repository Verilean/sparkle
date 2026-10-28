import Tools.ShippingKidsResetSat
import Tools.ShippingMergeKeepsBridge
set_option autoImplicit false
-- BUILT (unit SRM17): dev runs b6 (Body with Ran/Corr/ParentTest) exit 0; the final-SHA rebuild in REPORT-SRM17.md is the only final evidence.
-- SCOPE: PURE statement-list facts (no compiler run) for the three structural facts `IUb`/`Agb`/`Rdb` (the bodies of SRM16's `hIU`/`hAg`/`hRd` binders, per module) and their conjunction `ModP`:
-- * `modP_of_nodups`: distinct instance names + distinct register names + no memory statement give `ModP` of a body;
-- * `modP_of_perm`: a permutation of such a body keeps the three distinctness facts;
-- * `modP_mergeChecked`: `ModP X → ModP (mergeChecked X)` (the merge's body is the body or `body.map (rewriteStmt s)`, which keeps instance names, register names/inits and memory read-register names).
-- No `sorry`, no `axiom`, no `native_decide`.  Nothing here mentions a compiler run: PROVED statements about statement lists.
namespace Tools.ShippingSrm17Body
open Sparkle.IR.AST
open Tools.ShippingHierState (instNames)
open Tools.ShippingKidsResetSat (instAgree_of_nodup)
open Tools.ShippingMergeKeeps (rewriteStmt)

/-- instance names determine module names (the body of the `hIU`/`hIUraw` binder) -/
def IUb (body : List Stmt) : Prop :=
  ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
    Stmt.inst mn i c ∈ body → Stmt.inst mn' i c' ∈ body → mn = mn'

/-- same-name registers have equal `init.toNat` (the body of the `hAg` binder) -/
def Agb (body : List Stmt) : Prop :=
  ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
    Stmt.register r c rs inp init ∈ body → Stmt.register r c' rs' inp' init' ∈ body → init.toNat = init'.toNat

/-- a register named like a memory's read register has `init.toNat = 0` (the body of the `hRd` binder) -/
def Rdb (body : List Stmt) : Prop :=
  ∀ nm aw dw c wa wd we ra rd cr ew er,
    Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ body →
    ∀ c' rs' inp' (init' : Int), Stmt.register rd c' rs' inp' init' ∈ body → init'.toNat = 0

/-- the three facts of one module -/
def ModP (m : Module) : Prop := IUb m.body ∧ Agb m.body ∧ Rdb m.body

theorem ModP.iu {m : Module} (h : ModP m) : IUb m.body := h.1
theorem ModP.ag {m : Module} (h : ModP m) : Agb m.body := h.2.1
theorem ModP.rd {m : Module} (h : ModP m) : Rdb m.body := h.2.2

/-- no memory statement -/
def NoMemB (body : List Stmt) : Prop :=
  ∀ nm aw dw c wa wd we ra rd cr ew er, Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∉ body

/-- the output names of the register statements, in order -/
def regNames : List Stmt → List String
  | [] => []
  | .register o _ _ _ _ :: rest => o :: regNames rest
  | _ :: rest => regNames rest

theorem regNames_eq (l : List Stmt) : regNames l = l.filterMap (fun st => match st with
    | .register o _ _ _ _ => some o
    | _ => none) := by
  induction l with
  | nil => rfl
  | cons st rest ih => cases st <;> simp [regNames, ih]

theorem regNames_perm {l l' : List Stmt} (h : l.Perm l') : (regNames l).Perm (regNames l') := by
  rw [regNames_eq, regNames_eq]
  exact h.filterMap _

theorem mem_regNames : ∀ (body : List Stmt) (r : String) (c : String) (rs : String × Sparkle.IR.Type.ResetKind)
    (inp : Expr) (init : Int), Stmt.register r c rs inp init ∈ body → r ∈ regNames body
  | [], _, _, _, _, _, h => by cases h
  | st :: rest, r, c, rs, inp, init, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h; simp [regNames]
    · have := mem_regNames rest r c rs inp init h
      cases st <;> simp [regNames, this]

theorem agb_of_nodup : ∀ (body : List Stmt), (regNames body).Nodup → Agb body
  | [] => by intro _ r c rs inp init c' rs' inp' init' h; cases h
  | st :: rest => by
    intro hnd r c rs inp init c' rs' inp' init' h1 h2
    have ih := agb_of_nodup rest (by cases st <;> first | exact hnd | exact (List.nodup_cons.mp hnd).2)
    cases st with
    | register o cl rs0 inp0 init0 =>
      have hnd' : (o :: regNames rest).Nodup := hnd
      rw [List.nodup_cons] at hnd'
      rcases List.mem_cons.mp h1 with e1 | e1 <;> rcases List.mem_cons.mp h2 with e2 | e2
      · rw [Stmt.register.inj e1 |>.2.2.2.2, Stmt.register.inj e2 |>.2.2.2.2]
      · exfalso
        have hr : r = o := (Stmt.register.inj e1).1
        rw [hr] at e2
        exact hnd'.1 (mem_regNames rest o c' rs' inp' init' e2)
      · exfalso
        have hr : r = o := (Stmt.register.inj e2).1
        rw [hr] at e1
        exact hnd'.1 (mem_regNames rest o c rs inp init e1)
      · exact ih r c rs inp init c' rs' inp' init' e1 e2
    | assign a b =>
      exact ih r c rs inp init c' rs' inp' init'
        ((List.mem_cons.mp h1).resolve_left (by intro e; cases e))
        ((List.mem_cons.mp h2).resolve_left (by intro e; cases e))
    | memory nm aw dw cl wa wd wen ra rd cr ew er =>
      exact ih r c rs inp init c' rs' inp' init'
        ((List.mem_cons.mp h1).resolve_left (by intro e; cases e))
        ((List.mem_cons.mp h2).resolve_left (by intro e; cases e))
    | inst mn i cn =>
      exact ih r c rs inp init c' rs' inp' init'
        ((List.mem_cons.mp h1).resolve_left (by intro e; cases e))
        ((List.mem_cons.mp h2).resolve_left (by intro e; cases e))

theorem rdb_of_noMem {body : List Stmt} (h : NoMemB body) : Rdb body :=
  fun nm aw dw c wa wd we ra rd cr ew er hm => absurd hm (h nm aw dw c wa wd we ra rd cr ew er)

/-- **Distinct instance names, distinct register names and no memory statement give the three facts of a body.** -/
theorem modP_of_nodups {m : Module} (hi : (instNames m.body).Nodup) (hr : (regNames m.body).Nodup)
    (hm : NoMemB m.body) : ModP m :=
  ⟨instAgree_of_nodup m.body hi, agb_of_nodup m.body hr, rdb_of_noMem hm⟩

theorem noMemB_of_perm {l l' : List Stmt} (h : l.Perm l') (hm : NoMemB l) : NoMemB l' :=
  fun nm aw dw c wa wd we ra rd cr ew er hx => hm nm aw dw c wa wd we ra rd cr ew er (h.symm.subset hx)

/-- the register names of a body with no memory statement are its `nextKeys` -/
theorem nextKeys_eq_regNames : ∀ (l : List Stmt), NoMemB l → Sparkle.IR.Reorder.nextKeys l = regNames l
  | [], _ => rfl
  | st :: rest, hm => by
    have ih := nextKeys_eq_regNames rest (fun nm aw dw c wa wd we ra rd cr ew er hx =>
      hm nm aw dw c wa wd we ra rd cr ew er (List.mem_cons_of_mem _ hx))
    cases st with
    | memory nm aw dw c wa wd we ra rd cr ew er =>
      exact absurd List.mem_cons_self (hm nm aw dw c wa wd we ra rd cr ew er)
    | assign a b => simpa [Sparkle.IR.Reorder.nextKeys, regNames, List.flatMap_cons] using ih
    | register o cl rs inp init =>
      simp only [Sparkle.IR.Reorder.nextKeys, regNames, List.flatMap_cons] at ih ⊢
      rw [ih]; rfl
    | inst mn i cn => simpa [Sparkle.IR.Reorder.nextKeys, regNames, List.flatMap_cons] using ih

/-! ## The checked merge -/

open Sparkle.IR.Optimize (mapStmtExprs renameRefs)

theorem rs_inv (s : Std.HashMap String String) (st : Stmt) :
    (∃ n r, rewriteStmt s st = .assign n (.ref r)) ∨ rewriteStmt s st = mapStmtExprs (renameRefs s) st := by
  unfold rewriteStmt
  cases hd : Sparkle.IR.RegDedup.definedNode st with
  | none => exact Or.inr rfl
  | some n =>
    show (∃ n' r, Tools.ShippingMergeKeeps.rewriteNode s st n (s.get? n) = .assign n' (.ref r)) ∨
      Tools.ShippingMergeKeeps.rewriteNode s st n (s.get? n) = mapStmtExprs (renameRefs s) st
    cases hg : s.get? n with
    | none => exact Or.inr rfl
    | some r => exact Or.inl ⟨n, r, rfl⟩

theorem inst_of_rw {s : Std.HashMap String String} {body : List Stmt} {mn i : String} {c : List (String × Expr)}
    (h : Stmt.inst mn i c ∈ body.map (rewriteStmt s)) : ∃ c0, Stmt.inst mn i c0 ∈ body := by
  obtain ⟨st, hst, he⟩ := List.mem_map.mp h
  rcases rs_inv s st with ⟨n, r, hr⟩ | hr
  · rw [hr] at he; cases he
  · rw [hr] at he
    cases st with
    | inst mn0 i0 c0 =>
      simp only [mapStmtExprs, Stmt.inst.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      exact ⟨c0, hst⟩
    | assign a b => simp [mapStmtExprs] at he
    | register a b c d e => simp [mapStmtExprs] at he
    | memory a b c d e f g h i j k l => simp [mapStmtExprs] at he

theorem reg_of_rw {s : Std.HashMap String String} {body : List Stmt} {r c : String}
    {rs : String × Sparkle.IR.Type.ResetKind} {inp : Expr} {init : Int}
    (h : Stmt.register r c rs inp init ∈ body.map (rewriteStmt s)) :
    ∃ inp0, Stmt.register r c rs inp0 init ∈ body := by
  obtain ⟨st, hst, he⟩ := List.mem_map.mp h
  rcases rs_inv s st with ⟨n, r', hr⟩ | hr
  · rw [hr] at he; cases he
  · rw [hr] at he
    cases st with
    | register o c0 rs0 inp0 init0 =>
      simp only [mapStmtExprs, Stmt.register.injEq] at he
      obtain ⟨rfl, rfl, rfl, -, rfl⟩ := he
      exact ⟨inp0, hst⟩
    | assign a b => simp [mapStmtExprs] at he
    | inst a b c => simp [mapStmtExprs] at he
    | memory a b c d e f g h i j k l => simp [mapStmtExprs] at he

theorem mem_of_rw {s : Std.HashMap String String} {body : List Stmt} {nm : String} {aw dw : Nat} {c : String}
    {wa wd we ra : Expr} {rd : String} {cr : Bool} {ew : List (Expr × Expr × Expr)} {er : List (Expr × String)}
    (h : Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ body.map (rewriteStmt s)) :
    ∃ wa0 wd0 we0 ra0 ew0 er0, Stmt.memory nm aw dw c wa0 wd0 we0 ra0 rd cr ew0 er0 ∈ body := by
  obtain ⟨st, hst, he⟩ := List.mem_map.mp h
  rcases rs_inv s st with ⟨n, r', hr⟩ | hr
  · rw [hr] at he; cases he
  · rw [hr] at he
    cases st with
    | memory nm0 aw0 dw0 c0 wa1 wd1 we1 ra1 rd0 cr0 ew1 er1 =>
      simp only [mapStmtExprs, Stmt.memory.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl, -, -, -, -, rfl, rfl, -, -⟩ := he
      exact ⟨wa1, wd1, we1, ra1, ew1, er1, hst⟩
    | assign a b => simp [mapStmtExprs] at he
    | inst a b c => simp [mapStmtExprs] at he
    | register a b c d e => simp [mapStmtExprs] at he

theorem modP_body_map {body : List Stmt} (s : Std.HashMap String String)
    (hI : IUb body) (hA : Agb body) (hR : Rdb body) :
    IUb (body.map (rewriteStmt s)) ∧ Agb (body.map (rewriteStmt s)) ∧ Rdb (body.map (rewriteStmt s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mn i c mn' c' h1 h2
    obtain ⟨c0, h1'⟩ := inst_of_rw h1
    obtain ⟨c0', h2'⟩ := inst_of_rw h2
    exact hI mn i c0 mn' c0' h1' h2'
  · intro r c rs inp init c' rs' inp' init' h1 h2
    obtain ⟨i1, h1'⟩ := reg_of_rw h1
    obtain ⟨i2, h2'⟩ := reg_of_rw h2
    exact hA r c rs i1 init c' rs' i2 init' h1' h2'
  · intro nm aw dw c wa wd we ra rd cr ew er hm c' rs' inp' init' hr
    obtain ⟨wa0, wd0, we0, ra0, ew0, er0, hm0⟩ := mem_of_rw hm
    obtain ⟨i2, hr0⟩ := reg_of_rw hr
    exact hR nm aw dw c wa0 wd0 we0 ra0 rd cr ew0 er0 hm0 c' rs' i2 init' hr0

theorem mergeDuplicates_body (X : Module) :
    (Sparkle.IR.RegDedup.mergeDuplicates X).body = X.body ∨
    (Sparkle.IR.RegDedup.mergeDuplicates X).body = (Sparkle.IR.RegDedup.mergeDuplicatesParts X).1 := by
  unfold Sparkle.IR.RegDedup.mergeDuplicates Sparkle.IR.RegDedup.mergeDuplicatesRaw
  dsimp only
  split
  · split
    · right; rfl
    · left; rfl
  · right; rfl

theorem parts_shape (m : Module) :
    (Sparkle.IR.RegDedup.mergeDuplicatesParts m).1 = m.body ∨
    ∃ s, (Sparkle.IR.RegDedup.mergeDuplicatesParts m).1 = m.body.map (rewriteStmt s) := by
  rw [Tools.ShippingMergeKeeps.parts_eq_model, Tools.ShippingMergeKeeps.model_eq_rec]
  unfold Tools.ShippingMergeKeeps.partsRec
  split
  · left; rfl
  · unfold Tools.ShippingMergeKeeps.afterClasses
    split
    · left; rfl
    · unfold Tools.ShippingMergeKeeps.finish
      split
      · left; rfl
      · right; exact ⟨_, rfl⟩

/-- **The checked merge keeps the three facts.** -/
theorem modP_mergeChecked {X : Module} (h : ModP X) : ModP (Sparkle.IR.RefineCheck.mergeChecked X) := by
  obtain ⟨hI, hA, hR⟩ := h
  have key : ∀ b : List Stmt, (b = X.body ∨ b = (Sparkle.IR.RegDedup.mergeDuplicatesParts X).1) →
      IUb b ∧ Agb b ∧ Rdb b := by
    intro b hb
    rcases hb with rfl | rfl
    · exact ⟨hI, hA, hR⟩
    · rcases parts_shape X with h1 | ⟨s, h1⟩
      · rw [h1]; exact ⟨hI, hA, hR⟩
      · rw [h1]; exact modP_body_map s hI hA hR
  rcases Sparkle.IR.RefineCheck.mergeChecked_cases X with h | h
  · rw [h]
    exact key _ (mergeDuplicates_body X)
  · rw [h]
    exact ⟨hI, hA, hR⟩

end Tools.ShippingSrm17Body
