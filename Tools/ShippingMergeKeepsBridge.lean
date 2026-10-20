import Tools.ShippingMergeKeeps

/-! # `mergeDuplicatesParts` is the recursions of `Tools/ShippingMergeKeeps.lean` (round par/a-30)

The bridge from the compiler's `Id.run do` block
(`Sparkle/IR/RegDedup.lean` 234–293) to `partsRec`, and the theorems about
the compiler's functions:

    mergeRaw_keeps_nonAssign : LastNonAssign m.body →
      (mergeDuplicatesRaw m).body.all isAssign = false
    mergeChecked_keeps      : LastNonAssign m.body →
      (mergeChecked m).body.all isAssign = false

How the `do` block is reached WITHOUT reading its elaborated term (this
file was written without a build, and the `do` elaborator of the toolchain
is the new one — its output shape is not known to the author):

1. each loop is REPEATED here as a small `Id.run do` function of its list
   and its start state (`innerLoop`, `outerLoop` / `outerLoopR`, `repLoop`,
   `substLoop`), the loop text copied from the compiler;
2. `parts_eq_model`: the compiler's function is the model that calls these
   — by `rfl` (both sides are the same loops; unfolding the helpers gives the
   compiler's term back);
3. each helper has a `nil` and a `cons` equation — by `rfl` when the body
   has no `if`, else by a case split on the condition followed by `simp only`
   with the split's equation and `rfl`;
4. by these equations each helper IS its recursion (`*_eq`), by induction
   on the list; the range loop goes through
   `Std.Legacy.Range.forIn_eq_forIn_range'`.

Steps 2 and 3 are the ones that depend on the elaborated shape; each is
written as `first | … | …` over the routes the author could think of. If one
fails, the fix is local to that lemma: its STATEMENT is what the rest uses.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingMergeKeeps
open Sparkle.IR.AST Std
open Sparkle.IR.RegDedup (definedNode sigOf isAssign mergeDuplicatesParts mergeDuplicatesRaw
  mergeDuplicates)

/-! ## 1. The loops, repeated -/

/-- Lines 251–257 (the loop over the nodes inside a round). -/
def innerLoop (alias : HashMap String String) (cls : HashMap String Nat)
    (l : List (String × Stmt)) (ids0 next0 : HashMap String Nat) :
    HashMap String Nat × HashMap String Nat := Id.run do
  let mut ids : HashMap String Nat := ids0
  let mut next : HashMap String Nat := next0
  for (n, st) in l do
    let s := sigOf alias cls (cls.getD n 0) st
    let k := match ids.get? s with
      | some k => k
      | none => ids.size
    ids := ids.insert s k
    next := next.insert n k
  return (ids, next)

/-- Lines 248–261 over an index LIST. -/
def outerLoop (alias : HashMap String String) (nodes : List (String × Stmt)) (idx : List Nat)
    (cls0 : HashMap String Nat) (nc0 : Nat) : HashMap String Nat × Nat := Id.run do
  let mut cls : HashMap String Nat := cls0
  let mut nClasses : Nat := nc0
  for _ in idx do
    let p := innerLoop alias cls nodes {} {}
    let n' := p.1.size
    cls := p.2
    if n' == nClasses then break
    nClasses := n'
  return (cls, nClasses)

/-- Lines 248–261 over a range, as the compiler has it. -/
def outerLoopR (alias : HashMap String String) (nodes : List (String × Stmt))
    (r : Std.Legacy.Range) (cls0 : HashMap String Nat) (nc0 : Nat) :
    HashMap String Nat × Nat := Id.run do
  let mut cls : HashMap String Nat := cls0
  let mut nClasses : Nat := nc0
  for _ in r do
    let p := innerLoop alias cls nodes {} {}
    let n' := p.1.size
    cls := p.2
    if n' == nClasses then break
    nClasses := n'
  return (cls, nClasses)

/-- Lines 272–275. -/
def repLoop (cls : HashMap String Nat) (l : List (String × Stmt)) (rep0 : HashMap Nat String) :
    HashMap Nat String := Id.run do
  let mut rep : HashMap Nat String := rep0
  for (n, _) in l do
    let k := cls.getD n 0
    if !rep.contains k then rep := rep.insert k n
  return rep

/-- Lines 280–283. -/
def substLoop (cls : HashMap String Nat) (rep : HashMap Nat String) (l : List (String × Stmt))
    (s0 : HashMap String String) : HashMap String String := Id.run do
  let mut subst : HashMap String String := s0
  for (n, _) in l do
    let r := rep.getD (cls.getD n 0) n
    if r != n then subst := subst.insert n r
  return subst

/-! ## 2. Their equations -/

theorem innerLoop_nil (alias : HashMap String String) (cls : HashMap String Nat)
    (ids next : HashMap String Nat) : innerLoop alias cls [] ids next = (ids, next) := by
  first
    | rfl
    | (simp [innerLoop]; done)

theorem innerLoop_cons (alias : HashMap String String) (cls : HashMap String Nat) (n : String)
    (st : Stmt) (l : List (String × Stmt)) (ids next : HashMap String Nat) :
    innerLoop alias cls ((n, st) :: l) ids next =
      innerLoop alias cls l
        (ids.insert (sigOf alias cls (cls.getD n 0) st)
          (idOf ids (sigOf alias cls (cls.getD n 0) st)))
        (next.insert n (idOf ids (sigOf alias cls (cls.getD n 0) st))) := by
  first
    | rfl
    | (simp only [innerLoop, idOf, List.forIn_cons, List.forIn'_cons] <;> rfl)
    | (simp [innerLoop, idOf]; done)

theorem outerLoop_nil (alias : HashMap String String) (nodes : List (String × Stmt))
    (c : HashMap String Nat) (k : Nat) : outerLoop alias nodes [] c k = (c, k) := by
  first
    | rfl
    | (simp [outerLoop]; done)

theorem outerLoop_cons (alias : HashMap String String) (nodes : List (String × Stmt)) (i : Nat)
    (idx : List Nat) (c : HashMap String Nat) (k : Nat) :
    outerLoop alias nodes (i :: idx) c k =
      if (innerLoop alias c nodes {} {}).1.size == k then ((innerLoop alias c nodes {} {}).2, k)
      else outerLoop alias nodes idx (innerLoop alias c nodes {} {}).2
        (innerLoop alias c nodes {} {}).1.size := by
  first
    | (cases hb : ((innerLoop alias c nodes {} {}).1.size == k) <;>
        simp only [outerLoop, List.forIn_cons, List.forIn'_cons, hb, Bool.false_eq_true,
          ↓reduceIte] <;> rfl)
    | (by_cases hb : ((innerLoop alias c nodes {} {}).1.size == k) = true <;>
        simp only [outerLoop, List.forIn_cons, List.forIn'_cons, hb, ↓reduceIte] <;> rfl)
    | (simp only [outerLoop, List.forIn_cons, List.forIn'_cons]; split <;> rfl)
    | (simp [outerLoop]; done)

theorem repLoop_nil (cls : HashMap String Nat) (rep : HashMap Nat String) :
    repLoop cls [] rep = rep := by
  first
    | rfl
    | (simp [repLoop]; done)

theorem repLoop_cons (cls : HashMap String Nat) (n : String) (st : Stmt)
    (l : List (String × Stmt)) (rep : HashMap Nat String) :
    repLoop cls ((n, st) :: l) rep =
      repLoop cls l
        (if !rep.contains (cls.getD n 0) then rep.insert (cls.getD n 0) n else rep) := by
  first
    | (cases hb : rep.contains (cls.getD n 0) <;>
        simp only [repLoop, List.forIn_cons, List.forIn'_cons, hb, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ↓reduceIte] <;> rfl)
    | (by_cases hb : (!rep.contains (cls.getD n 0)) = true <;>
        simp only [repLoop, List.forIn_cons, List.forIn'_cons, hb, ↓reduceIte] <;> rfl)
    | (simp only [repLoop, List.forIn_cons, List.forIn'_cons]; split <;> rfl)
    | (simp [repLoop]; done)

theorem substLoop_nil (cls : HashMap String Nat) (rep : HashMap Nat String)
    (s : HashMap String String) : substLoop cls rep [] s = s := by
  first
    | rfl
    | (simp [substLoop]; done)

theorem substLoop_cons (cls : HashMap String Nat) (rep : HashMap Nat String) (n : String)
    (st : Stmt) (l : List (String × Stmt)) (s : HashMap String String) :
    substLoop cls rep ((n, st) :: l) s =
      substLoop cls rep l
        (if rep.getD (cls.getD n 0) n != n then s.insert n (rep.getD (cls.getD n 0) n)
          else s) := by
  first
    | (cases hb : (rep.getD (cls.getD n 0) n != n) <;>
        simp only [substLoop, List.forIn_cons, List.forIn'_cons, hb, Bool.false_eq_true,
          ↓reduceIte] <;> rfl)
    | (by_cases hb : (rep.getD (cls.getD n 0) n != n) = true <;>
        simp only [substLoop, List.forIn_cons, List.forIn'_cons, hb, ↓reduceIte] <;> rfl)
    | (simp only [substLoop, List.forIn_cons, List.forIn'_cons]; split <;> rfl)
    | (simp [substLoop]; done)

/-! ## 3. The loops are the recursions -/

theorem innerLoop_eq (alias : HashMap String String) (cls : HashMap String Nat) :
    ∀ (l : List (String × Stmt)) (ids next : HashMap String Nat),
      innerLoop alias cls l ids next = innerRec alias cls l ids next
  | [], ids, next => innerLoop_nil alias cls ids next
  | (n, st) :: l, ids, next =>
    (innerLoop_cons alias cls n st l ids next).trans (innerLoop_eq alias cls l _ _)

theorem outerLoop_eq (alias : HashMap String String) (nodes : List (String × Stmt)) :
    ∀ (idx : List Nat) (c : HashMap String Nat) (k : Nat),
      outerLoop alias nodes idx c k = outerRec alias nodes idx c k
  | [], c, k => outerLoop_nil alias nodes c k
  | i :: idx, c, k => by
    have h1 := outerLoop_cons alias nodes i idx c k
    rw [innerLoop_eq alias c nodes {} {},
      outerLoop_eq alias nodes idx (innerRec alias c nodes {} {}).2
        (innerRec alias c nodes {} {}).1.size] at h1
    exact h1

theorem repLoop_eq (cls : HashMap String Nat) :
    ∀ (l : List (String × Stmt)) (rep : HashMap Nat String), repLoop cls l rep = repRec cls l rep
  | [], rep => repLoop_nil cls rep
  | (n, st) :: l, rep => (repLoop_cons cls n st l rep).trans (repLoop_eq cls l _)

theorem substLoop_eq (cls : HashMap String Nat) (rep : HashMap Nat String) :
    ∀ (l : List (String × Stmt)) (s : HashMap String String),
      substLoop cls rep l s = substRec cls rep l s
  | [], s => substLoop_nil cls rep s
  | (n, st) :: l, s => (substLoop_cons cls rep n st l s).trans (substLoop_eq cls rep l _)

theorem outerLoopR_eq (alias : HashMap String String) (nodes : List (String × Stmt))
    (r : Std.Legacy.Range) (c : HashMap String Nat) (k : Nat) :
    outerLoopR alias nodes r c k =
      outerLoop alias nodes (List.range' r.start r.size r.step) c k := by
  unfold outerLoopR outerLoop
  first
    | (simp only [Std.Legacy.Range.forIn_eq_forIn_range'] <;> rfl)
    | (simp only [Std.Legacy.Range.forIn'_eq_forIn'_range',
        Std.Legacy.Range.forIn_eq_forIn_range'] <;> rfl)
    | (rw [Std.Legacy.Range.forIn_eq_forIn_range'] <;> rfl)

/-! ## 4. The compiler's function is the model -/

/-- Lines 241–244. -/
def aliasMap (m : Module) : HashMap String String :=
  m.body.foldl (init := {}) fun h st =>
    match st with
    | .assign y (.ref x) => if x != y then h.insert y x else h
    | _ => h

/-- Line 246. -/
def initCls (nodes : List (String × Stmt)) : HashMap String Nat :=
  nodes.foldl (fun h (n, _) => h.insert n 0) {}

/-- `afterClasses` with the loops. -/
def afterClassesL (m : Module) (cn : HashMap String Nat × Nat) :
    List Stmt × List (String × Expr) :=
  if cn.2 == (nodesOf m).length then (m.body, m.assertions)
  else finish m (substLoop cn.1 (repLoop cn.1 (nodesOf m) {}) (nodesOf m) {})

/-- `mergeDuplicatesParts`, calling the repeated loops. -/
def partsModel (m : Module) : List Stmt × List (String × Expr) :=
  if (nodesOf m).length < 2 then (m.body, m.assertions)
  else afterClassesL m
    (outerLoopR (aliasMap m) (nodesOf m) [0:(nodesOf m).length + 1] (initCls (nodesOf m)) 1)

/-- **The compiler's merge is the model** — the one statement about the
compiler's `do` block. -/
theorem parts_eq_model (m : Module) : mergeDuplicatesParts m = partsModel m := by
  first
    | rfl
    | (unfold mergeDuplicatesParts partsModel afterClassesL finish; rfl)
    | (simp only [mergeDuplicatesParts, partsModel, afterClassesL, finish, outerLoopR, innerLoop,
        repLoop, substLoop, nodesOf, nodesOfBody, nodeOf, aliasMap, initCls, rewriteStmt,
        rewriteNode] <;> rfl)

/-- The index list of the outer loop: `[0 : nodes.length + 1]` as a list. -/
def idxOf (m : Module) : List Nat :=
  List.range' ([0:(nodesOf m).length + 1] : Std.Legacy.Range).start
    ([0:(nodesOf m).length + 1] : Std.Legacy.Range).size
    ([0:(nodesOf m).length + 1] : Std.Legacy.Range).step

theorem idxOf_ne_nil (m : Module) : idxOf m ≠ [] := by
  intro he
  have hl : (idxOf m).length = 0 := by simp [he]
  have hlen : (idxOf m).length = ([0:(nodesOf m).length + 1] : Std.Legacy.Range).size := by
    unfold idxOf
    exact List.length_range'
  have hpos : 0 < ([0:(nodesOf m).length + 1] : Std.Legacy.Range).size := by
    first
      | (simp [Std.Legacy.Range.size]; done)
      | (simp only [Std.Legacy.Range.size]; omega)
      | (unfold Std.Legacy.Range.size; simp; done)
      | decide
  omega

theorem model_eq_rec (m : Module) :
    partsModel m = partsRec m (aliasMap m) (initCls (nodesOf m)) (idxOf m) := by
  first
    | (simp only [partsModel, partsRec, afterClassesL, afterClasses, idxOf, outerLoopR_eq,
        outerLoop_eq, repLoop_eq, substLoop_eq] <;> rfl)
    | (unfold partsModel partsRec afterClassesL afterClasses idxOf;
       rw [outerLoopR_eq, outerLoop_eq, repLoop_eq, substLoop_eq] <;> rfl)

/-! ## 5. The theorems about the compiler's functions -/

/-- **G-reg, the true statement, at `mergeDuplicatesParts`.** -/
theorem parts_keeps (m : Module) (hL : LastNonAssign m.body) :
    (mergeDuplicatesParts m).1.all isAssign = false := by
  rw [parts_eq_model, model_eq_rec]
  exact partsRec_keeps m _ _ _ (idxOf_ne_nil m) hL

/-- **`mergeRaw_keeps_nonAssign`** — the statement named in
`docs/parallel/A-leaf-entry-2.md` §1.3 and `docs/parallel/B-optprint.md`,
under the weaker hypothesis. -/
theorem mergeRaw_keeps_nonAssign {m : Module} (hL : LastNonAssign m.body) :
    (mergeDuplicatesRaw m).body.all isAssign = false :=
  parts_keeps m hL

/-- The same under distinct defined names (the candidate statement). -/
theorem mergeRaw_keeps_nonAssign_of_nodup {m : Module}
    (hnd : (m.body.filterMap definedNode).Nodup) (h : m.body.all isAssign = false) :
    (mergeDuplicatesRaw m).body.all isAssign = false :=
  mergeRaw_keeps_nonAssign (lastNonAssign_of_nodup hnd h)

theorem mergeDuplicates_keeps {m : Module} (hL : LastNonAssign m.body) :
    (mergeDuplicates m).body.all isAssign = false := by
  have hna := hL.nonAssign
  have hc : ¬ (m.body.all isAssign = true) := by
    rw [hna]
    exact Bool.false_ne_true
  have he : mergeDuplicates m = mergeDuplicatesRaw m := by
    unfold mergeDuplicates
    first
      | (show (if m.body.all isAssign = true then _ else mergeDuplicatesRaw m) =
          mergeDuplicatesRaw m; exact if_neg hc)
      | (simp [hna]; done)
  rw [he]
  exact mergeRaw_keeps_nonAssign hL

/-- **The checked merge keeps a non-assignment statement** — what the guard
"Diff 2" in `mergeChecked` would have enforced, proved instead, for a module
with `LastNonAssign`. -/
theorem mergeChecked_keeps {m : Module} (hL : LastNonAssign m.body) :
    (Sparkle.IR.RefineCheck.mergeChecked m).body.all isAssign = false := by
  rcases Sparkle.IR.RefineCheck.mergeChecked_cases m with h | h
  · rw [h]
    exact mergeDuplicates_keeps hL
  · rw [h]
    exact hL.nonAssign

end Tools.ShippingMergeKeeps
