import Tools.ShippingLegacySemEntryListD

/-! # The telescope's hand-over for ANY number of binders

`telescopeIn_of_lam2` / `telescopeIn_of_lam3` hand a two- / three-binder body
over to the entry walk, each by a hand case analysis on the list of variables
the Meta-library fact returns. Here: one statement for a binder list of any
length, so that the 45 structure projection functions of the census
(`k + 1` binders, `k ∈ {1, 2, 3, 4, 6, 9}`) need no per-arity lemma.

**Defined here**

* `TypesOkFrom sp bs fvars` — the oracle facts of the binders, in the form the
  telescope produces their declared types: the `j`-th type is
  `Tⱼ.instantiateRevRange 0 fvars.size fvars` for the array `fvars` of the
  variables opened before it, and the facts of the LATER binders are asked
  FOR EVERY variable `id` pushed on that array (the type of a later binder
  mentions the earlier variables — the domain variable in every real case).
  It also ties the names of `bs` to the names of `sp`.
* `LamTelescopeND` — `LamTelescopeN` with one more conjunct in its
  conclusion: the variables are DISTINCT (`ids.Nodup`). A Meta-library fact
  of the same class (`lambdaTelescope` opens fresh free variables); not
  provable here for the same reason (`lambdaTelescopeImp` is
  `private partial`). `LamTelescopeN` is kept; `LamTelescopeND.toN`.
  Why it is needed: `DeclsOpen` / `DeclsAtD` say that each variable is FOUND
  in the final local context with its own name and type — two positions
  holding the same variable are not excluded by that (two binders of one name
  and type), and the oracle facts do not exclude it either (`InfersHW` is a
  statement about returning runs only). The prepared setup's input map
  (`prepare`) is overwritten by a later binder with the same variable, so the
  generic input fact (`Tools/ShippingLegacySemInputAt.lean`) needs
  distinctness.
* `ListScopeDN` — `ListScopeD` with `ids.Nodup`.

**Proved here**

* `getElem_mapAppend`, `fvarAt` — the index fact: in
  `((pre ++ id :: rest).map .fvar).toArray` the entry at `pre.length` is the
  variable `id`.
* `fvars_push` — `push` on the array of a list of variables is the array of
  the list extended at its end (the two forms of the telescope's array).
* `declsAtD_of_open` — THE INDEXING LEMMA, with the accumulated prefix `pre`
  as the generalized invariant:
  `DeclsOpen mctx sp ids (pre.map .fvar).toArray` and
  `TypesOkFrom sp bs (pre.map .fvar).toArray` give
  `DeclsAtD mctx ((pre ++ ids).map .fvar).toArray pre.length bs ids`.
* `telescopeIn_of_lams` — from `LamTelescopeN`: `TelescopeIn body
  (ListScopeD bs leafOf)` for `body = lams sp b`.
* `telescopeIn_of_lamsN` — from `LamTelescopeND`: the same with
  `ListScopeDN`.

Nothing here reads a compiler definition's program text. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness

/-- The oracle facts of the binders `bs` on the declared types of the nested
lambdas `sp`, the variables `fvars` being already opened; the names agree. -/
def TypesOkFrom : List (Name × Lean.Expr × BinderInfo) → List (Name × MixedGateBinder) →
    Array Lean.Expr → Prop
  | [], [], _ => True
  | (n, T, _) :: sp, q :: bs, fvars =>
    q.1 = n ∧ TypeOk q.2 (T.instantiateRevRange 0 fvars.size fvars) ∧
      ∀ id : FVarId, TypesOkFrom sp bs (fvars.push (Lean.Expr.fvar id))
  | _, _, _ => False

/-- **The Meta-library fact about `lambdaTelescope`, for `n` binders, with
the distinctness of the opened variables.** -/
def LamTelescopeND : Prop :=
  ∀ (sp : List (Name × Lean.Expr × BinderInfo)) (b : Lean.Expr), b.isLambda = false →
  ∀ (α : Type) (k : Array Lean.Expr → Lean.Expr → MetaM α) (r : α),
    MReturns (Lean.Meta.lambdaTelescope (lams sp b) k) r →
    ∃ (mctx : Meta.Context) (ids : List FVarId),
      ids.Nodup ∧ DeclsOpen mctx sp ids #[] ∧
      MRunsIn (k (ids.map Lean.Expr.fvar).toArray
        (b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
          (ids.map Lean.Expr.fvar).toArray)) mctx r

theorem LamTelescopeND.toN (h : LamTelescopeND) : LamTelescopeN := by
  intro sp b hl α k r hrun
  obtain ⟨mctx, ids, _, hd, hk⟩ := h sp b hl α k r hrun
  exact ⟨mctx, ids, hd, hk⟩

/-- `ListScopeD` with the distinctness of the variables. -/
def ListScopeDN (bs : List (Name × MixedGateBinder)) (leafOf : List FVarId → Lean.Expr)
    (mctx : Meta.Context) (xs : Array Lean.Expr) (inner : Lean.Expr) : Prop :=
  ∃ ids : List FVarId, inner = leafOf ids ∧ DeclsAtD mctx xs 0 bs ids ∧ ids.Nodup

/-- In `(pre ++ a :: rest).map f` the entry at `pre.length` is `f a`. -/
theorem getElem_mapAppend {α β : Type} (f : α → β) (a : α) (rest : List α) (pre : List α) :
    ∃ h : pre.length < ((pre ++ a :: rest).map f).length,
      ((pre ++ a :: rest).map f)[pre.length]'h = f a := by
  induction pre with
  | nil =>
    first
      | exact ⟨Nat.zero_lt_succ _, rfl⟩
      | exact ⟨by simp, by simp⟩
  | cons p pre ih =>
    obtain ⟨h, e⟩ := ih
    first
      | exact ⟨Nat.succ_lt_succ h, e⟩
      | exact ⟨by simp, by simpa using e⟩
      | exact ⟨by simp, by simp⟩

/-- **The index fact**: in the array of the variables `pre ++ id :: rest` the
entry at `pre.length` is the variable `id`. -/
theorem fvarAt (pre : List FVarId) (id : FVarId) (rest : List FVarId) :
    ∃ h : pre.length < ((pre ++ id :: rest).map Lean.Expr.fvar).toArray.size,
      ((((pre ++ id :: rest).map Lean.Expr.fvar).toArray)[pre.length]'h).fvarId! = id := by
  obtain ⟨h, e⟩ := getElem_mapAppend Lean.Expr.fvar id rest pre
  have h' : pre.length < ((pre ++ id :: rest).map Lean.Expr.fvar).toArray.size := by
    first
      | exact h
      | simpa using h
  refine ⟨h', ?_⟩
  have e' : (((pre ++ id :: rest).map Lean.Expr.fvar).toArray)[pre.length]'h' =
      Lean.Expr.fvar id := by
    first
      | exact e
      | simpa using e
      | (rw [List.getElem_toArray]
         exact e)
  rw [e']
  first
    | rfl
    | simp [Lean.Expr.fvarId!]

/-- `push` on the array of a list of variables. -/
theorem fvars_push (pre : List FVarId) (id : FVarId) :
    (pre.map Lean.Expr.fvar).toArray.push (Lean.Expr.fvar id) =
      ((pre ++ [id]).map Lean.Expr.fvar).toArray := by
  first
    | (rw [List.push_toArray, List.map_append]
       rfl)
    | simp
    | (apply Array.ext'
       simp)

/-- The size of the array of a list of variables. -/
theorem fvars_size (l : List FVarId) : (l.map Lean.Expr.fvar).toArray.size = l.length := by
  first
    | exact List.length_map Lean.Expr.fvar
    | simp

/-- **The indexing lemma.** Generalized invariant: `pre` is the list of the
variables opened so far; the telescope's array at that point is
`(pre.map .fvar).toArray`, the final array is `((pre ++ ids).map .fvar).toArray`
and the next variable sits at index `pre.length` of it. -/
theorem declsAtD_of_open {mctx : Meta.Context} (sp : List (Name × Lean.Expr × BinderInfo)) :
    ∀ (bs : List (Name × MixedGateBinder)) (pre ids : List FVarId),
      DeclsOpen mctx sp ids (pre.map Lean.Expr.fvar).toArray →
      TypesOkFrom sp bs (pre.map Lean.Expr.fvar).toArray →
      DeclsAtD mctx ((pre ++ ids).map Lean.Expr.fvar).toArray pre.length bs ids := by
  induction sp with
  | nil =>
    intro bs pre ids ho ht
    cases ids with
    | cons id ids => exact False.elim ho
    | nil =>
      cases bs with
      | cons q bs => exact False.elim ht
      | nil =>
        rw [List.append_nil]
        exact Nat.le_of_eq (fvars_size pre)
  | cons s sp ih =>
    intro bs pre ids ho ht
    obtain ⟨n, T, bi⟩ := s
    cases ids with
    | nil => exact False.elim ho
    | cons id ids =>
      cases bs with
      | nil => exact False.elim ht
      | cons q bs =>
        obtain ⟨⟨d0, hf, hn, hty⟩, hrest⟩ := ho
        obtain ⟨hname, hok, hnext⟩ := ht
        have hrest' : DeclsOpen mctx sp ids ((pre ++ [id]).map Lean.Expr.fvar).toArray := by
          rw [← fvars_push pre id]
          exact hrest
        have hnext' : TypesOkFrom sp bs ((pre ++ [id]).map Lean.Expr.fvar).toArray := by
          rw [← fvars_push pre id]
          exact hnext id
        have ih' := ih bs (pre ++ [id]) ids hrest' hnext'
        have happ : (pre ++ [id]) ++ ids = pre ++ id :: ids := by
          first
            | (rw [List.append_assoc]
               rfl)
            | simp
        have hlen : (pre ++ [id]).length = pre.length + 1 := by
          first
            | (rw [List.length_append]
               rfl)
            | simp
        rw [happ, hlen] at ih'
        obtain ⟨h0, hx⟩ := fvarAt pre id ids
        have hnm : d0.userName = q.1 := hn.trans hname.symm
        have hto : TypeOk q.2 d0.type := by
          rw [hty]
          exact hok
        exact And.intro
          (Exists.intro h0 (And.intro hx (Exists.intro d0
            (And.intro hf (And.intro hnm hto)))))
          ih'

/-- What both hand-overs share: from the declarations the telescope installs
and the continuation's run, the walk's declarations, the length of the
variable list, and the continuation's run on `leafOf ids`. -/
theorem scope_of_open {mctx : Meta.Context} {sp : List (Name × Lean.Expr × BinderInfo)}
    {b : Lean.Expr} {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {α : Type} {k : Array Lean.Expr → Lean.Expr → MetaM α} {r : α} {ids : List FVarId}
    (hT : TypesOkFrom sp bs #[])
    (hi : ∀ ids : List FVarId, ids.length = bs.length →
      b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
        (ids.map Lean.Expr.fvar).toArray = leafOf ids)
    (hdecl : DeclsOpen mctx sp ids #[])
    (hk : MRunsIn (k (ids.map Lean.Expr.fvar).toArray
      (b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
        (ids.map Lean.Expr.fvar).toArray)) mctx r) :
    DeclsAtD mctx (ids.map Lean.Expr.fvar).toArray 0 bs ids ∧
    MRunsIn (k (ids.map Lean.Expr.fvar).toArray (leafOf ids)) mctx r := by
  have hd0 := declsAtD_of_open (mctx := mctx) sp bs [] ids hdecl hT
  have hd : DeclsAtD mctx (ids.map Lean.Expr.fvar).toArray 0 bs ids := by
    first
      | exact hd0
      | (rw [List.nil_append] at hd0
         exact hd0)
      | (simp only [List.nil_append, List.length_nil] at hd0
         exact hd0)
  have hlen : ids.length = bs.length := DeclsAtD.length bs ids 0 hd
  refine ⟨hd, ?_⟩
  rw [← hi ids hlen]
  exact hk

/-- **The telescope's hand-over for a body with any number of binders**, from
the Meta-library fact, the body's shape `lams sp b`, the oracle facts of the
declared types (`TypesOkFrom`), and the leaf equation. -/
theorem telescopeIn_of_lams (htel : LamTelescopeN) {body : Lean.Expr}
    {sp : List (Name × Lean.Expr × BinderInfo)} {b : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    (hb : body = lams sp b) (hl : b.isLambda = false)
    (hT : TypesOkFrom sp bs #[])
    (hi : ∀ ids : List FVarId, ids.length = bs.length →
      b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
        (ids.map Lean.Expr.fvar).toArray = leafOf ids) :
    TelescopeIn body (ListScopeD bs leafOf) := by
  intro α k r hrun
  rw [hb] at hrun
  obtain ⟨mctx, ids, hdecl, hk⟩ := htel sp b hl α k r hrun
  obtain ⟨hd, hk'⟩ := scope_of_open hT hi hdecl hk
  have hs : ListScopeD bs leafOf mctx (ids.map Lean.Expr.fvar).toArray (leafOf ids) := by
    unfold ListScopeD
    exact ⟨ids, rfl, hd⟩
  exact ⟨mctx, (ids.map Lean.Expr.fvar).toArray, leafOf ids, hs, hk'⟩

/-- **The same hand-over with the distinctness of the variables**, from
`LamTelescopeND`. -/
theorem telescopeIn_of_lamsN (htel : LamTelescopeND) {body : Lean.Expr}
    {sp : List (Name × Lean.Expr × BinderInfo)} {b : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    (hb : body = lams sp b) (hl : b.isLambda = false)
    (hT : TypesOkFrom sp bs #[])
    (hi : ∀ ids : List FVarId, ids.length = bs.length →
      b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
        (ids.map Lean.Expr.fvar).toArray = leafOf ids) :
    TelescopeIn body (ListScopeDN bs leafOf) := by
  intro α k r hrun
  rw [hb] at hrun
  obtain ⟨mctx, ids, hnd, hdecl, hk⟩ := htel sp b hl α k r hrun
  obtain ⟨hd, hk'⟩ := scope_of_open hT hi hdecl hk
  have hs : ListScopeDN bs leafOf mctx (ids.map Lean.Expr.fvar).toArray (leafOf ids) := by
    unfold ListScopeDN
    exact ⟨ids, rfl, hd, hnd⟩
  exact ⟨mctx, (ids.map Lean.Expr.fvar).toArray, leafOf ids, hs, hk'⟩

end Tools.ShippingLegacySem
