import Tools.VedU2HierRec

/-!
# Local lemmas of the recursive statement `U2HRStmtR` (CANDIDATE; Tools/VedU2HierRec.lean)

* L3 design restriction / fuel (`combR_sub_fuel`, `upsR_sub_fuel`, `stepR_sub_fuel`): a successful
  `stepR` in a sub-design `dC` (every module resolved in `dC` is the same module in `d`) is the same
  successful `stepR` in the parent's real design `d` at any larger fuel.
-/

namespace Tools.VedU2HierRec

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

/-- `dC` resolves a module name only to a module that `d` resolves it to as well. -/
def SubDesign (dC d : Design) : Prop :=
  ∀ n c, findMod dC n = some c → findMod d n = some c

theorem evalAssignsI_mono (we : WEnv) (ie ie' : InstEval)
    (hm : ∀ mn i cs env l, ie mn i cs env = some l → ie' mn i cs env = some l) :
    ∀ (b : List Stmt) (env e : Env), evalAssignsI we ie b env = some e →
      evalAssignsI we ie' b env = some e := by
  intro b
  induction b with
  | nil => intro env e h; exact h
  | cons s rest ih =>
    intro env e h
    simp only [evalAssignsI] at h ⊢
    cases hc : cellVals we ie s env with
    | none => simp [hc] at h
    | some l =>
      simp only [hc, Option.bind_eq_bind, Option.bind] at h
      have hc' : cellVals we ie' s env = some l := by
        cases s with
        | assign x r => simpa [cellVals] using hc
        | register o c r e i => simpa [cellVals] using hc
        | memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [cellVals] at hc
        | inst mn i cs => exact hm mn i cs env l hc
      simp only [hc', Option.bind_eq_bind, Option.bind]
      exact ih _ e h

theorem mapM_mono {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ y, f x = some y → g x = some y) →
      ∀ ys, xs.mapM f = some ys → xs.mapM g = some ys := by
  intro xs
  induction xs with
  | nil => intro _ ys h; exact h
  | cons x rest ih =>
    intro hm ys h
    simp only [List.mapM_cons] at h ⊢
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hr : rest.mapM f with
      | none => simp [hx, hr] at h
      | some zs =>
        simp only [hx, hr, Option.bind_eq_bind, Option.bind, pure] at h
        have h1 := hm x (List.mem_cons_self ..) y hx
        have h2 := ih (fun a ha => hm a (List.mem_cons_of_mem _ ha)) zs hr
        simp only [h1, h2, Option.bind_eq_bind, Option.bind, pure]
        exact h

theorem instEvalF_mono {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt)
    {comb comb' : Module → HSt → Env → Option Env}
    (hc : ∀ c st seed e, comb c st seed = some e → comb' c st seed = some e) (st : HSt) (we : WEnv) :
    ∀ mn i cs env l, instEvalF dC arr comb st we mn i cs env = some l →
      instEvalF d arr comb' st we mn i cs env = some l := by
  intro mn iname conns env l hl
  unfold instEvalF at hl ⊢
  cases hf : findMod dC mn with
  | none => simp [hf] at hl
  | some c =>
    simp only [hf] at hl
    simp only [hs mn c hf]
    by_cases hok : instOkR c conns = true
    · simp only [hok, if_true] at hl ⊢
      cases hsd : childSeedS c conns we env (regOuts (arr c)) (st [iname]) with
      | none => simp [hsd] at hl
      | some seed =>
        cases hcc : comb c (fun p => st (iname :: p)) seed with
        | none => simp [hsd, hcc] at hl
        | some envC =>
          simp only [hsd, hcc, hc _ _ _ _ hcc, Option.bind_eq_bind, Option.bind] at hl ⊢
          exact hl
    · simp [hok] at hl

theorem childUpsF_mono {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt)
    {comb comb' : Module → HSt → Env → Option Env} {ups ups' : Module → HSt → Env → Option Ups}
    (hc : ∀ c st seed e, comb c st seed = some e → comb' c st seed = some e)
    (hu : ∀ c st e u, ups c st e = some u → ups' c st e = some u) (we : WEnv) (st : HSt) (envF : Env) :
    ∀ x y, childUpsF dC arr comb ups we st envF x = some y →
      childUpsF d arr comb' ups' we st envF x = some y := by
  intro x y hy
  unfold childUpsF at hy ⊢
  cases hf : findMod dC x.1 with
  | none => simp [hf] at hy
  | some c =>
    simp only [hf] at hy
    simp only [hs _ c hf]
    by_cases hok : instOkR c x.2.2 = true
    · simp only [hok, if_true] at hy ⊢
      cases hsd : childSeedS c x.2.2 we envF (regOuts (arr c)) (st [x.2.1]) with
      | none => simp [hsd] at hy
      | some seed =>
        cases hcc : comb c (fun p => st (x.2.1 :: p)) seed with
        | none => simp [hsd, hcc] at hy
        | some envC =>
          cases huu : ups c (fun p => st (x.2.1 :: p)) envC with
          | none => simp [hsd, hcc, huu] at hy
          | some us =>
            simp only [hsd, hcc, huu, hc _ _ _ _ hcc, hu _ _ _ _ huu, Option.bind_eq_bind,
              Option.bind] at hy ⊢
            exact hy
    · simp [hok] at hy

theorem combR_sub_fuel {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt) :
    ∀ (k k' : Nat), k ≤ k' → ∀ (m : Module) (st : HSt) (env0 e : Env),
      combR dC arr k m st env0 = some e → combR d arr k' m st env0 = some e := by
  intro k
  induction k with
  | zero => intro k' _ m st env0 e h; simp [combR] at h
  | succ k ih =>
    intro k' hk m st env0 e h
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    simp only [combR] at h ⊢
    exact evalAssignsI_mono _ _ _
      (instEvalF_mono hs arr (fun c st seed e h => ih k'' (by omega) c st seed e h) st _) _ _ _ h

theorem upsR_sub_fuel {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt) :
    ∀ (k k' : Nat), k ≤ k' → ∀ (m : Module) (st : HSt) (envF : Env) (u : Ups),
      upsR dC arr k m st envF = some u → upsR d arr k' m st envF = some u := by
  intro k
  induction k with
  | zero => intro k' _ m st envF u h; simp [upsR] at h
  | succ k ih =>
    intro k' hk m st envF u h
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    simp only [upsR] at h ⊢
    cases hP : regNexts (declWidth m) (fun _ _ => 0) (arr m) envF with
    | none => simp [hP] at h
    | some nx =>
      cases hm : (instDecls (arr m)).mapM
          (childUpsF dC arr (combR dC arr k) (upsR dC arr k) (declWidth m) st envF) with
      | none => simp [hP, hm] at h
      | some ys =>
        have hm' := mapM_mono _ (childUpsF d arr (combR d arr k'') (upsR d arr k'') (declWidth m) st envF)
          (instDecls (arr m))
          (fun x _ y hy => childUpsF_mono hs arr
            (fun c st seed e h => combR_sub_fuel hs arr k k'' (by omega) c st seed e h)
            (fun c st e u h => ih k'' (by omega) c st e u h) _ _ _ x y hy) ys hm
        simp only [hP, hm, hm', Option.bind_eq_bind, Option.bind] at h ⊢
        exact h

theorem stepR_sub_fuel {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt)
    {k k' : Nat} (hk : k ≤ k') (m : Module) (st : HSt) (env0 : Env) (r : Env × Ups)
    (h : stepR dC arr k m st env0 = some r) : stepR d arr k' m st env0 = some r := by
  unfold stepR at h ⊢
  cases hc : combR dC arr k m st env0 with
  | none => simp [hc] at h
  | some e =>
    cases hu : upsR dC arr k m st e with
    | none => simp [hc, hu] at h
    | some u =>
      simp only [hc, hu, Option.bind_eq_bind, Option.bind] at h
      simp only [combR_sub_fuel hs arr k k' hk m st env0 e hc, upsR_sub_fuel hs arr k k' hk m st e u hu,
        Option.bind_eq_bind, Option.bind]
      exact h

/-! ## L2: the state slice per instance path -/

/-- The updates of `ups` that belong to the instance `i` (head `i`), with `i` removed from the path. -/
def sliceUps (i : String) (ups : Ups) : Ups :=
  ups.filterMap (fun u => match u.1 with
    | j :: p => if j = i then some (p, u.2) else none
    | [] => none)

theorem find_sliceUps (i : String) (p : Path) : ∀ ups : Ups,
    (sliceUps i ups).find? (fun u => u.1 == p) =
      (ups.find? (fun u => u.1 == i :: p)).map (fun u => (p, u.2)) := by
  intro ups
  induction ups with
  | nil => rfl
  | cons u rest ih =>
    obtain ⟨path, nx⟩ := u
    cases path with
    | nil => simp [sliceUps, List.find?_cons] at ih ⊢; exact ih
    | cons j q =>
      by_cases hj : j = i
      · subst hj
        by_cases hq : q = p
        · subst hq; simp [sliceUps, List.find?_cons]
        · simp [sliceUps, List.find?_cons, hq] at ih ⊢
          exact ih
      · simp [sliceUps, List.find?_cons, hj] at ih ⊢
        exact ih

/-- L2 (slice coherence of the simultaneous update): the slice at `i :: p` of the updated state is the
slice state updated by the slice of the updates. -/
theorem applyH_slice (S : HSt) (ups : Ups) (i : String) :
    (fun p => applyH S ups (i :: p)) = applyH (fun p => S (i :: p)) (sliceUps i ups) := by
  funext p n
  unfold applyH
  rw [find_sliceUps]
  cases ups.find? (fun u => u.1 == i :: p) <;> rfl

theorem sliceUps_append (i : String) (A B : Ups) :
    sliceUps i (A ++ B) = sliceUps i A ++ sliceUps i B := by
  simp [sliceUps, List.filterMap_append]

theorem sliceUps_root (i : String) (nx : List (String × Nat)) (R : Ups) :
    sliceUps i (([], nx) :: R) = sliceUps i R := by
  simp [sliceUps]

theorem sliceUps_prefix_same (i : String) : ∀ us : Ups,
    sliceUps i (us.map (fun u => (i :: u.1, u.2))) = us := by
  intro us
  induction us with
  | nil => rfl
  | cons u rest ih => simp [sliceUps] at ih ⊢; exact ih

theorem sliceUps_eq_nil (i : String) : ∀ b : Ups,
    (∀ u ∈ b, ∃ j q, j ≠ i ∧ u.1 = j :: q) → sliceUps i b = [] := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons u rest ih =>
    intro h
    obtain ⟨j, q, hj, hq⟩ := h u (List.mem_cons_self ..)
    have := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    obtain ⟨path, nx⟩ := u
    simp only at hq
    subst hq
    simp [sliceUps, hj] at this ⊢
    exact this

theorem mapM_mem_of {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y := by
  intro xs
  induction xs with
  | nil => intro ys h y hy; simp at h; subst h; cases hy
  | cons a rest ih =>
    intro ys h y hy
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hr : rest.mapM f with
      | none => simp [ha, hr] at h
      | some rs =>
        simp only [ha, hr, Option.bind_eq_bind, Option.bind, pure, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, List.mem_cons_self .., ha⟩
        · obtain ⟨x, hx, hfx⟩ := ih rs hr y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem sliceUps_flatten_mapM {X : Type} (i : String) (f : X → Option Ups) (head : X → String)
    (hhead : ∀ x us, f x = some us → ∀ u ∈ us, ∃ q, u.1 = head x :: q) :
    ∀ (xs : List X) (L : List Ups), xs.mapM f = some L → (xs.map head).Nodup →
      ∀ x ∈ xs, head x = i → ∀ us, f x = some us → sliceUps i L.flatten = sliceUps i us := by
  intro xs
  induction xs with
  | nil => intro L _ _ x hx; cases hx
  | cons y rest ih =>
    intro L hL hnd x hx hxi us hus
    simp only [List.mapM_cons] at hL
    cases hy : f y with
    | none => simp [hy] at hL
    | some b =>
      cases hr : rest.mapM f with
      | none => simp [hy, hr] at hL
      | some rs =>
        simp only [hy, hr, Option.bind_eq_bind, Option.bind, pure, Option.some.injEq] at hL
        subst hL
        simp only [List.map_cons, List.nodup_cons] at hnd
        simp only [List.flatten_cons, sliceUps_append]
        rcases List.mem_cons.mp hx with rfl | hxr
        · rw [hy] at hus
          cases hus
          have : sliceUps i rs.flatten = [] := by
            apply sliceUps_eq_nil
            intro u hu
            obtain ⟨b', hb', hub'⟩ := List.mem_flatten.mp hu
            obtain ⟨x', hx', hb'x⟩ := mapM_mem_of f rest rs hr b' hb'
            obtain ⟨q, hq⟩ := hhead x' b' hb'x u hub'
            refine ⟨head x', q, ?_, hq⟩
            intro he
            exact hnd.1 (List.mem_map.mpr ⟨x', hx', he.trans hxi.symm⟩)
          rw [this]; simp
        · have hne : head y ≠ i := by
            intro he
            exact hnd.1 (List.mem_map.mpr ⟨x, hxr, hxi.trans he.symm⟩)
          have h0 : sliceUps i b = [] := by
            apply sliceUps_eq_nil
            intro u hu
            obtain ⟨q, hq⟩ := hhead y b hy u hu
            exact ⟨head y, q, hne, hq⟩
          rw [h0, ih rs hr hnd.2 x hxr hxi us hus]
          simp

/-- The paths of one instance's updates start with its name. -/
theorem childUpsF_head {d : Design} {arr : Module → List Stmt}
    {comb : Module → HSt → Env → Option Env} {ups : Module → HSt → Env → Option Ups}
    {we : WEnv} {st : HSt} {envF : Env} {x : String × String × List (String × Expr)} {us : Ups}
    (h : childUpsF d arr comb ups we st envF x = some us) :
    ∀ u ∈ us, ∃ q, u.1 = x.2.1 :: q := by
  unfold childUpsF at h
  cases hf : findMod d x.1 with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hok : instOkR c x.2.2 = true
    · simp only [hok, if_true] at h
      cases hsd : childSeedS c x.2.2 we envF (regOuts (arr c)) (st [x.2.1]) with
      | none => simp [hsd] at h
      | some seed =>
        cases hcc : comb c (fun p => st (x.2.1 :: p)) seed with
        | none => simp [hsd, hcc] at h
        | some envC =>
          cases huu : ups c (fun p => st (x.2.1 :: p)) envC with
          | none => simp [hsd, hcc, huu] at h
          | some us' =>
            simp only [hsd, hcc, huu, Option.bind_eq_bind, Option.bind, Option.some.injEq] at h
            subst h
            intro u hu
            obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
            exact ⟨v.1, rfl⟩
    · simp [hok] at h

/-- Inversion of one instance's updates. -/
theorem childUpsF_inv {d : Design} {arr : Module → List Stmt}
    {comb : Module → HSt → Env → Option Env} {ups : Module → HSt → Env → Option Ups}
    {we : WEnv} {st : HSt} {envF : Env} {x : String × String × List (String × Expr)} {us : Ups}
    (h : childUpsF d arr comb ups we st envF x = some us) :
    ∃ c seed envC us', findMod d x.1 = some c ∧ instOkR c x.2.2 = true ∧
      childSeedS c x.2.2 we envF (regOuts (arr c)) (st [x.2.1]) = some seed ∧
      comb c (fun p => st (x.2.1 :: p)) seed = some envC ∧
      ups c (fun p => st (x.2.1 :: p)) envC = some us' ∧
      us = us'.map (fun u => (x.2.1 :: u.1, u.2)) := by
  unfold childUpsF at h
  cases hf : findMod d x.1 with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hok : instOkR c x.2.2 = true
    · simp only [hok, if_true] at h
      cases hsd : childSeedS c x.2.2 we envF (regOuts (arr c)) (st [x.2.1]) with
      | none => simp [hsd] at h
      | some seed =>
        cases hcc : comb c (fun p => st (x.2.1 :: p)) seed with
        | none => simp [hsd, hcc] at h
        | some envC =>
          cases huu : ups c (fun p => st (x.2.1 :: p)) envC with
          | none => simp [hsd, hcc, huu] at h
          | some us' =>
            simp only [hsd, hcc, huu, Option.bind_eq_bind, Option.bind, Option.some.injEq] at h
            exact ⟨c, seed, envC, us', rfl, hok, hsd, hcc, huu, h.symm⟩
    · simp [hok] at h

/-- L2 for the whole module: the updates of the instance `i` are the slice of the parent's updates. -/
theorem upsR_slice {d : Design} {arr : Module → List Stmt} {k : Nat} {m : Module} {st : HSt}
    {envF : Env} {ups : Ups} (h : upsR d arr (k + 1) m st envF = some ups)
    (hnd : ((instDecls (arr m)).map (·.2.1)).Nodup) {mn i : String} {cs : List (String × Expr)}
    (hin : (mn, i, cs) ∈ instDecls (arr m)) :
    ∃ c seed envC upsC, findMod d mn = some c ∧ instOkR c cs = true ∧
      childSeedS c cs (declWidth m) envF (regOuts (arr c)) (st [i]) = some seed ∧
      combR d arr k c (fun p => st (i :: p)) seed = some envC ∧
      upsR d arr k c (fun p => st (i :: p)) envC = some upsC ∧
      sliceUps i ups = upsC := by
  simp only [upsR] at h
  cases hP : regNexts (declWidth m) (fun _ _ => 0) (arr m) envF with
  | none => simp [hP] at h
  | some nx =>
    cases hm : (instDecls (arr m)).mapM
        (childUpsF d arr (combR d arr k) (upsR d arr k) (declWidth m) st envF) with
    | none => simp [hP, hm] at h
    | some L =>
      simp only [hP, hm, Option.bind_eq_bind, Option.bind, Option.some.injEq] at h
      subst h
      obtain ⟨us, hus, hfx⟩ := mapM_mem_ex _ _ _ hm (mn, i, cs) hin
      obtain ⟨c, seed, envC, us', hf, hok, hsd, hcc, huu, hus'⟩ := childUpsF_inv hfx
      refine ⟨c, seed, envC, us', hf, hok, hsd, hcc, huu, ?_⟩
      rw [sliceUps_root,
        sliceUps_flatten_mapM i _ (fun x => x.2.1) (fun x us h => childUpsF_head h) _ L hm
          (by simpa using hnd) (mn, i, cs) hin rfl us hfx,
        hus', sliceUps_prefix_same]

/-! ## L3 (lookup): a sub-design of the parent's real design, and the initial state path -/

theorem findMod_name {d : Design} {n : String} {c : Module} (h : findMod d n = some c) :
    c.name = n := by
  unfold findMod at h
  have := List.find?_some h
  simpa using this

theorem findMod_of_mem {d : Design} (hnd : (d.modules.map (·.name)).Nodup) {c : Module}
    (hc : c ∈ d.modules) : findMod d c.name = some c := by
  unfold findMod
  generalize d.modules = l at hnd hc
  induction l with
  | nil => cases hc
  | cons x rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hc with rfl | hm
    · simp [List.find?_cons]
    · have hne : x.name ≠ c.name := fun e => hnd.1 (List.mem_map.mpr ⟨c, hm, e.symm⟩)
      simp [List.find?_cons, hne, ih hnd.2 hm]

/-- A module list contained in the parent's (names distinct) resolves names exactly as the parent. -/
theorem subDesign_of_subset {dC d : Design} (hnd : (d.modules.map (·.name)).Nodup)
    (hsub : ∀ x ∈ dC.modules, x ∈ d.modules) : SubDesign dC d := by
  intro n c h
  have hc := findMod_mem h
  have hn := findMod_name h
  subst hn
  exact findMod_of_mem hnd (hsub c hc)

theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
    ∀ (l1 l2 : List α), l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length := by
  intro l1
  induction l1 with
  | nil => intro l2 _ _; exact Nat.zero_le _
  | cons a t ih =>
    intro l2 hnd hsub
    have hat : a ∉ t := (List.nodup_cons.mp hnd).1
    have hnt : t.Nodup := (List.nodup_cons.mp hnd).2
    have ha2 : a ∈ l2 := hsub a (List.mem_cons_self ..)
    have h2 : ∀ x ∈ t, x ∈ l2.erase a := by
      intro x hx
      have hne : x ≠ a := fun e => hat (e ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (List.mem_cons_of_mem _ hx))
    have := ih (l2.erase a) hnt h2
    rw [List.length_erase_of_mem ha2] at this
    have hpos : 0 < l2.length := List.length_pos_of_mem ha2
    simp only [List.length_cons]
    omega

/-- The sub-design is strictly smaller than the parent's design when the child itself is a module of
the parent that is not in the sub-design: the child's fuel `fuelR dC` fits under the parent's. -/
theorem fuel_le_of_sub {dC d : Design} (hndC : (dC.modules.map (·.name)).Nodup)
    (hsub : ∀ x ∈ dC.modules, x ∈ d.modules) {c : Module} (hc : c ∈ d.modules)
    (hcn : c ∉ dC.modules) : fuelR dC ≤ d.modules.length + 1 := by
  have hnd' : dC.modules.Nodup :=
    (List.pairwise_map.mp hndC).imp (fun {a b} h e => h (congrArg (·.name) e))
  have h1 : (c :: dC.modules).Nodup := List.nodup_cons.mpr ⟨hcn, hnd'⟩
  have h2 : ∀ x ∈ c :: dC.modules, x ∈ d.modules := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc
    · exact hsub x hx
  have := length_le_of_nodup_subset _ _ h1 h2
  simp only [List.length_cons] at this
  unfold fuelR
  omega

theorem st0Path_cons {d : Design} {m : Module} {mn i : String} {cs : List (String × Expr)}
    {c : Module} (hnd : (instNames m.body).Nodup) (hin : Stmt.inst mn i cs ∈ m.body)
    (hf : findMod d mn = some c) (p : Path) : st0Path d m (i :: p) = st0Path d c p := by
  have hmem : (mn, i, cs) ∈ instDecls m.body := (mem_instDecls_iff _ _).mpr hin
  have hfind : (instDecls m.body).find? (fun x => x.2.1 == i) = some (mn, i, cs) := by
    rw [instNames_eq] at hnd
    exact find_inst_decls _ hnd (mn, i, cs) hmem
  simp only [st0Path, hfind, hf]

/-- Every instance of the body resolves in `d`. -/
def ResolvedIn (d : Design) (c : Module) : Prop :=
  ∀ mn i cs, Stmt.inst mn i cs ∈ c.body → ∃ c', findMod d mn = some c'

theorem st0Path_agree {dC d : Design} (hs : SubDesign dC d)
    (hall : ∀ x ∈ dC.modules, ResolvedIn dC x) :
    ∀ (p : Path) (c0 : Module), ResolvedIn dC c0 → st0Path dC c0 p = st0Path d c0 p := by
  intro p
  induction p with
  | nil => intro c0 _; rfl
  | cons i p ih =>
    intro c0 hr
    simp only [st0Path]
    cases hx : (instDecls c0.body).find? (fun x => x.2.1 == i) with
    | none => rfl
    | some x =>
      obtain ⟨mn, i', cs⟩ := x
      simp only []
      have hmem : (mn, i', cs) ∈ instDecls c0.body := List.mem_of_find?_eq_some hx
      obtain ⟨c', hf⟩ := hr mn i' cs ((mem_instDecls_iff _ _).mp hmem)
      rw [hf, hs mn c' hf]
      exact ih c' (hall c' (findMod_mem hf))

theorem connsOkR_find {d : Design} {m : Module} {mn : String} {cs : List (String × Expr)}
    (h : connsOkR d m mn cs = true) : ∃ c, findMod d mn = some c := by
  unfold connsOkR at h
  cases hf : findMod d mn with
  | none => simp [hf] at h
  | some c => exact ⟨c, rfl⟩

theorem leafBody_no_inst {b : List Stmt} (h : leafBody b = true) :
    ∀ mn i cs, Stmt.inst mn i cs ∈ b → False := by
  intro mn i cs hin
  have := (mem_instDecls_iff b (mn, i, cs)).mpr hin
  rw [instDecls_leaf b h] at this
  cases this

theorem HierShapeR_resolved {d : Design} {m : Module} (h : HierShapeR d m = true) :
    ResolvedIn d m ∧ ∀ x ∈ d.modules, ResolvedIn d x := by
  simp only [HierShapeR, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, h5⟩, _⟩, _⟩, _⟩, hmods⟩ := h
  refine ⟨?_, ?_⟩
  · intro mn i cs hin
    have := List.all_eq_true.mp h5 _ hin
    exact connsOkR_find this
  · intro x hx mn i cs hin
    have hx' := List.all_eq_true.mp hmods x hx
    cases hl : leafBody x.body with
    | true => exact (leafBody_no_inst hl mn i cs hin).elim
    | false =>
      simp only [hl, Bool.false_or, modShapeR, Bool.and_eq_true] at hx'
      obtain ⟨⟨⟨⟨_, h2⟩, _⟩, _⟩, _⟩ := hx'
      exact connsOkR_find (List.all_eq_true.mp h2 _ hin)

end Tools.VedU2HierRec
