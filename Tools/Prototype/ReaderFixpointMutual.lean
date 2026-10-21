import Tools.Prototype.ReaderFixpoint

/-! # Unit LC8 prototype (part 3): the MUTUAL shape, on a reduced model

ISOLATED, REDUCED MODEL (NOT a copy of the production group): `convR` has only the arms `.lam`, `.app`,
`.letE` (which calls the partner `loopBodyM`, as `machConv` calls `machLoopRoot`/`machNested`), `.mdata`/
`.proj` refusal and the catch-all; `loopBodyM` is the verbatim body of `machLoopBody` with `machConv`
replaced by `convR`.  Purpose: show that Lean 4.32.1 accepts `partial_fixpoint` for a MUTUAL group in
`Option` whose members recurse into each other and through `List.foldlM`, and that the JOINT invariant on
successes is one induction over the group.

BUILT: lc8l, lc8s, lc8t exit 0 (Tools.Prototype.ReaderFixpointMutual; axioms propext, Classical.choice,
Quot.sound).  No `sorry`, no axiom, no `native_decide`.  The `Option` + `findSome?` shape that the production
code has is REJECTED by Lean 4.32.1 (recorded below as text, not as code); the `Option (Option _)` +
`findSomeM?` shape is accepted and carries the joint invariant `joint_lets_mono`. -/
namespace Tools.Prototype.ReaderFixpointMutual
open Lean Sparkle.Compiler.Elab Tools.Prototype.ReaderFixpoint

/-! ### Attempt 1 (RECORDED, does not build): the production shape `Option` + `findSome?`

With the production types (`Option` result, refusal = `none`) lean REJECTS the group:
(i) `match loopRootR … with | some … => … | none => none` on a recursive call is not monotone-provable (this
one is fixed by writing `do`, as below); (ii) `st.loopWs.findSome? (fun … => match loopBodyM … with …)`
(the sharing probe of `machLoopRoot`, and `st.nested.findSome?` of `machNested`) is rejected:
`findSome?` is NOT monotone in a flat order where `none` means both "refused" and "diverged" (a probe that
turns from `none` into `some _` changes the answer from the NEXT element's to its own).  See the proposal.

### Attempt 2 (BUILT): refusal and divergence told apart, `Option (Option α)`
outer `none` = no finite derivation (the least fixpoint's bottom), `some none` = refusal, `some (some a)` =
success.  This is the encoding of the existing fuel twin (`Tools/ShippingReaderFuelDefs.lean`, `RB`). -/
mutual
def convR (senv : StructEnv) : List MachVal → Nat → Lean.Expr → MachRead →
    Option (Option (Lean.Expr × MachRead))
  | env, d, .lam nm t b bi, st => do
    let r ← convR senv env d t st
    match r with
    | none => pure none
    | some (t', st) => do
      let r ← convR senv env (d + 1) b st
      match r with
      | none => pure none
      | some (b', st) => pure (some (.lam nm t' b' bi, st))
  | env, d, .app f a, st => do
    let r ← convR senv env d f st
    match r with
    | none => pure none
    | some (f', st) => do
      let r ← convR senv env d a st
      match r with
      | none => pure none
      | some (a', st) => pure (some (.app f' a', st))
  | env, _, e@(.letE nm ty v b nd), st =>
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then do
      let r ← loopRootR senv env v st
      match r with
      | none => pure none
      | some (mv, st) => convR senv (mv :: env) 0 b st
    else do
      let r ← loopBodyM senv 0 env e st
      match r with
      | none => pure none
      | some st => pure (some (e, st))
  | _, _, .mdata .., _ => pure none
  | _, _, .proj .., _ => pure none
  | _, _, e, st => pure (some (e, st))
partial_fixpoint

def loopBodyM (senv : StructEnv) (base : Nat) :
    List MachVal → Lean.Expr → MachRead → Option (Option MachRead)
  | env, .letE nm ty v b _, st => do
    let r ← convR senv env 0 v st
    match r with
    | none => pure none
    | some (v', st) =>
      let (x, lets) := if machIsSlot v' then machBindLetNamed nm ty v' st.lets
        else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
        else machBindLet nm ty v' st.lets
      loopBodyM senv base (.val x :: env) b { st with lets := lets }
  | env, tail, st =>
    match machLoopRegs tail with
    | none => pure none
    | some regs => do
      let r ← regs.foldlM (init := (some (([] : List (Nat × Lean.Expr)), st)))
        fun acc (_, _, nx) =>
          match acc with
          | none => pure none
          | some (ws, st) => do
            let r ← convR senv env 0 nx st
            match r with
            | none => pure none
            | some (nx', st) => pure (some (ws ++ [(base + ws.length, nx')], st))
      match r with
      | none => pure none
      | some (ws, st) => pure (some { st with ws := st.ws ++ ws.toArray })
partial_fixpoint

/-- `machLoopRoot` in the `Option (Option _)` encoding; the sharing probe is `List.findSomeM?`. -/
def loopRootR (senv : StructEnv) (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    Option (Option (MachVal × MachRead)) :=
  match inlSpine e [] with
  | (.const ``Sparkle.Core.Signal.Signal.loop _, [dom, _, _, .lam _ _ body _]) =>
    if st.inInner then pure none else
    match machLoopRegs (machLetTail body) with
    | none => pure none
    | some regs =>
    if regs.any (fun (ty, init, _) => ty.hasLooseBVars || init.hasLooseBVars) then pure none else
    match regs.mapM (fun (ty, _, _) => machSlotKind? ty) with
    | none => pure none
    | some kinds =>
    match (kinds.zip regs).mapM (fun (k, (_, init, _)) => machInit? senv.natOf k init) with
    | none => pure none
    | some inits => do
      let r ← convR senv env 0 dom st
      match r with
      | none => pure none
      | some (dom', st) =>
      if (match st.dom with | some d0 => d0 != dom' | none => false) then pure none else do
      let n := kinds.length
      let shared ← st.loopWs.toList.findSomeM? fun (b0, n0, ws0) =>
        if n0 != n then pure none else do
          let r ← loopBodyM senv b0 (.state b0 n :: env) body { st with ws := #[] }
          pure (match r with
            | some st' => if st'.ws.toList == ws0 then some (b0, { st' with ws := st.ws }) else none
            | none => none)
      match shared with
      | some (b0, st') => pure (some (.state b0 n, st'))
      | none =>
      let base := st.kinds.size
      let depth := st.loopDepth
      let st := { st with
        kinds := st.kinds ++ kinds.toArray
        inits := st.inits ++ inits.toArray
        names := st.names ++ ((List.range n).map fun i =>
          Name.mkSimple s!"loop{st.loops.size}_r{i}").toArray
        dom := some dom'
        loops := st.loops.push (base, n)
        nestedLoops := if depth ≥ 1 then st.nestedLoops + 1 else st.nestedLoops
        loopDepth := depth + 1 }
      let before := st.ws.size
      let r ← loopBodyM senv base (.state base n :: env) body st
      match r with
      | none => pure none
      | some st => pure (some (.state base n,
          { st with loopWs := st.loopWs.push (base, n, (st.ws.toList.drop before)),
                    loopDepth := depth }))
  | _ => pure none
partial_fixpoint
end



private theorem bind_size (nm : Name) (ty v' : Lean.Expr) (lets : MachLets) :
    lets.size ≤ (if machIsSlot v' then machBindLetNamed nm ty v' lets
          else if machIsLetVar v' then machBindLetAlias nm ty v' lets
          else machBindLet nm ty v' lets).2.size := by
  split
  · exact machBindLetNamed_size
  · split
    · exact machBindLetAlias_size
    · exact machBindLet_size

/-- `List.findSomeM?` in `Option`: a found value satisfies what every probe answer satisfies. -/
theorem findSomeM_inv {α β : Type} (P : β → Prop) (f : α → Option (Option β))
    (hf : ∀ a r, f a = some (some r) → P r) :
    ∀ (l : List α) (x : β), l.findSomeM? f = some (some x) → P x
  | [], x, h => by simp [List.findSomeM?] at h
  | a :: as, x, h => by
    simp only [List.findSomeM?] at h
    obtain ⟨o, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    cases o with
    | some b => simp at h2; subst h2; exact hf a b h1
    | none => exact findSomeM_inv P f hf as x h2

/-- the step function of `loopBodyM`'s tail fold -/
def foldStep (conv : Nat → Lean.Expr → MachRead → Option (Option (Lean.Expr × MachRead)))
    (base : Nat) (acc : Option (List (Nat × Lean.Expr) × MachRead))
    (r : Lean.Expr × Lean.Expr × Lean.Expr) : Option (Option (List (Nat × Lean.Expr) × MachRead)) :=
  match acc with
  | none => pure none
  | some (ws, st) => do
    let r' ← conv 0 r.2.2 st
    match r' with
    | none => pure none
    | some (nx', st) => pure (some (ws ++ [(base + ws.length, nx')], st))

theorem foldStep_none (conv) (base) :
    ∀ regs : List (Lean.Expr × Lean.Expr × Lean.Expr),
      regs.foldlM (foldStep conv base) none = some none
  | [] => rfl
  | a :: as => by
    simp only [List.foldlM, foldStep]
    exact foldStep_none conv base as

theorem foldStep_inv (conv : Nat → Lean.Expr → MachRead → Option (Option (Lean.Expr × MachRead)))
    (hc : ∀ nx st x, conv 0 nx st = some (some x) → st.lets.size ≤ x.2.lets.size)
    (base : Nat) :
    ∀ (regs : List (Lean.Expr × Lean.Expr × Lean.Expr)) ws0 st0 y,
      regs.foldlM (foldStep conv base) (some (ws0, st0)) = some (some y) →
      st0.lets.size ≤ y.2.lets.size
  | [], ws0, st0, y, h => by
    simp [List.foldlM] at h; subst h; exact Nat.le_refl _
  | a :: as, ws0, st0, y, h => by
    simp only [List.foldlM, foldStep] at h
    obtain ⟨o, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨o2, h3, h4⟩ := Option.bind_eq_some_iff.mp h1
    cases o2 with
    | none => simp at h4; subst h4; rw [foldStep_none] at h2; simp at h2
    | some p =>
      obtain ⟨nx', st1⟩ := p
      simp at h4; subst h4
      exact Nat.le_trans (hc _ _ _ h3) (foldStep_inv conv hc base as _ _ _ h2)

/-- the sharing probe of `loopRootR` (a `findSomeM?` closure calling a recursive member) never shrinks
the `let` table of its answer, given that member does not. -/
theorem probe_inv
    (g : Nat → List MachVal → Lean.Expr → MachRead → Option (Option MachRead))
    (hg : ∀ base env e st x, g base env e st = some (some x) → st.lets.size ≤ x.lets.size)
    (env : List MachVal) (body : Lean.Expr) (n : Nat) (st : MachRead) :
    ∀ (a : Nat × Nat × List (Nat × Lean.Expr)) (r : Nat × MachRead),
      (fun (x : Nat × Nat × List (Nat × Lean.Expr)) =>
        match x with
        | (b0, n0, ws0) =>
          if (n0 != n) = true then (pure none : Option (Option (Nat × MachRead))) else do
            let r ← g b0 (.state b0 n :: env) body { st with ws := #[] }
            pure (match r with
              | some st' => if (st'.ws.toList == ws0) = true then some (b0, { st' with ws := st.ws })
                  else none
              | none => none)) a = some (some r) →
      st.lets.size ≤ r.2.lets.size := by
  intro a r h
  obtain ⟨b0, n0, ws0⟩ := a
  simp only [] at h
  split at h
  · simp at h
  · obtain ⟨o, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    cases o with
    | none => simp at h2
    | some st' =>
      have := hg _ _ _ _ _ h1
      simp only [] at h2
      split at h2
      · simp at h2; subst h2; exact this
      all_goals simp at h2

/-- **JOINT invariant on successes of the 3-member mutual group** (`convR`, `loopBodyM`, `loopRootR`):
no member shrinks the `let` table.  ONE induction (`mutual_partial_correctness`); no hypothesis on any
partner; the `findSomeM?` sharing probe and the `foldlM` are covered. -/
theorem joint_lets_mono (senv : StructEnv) :
    (∀ env d e st x, convR senv env d e st = some (some x) → st.lets.size ≤ x.2.lets.size) ∧
    (∀ base env e st x, loopBodyM senv base env e st = some (some x) → st.lets.size ≤ x.lets.size) ∧
    (∀ env e st x, loopRootR senv env e st = some (some x) → st.lets.size ≤ x.2.lets.size) := by
  have := convR.mutual_partial_correctness senv
    (fun _ _ _ st r => ∀ x, r = some x → st.lets.size ≤ x.2.lets.size)
    (fun _ _ _ st r => ∀ x, r = some x → st.lets.size ≤ x.lets.size)
    (fun _ _ st r => ∀ x, r = some x → st.lets.size ≤ x.2.lets.size) ?_ ?_ ?_
  · exact ⟨fun env d e st x h => this.1 env d e st (some x) h x rfl,
           fun base env e st x h => this.2.1 base env e st (some x) h x rfl,
           fun env e st x h => this.2.2 env e st (some x) h x rfl⟩
  · intro f g k ih1 ih2 ih3 env d e st r h x hx
    split at h
    · obtain ⟨o1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      cases o1 with
      | none => simp at h2; subst h2; simp at hx
      | some p =>
        obtain ⟨t', st1⟩ := p
        obtain ⟨o2, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
        cases o2 with
        | none => simp at h4; subst h4; simp at hx
        | some q =>
          obtain ⟨b', st2⟩ := q
          simp at h4; subst h4; simp at hx; subst hx
          exact Nat.le_trans (ih1 _ _ _ _ _ h1 (t', st1) rfl) (ih1 _ _ _ _ _ h3 (b', st2) rfl)
    · obtain ⟨o1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      cases o1 with
      | none => simp at h2; subst h2; simp at hx
      | some p =>
        obtain ⟨t', st1⟩ := p
        obtain ⟨o2, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
        cases o2 with
        | none => simp at h4; subst h4; simp at hx
        | some q =>
          obtain ⟨b', st2⟩ := q
          simp at h4; subst h4; simp at hx; subst hx
          exact Nat.le_trans (ih1 _ _ _ _ _ h1 (t', st1) rfl) (ih1 _ _ _ _ _ h3 (b', st2) rfl)
    · split at h
      · obtain ⟨o1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
        cases o1 with
        | none => simp at h2; subst h2; simp at hx
        | some p =>
          obtain ⟨mv, st1⟩ := p
          exact Nat.le_trans (ih3 _ _ _ _ h1 _ rfl) (ih1 _ _ _ _ _ h2 x hx)
      · obtain ⟨o1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
        cases o1 with
        | none => simp at h2; subst h2; simp at hx
        | some st1 =>
          simp at h2; subst h2; simp at hx; subst hx
          exact ih2 _ _ _ _ _ h1 _ rfl
    · simp at h; subst h; simp at hx
    · simp at h; subst h; simp at hx
    · simp at h; subst h; simp at hx; subst hx; exact Nat.le_refl _
  · intro f g ih1 ih2 base env e st r h x hx
    split at h
    · rename_i nm ty v b nd
      obtain ⟨o1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      cases o1 with
      | none => simp at h2; subst h2; simp at hx
      | some p =>
        obtain ⟨v', st1⟩ := p
        have hb := bind_size nm ty v' st1.lets
        dsimp only at h2
        generalize (if machIsSlot v' then machBindLetNamed nm ty v' st1.lets
          else if machIsLetVar v' then machBindLetAlias nm ty v' st1.lets
          else machBindLet nm ty v' st1.lets) = q at hb h2
        obtain ⟨x', lets'⟩ := q
        exact Nat.le_trans (ih1 _ _ _ _ _ h1 _ rfl)
          (Nat.le_trans hb (ih2 _ _ _ _ _ h2 x hx))
    · split at h
      · simp at h; subst h; simp at hx
      · rename_i regs hregs
        obtain ⟨o1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
        cases o1 with
        | none => simp at h2; subst h2; simp at hx
        | some p =>
          obtain ⟨ws, st1⟩ := p
          simp at h2; subst h2; simp at hx; subst hx
          exact foldStep_inv (f env) (fun nx st x hx' => ih1 env 0 nx st _ hx' x rfl) base regs [] st
            (ws, st1) h1
  · intro f g ih1 ih2 env e st r h x hx
    split at h
    · rename_i dom body
      split at h
      · simp at h; subst h; simp at hx
      split at h
      · simp at h; subst h; simp at hx
      rename_i regs hregs
      split at h
      · simp at h; subst h; simp at hx
      split at h
      · simp at h; subst h; simp at hx
      rename_i kinds hk
      split at h
      · simp at h; subst h; simp at hx
      rename_i inits hi
      obtain ⟨o1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      cases o1 with
      | none => simp at h2; subst h2; simp at hx
      | some p =>
      obtain ⟨dom', st1⟩ := p
      simp only [] at h2
      split at h2
      · split at h2
        · simp at h2; subst h2; simp at hx
        · obtain ⟨o2, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
          have hd := ih1 _ _ _ _ _ h1 (dom', st1) rfl
          cases o2 with
          | some q =>
            obtain ⟨b0, st'⟩ := q
            simp at h4; subst h4; simp at hx; subst hx
            exact Nat.le_trans hd (findSomeM_inv (fun y => st1.lets.size ≤ y.2.lets.size) _
              (probe_inv g (fun b en e s y h => ih2 b en e s _ h y rfl) env _ _ st1) _ _ h3)
          | none =>
            obtain ⟨o3, h5, h6⟩ := Option.bind_eq_some_iff.mp h4
            cases o3 with
            | none => simp at h6; subst h6; simp at hx
            | some st2 =>
              simp at h6; subst h6; simp at hx; subst hx
              exact Nat.le_trans hd (ih2 _ _ _ _ _ h5 st2 rfl)
      · obtain ⟨o2, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
        have hd := ih1 _ _ _ _ _ h1 (dom', st1) rfl
        cases o2 with
        | some q =>
          obtain ⟨b0, st'⟩ := q
          simp at h4; subst h4; simp at hx; subst hx
          exact Nat.le_trans hd (findSomeM_inv (fun y => st1.lets.size ≤ y.2.lets.size) _
            (probe_inv g (fun b en e s y h => ih2 b en e s _ h y rfl) env _ _ st1) _ _ h3)
        | none =>
          obtain ⟨o3, h5, h6⟩ := Option.bind_eq_some_iff.mp h4
          cases o3 with
          | none => simp at h6; subst h6; simp at hx
          | some st2 =>
            simp at h6; subst h6; simp at hx; subst hx
            exact Nat.le_trans hd (ih2 _ _ _ _ _ h5 st2 rfl)
    · simp at h; subst h; simp at hx

#print axioms joint_lets_mono

/-! ## Code generation of a `partial_fixpoint` definition (checked by IR trace, run `lc8j`) -/
def countdown (n : Nat) : Option Nat :=
  if n = 0 then some 0 else countdown (n - 1)
partial_fixpoint

#eval countdown 5

end Tools.Prototype.ReaderFixpointMutual
