import Lean

/-!
# Slices of the packed register file (`ved.sseq.slice`, sparkle-ved-multiout unit 11)

A module with registers keeps ONE packed wire for its register file (`concat [r_0, r_1, …]`, MSB first) and reads each
register back by a (cascade of) slice(s).  After the evaluator is unfolded that wire is the nested natural number

  `pk A m₁ m₂ B  :=  A % m₁ * m₂ + B % m₂`      (`A` the first register, `m₁ = 2^w₀`; `B` the pack of the rest, `m₂ = 2^R`)

with `B` again of the same shape, and every read of register `k` is a slice of it.  Left to `simp`, the whole `K`-register
shape is inlined at every read (class (b), lost sharing; measured, toy K=26/N=50: 282M-node tree at `ved_ss_gen2`).

The local facts used here, all unconditional in the data (only literal side conditions `0 < m` / `m₁ * m₂ = M`, closed by `simp`):

* `ved_slice_div`  `(A % m₁ * m₂ + B % m₂) / m₂ = A % m₁`    — the first register (its `% m₁` is then removed by `Nat.mod_mod`);
* `ved_slice_mod`  `(A % m₁ * m₂ + B % m₂) % m₂ = B % m₂`    — the rest of the pack (the next cascade level);
* `ved_slice_modM` `(A % m₁ * m₂ + B % m₂) % M = A % m₁ * m₂ + B % m₂` for `m₁ * m₂ = M` (the whole pack fits its width).

Applied from the innermost read outwards, a read of register `k` (any depth) becomes `x_k % 2^{w_k}` after `k` uses of
`ved_slice_mod` / `ved_slice_modM` and one of `ved_slice_div`: the per-register slice fact
`(pack x₀ … x_{K-1}) / 2^{a_k} % 2^{w_k} = x_k % 2^{w_k}` is the composite of these, proved by one generic induction, not
once per register by `omega`/`simp` over the whole pack.
-/

namespace Tools.VedU1StructSlice

theorem ved_slice_div (A B m₁ m₂ : Nat) (h : 0 < m₂) : (A % m₁ * m₂ + B % m₂) / m₂ = A % m₁ := by
  have hb : B % m₂ < m₂ := Nat.mod_lt _ h
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ h, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem ved_slice_mod (A B m₁ m₂ : Nat) : (A % m₁ * m₂ + B % m₂) % m₂ = B % m₂ := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem ved_slice_modM (A B m₁ m₂ M : Nat) (h₁ : 0 < m₁) (hM : m₁ * m₂ = M) :
    (A % m₁ * m₂ + B % m₂) % M = A % m₁ * m₂ + B % m₂ := by
  subst hM
  rcases Nat.eq_zero_or_pos m₂ with h0 | h0
  · subst h0; simp
  · apply Nat.mod_eq_of_lt
    have h1 : A % m₁ + 1 ≤ m₁ := Nat.mod_lt _ h₁
    have h2 : B % m₂ < m₂ := Nat.mod_lt _ h0
    have h3 := Nat.mul_le_mul_right m₂ h1
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega


/-! ## Non-recursive zeta of the source value (`ved.sseq.zeta`)

`simp` zeta-reduces a `let`/`have` chain recursively (one stack frame group per link): on R184's `wPointOp` the stage
`ved_ss_core_simp_big [...] at hvsrc` stops with "maximum recursion depth has been reached" before any rewrite happens
(budgets are not raised).  `ved_ss_zeta h [F, …]` replaces the type of `h` by its let-free form, computed by an explicit
loop over every chain (`instantiate1` with the already-reduced value; every distinct sub-term is visited once through a
pointer-keyed cache, so the sharing of the value is kept) and, at the same time, unfolds the listed constants (the user's
own definition `F`, which `simp` would unfold by its equation lemma).  The new type is definitionally equal to the old one
(zeta and delta only): it is installed with `replaceLocalDeclDefEq` (no `isDefEq` in Meta; the kernel checks it).
-/

open Lean Meta Elab Tactic

/-- tree size of `e`, one visit per distinct sub-term -/
partial def treeOf (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get).get? e then return n
  let r ← match e with
    | .app f a => do pure ((← treeOf f) + (← treeOf a) + 1)
    | .lam _ t b _ => do pure ((← treeOf t) + (← treeOf b) + 1)
    | .forallE _ t b _ => do pure ((← treeOf t) + (← treeOf b) + 1)
    | .letE _ t v b _ => do pure ((← treeOf t) + (← treeOf v) + (← treeOf b) + 1)
    | .mdata _ b => do pure ((← treeOf b) + 1)
    | .proj _ _ b => do pure ((← treeOf b) + 1)
    | _ => pure 1
  modify (·.insert e r)
  return r

/-- (DAG size, tree size) of `e` -/
def dagTree (e : Expr) : Nat × Nat :=
  let (t, m) := (treeOf e).run {}
  (m.size, t)

/-- the depth of `e` as a tree of sub-terms (what a recursive traversal such as `simp`'s pays against `maxRecDepth`) -/
partial def depthOf (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get).get? e then return n
  let r ← match e with
    | .app f a => do pure (max (← depthOf f) (← depthOf a) + 1)
    | .lam _ t b _ => do pure (max (← depthOf t) (← depthOf b) + 1)
    | .forallE _ t b _ => do pure (max (← depthOf t) (← depthOf b) + 1)
    | .letE _ t v b _ => do pure (max (max (← depthOf t) (← depthOf v)) (← depthOf b) + 1)
    | .mdata _ b => do pure ((← depthOf b) + 1)
    | .proj _ _ b => do pure ((← depthOf b) + 1)
    | _ => pure 0
  modify (·.insert e r)
  return r

structure ZS where
  cache : Std.HashMap Expr Expr := {}
  lets : Nat := 0
  deltas : Nat := 0

mutual
/-- zeta (`letE`, `letFun`) and delta of `consts`, one visit per distinct sub-term -/
partial def zetaVisit (consts : Array Name) (e : Expr) : StateT ZS MetaM Expr := do
  if let some r := (← get).cache.get? e then return r
  let r ← match e with
    | .letE .. => zetaLets consts e
    | .app .. =>
      let fn := e.getAppFn
      if fn.isConstOf ``letFun && e.getAppNumArgs == 4 then zetaLets consts e
      else if let .const n us := fn then
        if consts.contains n then
          match (← getEnv).find? n with
          | some (.defnInfo ci) =>
            -- not a recursive definition (its value is the compiled `brecOn` / `WellFounded.fix` form)
            let v := ci.value
            if v.find? (fun x => x.isConstOf ``WellFounded.fix || (x.constName?.any fun c => c.isStr && c.getString! == "brecOn")) |>.isNone then
              modify fun st => { st with deltas := st.deltas + 1 }
              zetaVisit consts ((v.instantiateLevelParams ci.levelParams us).beta e.getAppArgs)
            else zetaApp consts e
          | _ => zetaApp consts e
        else zetaApp consts e
      else zetaApp consts e
    | .lam n t b bi => do
      let t' ← zetaVisit consts t
      let b' ← zetaVisit consts b
      pure (if t' == t && b' == b then e else .lam n t' b' bi)
    | .forallE n t b bi => do
      let t' ← zetaVisit consts t
      let b' ← zetaVisit consts b
      pure (if t' == t && b' == b then e else .forallE n t' b' bi)
    | .mdata d b => do
      let b' ← zetaVisit consts b
      pure (if b' == b then e else .mdata d b')
    | .proj sn i b => do
      let b' ← zetaVisit consts b
      pure (if b' == b then e else .proj sn i b')
    | _ => pure e
  modify fun st => { st with cache := st.cache.insert e r }
  return r

partial def zetaApp (consts : Array Name) (e : Expr) : StateT ZS MetaM Expr := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let fn' ← zetaVisit consts fn
  let mut changed := !fn' == fn
  let mut args' : Array Expr := #[]
  for a in args do
    let a' ← zetaVisit consts a
    changed := changed || !a' == a
    args' := args'.push a'
  pure (if changed then mkAppN fn' args' else e)

/-- a `let`/`have` chain: the links are taken off in a loop (the value reduced first, then substituted into the rest) -/
partial def zetaLets (consts : Array Name) (e : Expr) : StateT ZS MetaM Expr := do
  let mut cur := e
  repeat
    match cur with
    | .letE _ _ v b _ =>
      let v' ← zetaVisit consts v
      modify fun st => { st with lets := st.lets + 1 }
      cur := b.instantiate1 v'
    | _ =>
      if cur.isAppOfArity ``letFun 4 then
        let v' ← zetaVisit consts (cur.getArg! 2)
        modify fun st => { st with lets := st.lets + 1 }
        match cur.getArg! 3 with
        | .lam _ _ b _ => cur := b.instantiate1 v'
        | f => cur := (mkApp f v').headBeta
      else break
  zetaVisit consts cur
end

/-- `ved_ss_zeta h [F, …]`: the type of `h` with every `let`/`have` chain reduced non-recursively and the constants `F, …`
unfolded; the DAG and tree sizes before and after go to `VED_MS_LOG` -/
elab "ved_ss_zeta " h:ident " [" ns:ident,* "]" : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let consts ← ns.getElems.mapM fun n => realizeGlobalConstNoOverloadWithInfo n
  let t0 ← IO.monoMsNow
  let (ty', st) ← (zetaVisit consts ty).run {}
  let t1 ← IO.monoMsNow
  if let some path ← IO.getEnv "VED_MS_LOG" then
    let (d0, tr0) := dagTree ty
    let (d1, tr1) := dagTree ty'
    let dp0 := ((depthOf ty).run' {})
    let dp1 := ((depthOf ty').run' {})
    let hd ← IO.FS.Handle.mk path .append
    hd.putStrLn s!"VED ZETA {h.getId}: lets={st.lets} deltas={st.deltas} before dag={d0} tree={tr0} depth={dp0}; after dag={d1} tree={tr1} depth={dp1}; {t1 - t0}ms"
    hd.flush
  let g ← getMainGoal
  replaceMainGoal [← g.replaceLocalDeclDefEq d.fvarId ty']

end Tools.VedU1StructSlice
