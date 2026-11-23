import Lean
import Tools.VedMemLoop

/-!
# Local route for the tail goals (`ved.mem.s94Local`)

Observed (sparkle-ved-mem-s94, sixteenth unit): the 172 tail goals of R033 (after stamp 100) have 16 .. 2 900 DAG nodes each (tree 27 .. 8e11), the whole
design 11 552 DAG nodes in all, but every goal carries the full context of ~300 entries (the wire-environment facts `env "w" = tuple.snd.snd..`, the
state tuple, the case hypotheses) and the tail steps (`simp .. at *`, `omega`, `ved_loop_close`) read all of them: `simp only [ved_mul_lit_nat] at *`
costs ~29M heartbeats on EVERY goal, also on the goal `x.toNat = 4`.

`ved_cone_clear`: the cone of the main goal = the free variables of its target, and the context entries whose type mentions one of them (one step,
by the DAG, not the tree).  Every other entry is cleared (`tryClear`, so an entry that a kept entry depends on stays).
-/

namespace Tools.VedMemS94Local

open Lean Meta Elab Tactic Tools.VedU1WireShare

register_option ved.mem.s94Local : Bool := {
  defValue := false
  descr := "ved memory tail: close each tail goal from its own cone (context cleared to the entries that mention the target's variables) before the whole-goal tail steps; the old tail is the fallback (default false)"
}

/-- test seams / counters (CloseCheck) -/
initialize localHits : IO.Ref Nat ← IO.mkRef 0
initialize localTried : IO.Ref Nat ← IO.mkRef 0
initialize extractHits : IO.Ref Nat ← IO.mkRef 0
initialize localRefuse : IO.Ref Bool ← IO.mkRef false
initialize localFailLate : IO.Ref Bool ← IO.mkRef false

/-! ## the once-proved local lemmas: field extraction from a packed state `(a % 2^wl) * 2^s + r`, `r < 2^s` -/

theorem mod_div_mod (x M T Wm m t w : Nat) (hM : M = 2 ^ m) (hT : T = 2 ^ t) (hW : Wm = 2 ^ w) (h : t + w ≤ m) :
    x % M / T % Wm = x / T % Wm := by
  subst hM hT hW
  have h1 : 2 ^ m = 2 ^ t * 2 ^ (m - t) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow 2 (by omega)

theorem pack_hit (a r Wl C T Wm wl s : Nat) (hW : Wl = 2 ^ wl) (hC : C = 2 ^ s) (hT : T = C) (hWm : Wm = Wl)
    (hr : r < C) : (a % Wl * C + r) / T % Wm = a % Wl := by
  subst hT hWm
  have hCp : 0 < T := by subst hC; exact Nat.two_pow_pos s
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hCp, Nat.div_eq_of_lt hr, Nat.zero_add]
  exact Nat.mod_mod _ _

theorem pack_skip (a r Wl C T Wm wl s t w : Nat) (hW : Wl = 2 ^ wl) (hC : C = 2 ^ s) (hT : T = 2 ^ t) (hWm : Wm = 2 ^ w)
    (hr : r < C) (h : t + w ≤ s) : (a % Wl * C + r) / T % Wm = r / T % Wm := by
  subst hC hT hWm
  have hs : 2 ^ s = 2 ^ (s - t - w) * 2 ^ w * 2 ^ t := by rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have hTp : 0 < 2 ^ t := Nat.two_pow_pos t
  rw [hs, ← Nat.mul_assoc, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hTp]
  rw [Nat.add_mul_mod_self_right]

theorem mod_pow_dvd (a M Wm m w : Nat) (hM : M = 2 ^ m) (hW : Wm = 2 ^ w) (h : w ≤ m) : a % M % Wm = a % Wm := by
  subst hM hW
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)

theorem atom_div (x T Wm : Nat) (hT : T = 1) : x / T % Wm = x % Wm := by subst hT; rw [Nat.div_one]

theorem mod_as_div (x Wm : Nat) : x % Wm = x / 1 % Wm := by rw [Nat.div_one]

/-! ## the meta part: cone, field extraction, bounds -/

/-- the free variables of an expression, by the DAG -/
def fvarsOfDag (e : Expr) : Array FVarId := (collectDag (·.isFVar) e).map (·.fvarId!)

/-- a wire-environment fact `env "w" = ..` (the environment is a variable applied to a string literal): not part of a cone -/
def isEnvFact (t : Expr) : Bool :=
  match t.eq? with
  | some (_, .app (.fvar _) (.lit (.strVal _)), _) => true
  | _ => false

/-- the cone of the main goal: the free variables of its target, the context entries whose type mentions one of them (without the wire-environment
facts) and everything those entries depend on (types and values, to the fixpoint); the goal is replaced by one with the local context cut to the cone
(one pass, no `clear` per entry: that re-scans the context for every entry).  Returns (goal, entries kept, entries cleared) -/
def coneClear (g : MVarId) : MetaM (MVarId × Nat × Nat) := g.withContext do
  let lctx ← getLCtx
  let tgt ← instantiateMVars (← g.getType)
  let mut keep : Std.HashSet FVarId := {}
  let mut todo : Array FVarId := #[]
  for f in fvarsOfDag tgt do
    keep := keep.insert f
    todo := todo.push f
  let tfv := keep
  for d in lctx do
    if d.isImplementationDetail || keep.contains d.fvarId then continue
    let t ← instantiateMVars d.type
    if !isEnvFact t && (fvarsOfDag t).any (tfv.contains ·) then
      keep := keep.insert d.fvarId
      todo := todo.push d.fvarId
  while let some f := todo.back? do
    todo := todo.pop
    let d ← f.getDecl
    let mut xs := fvarsOfDag (← instantiateMVars d.type)
    if d.isLet then xs := xs ++ fvarsOfDag (← instantiateMVars d.value)
    for x in xs do
      unless keep.contains x do
        keep := keep.insert x
        todo := todo.push x
  let mut lctx' := lctx
  let mut cleared := 0
  for d in lctx do
    unless d.isImplementationDetail || keep.contains d.fvarId do
      lctx' := lctx'.erase d.fvarId
      cleared := cleared + 1
  if cleared == 0 then return (g, keep.size, 0)
  let insts := (← getLocalInstances).filter fun i => !i.fvar.isFVar || keep.contains i.fvar.fvarId!
  let newM ← mkFreshExprMVarAt lctx' insts tgt MetavarKind.syntheticOpaque (← g.getTag)
  g.assign newM
  return (newM.mvarId!, keep.size, cleared)

elab "ved_cone_clear" : tactic => do
  let g ← getMainGoal
  let (g', _, _) ← coneClear g
  replaceMainGoal [g']

private def nl (n : Nat) : Expr := mkNatLit n
private def pow2? (n : Nat) : Option Nat :=
  if n == 0 then none else
  let k := Nat.log2 n
  if 2 ^ k == n then some k else none
private def litNat? (e : Expr) : MetaM (Option Nat) := do
  if e.hasFVar || e.hasMVar then return none
  try evalNat e catch _ => pure none
private def leP (a b : Nat) : Expr := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (nl a) (nl b) (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
private def refl (e : Expr) : MetaM Expr := mkEqRefl e

/-- `E / T % Wm = v` for a packed state `E` (nested `(a % 2^wl) * 2^s + r % 2^s` under `% 2^m`): `v` is the field's value `a % 2^wl`
(`T = 2^t`, `Wm = 2^w` literals); the proof is built from the once-proved lemmas `mod_div_mod`, `pack_skip`, `pack_hit`, `atom_div` only -/
partial def extField (E T Wm : Expr) (t w : Nat) : MetaM (Option (Expr × Expr)) := do
  match E.getAppFnArgs with
  | (``HMod.hMod, #[_, _, _, _, x, M]) =>
    let some mv ← litNat? M | return none
    let some m := pow2? mv | return none
    unless t + w ≤ m do return none
    let some (v, pf) ← extField x T Wm t w | return none
    let step := mkAppN (mkConst ``mod_div_mod) #[x, M, T, Wm, nl m, nl t, nl w, ← refl M, ← refl T, ← refl Wm, leP (t + w) m]
    return some (v, ← mkEqTrans step pf)
  | (``HAdd.hAdd, #[_, _, _, _, ma, r]) =>
    let (``HMul.hMul, #[_, _, _, _, am, C]) := ma.getAppFnArgs | return none
    let (``HMod.hMod, #[_, _, _, _, a, Wl]) := am.getAppFnArgs | return none
    let some wlv ← litNat? Wl | return none
    let some wl := pow2? wlv | return none
    let some Cv ← litNat? C | return none
    let some s := pow2? Cv | return none
    let (``HMod.hMod, #[_, _, _, _, y, C']) := r.getAppFnArgs | return none
    unless (← litNat? C') == some Cv do return none
    let hr := mkApp3 (mkConst ``Nat.mod_lt) y C' (mkApp (mkConst ``Nat.two_pow_pos) (nl s))
    if t == s && w == wl then
      let pf := mkAppN (mkConst ``pack_hit) #[a, r, Wl, C, T, Wm, nl wl, nl s, ← refl Wl, ← refl C, ← refl C, ← refl Wl, hr]
      return some (am, pf)
    else if t + w ≤ s then
      let step := mkAppN (mkConst ``pack_skip) #[a, r, Wl, C, T, Wm, nl wl, nl s, nl t, nl w, ← refl Wl, ← refl C, ← refl T, ← refl Wm, hr, leP (t + w) s]
      let some (v, pf) ← extField r T Wm t w | return none
      return some (v, ← mkEqTrans step pf)
    else return none
  | _ =>
    unless t == 0 do return none
    let v ← mkAppM ``HMod.hMod #[E, Wm]
    return some (v, mkAppN (mkConst ``atom_div) #[E, T, Wm, ← refl T])

/-- a candidate `X` of the form `E / 2^t % 2^w` or `E % 2^w` (`E` a packed state or a `%` chain): the value and the proof of `X = v` -/
def tryExtract (X : Expr) : MetaM (Option (Expr × Expr)) := do
  let (``HMod.hMod, #[_, _, _, _, E, Wm]) := X.getAppFnArgs | return none
  let some wv ← litNat? Wm | return none
  let some w := pow2? wv | return none
  match E.getAppFnArgs with
  | (``HDiv.hDiv, #[_, _, _, _, E', T]) =>
    let some tv ← litNat? T | return none
    let some t := pow2? tv | return none
    extField E' T Wm t w
  | (``HAdd.hAdd, _) | (``HMod.hMod, _) =>
    let T := nl 1
    let some (v, pf) ← extField E T Wm 0 w | return none
    return some (v, ← mkEqTrans (mkAppN (mkConst ``mod_as_div) #[E, Wm]) pf)
  | _ => return none

/-- the first extraction candidate of an expression (parents first), by the DAG -/
def firstExtract (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  for x in collectDag (fun x => x.isAppOfArity ``HMod.hMod 6) e do
    if x.hasLooseBVars then continue
    if let some (v, pf) ← tryExtract x then return some (x, v, pf)
  return none

/-- rewrite every field extraction from a packed state in the target and in the context entries by the field's value; returns the goal and the number of rewrites -/
def extractAll (g0 : MVarId) : MetaM (MVarId × Nat) := do
  let mut g := g0
  let mut n := 0
  for _ in [0:64] do
    let mut progress := false
    let tgt ← g.withContext do instantiateMVars (← g.getType)
    if let some (x, v, pf) ← g.withContext (firstExtract tgt) then
      let motive ← g.withContext do withLocalDeclD `ved_x (← inferType x) fun xv => mkLambdaFVars #[xv] (tgt.replace fun e => if e == x then some xv else none)
      let newTgt := tgt.replace fun e => if e == x then some v else none
      g ← g.withContext do g.replaceTargetEq newTgt (← mkCongrArg motive pf)
      n := n + 1; progress := true
    let ds ← g.withContext do pure ((← getLCtx).decls.toList.filterMap id |>.filter (fun d => !d.isImplementationDetail) |>.map (·.fvarId))
    for f in ds do
      let found ← g.withContext do
        let t0 ← instantiateMVars (← f.getType)
        if t0.isForall then return none
        match ← firstExtract t0 with
        | some r => return some (t0, r)
        | none => return none
      if let some (t0, x, v, pf) := found then
        g ← g.withContext do
          let motive ← withLocalDeclD `ved_x (← inferType x) fun xv => mkLambdaFVars #[xv] (t0.replace fun e => if e == x then some xv else none)
          let newT := t0.replace fun e => if e == x then some v else none
          let eq ← mkCongrArg motive pf
          let pr ← mkAppM ``Eq.mp #[eq, mkFVar f]
          let (_, g1) ← (← g.assert (← f.getUserName) newT pr).intro1P
          g1.tryClear f
        n := n + 1; progress := true
        break
    if !progress then break
  return (g, n)

/-- `ved_pack_extract`: the field extractions from a packed state in the target and in the context (see `extField`); fails if nothing was rewritten -/
elab "ved_pack_extract" : tactic => do
  let g ← getMainGoal
  let (g', n) ← extractAll g
  if n == 0 then throwError "ved_pack_extract: no field extraction from a packed state"
  extractHits.modify (· + 1)
  replaceMainGoal [g']

/-- `ved_bv_bounds`: for each `BitVec` variable of the context, the fact `x.toNat < 2 ^ w` -/
elab "ved_bv_bounds" : tactic => do
  let mut g ← getMainGoal
  let fs ← g.withContext do
    let mut fs : Array Expr := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← whnfR (← instantiateMVars d.type)
      if t.isAppOf ``BitVec then fs := fs.push d.toExpr
    pure fs
  for x in fs do
    let (pr, ty) ← g.withContext do
      let pr ← mkAppM ``BitVec.isLt #[x]
      pure (pr, ← inferType pr)
    let (_, g1) ← (← g.assert `ved_bnd ty pr).intro1P
    g := g1
  replaceMainGoal [g]

/-- the goals of the local route are the small cones: a target with at most `ved.mem.s94Local` tree nodes (`localMaxTree`); `omega` and `split`
do not stop at the heartbeat limit on the large ones (observed: 1.2e9 heartbeats / 200 s on a 7e10-node goal with limit 3e7) -/
def localMaxTree : Nat := 2000000

elab "ved_local_small" : tactic => withMainContext do
  let n := Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← getMainTarget))
  if n > localMaxTree then throwError "ved_local_small: the target has {n} tree nodes (limit {localMaxTree})"

/-- `ved_local_close`: the goal from its own cone: cone clear, field extraction, bounds, then `omega` (with `split` for the `if`s) -/
macro "ved_local_close" : tactic =>
  `(tactic| (ved_cone_clear; ved_pack_extract; ved_local_small; (try dsimp only at *); ved_bv_bounds
             first | omega | (split <;> omega) | (split <;> split <;> omega)))

/-- the heartbeat limit of one local attempt (thousands; lower than any whole-goal step: a successful attempt needs at most about 4M) -/
def localCapK : Nat := 8000

/-- `ved_local_goal`: the local route for ONE goal (`ved.mem.s94Local`): `ved_local_close` under a heartbeat limit of its own; a goal it does not close stays exactly as it
was (state restored; also after a timeout, or when the test seam `localRefuse` / `localFailLate` is set) and the old tail handles it -/
elab "ved_local_goal" : tactic => do
  if ← localRefuse.get then throwError "ved_local_goal: refused (test seam)"
  localTried.modify (· + 1)
  let st ← saveState
  let hb0 ← IO.getNumHeartbeats
  let r ← tryCatchRuntimeEx
    (do
      withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then localCapK * 1000 else min c.maxHeartbeats (localCapK * 1000)), initHeartbeats := hb0 }) do
        evalTactic (← `(tactic| ved_local_close))
      if ← localFailLate.get then throwError "ved_local_goal: failed after its work (test seam)"
      pure true)
    (fun _ => pure false)
  if r then localHits.modify (· + 1)
  else
    st.restore
    throwError "ved_local_goal: the goal is not closed from its cone"

end Tools.VedMemS94Local
