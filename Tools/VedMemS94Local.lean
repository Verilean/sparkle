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

/-- a slice `[t, t+w)` of the field `a % 2^wl` at `[s, s+wl)` of a packed state (`s ≤ t`, `t + w ≤ s + wl`, `k = t - s`): the value is `a / 2^k % 2^w` -/
theorem pack_in (a r Wl C T Wm K wl s t w k : Nat) (hW : Wl = 2 ^ wl) (hC : C = 2 ^ s) (hT : T = 2 ^ t) (hWm : Wm = 2 ^ w) (hK : K = 2 ^ k)
    (hk : k + s = t) (hr : r < C) (hw : k + w ≤ wl) : (a % Wl * C + r) / T % Wm = a / K % Wm := by
  have hTC : T = C * K := by rw [hT, hC, hK, ← Nat.pow_add]; congr 1; omega
  have hCp : 0 < C := by subst hC; exact Nat.two_pow_pos s
  rw [hTC, ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.add_mul_div_right _ _ hCp, Nat.div_eq_of_lt hr, Nat.zero_add]
  exact mod_div_mod a Wl K Wm wl k w hW hK hWm hw

/-- the low `w ≤ wl` bits of the field at the start offset `s = t`: `a % 2^w` -/
theorem pack_hit_n (a r Wl C T Wm wl s w : Nat) (hW : Wl = 2 ^ wl) (hC : C = 2 ^ s) (hT : T = C) (hWm : Wm = 2 ^ w)
    (hr : r < C) (hw : w ≤ wl) : (a % Wl * C + r) / T % Wm = a % Wm := by
  subst hT
  have hCp : 0 < T := by subst hC; exact Nat.two_pow_pos s
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hCp, Nat.div_eq_of_lt hr, Nat.zero_add]
  subst hW hWm
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hw)

/-- the unmasked read `x % 2^m / 2^t` is the masked read `x % 2^m / 2^t % 2^(m-t)` (the mask is the top of the chain) -/
theorem div_top (x M T Wm m t w : Nat) (hM : M = 2 ^ m) (hT : T = 2 ^ t) (hW : Wm = 2 ^ w) (h : t + w = m) :
    x % M / T = x % M / T % Wm := by
  subst hM hT hW
  have h1 : 2 ^ m = 2 ^ t * 2 ^ w := by rw [← Nat.pow_add]; congr 1; omega
  symm
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos t), Nat.mul_comm, ← h1]
  exact Nat.mod_lt _ (Nat.two_pow_pos m)

/-! ## the register-update mux: `(if c then a else b) % m = if c' then a' else b'` (the declared next value of a register is a chain of `ite`, the
generated side the same chain under `% m`) closed branch by branch, without `split` (which runs `simp` on the whole 5e3-node goal and times out) -/

theorem mux_mod (c : Prop) [Decidable c] (a b m : Nat) : (if c then a else b) % m = if c then a % m else b % m := by
  by_cases h : c <;> simp [h]

theorem mux_cong {α : Sort _} (c c' : Prop) [Decidable c] [Decidable c'] (a b a' b' : α) (hc : c ↔ c') (ha : c → a = a') (hb : ¬c → b = b') :
    (if c then a else b) = (if c' then a' else b') := by
  by_cases h : c
  · rw [if_pos h, if_pos (hc.mp h)]; exact ha h
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]; exact hb h

theorem mux_l {α : Sort _} (c : Prop) [Decidable c] (a b r : α) (ha : c → a = r) (hb : ¬c → b = r) : (if c then a else b) = r := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

theorem mux_r {α : Sort _} (c : Prop) [Decidable c] (a b r : α) (ha : c → r = a) (hb : ¬c → r = b) : r = (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

/-- the mask of a 0/1 flag is redundant -/
theorem ite10_mod (p : Prop) [Decidable p] : (if p then 1 else 0) % 2 = (if p then 1 else 0 : Nat) := by
  by_cases h : p <;> simp [h]

/-- a 0/1 flag as a proposition: the condition of the case hypotheses `(if p then 1 else 0) % 2 = 1` -/
theorem ite10_mod2 (p : Prop) [Decidable p] : ((if p then 1 else 0) % 2 = 1) ↔ p := by
  by_cases h : p <;> simp [h]

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

/-- a hypothesis the local closer can use: an (in)equation / connective of arithmetic facts, not a `forall` (the memory facts `∀ a, env "m" (a % 16) = ..`) or an
invariant predicate (`MemInv ..`): `omega` ignores those, and `simp .. at *` pays for each of their (up to 4e5-node) terms -/
def isArithHyp (t : Expr) : Bool :=
  if t.isForall then false else
  match t.getAppFn with
  | .const n _ => n == ``Eq || n == ``Ne || n == ``LT.lt || n == ``LE.le || n == ``GT.gt || n == ``GE.ge || n == ``Not || n == ``And || n == ``Or || n == ``Iff
  | _ => false

/-- the cone of the main goal: the free variables of its target, the context entries whose type mentions one of them (without the wire-environment
facts) and everything those entries depend on (types and values, to the fixpoint); the goal is replaced by one with the local context cut to the cone
(one pass, no `clear` per entry: that re-scans the context for every entry).  Returns (goal, entries kept, entries cleared) -/
def coneClear (g : MVarId) (arithOnly : Bool := true) : MetaM (MVarId × Nat × Nat) := g.withContext do
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
    if !isEnvFact t && (fvarsOfDag t).any (tfv.contains ·) && (!arithOnly || !(← isProp t) || isArithHyp t) then
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

elab "ved_cone_clear_full" : tactic => do
  let g ← getMainGoal
  let (g', _, _) ← coneClear g false
  replaceMainGoal [g']

elab "ved_cone_clear" : tactic => do
  let g ← getMainGoal
  let (g', _, _) ← coneClear g
  replaceMainGoal [g']

/-- diagnosis: the free variables of the target after the cone clear, their types and the number of context hypotheses that mention them -/
elab "ved_cone_diag" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let mut out := ""
  for f in fvarsOfDag tgt do
    let d ← f.getDecl
    let mut n := 0
    for e in ← getLCtx do
      if e.isImplementationDetail || e.fvarId == f then continue
      if (← isProp e.type) && (fvarsOfDag (← instantiateMVars e.type)).contains f then n := n + 1
    let ty := (← ppExpr d.type).pretty.replace "\n" " "
    out := out ++ s!" {d.userName}:{ty.take 14}#{n}"
  logInfo m!"CONE{out}"

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

/-- diagnosis: the site (and offset t, width w) of the last `extField` failure -/
initialize extLastFail : IO.Ref String ← IO.mkRef ""
def failAt {α} (n t w : Nat) : MetaM (Option α) := do extLastFail.set s!"site {n} t={t} w={w}"; return none

/-- `E / T % Wm = v` for a packed state `E` (nested `(a % 2^wl) * 2^s + r % 2^s` under `% 2^m`): `v` is the field's value `a % 2^wl`
(`T = 2^t`, `Wm = 2^w` literals); the proof is built from the once-proved lemmas `mod_div_mod`, `pack_skip`, `pack_hit`, `atom_div` only -/
partial def extField (E T Wm : Expr) (t w : Nat) : MetaM (Option (Expr × Expr)) := do
  match E.getAppFnArgs with
  | (``HMod.hMod, #[_, _, _, _, x, M]) =>
    let some mv ← litNat? M | failAt 1 t w
    let some m := pow2? mv | failAt 2 t w
    unless t + w ≤ m do return (← failAt 3 t w)
    let some (v, pf) ← extField x T Wm t w | failAt 4 t w
    let step := mkAppN (mkConst ``mod_div_mod) #[x, M, T, Wm, nl m, nl t, nl w, ← refl M, ← refl T, ← refl Wm, leP (t + w) m]
    return some (v, ← mkEqTrans step pf)
  | (``HAdd.hAdd, #[_, _, _, _, ma, r]) =>
    let (``HMul.hMul, #[_, _, _, _, am, C]) := ma.getAppFnArgs | failAt 5 t w
    let (``HMod.hMod, #[_, _, _, _, a, Wl]) := am.getAppFnArgs | failAt 6 t w
    let some wlv ← litNat? Wl | failAt 7 t w
    let some wl := pow2? wlv | failAt 8 t w
    let some Cv ← litNat? C | failAt 9 t w
    let some s := pow2? Cv | failAt 10 t w
    let (``HMod.hMod, #[_, _, _, _, y, C']) := r.getAppFnArgs | failAt 11 t w
    unless (← litNat? C') == some Cv do return (← failAt 12 t w)
    let hr := mkApp3 (mkConst ``Nat.mod_lt) y C' (mkApp (mkConst ``Nat.two_pow_pos) (nl s))
    if t == s && w == wl then
      let pf := mkAppN (mkConst ``pack_hit) #[a, r, Wl, C, T, Wm, nl wl, nl s, ← refl Wl, ← refl C, ← refl C, ← refl Wl, hr]
      return some (am, pf)
    else if t == s && w < wl then
      -- the low `w` bits of the field: `a % 2^w`
      let pf := mkAppN (mkConst ``pack_hit_n) #[a, r, Wl, C, T, Wm, nl wl, nl s, nl w, ← refl Wl, ← refl C, ← refl C, ← refl Wm, hr, leP w wl]
      return some (← mkAppM ``HMod.hMod #[a, Wm], pf)
    else if s < t && t + w ≤ s + wl then
      -- a slice inside the field: `a / 2^(t-s) % 2^w`
      let k := t - s
      let K := nl (2 ^ k)
      let pf := mkAppN (mkConst ``pack_in) #[a, r, Wl, C, T, Wm, K, nl wl, nl s, nl t, nl w, nl k, ← refl Wl, ← refl C, ← refl T, ← refl Wm, ← refl K,
        ← mkEqRefl (nl t), hr, leP (k + w) wl]
      return some (← mkAppM ``HMod.hMod #[← mkAppM ``HDiv.hDiv #[a, K], Wm], pf)
    else if t + w ≤ s then
      let step := mkAppN (mkConst ``pack_skip) #[a, r, Wl, C, T, Wm, nl wl, nl s, nl t, nl w, ← refl Wl, ← refl C, ← refl T, ← refl Wm, hr, leP (t + w) s]
      let some (v, pf) ← extField r T Wm t w | failAt 13 t w
      return some (v, ← mkEqTrans step pf)
    else failAt 14 t w
  | _ =>
    unless t == 0 do return (← failAt 15 t w)
    let v ← mkAppM ``HMod.hMod #[E, Wm]
    return some (v, mkAppN (mkConst ``atom_div) #[E, T, Wm, ← refl T])

/-- drop the redundant mask of a whole field value (`y.toNat % 2^n` for `y : BitVec n`, `(if p then 1 else 0) % 2`): `omega` is incomplete on the masked forms
(observed: `(a % 32 / 4 % 4 * 4 + ..)` with `a < 32` and the equation `a % 32 = a` still fails, the unmasked form is proved) -/
def dropMask (r : Option (Expr × Expr)) : MetaM (Option (Expr × Expr)) := do
  let some (v, pf) := r | return none
  match v.getAppFnArgs with
  | (``HMod.hMod, #[_, _, _, _, a, L]) =>
    if a.isAppOfArity ``BitVec.toNat 2 then
      let y := a.appArg!
      let n := (← whnfR (← inferType y)).appArg!
      if (← litNat? L) == (← litNat? (← mkAppM ``HPow.hPow #[nl 2, n])) && (← litNat? L).isSome then
        return some (a, ← mkEqTrans pf (← mkAppM ``BitVec.toNat_mod_cancel #[y]))
    else if a.isAppOfArity ``ite 5 && (← litNat? L) == some 2 then
      unless (a.getArg! 3).nat? == some 1 && (a.getArg! 4).nat? == some 0 do return some (v, pf)
      return some (a, ← mkEqTrans pf (mkAppN (mkConst ``ite10_mod) #[a.getAppArgs[1]!, a.getAppArgs[2]!]))
    return some (v, pf)
  | _ => return some (v, pf)

/-- a candidate `X` of the form `E / 2^t % 2^w` or `E % 2^w` (`E` a packed state or a `%` chain): the value and the proof of `X = v` -/
def tryExtract0 (X : Expr) : MetaM (Option (Expr × Expr)) := do
  if let (``HDiv.hDiv, #[_, _, _, _, E, T]) := X.getAppFnArgs then
    -- `x % 2^m / 2^t` (no outer mask): the mask is the top of the chain, width `m - t`
    let (``HMod.hMod, #[_, _, _, _, x, M]) := E.getAppFnArgs | return none
    let some mv ← litNat? M | return none
    let some m := pow2? mv | return none
    let some tv ← litNat? T | return none
    let some t := pow2? tv | return none
    unless t < m do return none
    let w := m - t
    let Wm := nl (2 ^ w)
    let step := mkAppN (mkConst ``div_top) #[x, M, T, Wm, nl m, nl t, nl w, ← refl M, ← refl T, ← refl Wm, ← mkEqRefl (nl m)]
    let some (v, pf) ← extField E T Wm t w | return none
    return some (v, ← mkEqTrans step pf)
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

def tryExtract (X : Expr) : MetaM (Option (Expr × Expr)) := do dropMask (← tryExtract0 X)

/-- diagnosis (`ved_extract_diag`): the failure sites of the extraction candidates of the target -/
elab "ved_extract_diag" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let mut seen : Std.HashSet String := {}
  for x in collectDag (fun x => x.isAppOfArity ``HMod.hMod 6) tgt do
    if x.hasLooseBVars then continue
    extLastFail.set "no-pattern"
    if (← tryExtract x).isNone then
      let r ← extLastFail.get
      unless seen.contains r do
        seen := seen.insert r
        logInfo m!"EXTDIAG {r}"

/-- the first extraction candidate of an expression (parents first), by the DAG -/
def firstExtract (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  for x in collectDag (fun x => x.isAppOfArity ``HMod.hMod 6 || x.isAppOfArity ``HDiv.hDiv 6) e do
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
    -- only the variables the target or a hypothesis mentions: each fact is read by every `omega` call of the closer (the cone keeps the variables of the whole tuple)
    let mut used : Std.HashSet FVarId := {}
    for f in fvarsOfDag (← instantiateMVars (← g.getType)) do used := used.insert f
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← isProp d.type) then
        for f in fvarsOfDag (← instantiateMVars d.type) do used := used.insert f
    let mut fs : Array Expr := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || !used.contains d.fvarId then continue
      let t ← whnfR (← instantiateMVars d.type)
      if t.isAppOf ``BitVec then fs := fs.push d.toExpr
    pure fs
  for x in fs do
    let (pr, ty) ← g.withContext do
      let pr ← mkAppM ``BitVec.isLt #[x]
      pure (pr, ← inferType pr)
    let (_, g1) ← (← g.assert `ved_bnd ty pr).intro1P
    -- `x.toNat % 2^w = x.toNat`: the equation lets `omega` drop the `% 2^w` of the packed fields exactly (no dark shadow needed)
    let (pr2, ty2) ← g1.withContext do
      let pr ← mkAppM ``BitVec.toNat_mod_cancel #[x]
      pure (pr, ← inferType pr)
    let (_, g2) ← (← g1.assert `ved_bnd2 ty2 pr2).intro1P
    g := g2
  replaceMainGoal [g]

/-- `ved_bv_bounds_t` (s94s): the same bounds, but only for the `BitVec` variables of the TARGET and of the hypotheses that mention a variable of the target (the cone proper);
`ved_bv_bounds` adds two facts for every variable of every kept hypothesis (observed: 44 facts for a 27-node target, and `omega` reads each of them: 9.1M heartbeats against 8M
local limit on R033 goals 147 / 153) -/
elab "ved_bv_bounds_t" : tactic => do
  let mut g ← getMainGoal
  let fs ← g.withContext do
    let tfv := fvarsOfDag (← instantiateMVars (← g.getType))
    let mut used : Std.HashSet FVarId := {}
    for f in tfv do used := used.insert f
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← isProp d.type) then
        let xs := fvarsOfDag (← instantiateMVars d.type)
        if xs.any (tfv.contains ·) then
          for f in xs do used := used.insert f
    let mut fs : Array Expr := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || !used.contains d.fvarId then continue
      let t ← whnfR (← instantiateMVars d.type)
      if t.isAppOf ``BitVec then fs := fs.push d.toExpr
    pure fs
  for x in fs do
    let (pr, ty) ← g.withContext do
      let pr ← mkAppM ``BitVec.isLt #[x]
      pure (pr, ← inferType pr)
    let (_, g1) ← (← g.assert `ved_bnd ty pr).intro1P
    let (pr2, ty2) ← g1.withContext do
      let pr ← mkAppM ``BitVec.toNat_mod_cancel #[x]
      pure (pr, ← inferType pr)
    let (_, g2) ← (← g1.assert `ved_bnd2 ty2 pr2).intro1P
    g := g2
  replaceMainGoal [g]

/-- the goals of the local route are the small cones: a target with at most `ved.mem.s94Local` tree nodes (`localMaxTree`); `omega` and `split`
do not stop at the heartbeat limit on the large ones (observed: 1.2e9 heartbeats / 200 s on a 7e10-node goal with limit 3e7) -/
def localMaxTree : Nat := 2000000

elab "ved_local_small" : tactic => withMainContext do
  let n := Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← getMainTarget))
  if n > localMaxTree then throwError "ved_local_small: the target has {n} tree nodes (limit {localMaxTree})"

/-- `omega`, splitting one `if` at a time as long as it does not close the goal -/
syntax "ved_split_omega" : tactic
macro_rules
  | `(tactic| ved_split_omega) => `(tactic| first | omega | (split <;> ved_split_omega))

/-- `ved_mux`: an equation of two `ite` chains branch by branch (`mux_mod` pushes `% m` into the chain, `mux_cong` pairs the conditions, `mux_l` / `mux_r` when only one
side is a chain), the leaves by `ved_split_omega`; no `split` on the chain itself -/
syntax "ved_mux" : tactic
macro_rules
  | `(tactic| ved_mux) => `(tactic| first
      | with_reducible rfl
      | (rw [mux_mod]; ved_mux)
      | (refine mux_cong _ _ _ _ _ _ ?hc ?ha ?hb
         case hc => first | exact Iff.rfl | ved_split_omega
         case ha => intro _; ved_mux
         case hb => intro _; ved_mux)
      | (refine mux_l _ _ _ _ ?ha ?hb
         case ha => intro _; ved_mux
         case hb => intro _; ved_mux)
      | (refine mux_r _ _ _ _ ?ha ?hb
         case ha => intro _; ved_mux
         case hb => intro _; ved_mux)
      | ved_split_omega)

/-- `ved_local_close`: the goal from its own cone: cone clear, field extraction, bounds, then `omega` (with `split` for the `if`s) -/
macro "ved_local_close" : tactic =>
  `(tactic| (ved_cone_clear; (try ved_pack_extract); ved_local_small; (try dsimp only at *); (try simp only [ite10_mod2] at *);
             all_goals (ved_bv_bounds
                        (try simp only [mux_mod]); ved_mux)))

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
        withoutRecover (evalTactic (← `(tactic| ved_local_close)))
      if ← localFailLate.get then throwError "ved_local_goal: failed after its work (test seam)"
      pure true)
    (fun _ => pure false)
  if r then localHits.modify (· + 1)
  else
    st.restore
    throwError "ved_local_goal: the goal is not closed from its cone"


/-! ## class B: the address equalities of `ved_mem_addr` by the local lemmas

Observed (s94q, goals 6 and 17 of the t3 checkpoint, `VED_DUMP_DIR` pair files): the first address equality `ved_mem_addr` asks for is
`BitVec.extractLsb' 0 4 ck132 = BitVec.ofNat 4 ((PACK) % 2^110 / 2^105 % 2^(4+1))`, i.e. a FIELD EXTRACTION from the packed state; its old proof
(`ved_pack_simp; ved_bit_simp; simp ..` over the 25-level pack with 150-bit numerals) runs into the heartbeat limit before any address is rewritten.
`ved_mem_addr_l` is `ved_mem_addr` with that one proof replaced by `ved_addr_eq_local` (toNat, then the once-proved extraction lemmas) and WITHOUT the second
pass (the contextual `simp`, a walk of the tree of 8e8 .. 8e11 nodes over a DAG of <= 2.9k: observed 23 of the 41 memory goals time out in it, 3 without it; the address
rewriting of the first pass is by `Expr.replace` with the pointer cache); the rest (pairs, `ved_addr` tag) is the same text. -/

/-- the toNat form of an address equality, closed from its own cone by the extraction lemmas -/
macro "ved_addr_eq_local" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq
             simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
             ved_local_close))

/-- the same for an address built by `BitVec` arithmetic (`ite` of a `0#6 ++ extractLsb' ..` shuffle, `+`, `*`; observed on R033 goal 69: the first closer leaves `split` without an `if`
because `toNat` of `+ * ++` and of the `ite` stays unexpanded): the `toNat` lemmas first, then the same closer -/
macro "ved_addr_eq_local2" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq
             simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, apply_ite BitVec.toNat, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub,
               BitVec.toNat_append, Nat.zero_shiftLeft, Nat.zero_or, Nat.reduceMod, Nat.reducePow, Nat.shiftRight_eq_div_pow]
             ved_local_close))

/-- the heartbeat budget (thousands) of one argument comparison of `memCanon` (observed: the comparisons that finish need < 1M) -/
def memCanonBudgetK : Nat := 500
/-- the heartbeat budget (thousands) of all argument comparisons of one `memCanon` call -/
def memCanonTotalK : Nat := 6000
/-- the heartbeat budget (thousands) of ONE address equality of `ved_mem_addr_l` (observed: the equalities that succeed need < 1M) -/
def addrEqBudgetK : Nat := 12000
initialize addrEqTimeouts : IO.Ref Nat ← IO.mkRef 0
initialize memCanonTimeouts : IO.Ref Nat ← IO.mkRef 0

/-- two `memState` atoms whose first 8 arguments (initial value, write address / data / enable ports, ..) are only reducibly defeq (not syntactically equal) are one memory
spelled twice (observed s94r, R033 goals 40, 62: `ved_mem_diff` says `arg2:red arg3:red`; the trees of 2e7 .. 2e8 nodes are those port arguments): the first atom's arguments replace
the later one's (`replaceTargetDefEq`), so that the address pairing (`ved_mem_addr_l`) and `ved_addr_post_g` see ONE key.  Returns the number of atoms changed. -/
def memCanon (g : MVarId) : MetaM (MVarId × Nat) := g.withContext do
  let hbStart ← IO.getNumHeartbeats
  let tgt ← instantiateMVars (← g.getType)
  let isMem := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 9
  let occs := (collectDag isMem tgt).filter (!·.hasLooseBVars)
  let mut reps : Array (Expr × Array Expr) := #[]
  let mut map : Std.HashMap Expr Expr := {}
  for o in occs do
    let args := o.getAppArgs
    let fn := o.getAppFn
    let mut hit : Option (Array Expr) := none
    for (f, ra) in reps do
      if hit.isSome then break
      if f != fn || ra.size != 8 then continue
      let mut same := true
      let mut diff := false
      for k in [0:8] do
        if same && args[k]! != ra[k]! then
          diff := true
          -- s94s: each comparison under its own heartbeat budget (`memCanonBudgetK` thousand): on the R033 B goals 51 64 33 34 53 54 62 103 139 151 this `isDefEq` of two big port arguments
          -- (trees of 1e6 .. 3e7 nodes over a DAG of ~2e3, no sharing in the unifier) ran into the 30M limit of the WHOLE step `ved_mem_addr_l`; a comparison that does not finish is "not the same" (the atoms stay apart)
          let hb0 ← IO.getNumHeartbeats
          -- and the whole of `memCanon` under `memCanonTotalK` (a comparison after that is "not the same")
          let spent := (hb0 - hbStart) / 1000
          let r ← if spent ≥ memCanonTotalK then pure false else
            tryCatchRuntimeEx
              (withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then memCanonBudgetK * 1000 else min c.maxHeartbeats (memCanonBudgetK * 1000)), initHeartbeats := hb0 }) do
                withReducible (isDefEq args[k]! ra[k]!))
              (fun _ => do memCanonTimeouts.modify (· + 1); pure false)
          unless r do same := false
      if same then hit := some (if diff then ra else args.extract 0 8)
    match hit with
    | some ra =>
      if ra != args.extract 0 8 then map := map.insert o (mkAppN fn (ra ++ args.extract 8 args.size))
    | none => reps := reps.push (fn, args.extract 0 8)
  if map.isEmpty then return (g, 0)
  let tgt' := tgt.replace fun e => map[e]?
  return (← g.replaceTargetDefEq tgt', map.size)

elab "ved_mem_addr_l" : tactic => withMainContext do
  -- two spellings of one memory (ports only reducibly defeq) are made one first
  let (gC, nC) ← memCanon (← getMainGoal)
  if nC > 0 then replaceMainGoal [gC]
  -- cheap gate: nothing to unify unless two memState atoms differ only in the address (the simp below only drops branches)
  let tgt0 ← instantiateMVars (← getMainTarget)
  let isMem0 := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 9
  let mut seen0 : Array (Expr × Expr) := #[]
  let mut need := false
  for o in Tools.VedU1WireShare.collectDag isMem0 tgt0 do
    if o.hasLooseBVars then continue
    let args := o.getAppArgs
    let key := mkAppN o.getAppFn (args.extract 0 8)
    if seen0.any (fun (k, a) => k == key && a != args[8]!) then need := true; break
    seen0 := seen0.push (key, args[8]!)
  if !need then return
  Tools.VedMemLoop.dbgT "addr: gate passed"
  let g0 ← getMainGoal
  g0.setTag ((← g0.getTag) ++ `ved_addr)
  let isMem := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 9
  -- one rewrite per round, the atoms collected again after it (an address can contain another one: the rewrite of the
  -- inner one changes the outer one)
  let mut remaining := true
  for pass in [0:1] do
    if !remaining then break
    if pass == 1 then
      pure ()
      Tools.VedMemLoop.dbgT "addr: contextual simp done"
    for _ in [0:8] do
      let tgt ← instantiateMVars (← getMainTarget)
      let occs := Tools.VedU1WireShare.collectDag isMem tgt
      let mut groups : Array (Expr × Array Expr) := #[]
      for o in occs do
        if o.hasLooseBVars then continue
        let args := o.getAppArgs
        let key := mkAppN o.getAppFn (args.extract 0 8)
        let a := args[8]!
        match groups.findIdx? (fun g => g.1 == key) with
        | some i => if !groups[i]!.2.contains a then groups := groups.set! i (key, groups[i]!.2.push a)
        | none => groups := groups.push (key, #[a])
      remaining := groups.any (fun g => g.2.size ≥ 2)
      let mut progress := false
      for (_, addrs) in groups do
        if progress then break
        if addrs.size < 2 then continue
        let rep := addrs[0]!
        let repS ← Term.exprToSyntax rep
        for a in addrs.toList.drop 1 do
          if progress then break
          let aS ← Term.exprToSyntax a
          if let some dir ← IO.getEnv "VED_DUMP_DIR" then
            let n := (← IO.monoMsNow)
            IO.FS.writeFile s!"{dir}/pair{n}.txt" s!"A: {← withOptions (fun o => o.setBool `pp.deepTerms true) (ppExpr a)}\n\nREP: {← withOptions (fun o => o.setBool `pp.deepTerms true) (ppExpr rep)}\n"
          try
            -- s94s: the address equality under its own heartbeat budget (`addrEqBudgetK`).  Observed (t3c, goals 51 64 33 34 53 54 62 103 139 151): the first alternative `rfl` is an
            -- `isDefEq` of two addresses that contain `memState` atoms with big port arguments (trees of 1e6 .. 3e7 over a DAG of ~2e3: no sharing in the unifier) and ran into the 30M limit
            -- of the whole step; a runtime timeout is not caught by the `catch` below.  On exhaustion the state is restored and the pair counts as "no equality" (the loop goes on)
            let stP ← saveState
            let hbP ← IO.getNumHeartbeats
            tryCatchRuntimeEx
              (withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then addrEqBudgetK * 1000 else min c.maxHeartbeats (addrEqBudgetK * 1000)), initHeartbeats := hbP }) do
                evalTactic (← `(tactic| (have hmaddr : $aS = $repS := by
                                           first | (with_reducible rfl) | ved_addr_eq_local | ved_addr_eq_local2 | rfl))))
              (fun ex => do
                stP.restore
                addrEqTimeouts.modify (· + 1)
                throwError "address equality: budget exhausted ({← ex.toMessageData.toString})")
            Tools.VedMemLoop.dbgT "addr: have done"
            -- `rw [hmaddr]` abstracts the occurrences by `kabstract`, a walk of the TREE (12 s per goal of 3e8 nodes, R34); on a goal
            -- the packing step takes (`Tools.VedMemLoop.addrReplaceMinTree`: R034, 3e8) the replacement is `Expr.replace` (cached by pointer: one visit per
            -- shared node) with the `congrArg` of the motive; below it the `rw` as before (R032, 1.7e7 nodes: `rw` abstracts the
            -- occurrences up to instances, the syntactic `Expr.replace` leaves some, and the closing `omega` then fails)
            let tgt ← instantiateMVars (← getMainTarget)
            let hmFind : TacticM (Option Expr) := do
              -- the `have` made a new goal: its local context (not the one this tactic started with) holds `hmaddr`
              (← getMainGoal).withContext do
                let mut r : Option Expr := none
                for d in (← getLCtx).decls.toList.reverse do
                  if let some d := d then
                    if r.isNone && !d.isImplementationDetail then
                      if let some (_, l, rr) := (← instantiateMVars d.type).eq? then
                        if l == a && rr == rep then r := some d.toExpr
                pure r
            let small := Tools.VedU1Loop.treeSizeVal tgt < Tools.VedMemLoop.addrReplaceMinTree
            let hm? ← if small then pure none else hmFind
            Tools.VedMemLoop.dbgT s!"addr: hm found={hm?.isSome} tgt-tree={Tools.VedU1Loop.treeSizeVal tgt}"
            let replaceRoute (hm : Expr) : TacticM Unit := do
              let g ← getMainGoal
              -- in the context of the new goal: `hm` is a hypothesis of it, not of the context this tactic started with
              -- (`mkCongrArg` infers its type: "unknown free variable")
              g.withContext do
                let aTy ← inferType a
                let motive ← withLocalDeclD `ved_x aTy fun xv =>
                  mkLambdaFVars #[xv] (tgt.replace fun e => if e == a then some xv else none)
                let newTgt := tgt.replace fun e => if e == a then some rep else none
                replaceMainGoal [← g.replaceTargetEq newTgt (← mkCongrArg motive hm)]
            if let some hm := hm? then
              replaceRoute hm
            else if !small then
              evalTactic (← `(tactic| rw [hmaddr]))
            else
              -- s94s: the `rw` (kabstract: an `isDefEq` of the address against every candidate subterm, then `rfl`) under its own heartbeat budget (`addrEqBudgetK`).  Observed (t3c goals
              -- 33 34 53 54 151, trees of 1.2e7 .. 3.5e7 below `addrReplaceMinTree`): it ran into the 30M limit of the whole step; on exhaustion the `Expr.replace` route of the large goals is taken
              let stR ← saveState
              let hbR ← IO.getNumHeartbeats
              let okR ← tryCatchRuntimeEx
                (do
                  withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then addrEqBudgetK * 1000 else min c.maxHeartbeats (addrEqBudgetK * 1000)), initHeartbeats := hbR }) do
                    evalTactic (← `(tactic| rw [hmaddr]))
                  pure true)
                (fun _ => do stR.restore; addrEqTimeouts.modify (· + 1); pure false)
              unless okR do
                match ← hmFind with
                | some hm => replaceRoute hm
                | none => throwError "address rewrite: budget exhausted and no equation"
            -- the `rw` closes the goal by `rfl` when the two atoms were all there was (small cases; never on the R033 goals)
            if (← getGoals).isEmpty then return
            progress := true
            Tools.VedMemLoop.dbgT "addr: rewrite ok"
          catch e => Tools.VedMemLoop.dbgT "addr: equality failed"; Tools.VedMemLoop.dbgLog s!"no equality for {← ppExpr a}: {← e.toMessageData.toString}"
      if !progress then break

end Tools.VedMemS94Local
