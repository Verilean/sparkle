import Lean
import Tools.VedMemLoop
import Tools.VedMemS94Addr

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

register_option ved.mem.s94Cone2 : Bool := {
  defValue := false
  descr := "ved_cone_clear keeps a second hop: the small arithmetic context entries that mention a variable of a kept arithmetic hypothesis (the premise `phase = 2` of a path hypothesis `¬(phase = 2 ∧ ..)`), default false"
}

register_option ved.mem.s94Addr : Bool := {
  defValue := false
  descr := "ved_mem_addr_l: an address equality is first tried by `ved_addr_eq_bv` (toNat translation, field extraction, case split on the `if`s, then `decide` over the BitVec variables that are left, kernel-checked); the old closers are the fallback (default false)"
}

/-- a second-hop entry is kept only when its tree is at most this (the premises of a path hypothesis are small) -/
def cone2MaxTree : Nat := 400

/-- number of entries the second hop kept (test counter) -/
initialize cone2Kept : IO.Ref Nat ← IO.mkRef 0

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

theorem ite10_mod2_z (p : Prop) [Decidable p] : ((if p then 1 else 0) % 2 = 0) ↔ ¬p := by
  by_cases h : p <;> simp [h]

theorem ite10_eq1 (p : Prop) [Decidable p] : ((if p then 1 else 0 : Nat) = 1) ↔ p := by
  by_cases h : p <;> simp [h]

theorem ite10_eq0 (p : Prop) [Decidable p] : ((if p then 1 else 0 : Nat) = 0) ↔ ¬p := by
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
def coneClear (g : MVarId) (arithOnly : Bool := true) (hop2 : Bool := false) : MetaM (MVarId × Nat × Nat) := g.withContext do
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
  -- option `ved.mem.s94Cone2`: one more hop.  The variables of the kept arithmetic hypotheses (not of their dependencies) that the target does not mention; the small
  -- arithmetic entries over those variables are kept too (a path hypothesis `¬(phase = 2 ∧ w)` is useless without the premise `phase = 2` it was split under)
  if hop2 then
    let mut hv : Std.HashSet FVarId := {}
    for d in lctx do
      if keep.contains d.fvarId && !d.isImplementationDetail && !(d.isLet) then
        let t ← instantiateMVars d.type
        if (← isProp t) && isArithHyp t then
          for x in fvarsOfDag t do
            unless tfv.contains x do hv := hv.insert x
    for d in lctx do
      if d.isImplementationDetail || keep.contains d.fvarId then continue
      let t ← instantiateMVars d.type
      if !isEnvFact t && (← isProp t) && isArithHyp t && Tools.VedU1Loop.treeSizeVal t ≤ cone2MaxTree && (fvarsOfDag t).any (hv.contains ·) then
        keep := keep.insert d.fvarId
        todo := todo.push d.fvarId
        cone2Kept.modify (· + 1)
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
  let (g', _, _) ← coneClear g (hop2 := ved.mem.s94Cone2.get (← getOptions))
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

/-- `ved_or_gate`: refuses unless `ved.mem.s94OrDisj` is on -/
elab "ved_or_gate" : tactic => do
  unless Tools.VedMemS94Addr.ved.mem.s94OrDisj.get (← getOptions) do throwError "ved_or_gate: option ved.mem.s94OrDisj is off"

/-- `ved_split_omega_o` (option `ved.mem.s94OrDisj`): `ved_split_omega` whose leaves also try the bounds `x ||| y < 2 ^ k` of the bit-field terms the splitting produced (`ved_or_bounds`) -/
syntax "ved_split_omega_o" : tactic
macro_rules
  | `(tactic| ved_split_omega_o) => `(tactic| first | omega | (ved_or_bounds; omega) | (split <;> ved_split_omega_o))

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

/-- `ved_cong` (option-free; used by the new route only): `ved_mux` with one more alternative, the congruence step `congr 1` for two applications of the same head (`+ * % / ^ -`):
the sides that are two spellings of one arithmetic term (observed R033 goal 6: `(a * b + c) % 2^32 / 2^(m % 32)` on both sides, only the inner `ite`s and `% 65536` spelled differently)
are compared argument by argument, so that `omega` sees the same nonlinear atoms (`a * b`, `2 ^ (m % 32)`) on both sides -/
syntax "ved_cong" : tactic
macro_rules
  | `(tactic| ved_cong) => `(tactic| first
      | with_reducible rfl
      | omega
      | (rw [mux_mod]; ved_cong)
      | (refine mux_cong _ _ _ _ _ _ ?hc ?ha ?hb
         case hc => first | exact Iff.rfl | ved_split_omega
         case ha => intro _; ved_cong
         case hb => intro _; ved_cong)
      | (refine mux_l _ _ _ _ ?ha ?hb
         case ha => intro _; ved_cong
         case hb => intro _; ved_cong)
      | (refine mux_r _ _ _ _ ?ha ?hb
         case ha => intro _; ved_cong
         case hb => intro _; ved_cong)
      | (congr 1 <;> ved_cong)
      | ved_split_omega)

/-! ## memState atoms abstracted (shared with `Tools.VedMemS94Opaque`): the keys of the target, and with `ved.mem.s94OpaqueH` also those of the kept hypotheses -/

def isMemAtom (x : Expr) : Bool :=
  x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs == 9 && !x.hasLooseBVars

/-- the target with every atom `memState a0 .. a7 addr` whose key is in `keys` replaced by `M addr` (the address abstracted by the same map); memoised, one visit per shared node -/
partial def absGo (keys : Array (Expr × Expr)) (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some r := (← get)[e]? then return r
  let r ← do
    if isMemAtom e then
      let args := e.getAppArgs
      let key := mkAppN e.getAppFn (args.extract 0 8)
      match keys.find? (·.1 == key) with
      | some (_, m) => pure (mkApp m (← absGo keys args[8]!))
      | none => pure e
    else match e with
      | .app f a => pure (e.updateApp! (← absGo keys f) (← absGo keys a))
      | .lam _ t b _ => pure (e.updateLambdaE! (← absGo keys t) (← absGo keys b))
      | .forallE _ t b _ => pure (e.updateForallE! (← absGo keys t) (← absGo keys b))
      | .mdata _ b => pure (e.updateMData! (← absGo keys b))
      | .proj _ _ b => pure (e.updateProj! (← absGo keys b))
      | .letE n t v b nd => pure (Expr.letE n (← absGo keys t) (← absGo keys v) (← absGo keys b) nd)
      | _ => pure e
  modify (·.insert e r)
  return r

/-- abstract the distinct `memState` keys of the target; returns the new goal (the variables introduced) and their number (0: nothing to do, the goal is returned unchanged) -/
def memOpaque (g : MVarId) : MetaM (MVarId × Nat) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut keys : Array Expr := #[]
  for o in collectDag isMemAtom tgt do
    let key := mkAppN o.getAppFn (o.getAppArgs.extract 0 8)
    unless keys.contains key do keys := keys.push key
  if keys.isEmpty then return (g, 0)
  let mut tys : Array Expr := #[]
  for k in keys do tys := tys.push (← inferType k)
  -- bound variables of the abstraction, as free variables of a local telescope
  let rec go (i : Nat) (acc : Array (Expr × Expr)) : MetaM Expr := do
    if h : i < keys.size then
      withLocalDeclD (Name.mkSimple s!"ved_M{i}") tys[i]! fun m => do
        let body ← go (i + 1) (acc.push (keys[i]!, m))
        mkForallFVars #[m] body
    else
      let (t', _) := (absGo acc tgt).run {}
      return t'
  let absTy ← go 0 #[]
  let g' ← mkFreshExprSyntheticOpaqueMVar absTy (← g.getTag)
  g.assign (mkAppN g' keys)
  let (_, g'') ← g'.mvarId!.introN keys.size ((List.range keys.size).map fun i => Name.mkSimple s!"ved_M{i}")
  return (g'', keys.size)

register_option ved.mem.s94OpaqueH : Bool := {
  defValue := false
  descr := "ved_local_close: after the cone clear, abstract the memState keys of the kept hypotheses (and the target) to variables before the field extraction and omega, so that omega never walks the port arguments of a memory read inside a hypothesis (default false)"
}

/-- number of runs of `ved_cone_opaque` that abstracted something (test counter) -/
initialize coneOpaqueHits : IO.Ref Nat ← IO.mkRef 0

/-- abstract the `memState` keys of the target AND of the context propositions that contain one: those propositions are reverted, the target `H1 → .. → tgt` is abstracted by `memOpaque`,
and the propositions are introduced again under their names.  Returns the new goal and the number of keys (0: nothing to do, the goal is returned unchanged) -/
def memOpaqueH (g : MVarId) : MetaM (MVarId × Nat) := g.withContext do
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let t ← instantiateMVars d.type
    if (← isProp t) && !(collectDag isMemAtom t).isEmpty then hs := hs.push d.fvarId
  if hs.isEmpty && (collectDag isMemAtom (← instantiateMVars (← g.getType))).isEmpty then return (g, 0)
  let names ← hs.mapM fun f => do return (← f.getDecl).userName
  let (_, g1) ← g.revert hs (preserveOrder := true)
  let (g2, n) ← memOpaque g1
  let (_, g3) ← g2.introN hs.size names.toList
  return (g3, n)

/-- `ved_cone_opaque`: `memOpaqueH` on the main goal when `ved.mem.s94OpaqueH` is on; otherwise (and when there is no atom) it does nothing -/
elab "ved_cone_opaque" : tactic => do
  unless ved.mem.s94OpaqueH.get (← getOptions) do return
  let (g, n) ← memOpaqueH (← getMainGoal)
  if n == 0 then return
  coneOpaqueHits.modify (· + 1)
  replaceMainGoal [g]

register_option ved.mem.s94Spell : Bool := {
  defValue := false
  descr := "ved_local_close_new: two memState atoms that differ only in the spelling of their write ports (BitVec equation vs toNat form, factor order of a multiplication) are one atom (ved_mem_spell, before the atoms are abstracted); default false"
}

register_option ved.mem.s94HypSplit : Bool := {
  defValue := false
  descr := "ved_local_close: when `ved_mux` does not close the goal, split the `if`s of the HYPOTHESES (the path hypotheses of the A goals: the target has no `if`, `split` of `ved_split_omega` finds none) and close each leaf by omega (default false)"
}

/-- most leaves `ved_hyp_split_omega` produces -/
def hypSplitMaxLeaves : Nat := 48
initialize hypSplitHits : IO.Ref Nat ← IO.mkRef 0

/-- the context propositions that contain an `ite` -/
def hypIteDecls : MetaM (Array FVarId) := do
  let mut r := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let t ← instantiateMVars d.type
    if (← isProp t) && !(collectDag (fun x => x.isAppOf ``ite) t).isEmpty then r := r.push d.fvarId
  return r

/-- the message of the last failing `omega` of `hypSplitOmega` (diagnosis) -/
initialize lastOmegaMsg : IO.Ref String ← IO.mkRef ""

/-- `omega`; when it fails, one `if` of one hypothesis is split (`splitLocalDecl?`), both goals again; `fuel` bounds the number of leaves -/
partial def hypSplitOmega (g : MVarId) (fuel : IO.Ref Nat) : TacticM Unit := do
  let (ok, msg) ← try
      let gs ← Tactic.run g (Tactic.withoutRecover (evalTactic (← `(tactic| omega))))
      pure (gs.isEmpty, "")
    catch ex => pure (false, (← ex.toMessageData.toString).replace "\n" " | ")
  if ok then return
  lastOmegaMsg.set msg
  if (← fuel.get) == 0 then throwError "ved_hyp_split_omega: too many leaves"
  fuel.modify (· - 1)
  for f in ← g.withContext hypIteDecls do
    if let some gs ← Lean.Meta.splitLocalDecl? g f then
      for g' in gs do hypSplitOmega g' fuel
      return
  throwError "ved_hyp_split_omega: omega failed and no hypothesis `if` can be split: {(← lastOmegaMsg.get).take 2500}"

/-- the memory reads `(M e).toNat` (`M` a local function variable, as `ved_cone_opaque` leaves them) of the target and the context propositions become variables (`generalizeHyp`):
`splitLocalDecl?` otherwise splits the `if` inside the address `e` of a read (a `BitVec` `if` the arithmetic does not need) before the `if`s of the arithmetic (s94v, R033 goal 152 after
`ved_mem_spell`: 10M heartbeats of leaves) -/
def genMemReads (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let isRd (x : Expr) : Bool := x.isAppOfArity ``BitVec.toNat 2 && (x.getArg! 1).isApp && (x.getArg! 1).getAppFn.isFVar
  let mut cands : Array Expr := #[]
  let mut hs : Array FVarId := #[]
  for x in collectDag isRd (← instantiateMVars (← g.getType)) do
    unless cands.contains x do cands := cands.push x
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let t ← instantiateMVars d.type
    unless (← isProp t) do continue
    let cs := collectDag isRd t
    unless cs.isEmpty do
      hs := hs.push d.fvarId
      for x in cs do
        unless cands.contains x do cands := cands.push x
  if cands.isEmpty then return none
  let args := cands.map fun c => ({ expr := c, xName? := some `ved_gm } : GeneralizeArg)
  let (_, _, g') ← g.generalizeHyp args hs
  return some g'

/-- `ved_hyp_split_omega`: the main goal closed by `hypSplitOmega` (with `ved.mem.s94Spell`: first after `genMemReads`, the old path is the fallback) -/
elab "ved_hyp_split_omega" : tactic => do
  let g ← getMainGoal
  if ved.mem.s94Spell.get (← getOptions) then
    let st ← saveState
    try
      if let some g' ← genMemReads g then
        let fuel ← IO.mkRef hypSplitMaxLeaves
        hypSplitOmega g' fuel
        replaceMainGoal []
        hypSplitHits.modify (· + 1)
        return
    catch _ => st.restore
  let fuel ← IO.mkRef hypSplitMaxLeaves
  hypSplitOmega g fuel
  replaceMainGoal []
  hypSplitHits.modify (· + 1)

/-- `ved_hyp_split_omega_g`: `ved_hyp_split_omega` when `ved.mem.s94HypSplit` is on, else a refusal -/
elab "ved_hyp_split_omega_g" : tactic => do
  unless ved.mem.s94HypSplit.get (← getOptions) do throwError "ved_hyp_split_omega_g: option ved.mem.s94HypSplit is off"
  evalTactic (← `(tactic| ved_hyp_split_omega))

/-- the address spelling `BitVec.ofNat w x.toNat` of a word and its `extractLsb' 0 w x` are one word (observed R033 goals 26 35 148 154 and A 149 155 152 158: after `ved_cone_opaque` the two sides read
the abstracted memory at the two spellings, `M (extractLsb' 0 4 ck501)` and `M (ofNat 4 ck501.toNat)`, which `omega` takes for two different atoms) -/
theorem ofNat_toNat_extract {n : Nat} (w : Nat) (x : BitVec n) : BitVec.ofNat w x.toNat = BitVec.extractLsb' 0 w x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat]

theorem ofNat_mod_lit (w m n : Nat) (hm : 2 ^ w = m) : BitVec.ofNat w (n % m) = BitVec.ofNat w n := by
  subst hm
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mod_mod]

theorem ofNat_ite_lift (w : Nat) (c : Prop) [Decidable c] (a b : Nat) :
    BitVec.ofNat w (if c then a else b) = if c then BitVec.ofNat w a else BitVec.ofNat w b := by
  split <;> rfl

/-- number of runs of `ved_atom_args` that rewrote something (test counter) -/
initialize atomArgsHits : IO.Ref Nat ← IO.mkRef 0

/-- `ved_atom_args` (option `ved.mem.s94Addr`): after `ved_cone_opaque` (no `memState` atom left, so the terms are small) the address spellings `ofNat w x.toNat` are made `extractLsb' 0 w x` in the
target and the context (`simp only [ofNat_toNat_extract] at *`); does nothing when the option is off, when a `memState` atom is still in the target, or when nothing changes -/
elab "ved_atom_args" : tactic => withMainContext do
  unless ved.mem.s94Addr.get (← getOptions) do return
  unless (collectDag isMemAtom (← instantiateMVars (← getMainTarget))).isEmpty do return
  let st ← saveState
  let cntPat : TacticM Nat := do
    let mut n := 0
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      n := n + (collectDag (fun x => x.isAppOfArity ``BitVec.ofNat 2 && (x.getArg! 1).isAppOf ``BitVec.toNat) t).size
    pure (n + (collectDag (fun x => x.isAppOfArity ``BitVec.ofNat 2 && (x.getArg! 1).isAppOf ``BitVec.toNat) (← instantiateMVars (← getMainTarget))).size)
  let dbg := (← IO.getEnv "VED_ATOMDBG").isSome
  if dbg then IO.eprintln s!"ved_atom_args: ofNat-of-toNat patterns before: {← cntPat}"
  try
    evalTactic (← `(tactic| simp only [ofNat_toNat_extract, ofNat_mod_lit, ofNat_ite_lift, Tools.VedMem.ofNat_mod_eq_extract', Nat.reduceAdd, Nat.reducePow, Nat.reduceMod] at *))
    atomArgsHits.modify (· + 1)
    if dbg then IO.eprintln s!"ved_atom_args: ofNat-of-toNat patterns after: {← cntPat}"
  catch ex =>
    if (← IO.getEnv "VED_ATOMDBG").isSome then IO.eprintln s!"ved_atom_args: {(← ex.toMessageData.toString).take 300}"
    st.restore

/-- a flag `if p then 1 else 0` divided by 2 is 0 (observed R033 goals 149 155 152 158: the field extraction of a packed `Bool` leaves `(if p then 1 else 0) / 2` which `omega` takes as an atom) -/
theorem ite01_div2 (p : Prop) [Decidable p] : (if p then 1 else 0) / 2 = 0 := by
  split <;> rfl

/-- `ved_ite_div` (option `ved.mem.s94Addr`): `simp only [ite01_div2] at *`; nothing when the option is off or nothing changes -/
elab "ved_ite_div" : tactic => do
  unless ved.mem.s94Addr.get (← getOptions) do return
  let st ← saveState
  try evalTactic (← `(tactic| simp only [ite01_div2] at *))
  catch _ => st.restore

/-! ## two spellings of one memory (`ved.mem.s94Spell`, s94v)

Observed (s94v, `ved_port_dump` on the R033 goals 152 158): the A goals' hypotheses read ONE memory twice, `ved_M0` and `ved_M2` in the report's naming: two `memState` atoms
with the same width, the same write address and enable, and write data ports that are the same signal spelled two ways: `if nat(x) = 13 then 16 * (4 * a + b) + c else ..` against
`if x = 13#5 then ((a * 4) + b) * 16 + c else ..` (a `BitVec` equation against its `toNat` form, a literal factor on the other side of `*`).  The two atoms have different keys, so
`ved_cone_opaque` abstracts them to two unrelated memories and `omega` needs the content relation `M2[i] != 0 -> M0[i] != 0` that no hypothesis supplies (unsupplied local theorem (a):
the atoms are equal).  `ved_mem_spell` supplies it: for two atoms that differ only in the write address / data / enable ports, each differing port equation is proved by
`simp only [BitVec.mul_comm, BitVec.toNat_eq, ..]` (ordered rewriting makes both spellings one), the atom equation `forall addr, M_b addr = M_r addr` follows from
`memState_ports_congr` (proved once), and the atoms of the later spelling are rewritten to the first by this fact (`simp only [h] at *`, then `h` is cleared). -/


initialize spellHits : IO.Ref Nat ← IO.mkRef 0
initialize spellRefuse : IO.Ref Bool ← IO.mkRef false
initialize spellFailLate : IO.Ref Bool ← IO.mkRef false

open Sparkle.Core.Signal Sparkle.Core.Domain in
/-- the memory contents depend on the write ports only through the signals: equal ports, equal memory word -/
theorem memState_ports_congr {dom : DomainConfig} {aw dw : Nat} (init : BitVec aw → BitVec dw)
    (wa wa' : Signal dom (BitVec aw)) (wd wd' : Signal dom (BitVec dw)) (we we' : Signal dom Bool)
    (n : Nat) (addr : BitVec aw) (ha : wa = wa') (hd : wd = wd') (he : we = we') :
    Signal.memState init wa wd we n addr = Signal.memState init wa' wd' we' n addr := by
  subst ha hd he
  rfl

/-- the atoms `memState k0 .. k7 addr` (first eight arguments `bk`) of `e` as `M addr` (the address rewritten too) -/
partial def spellReplace (bk : Array Expr) (M : Expr) (e : Expr) : Expr :=
  e.replace fun x =>
    if isMemAtom x && x.getAppArgs.extract 0 8 == bk then some (mkApp M (spellReplace bk M x.getAppArgs[8]!)) else none

/-- `ved_mem_spell` (option `ved.mem.s94Spell`): see the section comment; fails when the option is off or no two atoms are spellings of one memory -/
elab "ved_mem_spell" : tactic => withMainContext do
  if (← spellRefuse.get) then throwError "ved_mem_spell: refused (test seam)"
  unless ved.mem.s94Spell.get (← getOptions) do throwError "ved_mem_spell: option ved.mem.s94Spell is off"
  let g ← getMainGoal
  let hb00 ← IO.getNumHeartbeats
  let mut atoms : Array Expr := #[]
  let mut props : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let t ← instantiateMVars d.type
    if (← isProp t) then props := props.push t
  for t in props do
    for a in collectDag isMemAtom t do
      unless atoms.contains a do atoms := atoms.push a
  let prove (l r : Expr) : TacticM (Option Expr) := do
    if l == r then return some (← mkEqRefl l)
    let mv ← mkFreshExprMVar (← mkEq l r)
    try
      let gs ← Tactic.run mv.mvarId! (withoutRecover (evalTactic (← `(tactic|
        simp only [BitVec.mul_comm, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]))))
      if gs.isEmpty then return some (← instantiateMVars mv) else return none
    catch _ => return none
  let mut facts : Array (Name × Expr × Expr) := #[]
  let mut done : Array Expr := #[]
  for i in [0:atoms.size] do
    for j in [i+1:atoms.size] do
      let r := atoms[i]!
      let b := atoms[j]!
      let ra := r.getAppArgs
      let ba := b.getAppArgs
      if done.contains b || done.contains r then continue
      unless ra[0]! == ba[0]! && ra[1]! == ba[1]! && ra[2]! == ba[2]! && ra[3]! == ba[3]! && ra[7]! == ba[7]! do continue
      if ra[4]! == ba[4]! && ra[5]! == ba[5]! && ra[6]! == ba[6]! then continue
      let some ha ← prove ba[4]! ra[4]! | continue
      let some hd ← prove ba[5]! ra[5]! | continue
      let some he ← prove ba[6]! ra[6]! | continue
      let aTy ← inferType ba[8]!
      let fact ← withLocalDeclD `a aTy fun a => do
        let ba' := ba.set! 8 a
        let ra' := ra.set! 8 a
        let _ := ra'
        let pf ← mkAppM ``memState_ports_congr #[ba[3]!, ba[4]!, ra[4]!, ba[5]!, ra[5]!, ba[6]!, ra[6]!, ba[7]!, a, ha, hd, he]
        mkLambdaFVars #[a] pf
      facts := facts.push (Name.mkSimple s!"ved_spell_h{facts.size}", fact, ← inferType fact)
      done := done.push b
  if facts.isEmpty then throwError "ved_mem_spell: no two atoms are spellings of one memory"
  Tools.VedMemLoop.dbgLog s!"spell: {facts.size} facts proved hb(k)={((← IO.getNumHeartbeats) - hb00) / 1000}"
  -- the atoms of the later spelling `b` become `M_r` applications: every proposition that contains one is rewritten by `congrArg` over the abstraction of `M_b` (no unification
  -- of the two big port terms: `simp only [h] at *` tried it on every atom of the other spelling, 9.3M heartbeats on R033 goal 152)
  let mut g' := g
  for (_, fact, _) in facts do
    let ty ← inferType fact
    let some (b, r) := (do
        let .forallE _ _ body _ := ty | none
        let (_, l, rr) ← body.eq?
        pure (l, rr)) | throwError "ved_mem_spell: unexpected fact"
    -- `b`, `r` are the atoms with the bound variable at argument 8
    let bk := b.getAppArgs.extract 0 8
    let Mb := mkAppN b.getAppFn bk
    let Mr := mkAppN r.getAppFn (r.getAppArgs.extract 0 8)
    let hfun ← mkAppM ``funext #[fact]
    let mTy ← inferType Mb
    let rewriteProp (T : Expr) : MetaM (Option (Expr × Expr)) := do
      if (collectDag (fun x => isMemAtom x && x.getAppArgs.extract 0 8 == bk) T).isEmpty then return none
      withLocalDeclD `M mTy fun M => do
        let Tabs := spellReplace bk M T
        let motive ← mkLambdaFVars #[M] Tabs
        let T' := Tabs.replaceFVar M Mr
        let pf ← mkExpectedTypeHint (← mkAppM ``congrArg #[motive, hfun]) (← mkEq T T')
        return some (T', pf)
    -- the hypotheses
    for d in ← g'.withContext getLCtx do
      if d.isImplementationDetail || d.isLet then continue
      let t ← instantiateMVars d.type
      unless (← g'.withContext (isProp t)) do continue
      if let some (t', pf) ← g'.withContext (rewriteProp t) then
        let (r : AssertAfterResult) ← g'.replaceLocalDecl d.fvarId t' pf
        g' := r.mvarId
    -- the target
    let tgt ← instantiateMVars (← g'.getType)
    if let some (t', pf) ← g'.withContext (rewriteProp tgt) then
      g' ← g'.replaceTargetEq t' pf
  replaceMainGoal [g']
  Tools.VedMemLoop.dbgLog s!"spell: rewritten hb(k)={((← IO.getNumHeartbeats) - hb00) / 1000}"
  if (← spellFailLate.get) then throwError "ved_mem_spell: late failure (test seam)"
  spellHits.modify (· + facts.size)

/-! ### `ved_conj_prune`: the conjunctions of bounds in the context, cut to the conjuncts about the atoms of the goal

Observed (s94w, R033 goal 48 / 23 after `ved_cone_clear`): the context keeps `ck31 : env t "_gen_start" < 2 ∧ env t "_gen_frameWriteEn" < 2 ∧ ..` (~40 conjuncts, one per wire of the
module) because every conjunct mentions the environment variables `ck2 ck4` of the target; `omega` reads the whole conjunction in EVERY leaf of `ved_mux` / `ved_split_omega`, the target
needs `env t "_gen_start" < 2` only. Cause (a) of the closing cost: the local theorem the leaf needs (one bound) is buried in a 40-conjunct hypothesis. -/

/-- an environment read `env t "wire"`: an application of a variable to a string literal -/
def isEnvRead (x : Expr) : Bool :=
  x.isApp && x.getAppFn.isFVar && x.appArg!.isStringLit

/-- the atoms of a term: its environment reads and the variables that are not an argument of one -/
def termAtoms (e : Expr) : Array Expr :=
  let reads := collectDag isEnvRead e
  let envFVs := reads.foldl (fun (acc : Std.HashSet FVarId) r => (fvarsOfDag r).foldl (·.insert ·) acc) {}
  reads ++ ((fvarsOfDag e).filter (!envFVs.contains ·)).map Expr.fvar

/-- the conjuncts of an `∧` tree with the projection proofs (`And.left` / `And.right`) -/
partial def conjLeaves (t pr : Expr) : Array (Expr × Expr) :=
  if t.isAppOfArity ``And 2 then
    conjLeaves (t.getArg! 0) (mkApp3 (mkConst ``And.left) (t.getArg! 0) (t.getArg! 1) pr) ++
    conjLeaves (t.getArg! 1) (mkApp3 (mkConst ``And.right) (t.getArg! 0) (t.getArg! 1) pr)
  else #[(t, pr)]

/-- fewest conjuncts of a hypothesis worth cutting -/
def conjPruneMin : Nat := 6
initialize conjPruneHits : IO.Ref Nat ← IO.mkRef 0
initialize conjPruneDropped : IO.Ref Nat ← IO.mkRef 0

/-- `ved_conj_prune`: each hypothesis that is an `∧` tree of >= `conjPruneMin` conjuncts is replaced by the conjuncts that share an atom with the target (closure over the kept conjuncts
and the other small arithmetic hypotheses, three rounds); the others are dropped. Only hypotheses are removed: sound, and a goal that needed a dropped one stays open (the caller restores). -/
elab "ved_conj_prune" : tactic => do
  let g ← getMainGoal
  let g' ← g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let mut big : Array (FVarId × Array (Expr × Expr)) := #[]
    let mut T : Std.HashSet Expr := {}
    for a in termAtoms tgt do T := T.insert a
    for d in ← getLCtx do
      if d.isImplementationDetail || d.isLet then continue
      let t ← instantiateMVars d.type
      unless (← isProp t) do continue
      if t.isAppOfArity ``And 2 then
        let ls := conjLeaves t d.toExpr
        if ls.size ≥ conjPruneMin then
          big := big.push (d.fvarId, ls)
          continue
      -- the small arithmetic hypotheses keep their atoms in the relevant set
      if isArithHyp t && Tools.VedU1Loop.treeSizeVal t ≤ 400 then
        for a in termAtoms t do T := T.insert a
    if big.isEmpty then return g
    let mut keep : Array (Array (Expr × Expr)) := big.map fun _ => #[]
    let mut kept : Array (Array Bool) := big.map fun (_, ls) => ls.map fun _ => false
    for _ in [0:3] do
      for i in [0:big.size] do
        for j in [0:big[i]!.2.size] do
          if kept[i]![j]! then continue
          let (c, _) := big[i]!.2[j]!
          let at_ := termAtoms (← instantiateMVars c)
          if at_.any T.contains then
            kept := kept.set! i (kept[i]!.set! j true)
            for a in at_ do T := T.insert a
    let mut g1 := g
    let mut dropped := 0
    for i in [0:big.size] do
      for j in [0:big[i]!.2.size] do
        if kept[i]![j]! then
          let (c, pr) := big[i]!.2[j]!
          let (_, g2) ← (← g1.assert `ved_cj (← instantiateMVars c) pr).intro1P
          g1 := g2
        else dropped := dropped + 1
    for (f, _) in big do g1 ← g1.tryClear f
    conjPruneDropped.modify (· + dropped)
    pure g1
  if g'.name == g.name && g' == g then throwError "ved_conj_prune: no hypothesis to cut"
  conjPruneHits.modify (· + 1)
  replaceMainGoal [g']

/-- `ved_read_bounds` (s94w): for every read `(f e).toNat` of the target and the hypotheses (`f` a variable, as `ved_cone_opaque` leaves the memories: `ved_M0 a`) the fact `(f e).toNat < 2 ^ w`
(`BitVec.isLt`). `ved_bv_bounds` bounds only the variables, so `omega` saw `X = (ved_M0 a).toNat` unbounded: `(65536 - X) % 65536` and `(65536 - X % 65536) % 65536` (the two spellings of
the absolute value of a quantizer input, R033 goal 6) are different numbers for `X >= 65536` (cause (a): the unsupplied local fact "a memory word is as wide as its data") -/
elab "ved_read_bounds" : tactic => do
  let mut g ← getMainGoal
  let rs ← g.withContext do
    let isRd (x : Expr) : Bool := x.isAppOfArity ``BitVec.toNat 2 && (x.getArg! 1).isApp && (x.getArg! 1).getAppFn.isFVar
    let mut rs : Array Expr := #[]
    for x in collectDag isRd (← instantiateMVars (← g.getType)) do
      unless rs.contains x do rs := rs.push x
    for d in ← getLCtx do
      if d.isImplementationDetail || d.isLet then continue
      let t ← instantiateMVars d.type
      unless (← isProp t) do continue
      if Tools.VedU1Loop.treeSizeVal t > 20000 then continue
      for x in collectDag isRd t do
        unless rs.contains x do rs := rs.push x
    pure rs
  if rs.isEmpty then throwError "ved_read_bounds: no memory read"
  for x in rs do
    let pr ← g.withContext (mkAppM ``BitVec.isLt #[x.getArg! 1])
    let (_, g1) ← (← g.assert `ved_rdb (← g.withContext (inferType pr)) pr).intro1P
    g := g1
  replaceMainGoal [g]

register_option ved.mem.s94StateSplit : Bool := {
  defValue := false
  descr := "ved_local_goal: a separate attempt (own limit stateCapK) for the ite towers over a small state variable: the 5-bit `x.toNat = k` conditions are decided by ONE case split on the value of x, then one omega per branch (ved_state_split); default false"
}

register_option ved.mem.s94MulShift : Bool := {
  defValue := false
  descr := "ved_local_goal: a separate attempt (own limit mulCapK) for the multiply-shift goals ((a * b + c) % 2^32 / 2^(m % 32), the quantizer): the spellings of the case conditions normalised, the memory reads bounded by their data width (ved_read_bounds), the `if`s split and the `% 2^k` of bounded terms cancelled, then omega on the leaves (default false)"
}

initialize mulShiftRefuse : IO.Ref Bool ← IO.mkRef false
initialize mulShiftFailLate : IO.Ref Bool ← IO.mkRef false

initialize stateSplitHits : IO.Ref Nat ← IO.mkRef 0
initialize stateSplitBranches : IO.Ref Nat ← IO.mkRef 0
initialize stateSplitRefuse : IO.Ref Bool ← IO.mkRef false
initialize stateSplitFailLate : IO.Ref Bool ← IO.mkRef false

register_option ved.mem.s94Gates : Bool := {
  defValue := false
  descr := "ved_local_goal: a syntactic test before the separate attempts of ved.mem.s94StateSplit (a variable x with enough comparisons x.toNat = k in the target) and ved.mem.s94MulShift (a power 2 ^ e with a non-literal exponent in the target): a goal without it does not pay the attempt (default false)"
}

initialize gateSkipped : IO.Ref Nat ← IO.mkRef 0

register_option ved.mem.s94StateMinConds : Nat := {
  defValue := 4
  descr := "ved_state_split: fewest comparisons `x.toNat = k` of one variable in the target that make a split worth it (default 4, the value of s94w)"
}

/-- most values of the split variable (the state / phase fields have 3 .. 5 bits) -/
def stateSplitMaxBits : Nat := 5
/-- fewest comparisons `x.toNat = literal` of one variable that make a split worth it -/
def stateSplitMinConds : Nat := 4

/-- the `BitVec n` variable (n <= `stateSplitMaxBits`) with the most distinct comparisons `x.toNat = literal` in the TARGET (>= `stateSplitMinConds`; the context hypotheses are not scanned: their tree sizes cost 3.7M heartbeats on R033 goal 46) -/
def stateSplitVar (g : MVarId) (minC : Option Nat := none) : MetaM (Option (Expr × Nat)) := g.withContext do
  let isCmp (e : Expr) : Bool :=
    e.isAppOfArity ``Eq 3 && (e.getArg! 2).isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).isAppOfArity ``BitVec.toNat 2 && ((e.getArg! 1).getArg! 1).isFVar
  let mut cnt : Std.HashMap FVarId Nat := {}
  let tys := [← instantiateMVars (← g.getType)]
  for t in tys do
    for c in collectDag isCmp t do
      let v := (c.getArg! 1).getArg! 1
      cnt := cnt.insert v.fvarId! (cnt.getD v.fvarId! 0 + 1)
  let mut best : Option (Expr × Nat) := none
  for (f, n) in cnt.toList do
    if n < minC.getD (ved.mem.s94StateMinConds.get (← getOptions)) then continue
    let ty ← whnfR (← instantiateMVars (← f.getType))
    unless ty.isAppOf ``BitVec do continue
    let some w := (← whnf ty.appArg!).rawNatLit? <|> (← instantiateMVars ty.appArg!).nat? | continue
    if w > stateSplitMaxBits then continue
    if best.all fun (_, m) => n > (cnt.getD (best.get!.1.fvarId!) 0) then best := some (.fvar f, w)
  return best

/-- `x = a ∨ x = a+1 ∨ .. ∨ x = n-1` with `OfNat` numerals -/
def natCasesProp (x : Expr) (a n : Nat) : MetaM Expr := do
  let natT := mkConst ``Nat
  let rec go (k : Nat) (fuel : Nat) : MetaM Expr := do
    let eq ← mkEq x (← mkNumeral natT k)
    match fuel with
    | 0 => return eq
    | f + 1 => if k + 1 >= n then return eq else return mkApp2 (mkConst ``Or) eq (← go (k + 1) f)
  go a n

/-- a proof of `natCasesProp x a n` from `hlo : a ≤ x`, `hhi : x < n` (by `Nat.eq_or_lt_of_le`, no `omega`: 2.4M heartbeats for the 32 cases) -/
partial def natCasesProof (x hlo hhi : Expr) (a n : Nat) : MetaM Expr := do
  let natT := mkConst ``Nat
  let la ← mkNumeral natT a
  if a + 1 >= n then
    -- x = a from a ≤ x and x < a+1
    let hle ← mkAppM ``Nat.le_of_lt_succ #[hhi]
    return ← mkAppM ``Nat.le_antisymm #[hle, hlo]
  let rest ← natCasesProp x (a + 1) n
  let eqP ← mkEq x la
  let dis ← mkAppM ``Nat.eq_or_lt_of_le #[hlo]          -- a = x ∨ a < x
  let hL ← withLocalDeclD `h (← mkEq la x) fun h => do mkLambdaFVars #[h] (← mkAppOptM ``Or.inl #[eqP, rest, ← mkEqSymm h])
  let hR ← withLocalDeclD `h (← mkAppM ``LT.lt #[la, x]) fun h => do
    let sub ← natCasesProof x h hhi (a + 1) n
    mkLambdaFVars #[h] (← mkAppOptM ``Or.inr #[eqP, rest, sub])
  mkAppM ``Or.elim #[dis, hL, hR]

/-- `ved_state_split`: the variable `v` found by `stateSplitVar`; the goal splits into the cases `v.toNat = 0 .. 2^w - 1` (`Or` chain proved by `omega` from `v.isLt`), and in the case `k`
the reads `v.toNat` of the TARGET are replaced by the literal `k` (the context is not touched: no `subst`, which reverts and re-introduces every hypothesis that mentions `v`, 260k heartbeats
per case on R033 goal 48; the case hypothesis `v.toNat = k` stays for `omega`). No such variable: a refusal. -/
def stateSplitRun (minC : Option Nat) : TacticM Unit := do
  let g ← getMainGoal
  let hb0 ← IO.getNumHeartbeats
  let stage {α} (nm : String) (m : MetaM α) : MetaM α := do
    let h ← IO.getNumHeartbeats
    let r ← try m catch e => throwError "ved_state_split[{nm}]: {e.toMessageData}"
    Tools.VedMemLoop.dbgLog s!"state_split {nm}: hb(k)={((← IO.getNumHeartbeats) - h) / 1000} total {((← IO.getNumHeartbeats) - hb0) / 1000}"
    pure r
  let some (v, w) ← stateSplitVar g minC | throwError "ved_state_split: no small variable with at least {minC.getD stateSplitMinConds} comparisons x.toNat = k"
  let n := 2 ^ w
  let rd ← stage "rd" <| g.withContext (mkAppM ``BitVec.toNat #[v])
  let natT := mkConst ``Nat
  let cs ← natCasesProp rd 0 n
  let (hcF, g3) ← stage "cases-prop" <| g.withContext do
    let hhi ← mkAppM ``BitVec.isLt #[v]
    let hlt ← mkAppM ``LT.lt #[rd, ← mkNumeral natT n]
    unless ← isDefEq (← inferType hhi) hlt do throwError "bound: 2^w is not {n}"
    let hhi' ← mkExpectedTypeHint hhi hlt
    let pr ← natCasesProof rd (← mkAppM ``Nat.zero_le #[rd]) hhi' 0 n
    unless ← isDefEq (← inferType pr) cs do throwError "bound has the wrong type"
    (← g.assert `ved_sv_cs cs pr).intro1P
  let tgt ← instantiateMVars (← g.getType)
  let rec casesLoop (g : MVarId) (h : FVarId) (k : Nat) : MetaM (List MVarId) := do
    let caseGoal (g : MVarId) (h : FVarId) : MetaM MVarId := g.withContext do
      let lit ← mkNumeral natT k
      let tgt' := tgt.replace fun e => if e == rd then some lit else none
      let lam := Expr.lam `ved_x natT (tgt.replace fun e => if e == rd then some (.bvar 0) else none) .default
      g.replaceTargetEq tgt' (← mkCongrArg lam (mkFVar h))
    if k + 1 >= n then
      return [← caseGoal g h]
    else
      let subs ← g.cases h
      let some s1 := subs[0]? | throwError "ved_state_split: cases"
      let some s2 := subs[1]? | throwError "ved_state_split: cases"
      let g1' ← caseGoal s1.mvarId s1.fields[0]!.fvarId!
      return g1' :: (← casesLoop s2.mvarId s2.fields[0]!.fvarId! (k + 1))
  let gs ← stage "cases" <| g3.withContext <| casesLoop g3 hcF 0
  stateSplitBranches.modify (· + gs.length)
  replaceMainGoal gs

elab "ved_state_split" : tactic => stateSplitRun none

/-- option `ved.mem.s94StateSplit2` (s94y): a branch of the state split that the closers of `ved_state_branch` do not close is split a SECOND time, on the best other small variable with at least one comparison
`x.toNat = k` left in its target (R033 goals 33 34, branch ck156 = 4: `ck164.toNat = 0`, `2 ^ ck164.toNat`); one level only -/
register_option ved.mem.s94StateSplit2 : Bool := {
  defValue := false
  descr := "ved_state_branch: a branch that its closers do not close is split once more on another small state variable (default false)"
}

/-- the number of nested splits made / the test seams of the nested split (CloseCheck) -/
initialize nestedSplits : IO.Ref Nat ← IO.mkRef 0
initialize nestedRefuse : IO.Ref Bool ← IO.mkRef false
initialize nestedFailLate : IO.Ref Bool ← IO.mkRef false

/-- `ved_nest_gate`: refused unless `ved.mem.s94StateSplit2` is on (no work before the refusal) -/
elab "ved_nest_gate" : tactic => do
  unless ved.mem.s94StateSplit2.get (← getOptions) do throwError "ved_nest_gate: option ved.mem.s94StateSplit2 is off"

/-- `ved_state_split2`: the second-level split (refused unless `ved.mem.s94StateSplit2` is on): one comparison is enough -/
elab "ved_state_split2" : tactic => do
  unless ved.mem.s94StateSplit2.get (← getOptions) do throwError "ved_state_split2: option ved.mem.s94StateSplit2 is off"
  if ← nestedRefuse.get then throwError "ved_state_split2: refused (test seam)"
  stateSplitRun (some 1)
  nestedSplits.modify (· + 1)
  if ← nestedFailLate.get then throwError "ved_state_split2: failed after its work (test seam)"

/-- option `ved.mem.s94CondSplit` (s94y): the leaf closer of the state branches splits the most frequent `if` condition of the target (`by_cases`, then ONE `simp only [h]` that decides the `if`s with that condition,
no `split`) until the target has no `if` left, then `omega`; the old closers stay the fallback.  R033 goals 33 34 (branch ck156 = 4, after the second split) and 62 (branch 12): `split` walks the 4e5 .. 8e5-node
tree for every one of the 75 `if`s and its internal simp times out at 8M, the DAG has 600 nodes and three distinct conditions (cause (a): a leaf closer that is too expensive, not an unsupplied lemma) -/
register_option ved.mem.s94CondSplit : Bool := {
  defValue := false
  descr := "ved_cond_split: leaves of the state branches closed by case splits on the most frequent if-condition (one simp each) and omega (default false)"
}

/-- test seams / counters (CloseCheck) -/
initialize condSplits : IO.Ref Nat ← IO.mkRef 0
initialize condRefuse : IO.Ref Bool ← IO.mkRef false
initialize condFailLate : IO.Ref Bool ← IO.mkRef false

/-- the `if` condition of the target with the most `ite` nodes (DAG; ties: the smaller condition) -/
def iteCondTop (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut cnt : Std.HashMap Expr Nat := {}
  for x in collectDag (fun x => x.isAppOfArity ``ite 5) tgt do
    let c := x.getArg! 1
    cnt := cnt.insert c (cnt.getD c 0 + 1)
  let mut best : Option (Expr × Nat) := none
  -- the conditions that contain no `if` themselves first (the innermost ones: deciding them lets the outer ones reduce)
  let plain := cnt.toList.filter fun (c, _) => (collectDag (fun x => x.isAppOfArity ``ite 5) c).isEmpty
  for (c, n) in (if plain.isEmpty then cnt.toList else plain) do
    match best with
    | none => best := some (c, n)
    | some (c0, n0) => if n > n0 || (n == n0 && (collectDag (fun _ => true) c).size < (collectDag (fun _ => true) c0).size) then best := some (c, n)
  return best.map (·.1)

/-- the target with every `ite c t e` (the condition `c`, `hc : c` when `pos`, else `hc : ¬ c`) replaced by `t` (`e`): one `congrArg` over the abstraction of the node per node (DAG replace, no `simp`: the
simp of a 2e5-node tree costs 7M heartbeats for the first split, 1e5 .. 4e5 for the later ones); outer nodes first, a node that went away with a discarded branch is skipped -/
def decideIte (g : MVarId) (c hc : Expr) (pos : Bool) : MetaM MVarId := do
  let mut g := g
  let tgt0 ← instantiateMVars (← g.getType)
  for node in collectDag (fun x => x.isAppOfArity ``ite 5 && x.getArg! 1 == c) tgt0 do
    let tgt ← instantiateMVars (← g.getType)
    if (tgt.find? (· == node)).isNone then continue
    g ← g.withContext do
      let α := node.getArg! 0
      let inst := node.getArg! 2
      let t := node.getArg! 3
      let e := node.getArg! 4
      let u ← getLevel α
      let (b, h) := if pos then (t, mkApp6 (mkConst ``if_pos [u]) c inst hc α t e) else (e, mkApp6 (mkConst ``if_neg [u]) c inst hc α t e)
      let aTy ← inferType node
      withLocalDeclD `ved_x aTy fun x => do
        let Tabs := tgt.replace fun y => if y == node then some x else none
        let motive ← mkLambdaFVars #[x] Tabs
        let T' := Tabs.replaceFVar x b
        g.replaceTargetEq T' (← mkExpectedTypeHint (← mkAppM ``congrArg #[motive, h]) (← mkEq tgt T'))
  return g

/-- the fewest `ite` DAG nodes of a target for `ved_cond_split` (R033: the towers of 33 34 (85) 62 (54) 53 (> 40); the small branches that the old closers close have <= 25) -/
def condSplitMinIte : Nat := 30

/-- `ved_cond_gate`: refused unless `ved.mem.s94CondSplit` is on (no work before the refusal) -/
elab "ved_cond_gate" : tactic => do
  unless ved.mem.s94CondSplit.get (← getOptions) do throwError "ved_cond_gate: option ved.mem.s94CondSplit is off"
  -- only a tower (at least `condSplitMinIte` distinct `if` nodes): a small goal is closed by the old closers for 0.1 .. 3M and must keep its budget
  let tgt ← instantiateMVars (← (← getMainGoal).getType)
  if (collectDag (fun x => x.isAppOfArity ``ite 5) tgt).size < condSplitMinIte then throwError "ved_cond_gate: fewer than {condSplitMinIte} if nodes"

/-- the truth value of a closed proposition `c` by evaluation (`Decidable.decide c` reduced with the literal simprocs of `whnf`): `(true, proof of c)` / `(false, proof of ¬ c)`, none if it does not evaluate -/
def groundTruth (c : Expr) : MetaM (Option (Bool × Expr)) := do
  let some inst ← (try some <$> synthInstance (mkApp (mkConst ``Decidable) c) catch _ => pure none) | return none
  let d := mkApp2 (mkConst ``Decidable.decide) c inst
  let r ← withDefault (whnf d)
  if r.isConstOf ``Bool.true then
    return some (true, mkApp3 (mkConst ``of_decide_eq_true) c inst (← mkEqRefl (mkConst ``Bool.true)))
  else if r.isConstOf ``Bool.false then
    return some (false, mkApp3 (mkConst ``of_decide_eq_false) c inst (← mkEqRefl (mkConst ``Bool.false)))
  else return none

/-- `ved_orb_mod`: the facts `x ||| y < 2 ^ k` of `ved_or_bounds` (`ved_orb`) as rewrite rules `x ||| y % 2 ^ k = x ||| y` (`Nat.mod_eq_of_lt`, no discharger: `simp` with `omega` as discharger costs 11M here); fails
when there is none or nothing changes -/
elab "ved_orb_mod" : tactic => withMainContext do
  let mut ls : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for d in ← getLCtx do
    if d.userName == `ved_orb then
      let h ← Term.exprToSyntax d.toExpr
      ls := ls.push (← `(Lean.Parser.Tactic.simpLemma| Nat.mod_eq_of_lt $h:term))
  if ls.isEmpty then throwError "ved_orb_mod: no bound"
  evalTactic (← `(tactic| simp only [$ls,*]))

/-- `ved_dedup`: a hypothesis whose type is that of an earlier one is cleared (the bound facts `ved_bnd` are asserted again by every closer that runs `ved_bv_bounds`: `omega` reads every copy); fails when nothing is cleared -/
elab "ved_dedup" : tactic => withMainContext do
  let mut seen : Std.HashSet Expr := {}
  let mut dups : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let t ← instantiateMVars d.type
    unless (← isProp t) do continue
    if seen.contains t then dups := dups.push d.fvarId else seen := seen.insert t
  if dups.isEmpty then throwError "ved_dedup: no duplicate"
  let mut g ← getMainGoal
  for f in dups.reverse do g ← g.tryClear f
  replaceMainGoal [g]

/-- option `ved.mem.s94CondAbsurd`: in a leaf of `ved_cond_split` the case hypotheses (`ved_hc`) are first tried for a contradiction on their own, in a context of those and the variable bounds only (a path whose conditions
cannot hold together is closed without looking at the equation: R033 goals 33 / 34 branch ck156 = 4, the final `omega` of the leaves 12 .. 25M with the two-spelling `|||` products of the target in its problem) -/
register_option ved.mem.s94CondAbsurd : Bool := {
  defValue := false
  descr := "ved_cond_split: a leaf whose case hypotheses contradict each other is closed by omega on them alone (default false)"
}

/-- the heartbeat limit of the contradiction attempt (thousands) -/
def condAbsurdCapK : Nat := 1000

/-- `ved_hc_absurd`: `False` from the `ved_hc` / `ved_bnd` hypotheses by `omega` (limit `condAbsurdCapK`); refused when the option is off, fails when there is no contradiction -/
elab "ved_hc_absurd" : tactic => do
  unless ved.mem.s94CondAbsurd.get (← getOptions) do throwError "ved_hc_absurd: option ved.mem.s94CondAbsurd is off"
  let g ← getMainGoal
  let hb0 ← IO.getNumHeartbeats
  let mv ← g.withContext (Tools.VedMemS94Addr.trimmedMVarWith (mkConst ``False) fun n => n == `ved_hc || n == `ved_bnd || n == `ved_bnd2)
  let gs ← withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then condAbsurdCapK * 1000 else min c.maxHeartbeats (condAbsurdCapK * 1000)), initHeartbeats := hb0 }) do
    Tactic.run mv.mvarId! (withoutRecover (evalTactic (← `(tactic| omega))))
  unless gs.isEmpty do throwError "ved_hc_absurd: no contradiction"
  let pr ← instantiateMVars mv
  g.assign (← mkFalseElim (← g.getType) pr)
  replaceMainGoal []

partial def condSplitGo (depth : Nat) : TacticM Unit := do
  let hc := mkIdent `ved_hc
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  if (collectDag (fun x => x.isAppOfArity ``ite 5) tgt).isEmpty then
    -- the leaf: the exponents / addresses the splits brought into two spellings unified, the `|||` bounds, then omega
    let hb0 ← IO.getNumHeartbeats
    if (← IO.getEnv "VED_CONDDBG").isSome then
      IO.eprintln s!"cond_split[{depth}]: leaf start: {((← g.withContext (ppExpr (← instantiateMVars (← g.getType)))).pretty.replace "\n" " ").take 3000}"
    try
      -- the steps one after the other (the same sequence as one `;` chain); the heartbeat marks are printed only under `VED_CONDDBG`
      let hbl (nm : String) : IO Unit := do
        if (← IO.getEnv "VED_CONDDBG").isSome then IO.eprintln s!"cond_split[{depth}]: leaf {nm}: hb(k) since start {((← IO.getNumHeartbeats) - hb0) / 1000}"
      -- (option `ved.mem.s94CondAbsurd`) a path whose case hypotheses contradict each other needs nothing else
      if ved.mem.s94CondAbsurd.get (← getOptions) then
        let closed ← tryCatchRuntimeEx (do evalTactic (← `(tactic| ved_hc_absurd)); pure true) (fun _ => pure false)
        hbl s!"absurd {closed}"
        if closed then return
      evalTactic (← `(tactic| (try ved_spell_unify)))
      hbl "unify"
      evalTactic (← `(tactic| (try ved_or_bounds)))
      hbl "or_bounds"
      evalTactic (← `(tactic| (try ved_orb_mod)))
      hbl "orb_mod"
      evalTactic (← `(tactic| (try (ved_or_bounds; ved_orb_mod))))
      hbl "or_bounds2"
      if (← IO.getEnv "VED_CONDDBG").isSome && !(← getGoals).isEmpty then
        let g1 ← getMainGoal
        IO.eprintln s!"cond_split[{depth}]: leaf before omega, target: {((← g1.withContext (ppExpr (← instantiateMVars (← g1.getType)))).pretty.replace "\n" " ").take 3000}"
        g1.withContext do
          for d in ← getLCtx do
            if d.userName == `ved_orb || d.userName == `ved_hc then IO.eprintln s!"cond_split[{depth}]: leaf before omega, {d.userName}: {((← ppExpr d.type).pretty.replace "\n" " ").take 500}"
      evalTactic (← `(tactic| all_goals (try ved_dedup)))
      hbl "dedup"
      evalTactic (← `(tactic| all_goals omega))
      hbl "omega"
    catch e =>
      if (← IO.getEnv "VED_CONDDBG").isSome then
        IO.eprintln s!"cond_split[{depth}]: leaf FAILED after hb(k)={((← IO.getNumHeartbeats) - hb0) / 1000}"
        IO.eprintln s!"cond_split[{depth}]: leaf goal: {((← g.withContext (ppExpr (← instantiateMVars (← g.getType)))).pretty.replace "\n" " ").take 3000}"
        g.withContext do
          for d in (← getLCtx) do
            if d.userName == `ved_hc then
              IO.eprintln s!"cond_split[{depth}]: leaf hyp: {((← ppExpr d.type).pretty.replace "\n" " ").take 700}"
      throw e
    if (← IO.getEnv "VED_CONDDBG").isSome then IO.eprintln s!"cond_split[{depth}]: leaf ok hb(k)={((← IO.getNumHeartbeats) - hb0) / 1000}"
  else
    if depth == 0 then throwError "ved_cond_split: depth"
    let some c ← iteCondTop g | throwError "ved_cond_split: no condition"
    if (← IO.getEnv "VED_CONDDBG").isSome then IO.eprintln s!"cond_split[{depth}]: cond chosen, hb(k)={(← IO.getNumHeartbeats) / 1000}"
    -- a condition without a free variable (the literals the earlier decisions left: `((1 ^^^ 1) % 2 ||| 1) % 2 = 0`) is evaluated, not split: one branch was a false statement that `omega`
    -- cannot refute (its bit operations are atoms) and cost the whole leaf limit
    if (collectDag (·.isFVar) c).isEmpty then
      if let some (pos, hcE) ← g.withContext (groundTruth c) then
        let g2 ← decideIte g c hcE pos
        setGoals [g2]
        if (← IO.getEnv "VED_CONDDBG").isSome then IO.eprintln s!"cond_split[{depth}]: ground condition decided ({pos})"
        condSplitGo depth
        return
    let cs ← g.withContext (Term.exprToSyntax c)
    if (← IO.getEnv "VED_CONDDBG").isSome then
      IO.eprintln s!"cond_split[{depth}]: {((← g.withContext (ppExpr c)).pretty.replace "\n" " ").take 300}"
    evalTactic (← `(tactic| by_cases $hc:ident : $cs))
    condSplits.modify (· + 1)
    let mut pos := true
    for g1 in ← getGoals do
      let hcE ← g1.withContext do
        let some d := (← getLCtx).findFromUserName? `ved_hc | throwError "ved_cond_split: hypothesis"
        pure d.toExpr
      let g2 ← decideIte g1 c hcE pos
      pos := false
      setGoals [g2]
      if (← IO.getEnv "VED_CONDDBG").isSome then IO.eprintln s!"cond_split[{depth}]: decided, hb(k)={(← IO.getNumHeartbeats) / 1000}"
      condSplitGo (depth - 1)

/-- `ved_cond_split d`: see `ved.mem.s94CondSplit`; at most `d` nested splits; refused when the option is off -/
elab "ved_cond_split " d:num : tactic => do
  unless ved.mem.s94CondSplit.get (← getOptions) do throwError "ved_cond_split: option ved.mem.s94CondSplit is off"
  if ← condRefuse.get then throwError "ved_cond_split: refused (test seam)"
  try condSplitGo d.getNat
  catch e =>
    if (← IO.getEnv "VED_CONDDBG").isSome then IO.eprintln s!"cond_split: threw: {((← e.toMessageData.toString).replace "\n" " ").take 2500}"
    throw e
  if ← condFailLate.get then throwError "ved_cond_split: failed after its work (test seam)"

/-- `ved_state_simp`: the target of EVERY goal simplified by the decide-able part of the case conditions (literal comparisons, `if` of a literal condition, the 0/1 flags `(if p then 1 else 0) % 2 = 1 / 0`, the bit operations on
literals, `x % m` of an `if`): ONE simp context for all the goals (the context of the simp set is built once, not per branch: 100k+ heartbeats each); goals the simp does not change are kept. -/
elab "ved_state_simp" : tactic => do
  let stx ← `(tactic| simp only [Nat.reduceEqDiff, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow, Nat.reduceAnd, Nat.reduceOr, Nat.reduceXor, ↓reduceIte, true_and, and_true, false_and, and_false,
    false_or, or_false, true_or, or_true, and_self, not_true_eq_false, not_false_eq_true, if_true, if_false, true_imp_iff, false_imp_iff, Tools.VedMemS94Addr.or_eq_zero_iff', ite10_mod2, ite10_mod2_z, ite10_eq1, ite10_eq0, Classical.not_not, mux_mod,
    Nat.zero_and, Nat.and_zero, Nat.zero_or, Nat.or_zero, Nat.zero_xor, Nat.xor_zero, Nat.zero_mod])
  let sc ← mkSimpContext stx (eraseLocal := false)
  let mut out : Array MVarId := #[]
  for g in ← getGoals do
    let r ← try g.withContext (some <$> Meta.simpTarget g sc.ctx sc.simprocs (← sc.dischargeWrapper.with fun d? => pure d?)) catch _ => pure none
    match r with
    | some (some g', _) => out := out.push g'
    | some (none, _) => pure ()
    | none => out := out.push g
  setGoals out.toList

/-- `ved_local_new_gate`: refuses unless `ved.mem.s94Addr` or `ved.mem.s94HypSplit` is on (the second alternative of `ved_local_close` exists only for those) -/
elab "ved_local_new_gate" : tactic => do
  unless ved.mem.s94Addr.get (← getOptions) || ved.mem.s94HypSplit.get (← getOptions) do throwError "ved_local_new_gate: no s94u option is on"

/-- `ved_local_close`: the goal from its own cone: cone clear, field extraction, bounds, then `omega` (with `split` for the `if`s) -/
macro "ved_local_close" : tactic =>
  `(tactic| (ved_cone_clear; (try ved_cone_opaque); (try ved_pack_extract); ved_local_small; (try dsimp only at *); (try simp only [ite10_mod2] at *);
             all_goals (ved_bv_bounds
                        (try simp only [mux_mod]); ved_mux)))

/-- `ved_local_close_new` (s94u; refused unless `ved.mem.s94Addr` or `ved.mem.s94HypSplit` is on): the second alternative of `ved_local_goal`, tried only when `ved_local_close` did not close the goal (NOT part of
`ved_local_close`: that one is also the closer of the address equalities, whose one budget the new steps must not use up, observed R033 goal 40): the address spellings of the memory reads normalised,
`(if p then 1 else 0) / 2`, the `if`s of the hypotheses split -/
macro "ved_local_close_new" : tactic =>
  `(tactic| (ved_local_new_gate; ved_cone_clear; (try ved_cone_opaque); (try ved_pack_extract); (try ved_atom_args);
             -- `ved_atom_args` can close the goal (a hypothesis became `False`): the rest runs on the goals that are left
             all_goals (ved_local_small; (try dsimp only at *); (try simp only [ite10_mod2] at *); (try ved_ite_div)
                        all_goals (ved_bv_bounds
                                   (try simp only [mux_mod]); first | ved_mux | ved_hyp_split_omega_g))))

/-- `ved_local_close_spell` (s94v; refused unless `ved.mem.s94Spell` is on): the third alternative of `ved_local_goal`, a separate attempt under its own limit `spellCapK` (the first two, under
`localCapK`, did not close the goal): `ved_mem_spell` (two spellings of one memory are one atom), then the steps of `ved_local_close_new` -/
macro "ved_local_close_spell" : tactic =>
  `(tactic| (ved_cone_clear; ved_mem_spell; (try ved_cone_opaque); (try ved_pack_extract); (try ved_atom_args);
             all_goals (ved_local_small; (try dsimp only at *); (try simp only [ite10_mod2] at *); (try ved_ite_div)
                        all_goals (ved_bv_bounds
                                   (try simp only [mux_mod]); first | ved_mux | ved_hyp_split_omega_g))))

/-- the spellings of the case conditions made one: `(if p then 1 else 0) % 2 = 0 / 1`, `(if p then 1 else 0) = 0 / 1`, `¬ x % 2 = 1` (the two sides of a goal spell one condition both ways: the `if`s
of the two sides are different atoms for `omega` / `split` otherwise, R033 goal 6: `(if ck132 / 4 % 2 = 1 then 1 else 0) % 2 = 0` against `ck132 / 4 % 2 = 0`) -/
macro "ved_cond_norm" : tactic =>
  `(tactic| simp only [ite10_mod2, ite10_mod2_z, ite10_eq1, ite10_eq0, Nat.mod_two_ne_one, Nat.mod_two_ne_zero, Nat.reducePow, Nat.reduceAdd, Nat.reduceMod] at *)

/-- `ved_mul_opt_gate`: refuses unless `ved.mem.s94MulShift` is on (the multiply-shift closing as an alternative of the state branch closer) -/
elab "ved_mul_opt_gate" : tactic => do
  unless ved.mem.s94MulShift.get (← getOptions) do throwError "ved_mul_opt_gate: option ved.mem.s94MulShift is off"

/-- `ved_state_cheap_gate` (option `ved.mem.s94Gates`): the state attempt needs a variable with enough comparisons `x.toNat = k` in the target; no such variable: refused at once (the option off: no test) -/
elab "ved_state_cheap_gate" : tactic => do
  unless ved.mem.s94Gates.get (← getOptions) do return
  let g ← getMainGoal
  if (← stateSplitVar g).isNone then
    gateSkipped.modify (· + 1)
    throwError "ved_state_cheap_gate: no state variable in the target"

/-- `ved_pow_gate` (option `ved.mem.s94Gates`): the multiply-shift attempt needs a power `2 ^ e` with a non-literal exponent in the target (the shift by a variable amount) -/
elab "ved_pow_gate" : tactic => do
  unless ved.mem.s94Gates.get (← getOptions) do return
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let isVarPow (x : Expr) : Bool := x.isAppOfArity ``HPow.hPow 6 && !(x.getArg! 5).isAppOf ``OfNat.ofNat && !(x.getArg! 5).isRawNatLit
  if (collectDag isVarPow tgt).isEmpty then
    gateSkipped.modify (· + 1)
    throwError "ved_pow_gate: no power with a variable exponent in the target"

/-- `ved_state_late` / `ved_mul_late`: the test seams "the attempt failed after its work" (the caller restores the goal) -/
elab "ved_state_late" : tactic => do
  if ← stateSplitFailLate.get then throwError "ved_state_late: failed after its work (test seam)"
elab "ved_mul_late" : tactic => do
  if ← mulShiftFailLate.get then throwError "ved_mul_late: failed after its work (test seam)"

/-- `ved_state_gate`: refuses unless `ved.mem.s94StateSplit` is on (and the test seam `stateSplitRefuse` is off) -/
elab "ved_state_gate" : tactic => do
  unless ved.mem.s94StateSplit.get (← getOptions) do throwError "ved_state_gate: option ved.mem.s94StateSplit is off"
  if ← stateSplitRefuse.get then throwError "ved_state_gate: refused (test seam)"

/-- the closer of one branch of the state split (a small goal: the literal conditions are decided, the rest are linear `if`s of a few atoms): its own cone, the bounds of its variables, `ved_split_omega`;
the bit operations on 0/1 flags by `split` and the literal simprocs -/
macro "ved_state_leaf_body" : tactic =>
  `(tactic| (ved_cone_clear; (try ved_spell_unify); (try ved_read_lift); ved_bv_bounds_t
             first
             | (simp only [mux_mod]; done)
             | (ved_cond_gate; (try simp only [mux_mod]); ved_cond_split 12)
             | ((try simp only [mux_mod]); ved_or_gate; ved_split_omega_o)
             | ((try simp only [mux_mod]); ved_split_omega)
             | (ved_mul_opt_gate; (try ved_cond_norm); (try ved_read_bounds); ved_bv_bounds; (try simp only [mux_mod]); (repeat' split)
                all_goals (try simp (disch := omega) only [Nat.mod_eq_of_lt, Nat.reducePow, Nat.reduceAdd, Nat.reduceMod])
                all_goals omega)
             | ((repeat' split) <;> (try simp only [Nat.reduceAnd, Nat.reduceOr, Nat.reduceXor, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow, Nat.reduceEqDiff, ↓reduceIte, true_and, and_true, false_and, and_false] at *) <;> omega)))

/-- the closer of one branch with the nested split (option `ved.mem.s94StateSplit2`): the leaf closers first (as before), else the branch is split once more and each leaf closed by them -/
macro "ved_state_branch_body" : tactic =>
  `(tactic| first
            | ved_state_leaf_body
            | (ved_nest_gate; ved_cone_clear; (try ved_spell_unify); (try ved_read_lift); ved_bv_bounds_t
               ved_state_split2; ved_state_simp; all_goals ved_state_leaf_body))

/-- the heartbeat limit of ONE branch of the state split (thousands; option `ved.mem.s94Gates`): the branches that close cost 0.2 .. 5M on R033 (goals 23 26 35 46 48 49 54 57 64), a branch that does not
close used up the whole attempt limit before (the timeouts of 33 34 53 62 at 20M) -/
def branchCapK : Nat := 8000

/-- `ved_branch_cap tac` (option `ved.mem.s94Gates`): `tac` under `min (what is left of the limit) branchCapK`; a branch over it is a failure of the attempt (the heartbeat exception goes up to
`ved_local_goal`, which restores the goal); the option off: `tac` as it is -/
elab "ved_branch_cap " t:tacticSeq : tactic => do
  if !ved.mem.s94Gates.get (← getOptions) then evalTactic t
  else
    let hb0 ← IO.getNumHeartbeats
    withTheReader Core.Context (fun c =>
      let left := if c.maxHeartbeats == 0 then branchCapK * 1000 else (c.initHeartbeats + c.maxHeartbeats) - hb0
      { c with maxHeartbeats := max 1 (min left (branchCapK * 1000)), initHeartbeats := hb0 }) do
      evalTactic t

macro "ved_state_branch" : tactic => `(tactic| ved_branch_cap (ved_state_branch_body))

/-- `ved_local_close_state` (s94w; refused unless `ved.mem.s94StateSplit` is on): the fourth attempt of `ved_local_goal`, under its own limit `stateCapK` (the earlier ones did not close the goal): the cone, the
conjunctions of bounds cut to the atoms of the target (`ved_conj_prune`), then the ite tower decided by ONE case split on the value of the state variable (`ved_state_split`, `ved_state_simp`) and one
`omega` per remaining branch; with no state variable (fewer than `stateSplitMinConds` comparisons `x.toNat = k` in the target) only the pruned context is used (`ved_mux`) -/
macro "ved_local_close_state" : tactic =>
  `(tactic| (ved_state_gate; ved_state_cheap_gate; ved_cone_clear; (try ved_mem_spell); (try ved_cone_opaque); (try ved_pack_extract); ved_local_small; (try dsimp only at *); (try simp only [ite10_mod2] at *)
             (try ved_conj_prune)
             first
             | (ved_state_split; ved_state_simp; all_goals ved_state_branch; ved_state_late)
             | ((try ved_atom_args); all_goals ((try ved_ite_div); (try ved_cond_norm); (try ved_spell_unify); (try ved_read_lift); (try ved_read_bounds); ved_bv_bounds; first | (simp only [mux_mod]; done) | ((try simp only [mux_mod]); ved_mux)))))

/-- `ved_mul_gate`: refuses unless `ved.mem.s94MulShift` is on -/
elab "ved_mul_gate" : tactic => do
  unless ved.mem.s94MulShift.get (← getOptions) do throwError "ved_mul_gate: option ved.mem.s94MulShift is off"
  if ← mulShiftRefuse.get then throwError "ved_mul_gate: refused (test seam)"

/-- `ved_local_close_mulshift` (s94w; refused unless `ved.mem.s94MulShift` is on): the fifth attempt of `ved_local_goal`, own limit `mulCapK`: the multiply-shift goals. Both sides spell the same
`((|a| * b + c) % 2^32 / 2^(m % 32)) % 65536`; what the closing arithmetic lacks is (a) the conditions spelled one way (`ved_cond_norm`), (b) `(f e).toNat < 2^w` for the memory reads (`ved_read_bounds`) and
the bounds of the variables, so that `x % 2^k = x` for the bounded factors (`Nat.mod_eq_of_lt` with `omega` as discharger) makes the nonlinear products `|a| * b` (and `2 ^ (m % 32)`) the same atom of both
sides after the `if`s are split; no case split on the shift amount is needed (it is the same atom on both sides) -/
macro "ved_local_close_mulshift" : tactic =>
  `(tactic| (ved_mul_gate; ved_pow_gate; ved_cone_clear; (try ved_cone_opaque); (try ved_pack_extract); (try ved_atom_args)
             all_goals (ved_local_small; (try dsimp only at *); (try simp only [ite10_mod2] at *); (try ved_ite_div))
             (try ved_conj_prune)
             (try ved_cond_norm); (try ved_read_bounds); ved_bv_bounds; (try simp only [mux_mod])
             (repeat' split)
             all_goals (try simp (disch := omega) only [Nat.mod_eq_of_lt, Nat.reducePow, Nat.reduceAdd, Nat.reduceMod])
             all_goals omega
             ved_mul_late))

/-- the heartbeat limit of the separate attempt `ved_local_close_mulshift` (thousands; R033 goals 6 95 107 111: 7 .. 14M) -/
def mulCapK : Nat := 16000

/-- the heartbeat limit of the separate attempt `ved_local_close_state` (thousands; R033 goals 23 46 48 49 57: 7 .. 15M) -/
def stateCapK : Nat := 16000

/-- the heartbeat limit of the separate attempt `ved_local_close_spell` (thousands; the proof of the port equation 3M, the rewrite 0.1M, the closing arithmetic 6M on R033 goals 152 158) -/
def spellCapK : Nat := 12000

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
        withoutRecover (evalTactic (← `(tactic| first | ved_local_close | ved_local_close_new)))
      if ← localFailLate.get then throwError "ved_local_goal: failed after its work (test seam)"
      pure true)
    (fun _ => pure false)
  -- the separate attempt of `ved.mem.s94Spell` (own limit), on the restored state
  let r ← if r || !ved.mem.s94Spell.get (← getOptions) then pure r else do
    st.restore
    let hb1 ← IO.getNumHeartbeats
    tryCatchRuntimeEx
      (do
        withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then spellCapK * 1000 else min c.maxHeartbeats (spellCapK * 1000)), initHeartbeats := hb1 }) do
          withoutRecover (evalTactic (← `(tactic| ved_local_close_spell)))
        if ← localFailLate.get then throwError "ved_local_goal: failed after its work (test seam)"
        pure true)
      (fun _ => pure false)
  Tools.VedMemLoop.dbgLog s!"local_goal: after spell {r} hb(k)={((← IO.getNumHeartbeats) - hb0) / 1000}"
  -- the separate attempt of `ved.mem.s94StateSplit` (own limit), on the restored state
  let r ← if r || !ved.mem.s94StateSplit.get (← getOptions) then pure r else do
    st.restore
    let hb2 ← IO.getNumHeartbeats
    tryCatchRuntimeEx
      (do
        withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then stateCapK * 1000 else min c.maxHeartbeats (stateCapK * 1000)), initHeartbeats := hb2 }) do
          withoutRecover (evalTactic (← `(tactic| ved_local_close_state)))
        if ← stateSplitFailLate.get then throwError "ved_local_goal: failed after its work (test seam)"
        pure true)
      (fun _ => pure false)
  Tools.VedMemLoop.dbgLog s!"local_goal: after state {r} hb(k)={((← IO.getNumHeartbeats) - hb0) / 1000}"
  -- the separate attempt of `ved.mem.s94MulShift` (own limit), on the restored state
  let r ← if r || !ved.mem.s94MulShift.get (← getOptions) then pure r else do
    st.restore
    let hb3 ← IO.getNumHeartbeats
    tryCatchRuntimeEx
      (do
        withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then mulCapK * 1000 else min c.maxHeartbeats (mulCapK * 1000)), initHeartbeats := hb3 }) do
          withoutRecover (evalTactic (← `(tactic| ved_local_close_mulshift)))
        if ← mulShiftFailLate.get then throwError "ved_local_goal: failed after its work (test seam)"
        pure true)
      (fun _ => pure false)
  Tools.VedMemLoop.dbgLog s!"local_goal: after mulshift {r} hb(k)={((← IO.getNumHeartbeats) - hb0) / 1000}"
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

/-- most bits of BitVec variables one leaf of `ved_bv_enum` enumerates (2^bits cases of `decide +kernel`) -/
def bvEnumMaxBits : Nat := 12
/-- most leaves the `if` split of `ved_bv_enum` produces -/
def bvEnumMaxLeaves : Nat := 64

/-- test counters of `ved_bv_enum`: leaves closed, enumerated bits (total) -/
initialize bvEnumLeaves : IO.Ref Nat ← IO.mkRef 0
initialize bvEnumBits : IO.Ref Nat ← IO.mkRef 0

/-- the width of a `BitVec w` type with a literal `w`; a `Bool` has 1 -/
def bvVarBits (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnfR (← instantiateMVars ty)
  if ty.isConstOf ``Bool then return some 1
  if ty.isAppOfArity ``BitVec 1 then
    let w ← instantiateMVars ty.appArg!
    return (← Meta.evalNat w).map id
  return none

/-- `ved_bv_enum_leaf`: the main goal is a proposition over BitVec / Bool variables only (no other variable in the goal): revert those variables and the context propositions
over them, and close the finite statement by `decide +kernel` (kernel evaluation, no `ofReduceBool`). Fails when a variable of another type occurs or the bits exceed `bvEnumMaxBits`. -/
elab "ved_bv_enum_leaf" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let fvs := (collectFVars {} tgt).fvarIds
  let mut vars : Array FVarId := #[]
  let mut bits := 0
  for f in fvs do
    let d ← f.getDecl
    match ← bvVarBits d.type with
    | some b => vars := vars.push f; bits := bits + b
    | none => throwError "ved_bv_enum_leaf: variable {d.userName} of a type that cannot be enumerated"
  if bits > bvEnumMaxBits then throwError "ved_bv_enum_leaf: {bits} bits to enumerate (limit {bvEnumMaxBits})"
  -- context propositions whose variables are all among `vars`
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet || vars.contains d.fvarId then continue
    let t ← instantiateMVars d.type
    unless (← isProp t) do continue
    let fs := (collectFVars {} t).fvarIds
    if !fs.isEmpty && fs.all (vars.contains ·) then hs := hs.push d.fvarId
  let (_, g1) ← g.revert (vars ++ hs) (preserveOrder := true)
  replaceMainGoal [g1]
  evalTactic (← `(tactic| decide +kernel))
  bvEnumLeaves.modify (· + 1)
  bvEnumBits.modify (· + bits)

/-- `ved_bv_enum`: split the `if`s of the main goal (at most `bvEnumMaxLeaves` leaves), then `ved_bv_enum_leaf` on every leaf -/
macro "ved_bv_enum" : tactic =>
  `(tactic| ((repeat' split); all_goals ved_bv_enum_leaf))

/-- the heartbeat budget (thousands) of one `ved_addr_eq_bv` attempt: it runs first in the chain of the address equality (which has ONE budget, `addrEqBudgetK`), so a failing attempt must not
use up what the old closers behind it need (observed R033 goal 40: the old closers close the pair in ~9M of the 12M, the new one failed after ~4M and the pair stayed open) -/
def bvAddrBudgetK : Nat := 4000

/-- the BitVec-level closer of an address equality (option `ved.mem.s94Addr`): `toNat` form, field extraction, then `ved_bv_enum`; fails at once when the option is off -/
elab "ved_addr_eq_bv" : tactic => do
  unless ved.mem.s94Addr.get (← getOptions) do throwError "ved_addr_eq_bv: option ved.mem.s94Addr is off"
  let st ← saveState
  let hb0 ← IO.getNumHeartbeats
  let r ← tryCatchRuntimeEx
    (do
      withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then bvAddrBudgetK * 1000 else min c.maxHeartbeats (bvAddrBudgetK * 1000)), initHeartbeats := hb0 }) do
        evalTactic (← `(tactic| apply BitVec.eq_of_toNat_eq))
        evalTactic (← `(tactic| simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, apply_ite BitVec.toNat, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub,
                       BitVec.toNat_append, Nat.zero_shiftLeft, Nat.zero_or, Nat.reduceMod, Nat.reducePow, Nat.shiftRight_eq_div_pow]))
        evalTactic (← `(tactic| (ved_cone_clear; (try ved_pack_extract); ved_local_small; (try dsimp only at *); (try simp only [ite10_mod2] at *); ved_bv_enum)))
      pure none)
    (fun ex => pure (some ex))
  if let some ex := r then
    st.restore
    throwError "ved_addr_eq_bv: failed or over its budget ({(← ex.toMessageData.toString).take 120})"

/-- the heartbeat budget (thousands) of one argument comparison of `memCanon` (observed: the comparisons that finish need < 1M) -/
def memCanonBudgetK : Nat := 500
/-- the heartbeat budget (thousands) of all argument comparisons of one `memCanon` call -/
def memCanonTotalK : Nat := 6000
/-- the size of a target (tree nodes) from which `ved_mem_addr_l` replaces the address by `Expr.replace` and does not try `rw` (the `rw` of such a tree is a walk that cannot be interrupted) -/
def rwMaxTree : Nat := 10000000
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
            -- s94u (option `ved.mem.s94Addr`): the old chain is unchanged and first (observed R033 goal 40, 41: a new closer in front of it changed what the old one proves, 7 / 18: the representative);
            -- only when it did not close the pair the BitVec-level closer `ved_addr_eq_bv` runs, under its OWN budget (`bvAddrBudgetK`), and closes it or the pair stays open as before
            let useBv := ved.mem.s94Addr.get (← getOptions)
            let hbP ← IO.getNumHeartbeats
            let oldChain : TacticM Unit :=
              tryCatchRuntimeEx
                (withTheReader Core.Context (fun c => { c with maxHeartbeats := (if c.maxHeartbeats == 0 then addrEqBudgetK * 1000 else min c.maxHeartbeats (addrEqBudgetK * 1000)), initHeartbeats := hbP }) do
                  evalTactic (← `(tactic| (have hmaddr : $aS = $repS := by
                                             first | rfl | ved_addr_eq_local | ved_addr_eq_local2))))
                (fun ex => do
                  stP.restore
                  addrEqTimeouts.modify (· + 1)
                  throwError "address equality: budget exhausted ({← ex.toMessageData.toString})")
            let dbgA := (← IO.getEnv "VED_ADDRDBG").isSome
            if useBv then
              try
                oldChain
                if dbgA then IO.eprintln s!"ADDRDBG old chain closed the pair ({((← IO.getNumHeartbeats) - hbP) / 1000}k)"
              catch ex =>
                if dbgA then IO.eprintln s!"ADDRDBG old chain failed ({((← IO.getNumHeartbeats) - hbP) / 1000}k): {(← ex.toMessageData.toString).take 200}"
                stP.restore
                try evalTactic (← `(tactic| (have hmaddr : $aS = $repS := by ved_addr_eq_bv)))
                catch ex => stP.restore; throw ex
            else oldChain
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
            -- s94t: the `rw` of a goal of >= `rwMaxTree` nodes is not entered: `kabstract` walks the tree without polling the heartbeat limit (observed t3c goals 53 103: the
            -- 12M budget of the `rw` below was exceeded by 24M hb before the timeout fired, then the whole step hit its 30M limit), the `Expr.replace` route takes it directly
            let viaRw := small && Tools.VedU1Loop.treeSizeVal tgt < rwMaxTree
            let hm? ← if viaRw then pure none else hmFind
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
              Tools.VedMemLoop.dbgT "addr: replace route done"
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
                Tools.VedMemLoop.dbgT "addr: rw budget exhausted, Expr.replace route"
                match ← hmFind with
                | some hm => replaceRoute hm; Tools.VedMemLoop.dbgT "addr: replace route done"
                | none => throwError "address rewrite: budget exhausted and no equation"
            -- the `rw` closes the goal by `rfl` when the two atoms were all there was (small cases; never on the R033 goals)
            if (← getGoals).isEmpty then return
            progress := true
            Tools.VedMemLoop.dbgT "addr: rewrite ok"
          catch e => Tools.VedMemLoop.dbgT "addr: equality failed"; Tools.VedMemLoop.dbgLog s!"no equality for {← ppExpr a}: {← e.toMessageData.toString}"
      if !progress then break

end Tools.VedMemS94Local
