import Lean
import Std.Data.HashMap
import Tools.VedMemLoop

/-!
# Field reads of the packed state, once per distinct read (`sparkle-ved-memory-rows`)

The module packs the registers of a loop into one wire (`a * 2^k + b`) and every use of a register reads the field back
(`P / 2^k % 2^w`).  The goal of a step is a small DAG (hundreds of nodes: each distinct read occurs once) but a large
TREE (a read inside the chain of wires is repeated at every use), and the tactics that follow (`ved_wire`, `ved_pack_simp`, `omega`)
cost per tree node.  `ved_pack_dag` rewrites each distinct maximal read to the field it reads, once, over the DAG:

* `eval` reads a `Nat` expression built from `+`, `* 2^k`, `% 2^k`, `/ 2^k`, literals and atoms `t % 2^w` as a bit-field value
  `c + Σ atom_i * 2^lo_i` (disjoint ranges);
* a maximal `%` / `/` node whose value is such a sum is replaced by the sum (the field `t % 2^w` for a slice of one field);
* every replacement is justified by the closed equation `∀ vars, S = F`, proved by `ved_pack_simp` (a goal of tens of nodes with no
  hypotheses), cached by its closed statement across goals, and applied with `congrArg` over the DAG.

Untrusted: a failed equation leaves the read as it was; the kernel checks the rewrites.
-/

namespace Tools.VedMemPack

open Lean Meta Elab Tactic

/-- a field of a bit-field value: the atom `t % 2^w` sits at bit `lo` -/
structure Fld where
  lo : Nat
  w : Nat
  atom : Lean.Expr

/-- `c + Σ fs[i].atom * 2^lo_i`, the ranges (and the bits of `c`) pairwise disjoint -/
structure BV where
  c : Nat
  fs : Array Fld

def pow2? (m : Nat) : Option Nat := if m > 0 && 2 ^ m.log2 == m then some m.log2 else none

/-- a numeral, or a power / sum / product of numerals -/
partial def natLit? (e : Lean.Expr) : MetaM (Option Nat) := do
  if let some n := e.nat? then return some n
  if e.isRawNatLit then return e.rawNatLit?
  if e.isAppOfArity ``HPow.hPow 6 || e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HMul.hMul 6 then
    let some a ← natLit? (e.getArg! 4) | return none
    let some b ← natLit? (e.getArg! 5) | return none
    if e.isAppOfArity ``HPow.hPow 6 then return (if b ≤ 4096 then some (a ^ b) else none)
    if e.isAppOfArity ``HAdd.hAdd 6 then return some (a + b)
    return some (a * b)
  return none

def isNatOp (e : Lean.Expr) (op : Name) : Bool := e.isAppOfArity op 6 && (e.getArg! 0).isConstOf ``Nat

def disjointBV (a b : BV) : Bool :=
  (a.fs.all fun f => b.fs.all fun g => f.lo + f.w ≤ g.lo || g.lo + g.w ≤ f.lo)
  && (a.c &&& b.c) == 0
  && ((a.fs ++ b.fs).all fun f => ((a.c ||| b.c) >>> f.lo) % 2 ^ f.w == 0)

abbrev EvalM := StateRefT (Std.HashMap Lean.Expr (Option BV)) MetaM

partial def eval (e : Lean.Expr) : EvalM (Option BV) := do
  if let some r := (← get)[e]? then return r
  let r ← go e
  modify (·.insert e r)
  return r
where
  go (e : Lean.Expr) : EvalM (Option BV) := do
    if let some n := e.nat? then return some ⟨n, #[]⟩
    if e.isRawNatLit then return e.rawNatLit?.map fun n => ⟨n, #[]⟩
    if isNatOp e ``HAdd.hAdd then
      let some a ← eval (e.getArg! 4) | return none
      let some b ← eval (e.getArg! 5) | return none
      unless disjointBV a b do return none
      return some ⟨a.c + b.c, a.fs ++ b.fs⟩
    if isNatOp e ``HMul.hMul then
      let shift := fun (a : BV) (k : Nat) => some (⟨a.c <<< k, a.fs.map fun f => { f with lo := f.lo + k }⟩ : BV)
      if let some m ← natLit? (e.getArg! 5) then
        let some k := pow2? m | return none
        let some a ← eval (e.getArg! 4) | return none
        return shift a k
      if let some m ← natLit? (e.getArg! 4) then
        let some k := pow2? m | return none
        let some a ← eval (e.getArg! 5) | return none
        return shift a k
      return none
    if isNatOp e ``HMod.hMod then
      let some m ← natLit? (e.getArg! 5) | return none
      let some k := pow2? m | return none
      match ← eval (e.getArg! 4) with
      | none => return some ⟨0, #[⟨0, k, e⟩]⟩
      | some a =>
        let mut fs : Array Fld := #[]
        for f in a.fs do
          if f.lo + f.w ≤ k then fs := fs.push f
          else if f.lo < k then return none
        return some ⟨a.c % 2 ^ k, fs⟩
    if isNatOp e ``HDiv.hDiv then
      let some m ← natLit? (e.getArg! 5) | return none
      let some k := pow2? m | return none
      let some a ← eval (e.getArg! 4) | return none
      let mut fs : Array Fld := #[]
      for f in a.fs do
        if k ≤ f.lo then fs := fs.push { f with lo := f.lo - k }
        else if f.lo + f.w > k then return none
      return some ⟨a.c / 2 ^ k, fs⟩
    return none

/-- the expression of a value -/
def BV.toExpr (a : BV) : Lean.Expr := Id.run do
  let mut r : Option Lean.Expr := none
  for f in a.fs do
    let t := if f.lo == 0 then f.atom else mkNatMul f.atom (mkNatLit (2 ^ f.lo))
    r := some (match r with | none => t | some x => mkNatAdd x t)
  match r with
  | none => return mkNatLit a.c
  | some x => return if a.c == 0 then x else mkNatAdd x (mkNatLit a.c)

/-- the maximal reads (`/`, `%` nodes by `2^k` whose operand is a bit-field value) below `e`, each distinct node once, with the field value;
a read that is already an atom or does not get smaller is not a candidate -/
partial def collect (e : Lean.Expr) : EvalM (Array (Lean.Expr × Lean.Expr)) := do
  let seen ← IO.mkRef (∅ : Std.HashSet Lean.Expr)
  let out ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  let rec go (x : Lean.Expr) : EvalM Unit := do
    if (← seen.get).contains x then return
    seen.modify (·.insert x)
    if isNatOp x ``HMod.hMod || isNatOp x ``HDiv.hDiv then
      if (← eval (x.getArg! 4)).isSome then
        if let some v ← eval x then
          let f := v.toExpr
          if (Tools.VedU1Loop.treeSizeVal f) < (Tools.VedU1Loop.treeSizeVal x) then
            out.modify (·.push (x, f))
            return
    match x with
    | .app f a => go f; go a
    | .lam _ t b _ => go t; go b
    | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  out.get

initialize bigShown : IO.Ref Nat ← IO.mkRef 0

initialize proofCache : IO.Ref (Std.HashMap Lean.Expr (Option Lean.Expr)) ← IO.mkRef {}

/-- the fvars of `e` and of their types, in the order of the local context -/
def closure (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let lctx ← getLCtx
  let mut ids : Std.HashSet FVarId := {}
  let mut todo : Array FVarId := (collectFVars {} e).fvarIds
  while !todo.isEmpty do
    let i := todo.back!
    todo := todo.pop
    if ids.contains i then continue
    ids := ids.insert i
    if let some d := lctx.find? i then
      for j in (collectFVars {} (← instantiateMVars d.type)).fvarIds do todo := todo.push j
  let mut r : Array Lean.Expr := #[]
  for d in lctx do
    if ids.contains d.fvarId then r := r.push (.fvar d.fvarId)
  return r

/-- the proof of `S = F` as a closed statement over its free variables (cached by the closed statement); `none` when `ved_pack_simp` fails -/
def proveRead (S F : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let eq ← mkEq S F
  let fvs ← closure eq
  let closed ← mkForallFVars fvs eq
  if let some r := (← proofCache.get)[closed]? then
    return r.map fun p => mkAppN p fvs
  let m ← withLCtx {} #[] (mkFreshExprMVar closed)
  let saved ← getGoals
  setGoals [m.mvarId!]
  let ok ← try
      evalTactic (← `(tactic| (intros; first | (ved_pack_simp; done) | omega)))
      pure ((← getGoals).isEmpty)
    catch _ => pure false
  setGoals saved
  let r ← if ok then pure (some (← instantiateMVars m)) else pure none
  proofCache.modify (·.insert closed r)
  return r.map fun p => mkAppN p fvs

/-- a goal with fewer tree nodes than this is left to the packing step of the loop script (the rewriting below is for goals whose tree is
what the later tactics pay for; a small goal gains nothing) -/
def minTree : Nat := 20000

/-- the goal went through `ved_pack_dag_wire_all`'s rewriting (it carries the tag `ved_dag`) -/
def isDagged (g : MVarId) : MetaM Bool := do
  return ((← g.getTag).toString.splitOn "ved_dag").length > 1

/-- the goal (target, hypotheses without signals) still has a read `ved_pack_dag` would rewrite -/
def hasReads : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let (r, _) ← (do
      if !(← collect tgt).isEmpty then return true
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          let ty ← instantiateMVars d.type
          if (ty.find? fun e => e.isConst && e.constName!.getPrefix == `Sparkle.Core.Signal.Signal).isNone then
            if !(← collect ty).isEmpty then return true
      return false : EvalM Bool).run {}
  return r

/-- `ved_pack_dag`: see the module comment -/
elab "ved_pack_dag" : tactic => withMainContext do
  let h0 ← IO.getNumHeartbeats
  let t0 ← IO.monoMsNow
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let sz0 := Tools.VedU1Loop.treeSizeVal tgt
  let mut nCands := 0
  let mut nProved := 0
  let mut failed := 0
  let mut rounds := 0
  -- the atoms of a replacement field (`t % 2^w`, `t` any expression) hold reads of their own: collect again until none is left
  for _ in [0:12] do
    let g ← getMainGoal
    let tgt ← instantiateMVars (← g.getType)
    let (cands, _) ← (do
        let mut cs : Array (Lean.Expr × Lean.Expr) := #[]
        for (x, f) in ← collect tgt do
          unless cs.any (·.1 == x) do cs := cs.push (x, f)
        for d in ← getLCtx do
          unless d.isImplementationDetail do
            let ty ← instantiateMVars d.type
            if (ty.find? fun e => e.isConst && e.constName!.getPrefix == `Sparkle.Core.Signal.Signal).isNone then
              for (x, f) in ← collect ty do
                unless cs.any (·.1 == x) do cs := cs.push (x, f)
        return cs : EvalM _).run {}
    if cands.isEmpty then break
    nCands := nCands + cands.size
    let mut proved : Array (Lean.Expr × Lean.Expr × Lean.Expr) := #[]
    for (x, f) in cands do
      match ← proveRead x f with
      | some pf => proved := proved.push (x, f, pf)
      | none => failed := failed + 1
    if proved.isEmpty then break
    nProved := nProved + proved.size
    rounds := rounds + 1
    -- the target, then each hypothesis that has a read
    for (x, f, pf) in proved do
      let g ← getMainGoal
      let tgt ← instantiateMVars (← g.getType)
      if (tgt.find? (· == x)).isSome then
        let ty ← inferType x
        let motive ← withLocalDeclD `ved_x ty fun xv =>
          mkLambdaFVars #[xv] (tgt.replace fun e => if e == x then some xv else none)
        let new := tgt.replace fun e => if e == x then some f else none
        replaceMainGoal [← g.replaceTargetEq new (← mkCongrArg motive pf)]
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          let ty ← instantiateMVars d.type
          if (ty.find? (· == x)).isSome then
            let xty ← inferType x
            let motive ← withLocalDeclD `ved_x xty fun xv =>
              mkLambdaFVars #[xv] (ty.replace fun e => if e == x then some xv else none)
            let new := ty.replace fun e => if e == x then some f else none
            let g ← getMainGoal
            let r ← g.replaceLocalDecl d.fvarId new (← mkCongrArg motive pf)
            replaceMainGoal [r.mvarId]
  if (← IO.getEnv "VED_DUMP_DIR").isSome then
    let g ← getMainGoal
    let sz1 := Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType))
    if sz1 > 100000 && (← IO.getEnv "VED_DUMP_BIG").isSome then
      let n ← bigShown.modifyGet fun n => (n, n + 1)
      if n < 1 then
        let tg ← instantiateMVars (← g.getType)
        let t ← withOptions (fun o => (o.insert `format.width (200 : Nat)).setBool `pp.deepTerms true |>.insert `pp.maxSteps (10000000 : Nat)) do
          return toString (← ppExpr tg)
        let dag := (Tools.VedU1WireShare.collectDag (fun _ => true) tg).size
        Tools.VedMemLoop.dbgLog s!"BIG target dag={dag} chars={t.length}"
    Tools.VedMemLoop.dbgLog s!"pack_dag: rounds={rounds} cands={nCands} proved={nProved} failed={failed} tree {sz0} -> {sz1} ms={(← IO.monoMsNow) - t0} hb={((← IO.getNumHeartbeats) - h0) / 1000}"

/-- stage 5 of the memory script: `ved_pack_dag` on every goal, then `ved_pack_wire` (the packing step of the loop script, `ved_wire`
on goals of 150000 nodes) only on a goal that still has a read of the packed state (the packing step on a goal without one is a
traversal of the whole tree that changes nothing) -/
elab "ved_pack_dag_wire_all" : tactic => do
  let gs ← getGoals
  let mut rest : List MVarId := []
  let mut skipped := 0
  let dump := (← IO.getEnv "VED_DUMP_DIR").isSome
  let mut allSz : Array Nat := #[]
  for g in gs do
    setGoals [g]
    let sz ← g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType))
    if sz < minTree then
      -- a goal of ordinary size: the packing step as before
      evalTactic (← `(tactic| ved_pack_wire))
      rest := rest ++ (← getGoals)
      continue
    evalTactic (← `(tactic| try ved_pack_dag))
    if (← getGoals).isEmpty then continue
    let g := (← getGoals).head!
    g.setTag (Name.str (← g.getTag) "ved_dag")
    if dump then
      allSz := allSz.push (← g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType)))
    if (← try hasReads catch _ => pure true) then
      let h0 ← IO.getNumHeartbeats
      evalTactic (← `(tactic| ved_pack_wire))
      if dump then Tools.VedMemLoop.dbgLog s!"pack_wire (reads left): hb={((← IO.getNumHeartbeats) - h0) / 1000}"
    else skipped := skipped + 1
    rest := rest ++ (← getGoals)
  if dump then Tools.VedMemLoop.dbgLog s!"pack_dag_wire_all: goals={gs.length} skipped_wire={skipped} sizes after dag {allSz}"
  setGoals rest

/-- `ved_pack_simp` on a goal that still has a read of the packed state (after `ved_pack_dag` it is a traversal that changes nothing) -/
elab "ved_pack_simp_g" : tactic => do
  unless ← isDagged (← getMainGoal) do
    evalTactic (← `(tactic| ved_pack_simp))
    return
  if ← hasReads then
    if (← IO.getEnv "VED_DUMP_DIR").isSome then
      let g ← getMainGoal
      let msg ← g.withContext do
        let (r, _) ← (do
            let mut out := ""
            let tgt ← instantiateMVars (← g.getType)
            for (x, f) in ← collect tgt do
              out := out ++ s!"TARGET {(← ppExpr x).pretty.take 300 |>.replace "\n" " "} => {(← ppExpr f).pretty.take 100 |>.replace "\n" " "}\n"
            for d in ← getLCtx do
              unless d.isImplementationDetail do
                let ty ← instantiateMVars d.type
                if (ty.find? fun e => e.isConst && e.constName!.getPrefix == `Sparkle.Core.Signal.Signal).isNone then
                  for (x, f) in ← collect ty do
                    out := out ++ s!"HYP {d.userName} {(← ppExpr x).pretty.take 300 |>.replace "\n" " "} => {(← ppExpr f).pretty.take 100 |>.replace "\n" " "}\n"
            return out : EvalM _).run {}
        pure r
      Tools.VedMemLoop.dbgLog s!"pack_simp_g runs: {msg.take 1500}"
    evalTactic (← `(tactic| ved_pack_simp))

/-- `all_goals t` with a stage-log line per goal (size, ms, heartbeats; only with `VED_DUMP_DIR`) -/
elab "ved_all_goals_log " "(" t:tactic ")" : tactic => do
  let gs ← getGoals
  let dump := (← IO.getEnv "VED_DUMP_DIR").isSome
  let mut rest : List MVarId := []
  let mut i := 0
  for g in gs do
    setGoals [g]
    let sz ← if dump then g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType)) else pure 0
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoMsNow
    try evalTactic t
    catch e =>
      if dump then Tools.VedMemLoop.dbgLog s!"close goal {i}: size={sz} FAILED ms={(← IO.monoMsNow) - t0} hb={((← IO.getNumHeartbeats) - h0) / 1000}"
      throw e
    if dump then Tools.VedMemLoop.dbgLog s!"close goal {i}: size={sz} ms={(← IO.monoMsNow) - t0} hb={((← IO.getNumHeartbeats) - h0) / 1000} left={(← getGoals).length}"
    i := i + 1
    rest := rest ++ (← getGoals)
  setGoals rest

/-- `ved_bit_simp` on a goal that went through `ved_pack_dag` (the 0/1 `&&&` / `|||` of the wires need the field variables) -/
elab "ved_bit_simp_g" : tactic => do
  if ← isDagged (← getMainGoal) then evalTactic (← `(tactic| ved_bit_simp))

/-- fails unless the main goal went through `ved_pack_dag_wire_all`'s rewriting -/
elab "ved_dag_only" : tactic => do
  unless ← isDagged (← getMainGoal) do throwError "ved_dag_only: not a goal of the rewriting"

/-! ## Stage 7: goals that are small functions of a few small variables

The closing tactic `(repeat' split) <;> omega` splits every `if` (2^k cases) although the goal is a tiny function of a few bounded variables.
`ved_decide_small2` closes such a goal by one kernel evaluation: the distinct atoms (`BitVec.toNat v` for a variable `v`, and `ins s "name"`
with a bound `ins s "name" < n` in a hypothesis) are generalised to bounded `Nat` variables and `decide +kernel` decides the
`∀ a < n, ..` statement.  The syntactic test (every free variable of the goal under an atom, at most 16384 cases) is a traversal of the DAG;
a goal with a wide data field fails the test and keeps the old closer. -/

/-- the bound `n` of a hypothesis `.. ∧ atom < n ∧ ..` -/
partial def boundOf? (atom : Lean.Expr) (t : Lean.Expr) : Option Nat :=
  if t.isAppOfArity ``And 2 then
    (boundOf? atom (t.getArg! 0)).orElse fun _ => boundOf? atom (t.getArg! 1)
  else if t.isAppOfArity ``LT.lt 4 && t.getArg! 2 == atom then (t.getArg! 3).nat?
  else none

def decideSmall2Core : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let isAtom := fun (e : Lean.Expr) =>
    (e.isAppOfArity ``BitVec.toNat 2 && (e.getArg! 1).isFVar)
    || (e.isApp && e.getAppNumArgs == 2 && e.getAppFn.isFVar && (e.getArg! 0).isFVar
        && ((e.getArg! 1).isLit || (e.getArg! 1).isAppOf ``String.mk || (e.getArg! 1).isAppOf ``OfNat.ofNat))
  let mut atoms : Array Lean.Expr := #[]
  for o in Tools.VedU1WireShare.collectDag isAtom tgt do
    unless atoms.contains o do atoms := atoms.push o
  if atoms.isEmpty then throwError "ved_decide_small2: no atom"
  let rest := atoms.foldl (fun (t : Lean.Expr) a => t.replace fun e => if e == a then some (mkNatLit 0) else none) tgt
  if rest.hasFVar then throwError "ved_decide_small2: other variables"
  let mut cases : Nat := 1
  let mut bounds : Array Nat := #[]
  for a in atoms do
    let some n ← (do
        if a.isAppOfArity ``BitVec.toNat 2 then
          let ty ← whnf (← inferType (a.getArg! 1))
          return (ty.getArg! 0).nat?.map (2 ^ ·)
        let mut r : Option Nat := none
        for d in ← getLCtx do
          unless d.isImplementationDetail || r.isSome do
            r := boundOf? a (← instantiateMVars d.type)
        return r) | throwError "ved_decide_small2: no bound"
    cases := cases * n
    bounds := bounds.push n
    if cases > 16384 then throwError "ved_decide_small2: too many cases"
  let mut names : Array (TSyntax `ident) := #[]
  let mut k := 0
  for a in atoms do
    let nm := mkIdent (Name.mkSimple s!"ved_ds_a{k}")
    let bn := mkIdent (Name.mkSimple s!"ved_ds_b{k}")
    let aS ← Term.exprToSyntax a
    let hk := mkIdent (Name.mkSimple s!"ved_ds_h{k}")
    let nS := Syntax.mkNumLit (toString bounds[k]!)
    if a.isAppOfArity ``BitVec.toNat 2 then
      let vS ← Term.exprToSyntax (a.getArg! 1)
      evalTactic (← `(tactic| generalize $hk:ident : $aS = $nm))
      evalTactic (← `(tactic| have $bn : $nm < $nS := by rw [← $hk:ident]; exact BitVec.isLt $vS))
      evalTactic (← `(tactic| clear $hk:ident))
    else
      evalTactic (← `(tactic| have $bn : $aS < $nS := by omega))
      evalTactic (← `(tactic| generalize $hk:ident : $aS = $nm at $bn:ident ⊢))
      evalTactic (← `(tactic| clear $hk:ident))
    names := names.push nm
    k := k + 1
  for nm in names.reverse do
    evalTactic (← `(tactic| revert $nm))
  evalTactic (← `(tactic| decide +kernel))

elab "ved_decide_small2" : tactic => do
  let dump := (← IO.getEnv "VED_DUMP_DIR").isSome
  try decideSmall2Core
  catch e =>
    if dump then Tools.VedMemLoop.dbgLog s!"decide_small2: {← e.toMessageData.toString}"
    throw e

/-! ## Stage 7: control fields by case analysis, the data part by `omega`

A goal over small control fields (`BitVec.toNat v` of at most 4 bits, `ins s "name"` with a bound of at most 16) and wide data fields
(16-bit additions under the `if`s on the control fields) is closed by `ved_ctrl_cases`: the control atoms are generalised to bounded
`Nat` variables, split one at a time into all their values (`ved_cases_lt`, one new goal per value, in the same context), and each case
is simplified with literal arithmetic (the `if`s on the control fields reduce), skipping a variable that no longer occurs.  What is left
is a data goal for `omega`, proved once per distinct residual statement (the cases share them).  The cost is that of the control tuples
(not of the tree).  Fails when there is no control atom or the cases exceed 4096. -/

theorem ved_cases_lt {P : Nat → Prop} {n v : Nat} (h : v < n) (hs : ∀ i, i < n → P i) : P v := hs v h
theorem ved_ball_zero {P : Nat → Prop} : ∀ i, i < 0 → P i := fun i h => absurd h (Nat.not_lt_zero i)
theorem ved_ball_succ {P : Nat → Prop} {n : Nat} (h : ∀ i, i < n → P i) (hn : P n) : ∀ i, i < n + 1 → P i :=
  fun i hi => if e : i = n then e ▸ hn else h i (by omega)

structure CtrlSimp where
  ctx : Simp.Context
  sp : Simp.SimprocsArray

def mkCtrlSimp : TacticM CtrlSimp := do
  let stx ← `(tactic| simp (config := {decide := true}) only [Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub, Nat.reduceDiv, and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or, not_true_eq_false, not_false_eq_true, true_implies, false_implies, implies_true, if_true, if_false])
  let r ← mkSimpContext stx false
  return ⟨r.ctx, r.simprocs⟩

partial def ctrlCases (sc : CtrlSimp) (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr)) (vars : List (Name × Name × Nat)) : TacticM Unit := do
  match vars with
  | [] =>
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    if let some pf := (← cache.get).get? ty then
      g.assign pf
      setGoals []
    else
      evalTactic (← `(tactic| omega))
      cache.modify fun m => m.insert ty (Lean.Expr.mvar g)
  | (vn, bn, n) :: rest =>
    let g ← getMainGoal
    let lctx ← g.withContext getLCtx
    let (some ld, some hv) := (lctx.findFromUserName? vn, lctx.findFromUserName? bn) | ctrlCases sc cache rest
    let v := ld.fvarId
    let tgt ← instantiateMVars (← g.getType)
    if !(tgt.containsFVar v) then ctrlCases sc cache rest
    else
      let abs := tgt.abstract #[mkFVar v]
      let motive := Lean.Expr.lam `v (mkConst ``Nat) abs .default
      let mut mvs : Array MVarId := #[]
      let mut chain := mkApp (mkConst ``ved_ball_zero) motive
      for i in [0:n] do
        let m ← g.withContext <| mkFreshExprSyntheticOpaqueMVar (abs.instantiate1 (mkNatLit i))
        mvs := mvs.push m.mvarId!
        chain := mkApp4 (mkConst ``ved_ball_succ) motive (mkNatLit i) chain m
      g.assign (mkApp5 (mkConst ``ved_cases_lt) motive (mkNatLit n) (mkFVar v) hv.toExpr chain)
      let mut done : List MVarId := []
      for g in mvs do
        setGoals [g]
        let (r, _) ← simpGoal g sc.ctx sc.sp
        match r with
        | none => setGoals []
        | some (_, g') => setGoals [g']
        unless (← getGoals).isEmpty do ctrlCases sc cache rest
        done := done ++ (← getGoals)
      setGoals done

def ctrlCasesCore : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let isAtom := fun (e : Lean.Expr) =>
    (e.isAppOfArity ``BitVec.toNat 2 && (e.getArg! 1).isFVar)
    || (e.isApp && e.getAppNumArgs == 2 && e.getAppFn.isFVar && (e.getArg! 0).isFVar
        && ((e.getArg! 1).isLit || (e.getArg! 1).isAppOf ``String.mk || (e.getArg! 1).isAppOf ``OfNat.ofNat))
  let mut atoms : Array Lean.Expr := #[]
  for o in Tools.VedU1WireShare.collectDag isAtom tgt do
    unless atoms.contains o do atoms := atoms.push o
  let mut ctl : Array (Lean.Expr × Nat) := #[]
  let mut cases := 1
  for a in atoms do
    let b? ← (do
        if a.isAppOfArity ``BitVec.toNat 2 then
          let ty ← whnf (← inferType (a.getArg! 1))
          return (ty.getArg! 0).nat?.map (2 ^ ·)
        let mut r : Option Nat := none
        for d in ← getLCtx do
          unless d.isImplementationDetail || r.isSome do
            r := boundOf? a (← instantiateMVars d.type)
        return r)
    if let some n := b? then
      if n ≤ 16 then
        ctl := ctl.push (a, n)
        cases := cases * n
  if ctl.isEmpty then throwError "ved_ctrl_cases: no control atom"
  if cases > 4096 then throwError "ved_ctrl_cases: too many cases"
  let mut vars : List (Name × Name × Nat) := []
  let mut k := 0
  for (a, n) in ctl do
    let nm := mkIdent (Name.mkSimple s!"ved_cv{k}")
    let bn := mkIdent (Name.mkSimple s!"ved_cb{k}")
    let hk := mkIdent (Name.mkSimple s!"ved_ch{k}")
    let aS ← Term.exprToSyntax a
    let nS := Syntax.mkNumLit (toString n)
    if a.isAppOfArity ``BitVec.toNat 2 then
      evalTactic (← `(tactic| generalize $hk:ident : $aS = $nm))
      evalTactic (← `(tactic| have $bn : $nm < $nS := by rw [← $hk:ident]; exact BitVec.isLt _))
      evalTactic (← `(tactic| clear $hk:ident))
    else
      evalTactic (← `(tactic| have $bn : $aS < $nS := by omega))
      evalTactic (← `(tactic| generalize $hk:ident : $aS = $nm at $bn:ident ⊢))
      evalTactic (← `(tactic| clear $hk:ident))
    vars := vars ++ [(Name.mkSimple s!"ved_cv{k}", Name.mkSimple s!"ved_cb{k}", n)]
    k := k + 1
  let sc ← mkCtrlSimp
  let cache ← IO.mkRef {}
  ctrlCases sc cache vars

elab "ved_ctrl_cases" : tactic => do
  let dump := (← IO.getEnv "VED_DUMP_DIR").isSome
  try ctrlCasesCore
  catch e =>
    if dump then Tools.VedMemLoop.dbgLog s!"ctrl_cases: {(← e.toMessageData.toString).take 300}"
    throw e

end Tools.VedMemPack
