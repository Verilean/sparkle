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

/-- a numeral, or a power / sum / product of numerals (pure) -/
partial def natLitP? (e : Lean.Expr) : Option Nat :=
  if let some n := e.nat? then some n
  else if e.isRawNatLit then e.rawNatLit?
  else if e.isAppOfArity ``HPow.hPow 6 || e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HMul.hMul 6 then
    -- the right operand only when the left one is a numeral (a non-numeral sum over a shared term of 1e5 tree nodes: the walk of both
    -- operands at every node of `canonNat`'s traversal is a walk of the tree)
    match natLitP? (e.getArg! 4) with
    | none => none
    | some a =>
      match natLitP? (e.getArg! 5) with
      | none => none
      | some b =>
        if e.isAppOfArity ``HPow.hPow 6 then (if b ≤ 4096 then some (a ^ b) else none)
        else if e.isAppOfArity ``HAdd.hAdd 6 then some (a + b) else some (a * b)
  else none

/-- `e` with every numeral expression `2 ^ (1 + 1)` replaced by its value `4` (the spelling-independent key of a read) -/
def canonNat (e : Lean.Expr) : Lean.Expr :=
  e.replace fun x =>
    if x.isAppOfArity ``HPow.hPow 6 || x.isAppOfArity ``HAdd.hAdd 6 || x.isAppOfArity ``HMul.hMul 6 then
      (natLitP? x).map mkNatLit
    else none

/-- `e` with the projections of constructors reduced (`(a, b).fst` to `a`): the same read is spelled with and without them -/
def normProj (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun x => do
    if let .const n _ := x.getAppFn then
      if (← getProjectionFnInfo? n).isSome then
        if let some x' ← unfoldDefinition? x then return .visit (← whnfCore x')
    let x' ← whnfCore x
    return if x' == x then .done x else .visit x')

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

/-- test-only evidence that a tactic ran (`Tests/Ved/VedMemPackCheck.lean` clears and reads it): one entry per success of
`ved_pack_dag` (`pack_dag`, and `pack_dag_class` once per rewritten class of several spellings), `ved_decide_small2`, `ved_ctrl_cases`.
It is read by nothing in the proof path. -/
initialize ranLog : IO.Ref (Array String) ← IO.mkRef #[]

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

/-- `proveRead` tries `omega` after `ved_pack_simp` only on a read with fewer tree nodes than this -/
def omegaMaxTree : Nat := 20000

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
      -- `omega` reads a nested `%` / `/` chain as a tree: on a "read" of 3e4 tree nodes whose field value is itself that large (not a
      -- packed read: R034 goal 54, f-tree 30849 of x-tree 30969) it runs out of memory (23 GB) instead of failing
      if Tools.VedU1Loop.treeSizeVal S < omegaMaxTree then
        evalTactic (← `(tactic| (intros; first | (ved_pack_simp; done) | omega)))
      else
        evalTactic (← `(tactic| (intros; ved_pack_simp; done)))
      pure ((← getGoals).isEmpty)
    catch _ => pure false
  setGoals saved
  let r ← if ok then pure (some (← instantiateMVars m)) else pure none
  proofCache.modify (·.insert closed r)
  return r.map fun p => mkAppN p fvs

/-- a goal with fewer tree nodes than this is left to the packing step of the loop script (the rewriting below is for goals whose tree is
what the later tactics pay for; a small goal gains nothing) -/
def minTree : Nat := 5000

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

/-- the goal is left to stage 5 (`ved_pack_dag`, then `ved_bit_simp_g`): at least `minTree` nodes and a read of the packed state.  `ved_bit_simp`
before the rewriting reads each packed read as a tree of nested `%` / `/` (the discharging `omega`; R34: 64 s and 3.8M heartbeats per goal of
4e4 nodes, then `simp` fails with the step limit and the goal is unchanged); after it the reads are field atoms -/
def deferBits : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let sz := Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType))
  if sz < minTree then return false
  try hasReads catch _ => return false

/-- `ved_bit_simp_share` (stage 2), except on a goal that `deferBits` leaves to stage 5 -/
elab "ved_bit_simp_pre" : tactic => do
  if ← deferBits then
    Tools.VedMemLoop.dbgLog "bit_simp_pre: deferred"
    return
  evalTactic (← `(tactic| ved_bit_simp_share))

/-- `ved_bit_simp_share` on every goal with a log line per goal (tree size, number of bit operations, ms, heartbeats; only with `VED_DUMP_DIR`) -/
elab "ved_bit_simp_share_m" : tactic => do
  let gs ← getGoals
  let mut rest : List MVarId := []
  let mut i := 0
  for g in gs do
    setGoals [g]
    let (sz, nb) ← g.withContext do
      let t ← instantiateMVars (← g.getType)
      return (Tools.VedU1Loop.treeSizeVal t, (Tools.VedU1Loop.natBitOps t).size)
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoMsNow
    evalTactic (← `(tactic| ved_bit_simp_pre))
    Tools.VedMemLoop.dbgLog s!"bit_simp_share goal {i}: size={sz} bitops={nb} ms={(← IO.monoMsNow) - t0} hb={((← IO.getNumHeartbeats) - h0) / 1000}"
    i := i + 1
    rest := rest ++ (← getGoals)
  setGoals rest

/-- `ved_or_lit_m` (stage 3), except on a goal that `ved_wire` takes (at least `shareMinTree` nodes) with a `|||`: the `omega` calls read the
operand of a `|||` as a tree (R34: 12 s per goal of 3e8 nodes, 16 such goals), and `ved_wire` (stage 5) rewrites the `|||` of its wires itself
(`addBitFacts`: `or_hi` as an implication) -/
elab "ved_or_lit_g" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if Tools.VedU1Loop.treeSizeVal tgt ≥ Tools.VedU1Loop.shareMinTree && !(Tools.VedU1Loop.natOrs tgt).isEmpty then
    Tools.VedMemLoop.dbgLog "or_lit_g: left to ved_wire"
    return
  evalTactic (← `(tactic| ved_or_lit_m))

/-- `ved_addr_post` (stage 4) with the bit step of `deferBits`' goals left to stage 5 -/
elab "ved_addr_post_g" : tactic => do
  let g ← getMainGoal
  if (← g.getTag).toString.endsWith "ved_addr" then
    evalTactic (← `(tactic| ved_mem_gen))
  unless ← deferBits do
    evalTactic (← `(tactic| (try ved_bit_simp)))
  evalTactic (← `(tactic| (try ved_hyp_bits)))

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
    Tools.VedMemLoop.dbgLog s!"pack_dag: round collected {cands.size} cands ms={(← IO.monoMsNow) - t0} hb={((← IO.getNumHeartbeats) - h0) / 1000} tree={sz0}"
    if cands.isEmpty then break
    nCands := nCands + cands.size
    let mut proved : Array (Lean.Expr × Lean.Expr × Lean.Expr) := #[]
    for (x, f) in cands do
      let tp0 ← IO.monoMsNow
      Tools.VedMemLoop.dbgLog s!"pack_dag: proveRead BEGIN x-tree={Tools.VedU1Loop.treeSizeVal x} f-tree={Tools.VedU1Loop.treeSizeVal f} x-dag={(Tools.VedU1WireShare.collectDag (fun _ => true) x).size}"
      let r ← proveRead x f
      Tools.VedMemLoop.dbgLog s!"pack_dag: proveRead x-tree={Tools.VedU1Loop.treeSizeVal x} f-tree={Tools.VedU1Loop.treeSizeVal f} ok={r.isSome} ms={(← IO.monoMsNow) - tp0}"
      match r with
      | some pf => proved := proved.push (x, f, pf)
      | none => failed := failed + 1
    if proved.isEmpty then break
    nProved := nProved + proved.size
    rounds := rounds + 1
    -- reads that differ only in the spelling of a numeral (`2 ^ (1 + 1)` / `4`) or in a projection of a constructor are one class:
    -- the `Decidable` instance of an `ite` and its proposition spell the same read differently, and a rewrite of one spelling alone
    -- is not well typed up to cheap defeq (the kernel then decides the defeq of the two by unfolding `Nat.div` / `Nat.mod`: memory and
    -- `deep recursion`); a class is rewritten at all its spellings at once, by the proof of its first member
    let mut classes : Array (Lean.Expr × Lean.Expr × Lean.Expr × Array Lean.Expr) := #[]
    let tc0 ← IO.monoMsNow
    for (x, f, pf) in proved do
      let tn0 ← IO.monoMsNow
      let xn ← normProj x
      let tn1 ← IO.monoMsNow
      let k := canonNat xn
      Tools.VedMemLoop.dbgLog s!"pack_dag: class key x-tree={Tools.VedU1Loop.treeSizeVal x} normProj ms={tn1 - tn0} canonNat ms={(← IO.monoMsNow) - tn1}"
      match classes.findIdx? (fun c => c.1 == k) with
      | some idx => classes := classes.modify idx fun c => (c.1, c.2.1, c.2.2.1, c.2.2.2.push x)
      | none => classes := classes.push (k, f, pf, #[x])
    -- the target, then each hypothesis that has a read
    for (_, f, pf, xs) in classes do
      if xs.size > 1 then ranLog.modify (·.push "pack_dag_class")
      let x0 := xs[0]!
      let isX := fun (e : Lean.Expr) => xs.contains e
      let g ← getMainGoal
      let tr0 ← IO.monoMsNow
      let tgt ← instantiateMVars (← g.getType)
      Tools.VedMemLoop.dbgLog s!"pack_dag: class rewrite start xs={xs.size} x-tree={Tools.VedU1Loop.treeSizeVal x0} f-tree={Tools.VedU1Loop.treeSizeVal f} tgt-tree={Tools.VedU1Loop.treeSizeVal tgt} ms={(← IO.monoMsNow) - tr0}"
      if (tgt.find? isX).isSome then
        Tools.VedMemLoop.dbgLog s!"pack_dag: found in target ms={(← IO.monoMsNow) - tr0}"
        let ty0 ← inferType x0
        let ty ← inferType x0
        let motive ← withLocalDeclD `ved_x ty fun xv =>
          mkLambdaFVars #[xv] (tgt.replace fun e => if isX e then some xv else none)
        let new := tgt.replace fun e => if isX e then some f else none
        Tools.VedMemLoop.dbgLog s!"pack_dag: motive+new built ms={(← IO.monoMsNow) - tr0}"
        let cg ← mkCongrArg motive pf
        Tools.VedMemLoop.dbgLog s!"pack_dag: congrArg ms={(← IO.monoMsNow) - tr0}"
        replaceMainGoal [← g.replaceTargetEq new cg]
        Tools.VedMemLoop.dbgLog s!"pack_dag: replaceTargetEq ms={(← IO.monoMsNow) - tr0}"
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          let ty ← instantiateMVars d.type
          if (ty.find? isX).isSome then
            let xty ← inferType x0
            let motive ← withLocalDeclD `ved_x xty fun xv =>
              mkLambdaFVars #[xv] (ty.replace fun e => if isX e then some xv else none)
            let new := ty.replace fun e => if isX e then some f else none
            let g ← getMainGoal
            Tools.VedMemLoop.dbgLog s!"pack_dag: hyp {d.userName} replace start ms={(← IO.monoMsNow) - tr0}"
            let r ← g.replaceLocalDecl d.fvarId new (← mkCongrArg motive pf)
            replaceMainGoal [r.mvarId]
            Tools.VedMemLoop.dbgLog s!"pack_dag: hyp {d.userName} replace done ms={(← IO.monoMsNow) - tr0}"
  if nProved > 0 then ranLog.modify (·.push "pack_dag")
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

/-- heartbeats (thousands) of the fallback `ved_pack_simp` of `ved_pack_wire_m` on a goal of at least 20000 nodes -/
def packSimpFallbackHb : Nat := 1000

/-- `ved_pack_wire` (`Tools/VedU1Wire.lean`) with a stage-log line per branch (only with `VED_DUMP_DIR`; the same tactics in the same order, but the fallback `ved_pack_simp` after a failed `ved_wire_bits` has a heartbeat budget of its own) -/
elab "ved_pack_wire_m" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let size := Tools.VedU1Loop.treeSizeVal tgt
  let nb := (Tools.VedU1Loop.natBitOps tgt).size
  let t0 ← IO.monoMsNow
  let h0 ← IO.getNumHeartbeats
  let stamp := fun (what : String) => do
    Tools.VedMemLoop.dbgLog s!"pack_wire_m: {what} size={size} bitops={nb} ms={(← IO.monoMsNow) - t0} hb={((← IO.getNumHeartbeats) - h0) / 1000}"
  stamp "begin"
  if size < Tools.VedU1Loop.shareMinTree then
    if size ≥ 20000 && nb ≥ Tools.VedU1Loop.bitsSmallOps then
      -- (`ved_pack_wire` tries `ved_wire_bits` first here.  This goal went through `ved_pack_dag` and still has reads: R034 goals 54-85,
      -- 47899 nodes, 18 bit operations: `ved_wire_bits` fails after 64 s / 0.73M heartbeats on EACH of them, the whole budget; so only
      -- the packing step, with a budget of its own: it does not end on such a goal either (800 s, 40M heartbeats))
      -- local budget never above what is left of the ambient one (`withLocalHb`); a failure restores the state from before
      let s ← saveState
      try
        tryCatchRuntimeEx
          (Tools.VedMemLoop.withLocalHb (packSimpFallbackHb * 1000)
            (Tactic.withoutRecover (evalTactic (← `(tactic| ved_pack_simp)))))
          fun _ => throwError "ved_pack_simp: no result within the budget"
      catch _ => s.restore
      stamp "pack_simp done"
    else
      evalTactic (← `(tactic| try ved_pack_simp))
  else
    evalTactic (← `(tactic| ved_wire))
  stamp "end"

/-- stage 5 of the memory script: `ved_pack_dag` on every goal, then `ved_pack_wire` (the packing step of the loop script, `ved_wire`
on goals of 150000 nodes) only on a goal that still has a read of the packed state (the packing step on a goal without one is a
traversal of the whole tree that changes nothing) -/
elab "ved_pack_dag_wire_all" : tactic => do
  let gs ← getGoals
  let mut rest : List MVarId := []
  let mut skipped := 0
  let dump := (← IO.getEnv "VED_DUMP_DIR").isSome
  let mut allSz : Array Nat := #[]
  let fromGoal := ((← IO.getEnv "VED_PACK_FROM").bind String.toNat?).getD 0
  let mut gi := 0
  for g in gs do
    gi := gi + 1
    if gi - 1 < fromGoal then
      rest := rest ++ [g]
      continue
    setGoals [g]
    let sz ← g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType))
    -- a goal of ordinary size WITHOUT a read of the packed state: the packing step as before (with a read it goes the way of the big goals:
    -- the packing step on a goal of 3e3 nodes with such reads is 30 s / 1.4M heartbeats, R34, the rewriting 0.3 s)
    -- a goal below `minTree` WITH a read goes the way of the big goals (R034: three goals of 1.6k-3.2k nodes, `ved_pack_wire` 26-28 s / 1.4M
    -- heartbeats each, `ved_pack_dag` 0.3 s)
    let smallHasRead ← if sz < minTree then (do try hasReads catch _ => pure true) else pure false
    if sz < minTree && !smallHasRead then
      -- (the packing step as before)
      let tw0 ← IO.monoMsNow
      let hw0 ← IO.getNumHeartbeats
      evalTactic (← `(tactic| ved_pack_wire))
      Tools.VedMemLoop.dbgLog s!"pack_dag_wire_all: small goal {sz}: pack_wire ms={(← IO.monoMsNow) - tw0} hb={((← IO.getNumHeartbeats) - hw0) / 1000}"
      rest := rest ++ (← getGoals)
      continue
    Tools.VedMemLoop.dbgLog s!"pack_dag_wire_all: goal #{gi - 1} size {sz}"
    evalTactic (← `(tactic| try ved_pack_dag))
    if (← getGoals).isEmpty then continue
    let g := (← getGoals).head!
    g.setTag (Name.str (← g.getTag) "ved_dag")
    if dump then
      allSz := allSz.push (← g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType)))
    let th0 ← IO.monoMsNow
    let hr ← try hasReads catch _ => pure true
    Tools.VedMemLoop.dbgLog s!"pack_dag_wire_all: hasReads={hr} ms={(← IO.monoMsNow) - th0}"
    if hr then
      let h0 ← IO.getNumHeartbeats
      evalTactic (← `(tactic| ved_pack_wire_m))
      if dump then Tools.VedMemLoop.dbgLog s!"pack_wire (reads left): hb={((← IO.getNumHeartbeats) - h0) / 1000}"
    else skipped := skipped + 1
    rest := rest ++ (← getGoals)
  if dump then Tools.VedMemLoop.dbgLog s!"pack_dag_wire_all: goals={gs.length} skipped_wire={skipped} sizes after dag {allSz}"
  setGoals rest

/-- `ved_omega` on a side condition without the hypotheses about signals (the packed memory rows `hM1`, `hD1`, ..: 1.6e8 tree nodes in R034;
`omega` reads every hypothesis, and they are no `Nat` / `Int` facts).  Only the side-condition goal loses them. -/
elab "ved_omega_c" : tactic => do
  let mut g ← getMainGoal
  for d in ← g.withContext getLCtx do
    unless d.isImplementationDetail do
      if (d.type.find? fun e => e.isConst && e.constName!.getPrefix == `Sparkle.Core.Signal.Signal).isSome then
        g ← g.tryClear d.fvarId
  setGoals [g]
  if let some dir ← IO.getEnv "VED_OMEGA_LOG" then
   if ← System.FilePath.pathExists s!"{dir}/on" then
    -- test only: the side condition being proved (overwritten at each call; the last one is the one a hanging `omega` works on)
    let txt ← g.withContext do
      let ty ← instantiateMVars (← g.getType)
      let sz := Tools.VedU1Loop.treeSizeVal ty
      let mut nh := 0
      let mut hs := ""
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          nh := nh + 1
          let t ← instantiateMVars d.type
          let ts := Tools.VedU1Loop.treeSizeVal t
          let pp ← if ts < 2000 then pure ((← ppExpr t).pretty.take 150 |>.replace "\n" " ") else pure "(big)"
          hs := hs ++ s!"  {d.userName} [{ts}] let={d.value?.isSome} : {pp}\n"
      let pp ← if sz < 3000 then pure ((← ppExpr ty).pretty.take 3000) else pure ""
      return s!"tree={sz} hyps={nh}\n{pp}\n{hs}"
    IO.FS.writeFile s!"{dir}/omega_last.txt" txt
  evalTactic (← `(tactic| ved_omega))

/-- `ved_omega_c`, also without the hypotheses of at least this many tree nodes: the packed reads left in the context (`this : S = F`,
900-1100 nodes each) and the register equalities (`hreg0..7`, 600-960): `omega` reads them as `/` `%` chains and its elimination
(no heartbeat check) does not end on a failing side condition (R034 goal 44 of stage 6: 8 of them, > 500 s, 100% in `Lean.Omega`) -/
def omegaHypMaxTree : Nat := 300

/-- `ved_omega_c` with only the small hypotheses (range facts) -/
elab "ved_omega_s" : tactic => do
  let mut g ← getMainGoal
  for d in ← g.withContext getLCtx do
    unless d.isImplementationDetail do
      if Tools.VedU1Loop.treeSizeVal (← g.withContext (instantiateMVars d.type)) ≥ omegaHypMaxTree then
        g ← g.tryClear d.fvarId
  setGoals [g]
  evalTactic (← `(tactic| ved_omega_c))

/-- `omega` on the small hypotheses only (as `ved_omega_s`, no signal hypotheses, none of `omegaHypMaxTree` nodes or more) and without the
2M heartbeat cap of `ved_omega`: the leaf of `ved_ctrl_cases` is a data goal that holds, and `omega` needs more than the cap for the
`%` / `/` chains of the 16-bit sums (3.0M for the residual of R034 goal 44) -/
elab "ved_omega_t" : tactic => do
  let mut g ← getMainGoal
  for d in ← g.withContext getLCtx do
    unless d.isImplementationDetail do
      if (d.type.find? fun e => e.isConst && e.constName!.getPrefix == `Sparkle.Core.Signal.Signal).isSome
          || Tools.VedU1Loop.treeSizeVal (← g.withContext (instantiateMVars d.type)) ≥ omegaHypMaxTree then
        g ← g.tryClear d.fvarId
  setGoals [g]
  evalTactic (← `(tactic| omega))

/-- `(a % M + b % M + c) % M = (a + b + c) % M`: the carry bit of a 16-bit sum of already reduced operands is that of the plain sum -/
theorem ved_mod_sum (a b c M : Nat) : (a % M + b % M + c) % M = (a + b + c) % M := by
  rw [Nat.add_right_comm, Nat.add_mod_mod, Nat.add_assoc, Nat.mod_add_mod]
  congr 1
  omega

/-- the `e % m` subterms (`m` a literal) of `tgt`, smallest first -/
def modTerms (tgt : Lean.Expr) : Array Lean.Expr :=
  let src := fun (e : Lean.Expr) => e.isAppOfArity ``HMod.hMod 6 && (e.getArg! 5).nat?.isSome
  (Tools.VedU1WireShare.collectDag src tgt).qsort fun a b => Tools.VedU1Loop.treeSizeVal a < Tools.VedU1Loop.treeSizeVal b

/-- the packed flags of a 16-bit sum are bits of `(sum) % 65536` written in several spellings (nested `%` of the operands, other
order of the summands): `omega` meets 30 and more `%` / `/` atoms and does not end (R034 goal 54, 4 spellings of one sum, 4 flags).
`ved_mod_norm` rewrites every `e % m` that `omega` proves equal to a smaller one (small side goals, smallest first, the inner sums first)
to that one, then generalises each `sum % m` that is the argument of a `/` to a bounded variable: the goal is then about ONE
variable per sum -/
elab "ved_mod_norm" : tactic => withMainContext do
  let mut changed : Bool := true
  let mut rounds : Nat := 0
  while changed && decide (rounds < 20) do
    changed := false
    rounds := rounds + 1
    let cs := modTerms (← instantiateMVars (← getMainTarget))
    if cs.size > 12 then throwError "ved_mod_norm: too many sums"
    for i in [0:cs.size] do
      unless changed do
        for j in [i+1:cs.size] do
          unless changed do
            let r := cs[i]!
            let x := cs[j]!
            if r.getArg! 5 == x.getArg! 5 then
              try
                let m ← mkFreshExprMVar (← mkEq r x)
                let _ ← Tactic.run m.mvarId! (evalTactic (← `(tactic| omega)))
                evalTactic (← `(tactic| rw [← $(← Term.exprToSyntax m):term]))
                changed := true
              catch _ => pure ()
  let src := fun (e : Lean.Expr) =>
    e.isAppOfArity ``HDiv.hDiv 6 && (e.getArg! 5).nat?.isSome && (e.getArg! 4).isAppOfArity ``HMod.hMod 6
      && (e.getArg! 4 |>.getArg! 5).nat?.isSome
  let mut cands : Array Lean.Expr := #[]
  for e in Tools.VedU1WireShare.collectDag src (← instantiateMVars (← getMainTarget)) do
    unless cands.contains (e.getArg! 4) do cands := cands.push (e.getArg! 4)
  if cands.isEmpty then throwError "ved_mod_norm: no sum"
  let mut k := 0
  for r in cands do
    let rS ← Term.exprToSyntax r
    let mS ← Term.exprToSyntax (r.getArg! 5)
    let nm := mkIdent (Name.mkSimple s!"ved_ms{k}")
    let bn := mkIdent (Name.mkSimple s!"ved_mb{k}")
    let hk := mkIdent (Name.mkSimple s!"ved_mh{k}")
    evalTactic (← `(tactic| have $bn : $rS < $mS := Nat.mod_lt _ (by omega)))
    evalTactic (← `(tactic| generalize $hk:ident : $rS = $nm at $bn:ident ⊢))
    evalTactic (← `(tactic| clear $hk:ident))
    k := k + 1

/-- the operands that are below the modulus lose their `% 65536` (`Nat.mod_eq_of_lt`),
`ved_mod_sum` merges nested sums, `ved_mod_norm` makes the carry bits one variable, then `omega`; `ved_omega_t` when that fails (plain `omega` first does not end on
R034 goal 54's nested sums) -/
elab "ved_omega_n" : tactic => do
  let g0 ← getMainGoal
  let saved ← saveState
  try
    let mut g := g0
    for d in ← g.withContext getLCtx do
      unless d.isImplementationDetail do
        if (d.type.find? fun e => e.isConst && e.constName!.getPrefix == `Sparkle.Core.Signal.Signal).isSome
            || Tools.VedU1Loop.treeSizeVal (← g.withContext (instantiateMVars d.type)) ≥ omegaHypMaxTree then
          g ← g.tryClear d.fvarId
    setGoals [g]
    evalTactic (← `(tactic| simp (disch := omega) only [Nat.mod_eq_of_lt, ved_mod_sum] <;> (try ved_mod_norm) <;> omega))
  catch _ =>
    saved.restore
    evalTactic (← `(tactic| ved_omega_t))

/-- set when the leaf of `ved_ctrl_cases` fails (a data goal after the control cases that `omega` could not prove), the context has a
hypothesis of `omegaHypMaxTree` nodes or more, and the residual has at least two DISTINCT subterms `(a % m) / k` with a literal `k`.
A heuristic refusal rule: it does not check the width (16 bit or other) nor that the `a % m` are spellings of the same sum.
Cleared by `ved_ctrl_cases` on entry and on success, and by `ved_leaf_gate` when it reads it. -/
initialize ctrlLeafFailed : IO.Ref Bool ← IO.mkRef false

/-- `t` unless the last `ved_ctrl_cases` ended on a failing leaf: the leafwise closers of such a goal do not end (`omega`'s elimination has no
heartbeat check, so a local cap does not bound it: R034 goal 54 ran the rest of the 900 s), the refusal comes back at once -/
elab "ved_leaf_gate " t:tactic : tactic => do
  if ← ctrlLeafFailed.modifyGet fun b => (b, false) then
    throwError "ved_leaf_gate: ved_ctrl_cases ended on a failing leaf, leafwise closers skipped"
  evalTactic t

/-- `ved_pack_simp` with `ved_omega_s` as side-condition prover (the plain one reads the 1.6e8-node signal hypotheses at every side condition) -/
macro "ved_pack_simp_c" : tactic =>
  `(tactic| simp (disch := first | ved_omega_s | fail) only
      [Nat.reducePow, Nat.reduceAdd, Nat.mod_eq_of_lt, Nat.div_eq_of_lt, Tools.VedU1Loop.div_pack, Tools.VedU1Loop.mod_pack, Nat.add_mod_left, Nat.add_zero])

/-- `ved_pack_simp` on a goal that still has a read of the packed state (after `ved_pack_dag` it is a traversal that changes nothing) -/
elab "ved_pack_simp_g" : tactic => do
  if let some dir ← IO.getEnv "VED_OMEGA_LOG" then IO.FS.writeFile s!"{dir}/on" "1"
  unless ← isDagged (← getMainGoal) do
    evalTactic (← `(tactic| ved_pack_simp))
    return
  if ← hasReads then
    -- a dagged goal of `omegaMaxTree` nodes or more that still has reads: the closers (`ved_ctrl_cases` after `ved_or_lit_post`) close it without
    -- the packing step, which costs 4.2e5 heartbeats on each of R034's goals 44/45 (45231 nodes) and changes nothing they need
    let sz := Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← getMainTarget))
    if sz ≥ omegaMaxTree then
      Tools.VedMemLoop.dbgLog s!"pack_simp_g: skipped on a goal of {sz} nodes"
      return
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
    evalTactic (← `(tactic| ved_pack_simp_c))

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
    if dump then Tools.VedMemLoop.dbgLog s!"start goal {i}: size={sz}"
    try evalTactic t
    catch e =>
      if dump then Tools.VedMemLoop.dbgLog s!"close goal {i}: size={sz} FAILED ms={(← IO.monoMsNow) - t0} hb={((← IO.getNumHeartbeats) - h0) / 1000}"
      throw e
    if dump then Tools.VedMemLoop.dbgLog s!"close goal {i}: size={sz} ms={(← IO.monoMsNow) - t0} hb={((← IO.getNumHeartbeats) - h0) / 1000} left={(← getGoals).length}"
    i := i + 1
    rest := rest ++ (← getGoals)
  setGoals rest

/-- clear the hypotheses about signals of the main goal (the packed memory rows: 1.6e8 tree nodes in R034; `omega` reads every
hypothesis, they are no `Nat` / `Int` facts) -/
def clearSigHyps : TacticM Unit := do
  let mut g ← getMainGoal
  for d in ← g.withContext getLCtx do
    unless d.isImplementationDetail do
      if (d.type.find? fun e => e.isConst && e.constName!.getPrefix == `Sparkle.Core.Signal.Signal).isSome then
        g ← g.tryClear d.fvarId
  setGoals [g]

/-- the closing stage on a goal of at least `omegaMaxTree` nodes: drop the hypotheses about signals (see `ved_omega_c`) -- plain `omega` of
the closers reads them all -/
elab "ved_clear_sig_big" : tactic => do
  let g ← getMainGoal
  let sz ← g.withContext do return Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← g.getType))
  if sz ≥ omegaMaxTree then clearSigHyps

/-- `ved_or_lit_m` on a goal that `ved_or_lit_g` left to `ved_wire` (at least `shareMinTree` nodes, a `|||`) but that `ved_pack_dag` has
since brought below `shareMinTree` and `ved_wire` has not taken (R034 goals 44/45: 45231 nodes, `|||` of two 16-bit rotation halves: the closers
exhaust the budget on them, `ved_or_lit_m` 38k heartbeats and `ved_ctrl_cases` 29k close it); without the signal hypotheses for `omega` -/
elab "ved_or_lit_post" : tactic => do
  let tgt ← withMainContext do instantiateMVars (← getMainTarget)
  if Tools.VedU1Loop.treeSizeVal tgt < Tools.VedU1Loop.shareMinTree && !(Tools.VedU1Loop.natOrs tgt).isEmpty then
    evalTactic (← `(tactic| ved_clear_sig_big))
    evalTactic (← `(tactic| ved_or_lit_m))

/-- `ved_bit_simp` with `ved_omega_c` as side-condition prover -/
macro "ved_bit_simp_c" : tactic =>
  `(tactic| simp (disch := first | ved_omega_c | (split <;> ved_omega_c) | fail) only
      [Tools.VedU1Loop.and_lt2_l, Tools.VedU1Loop.and_lt2_r, Tools.VedU1Loop.or_lt2, Tools.VedU1Loop.xor_lt2])

/-- `ved_bit_simp` on a goal that went through `ved_pack_dag` (the 0/1 `&&&` / `|||` of the wires need the field variables) -/
elab "ved_bit_simp_g" : tactic => do
  if ← isDagged (← getMainGoal) then evalTactic (← `(tactic| ved_bit_simp_c))

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
  try clearSigHyps; decideSmall2Core; ranLog.modify (·.push "decide_small2")
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
  let stx ← `(tactic| simp (config := {decide := true}) only [Nat.reduceMod, Nat.reduceEqDiff, Fin.val_add, Fin.val_mk, BitVec.val_toFin, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub, Nat.reduceDiv, and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or, not_true_eq_false, not_false_eq_true, true_implies, false_implies, implies_true, if_true, if_false])
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
      if (← IO.getEnv "VED_DUMP_DIR").isSome then
        -- test only: the residual about to be tried (the last one logged is the one a hanging leaf works on)
        Tools.VedMemLoop.dbgLog s!"ctrl_cases leaf: {(← ppExpr ty).pretty.take 6000}"
      try evalTactic (← `(tactic| ved_omega_n))
      catch e =>
        if (← IO.getEnv "VED_DUMP_DIR").isSome then
          -- test only: the residual statement `omega` could not prove, with the context it is given
          let txt ← g.withContext do
            let mut hs := ""
            for d in ← getLCtx do
              unless d.isImplementationDetail do
                let t ← instantiateMVars d.type
                hs := hs ++ s!"  {d.userName} [{Tools.VedU1Loop.treeSizeVal t}]\n"
            return s!"{(← ppExpr ty).pretty.take 6000}\n{hs}"
          Tools.VedMemLoop.dbgLog s!"ctrl_cases leaf failed: {txt}"
        -- the leafwise closers hang only where `omega` reads hypotheses of `omegaHypMaxTree` nodes or more (R034 goal 54: the 8 `hx` of 850-1100)
        let bigHyp ← g.withContext do
          for d in ← getLCtx do
            unless d.isImplementationDetail do
              if Tools.VedU1Loop.treeSizeVal (← instantiateMVars d.type) ≥ omegaHypMaxTree then return true
          return false
        -- and the residual has at least two distinct `(a % m) / k` (literal `k`; on R034 goal 54 they are spellings of one 16-bit sum's
        -- carry bits, but neither the width nor the sameness is checked: a heuristic; with one such term the leafwise closers may still rescue it: R037)
        let mut sums : Array Lean.Expr := #[]
        for e in Tools.VedU1WireShare.collectDag (fun e => e.isAppOfArity ``HDiv.hDiv 6 && (e.getArg! 5).nat?.isSome
            && (e.getArg! 4).isAppOfArity ``HMod.hMod 6) ty do
          unless sums.contains (e.getArg! 4) do sums := sums.push (e.getArg! 4)
        ctrlLeafFailed.set (bigHyp && sums.size ≥ 2)
        throw e
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
  -- the flag `ved_leaf_gate` reads describes THIS call only (a leaf failure that an earlier call caught must not gate a later goal)
  ctrlLeafFailed.set false
  try clearSigHyps; ctrlCasesCore; ranLog.modify (·.push "ctrl_cases"); ctrlLeafFailed.set false
  catch e =>
    if dump then Tools.VedMemLoop.dbgLog s!"ctrl_cases: {(← e.toMessageData.toString).take 300}"
    throw e

end Tools.VedMemPack
