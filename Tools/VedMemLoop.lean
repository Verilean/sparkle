import Lean
import Tools.VedMem
import Tools.VedU1Entry
import Tools.VedU1WireShare

/-!
# Loop unfolding for a loop body that holds a memory (`sparkle-ved-memory`)

`ved_loop_unfold_mem t` is `ved_loop_unfold_share t` (`Tools/VedU1WireShare.lean`) with the strong fixpoint
equation `Tools.VedMem.loop_val_unfold_strong` in place of `Tools.VedU1Loop.loop_val_unfold`: the loop body's
value at `t+1` may depend on its argument at every cycle `≤ t`, which is what a memory inside the body does.
The side condition is discharged by `ved_causal`: reduce both sides, replace each `memState` of the left side
by the one over the other argument (`Tools.VedMem.memState_congr`, its three side conditions are pointwise
equalities of the port signals, each follows from the agreement hypothesis), then rewrite the value at `t`.
Untrusted: the kernel checks the resulting proof.
-/

namespace Tools.VedMemLoop

open Lean Meta Elab Tactic Sparkle.Core.Signal

/-! `.val` of an operator applied directly through the `BitVec`-`Signal` / `Signal`-`BitVec` instances (as the synthesizer's
source writes `0#16 - x`): `Tools.VedU1Lemmas.*_val_sc/_cs` are stated with the other elaboration (`Signal.pure a`). -/
section DirectOps
open Sparkle.Core.Domain
variable {dom : DomainConfig} {n : Nat}
theorem add_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HAdd.hAdd (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a + b.val s := rfl
theorem add_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HAdd.hAdd (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s + b := rfl
theorem sub_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HSub.hSub (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a - b.val s := rfl
theorem sub_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HSub.hSub (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s - b := rfl
theorem mul_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HMul.hMul (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a * b.val s := rfl
theorem mul_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HMul.hMul (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s * b := rfl
theorem and_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HAnd.hAnd (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a &&& b.val s := rfl
theorem and_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HAnd.hAnd (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s &&& b := rfl
theorem or_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HOr.hOr (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a ||| b.val s := rfl
theorem or_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HOr.hOr (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s ||| b := rfl
theorem xor_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HXor.hXor (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a ^^^ b.val s := rfl
theorem xor_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HXor.hXor (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s ^^^ b := rfl
theorem shl_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HShiftLeft.hShiftLeft (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a <<< b.val s := rfl
theorem shl_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HShiftLeft.hShiftLeft (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s <<< b := rfl
theorem shr_val_bs (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) :
    (@HShiftRight.hShiftRight (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) _ a b).val s = a >>> b.val s := rfl
theorem shr_val_sb (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) :
    (@HShiftRight.hShiftRight (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) _ a b).val s = a.val s >>> b := rfl
end DirectOps

/-- the first pair of differing subterms of two expressions (descending through equal heads / binder bodies) -/
partial def exprDiff (a b : Expr) : Option (Expr × Expr) :=
  if a == b then none else
  match a, b with
  | .app .., .app .. =>
    if a.getAppNumArgs == b.getAppNumArgs && a.getAppFn == b.getAppFn then
      (List.range a.getAppNumArgs).findSome? fun i => exprDiff (a.getAppArgs[i]!) (b.getAppArgs[i]!)
    else some (a, b)
  | .lam _ t x _, .lam _ t' x' _ => (exprDiff t t').orElse fun _ => exprDiff x x'
  | .mdata _ x, _ => exprDiff x b
  | _, .mdata _ x => exprDiff a x
  | _, _ => some (a, b)

/-- the number of nodes of an expression as a tree (shared subterms counted at each occurrence), and as a DAG -/
partial def treeSize (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get)[e]? then return n
  let n ← match e with
    | .app f a => do pure ((← treeSize f) + (← treeSize a) + 1)
    | .lam _ t b _ => do pure ((← treeSize t) + (← treeSize b) + 1)
    | .forallE _ t b _ => do pure ((← treeSize t) + (← treeSize b) + 1)
    | .letE _ t v b _ => do pure ((← treeSize t) + (← treeSize v) + (← treeSize b) + 1)
    | .mdata _ b => treeSize b
    | .proj _ _ b => do pure ((← treeSize b) + 1)
    | _ => pure 1
  modify (·.insert e n)
  return n

/-- `ved_mem_shape ite|lam|fvar`: the memory-array argument (the last) of the goal `MemInv ..` has that outer shape, as written
(the peel must not let the unifier match an `ite` against a `fun` by eta / unfolding: that produces junk) -/
elab "ved_mem_shape " k:ident : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOf ``Tools.VedMem.MemInv do throwError "ved_mem_shape: not a MemInv goal"
  let m := (tgt.getArg! (tgt.getAppNumArgs - 1)).consumeMData
  let ok := match k.getId.eraseMacroScopes.toString with
    | "ite" => m.isAppOf ``ite
    | "lam" => m.isLambda
    | "fvar" => m.isFVar
    | _ => false
  unless ok do throwError "ved_mem_shape: not {k.getId.eraseMacroScopes}"

/-- debugging: log the part of the main goal from the first `HSub.hSub`, `pp.explicit`, cut to 3500 characters -/
elab "ved_dbg_goal" : tactic => withMainContext do
  let g ← getMainGoal
  let txt ← withOptions (fun o => o.setBool `pp.explicit true) do return toString (← ppGoal g)
  let i := (txt.splitOn "HSub.hSub").head!.length
  logInfo m!"DBG {(txt.drop (i - 500)).take 1200}"

/-- debugging: the number of goals and the target of the first two, each cut to 2500 characters -/
elab "ved_dbg_state" : tactic => do
  let gs ← getGoals
  let mut out := s!"{gs.length} goals"
  if let some dir ← IO.getEnv "VED_DUMP_DIR" then
    let mut k := 0
    for g in gs do
      let t ← g.withContext do
        withOptions (fun o => (o.insert `format.width (160 : Nat)).setBool `pp.deepTerms true |>.insert `pp.maxSteps (10000000 : Nat)) do
          return toString (← ppGoal g)
      IO.FS.writeFile s!"{dir}/goal{k}.txt" t
      k := k + 1
  for g in gs.take 2 do
    let t ← g.withContext do return toString (← ppExpr (← instantiateMVars (← g.getType)))
    out := out ++ s!"\n--- target ({t.length} chars):\n" ++ t.take 800 ++ "\n.....\n" ++ t.drop (t.length - 1800)
  let mut summary := ""
  for g in gs do
    let tl := Tools.VedU1WireShare.loopsDag (← g.withContext do instantiateMVars (← g.getType))
    let hs ← g.withContext do
      let mut c := 0
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          c := c + (Tools.VedU1WireShare.loopsDag (← instantiateMVars d.type)).size
      return c
    summary := summary ++ s!" [T{tl.size}/H{hs}]"
  out := out ++ "\nPER GOAL loops (target/hyps):" ++ summary
  let mut sizes := ""
  for g in gs do
    let t ← g.withContext do instantiateMVars (← g.getType)
    let (tr, _) := (treeSize t).run {}
    sizes := sizes ++ s!" [tree {tr}/dag {(Tools.VedU1WireShare.collectDag (fun _ => true) t).size}]"
  out := out ++ "\nGOAL SIZES:" ++ sizes
  let mut shorts := ""
  let mut gi := 0
  for g in gs do
    let t ← g.withContext do return toString (← ppExpr (← instantiateMVars (← g.getType)))
    shorts := shorts ++ s!"\n  #{gi}: " ++ (let t1 := (t.replace "\n" " "); (t1.take 150).toString ++ " ..... " ++ (t1.drop (t1.length - 220)).toString)
    gi := gi + 1
  out := out ++ "\nALL TARGETS:" ++ shorts.take 9000
  for g in gs do
    let tg ← g.withContext do instantiateMVars (← g.getType)
    if tg.isAppOf ``Tools.VedMem.MemInv then
      let rep ← g.withContext do
        let mut o := ""
        for d in ← getLCtx do
          unless d.isImplementationDetail do
            let ty ← instantiateMVars d.type
            if ty.isAppOf ``Tools.VedMem.MemInv then
              let a := tg.getAppArgs
              let b := ty.getAppArgs
              let eqs := (List.range (min a.size b.size)).map fun i => a[i]! == b[i]!
              o := o ++ s!"\n  MEMINV goal vs {d.userName}: arg equal? {eqs}"
              for i in (if a[3]! == b[3]! then [5, 6, 7] else []) do
                if let some (x, y) := exprDiff a[i]! b[i]! then
                  let xs := toString (← ppExpr x)
                  let ys := toString (← ppExpr y)
                  o := o ++ s!"\n   arg {i} first diff:\n    GOAL: {xs.take 500}\n    HYP:  {ys.take 500}"
        return o
      out := out ++ "\nMEMINV GOAL" ++ rep
      if tg.getAppNumArgs ≥ 10 then
        let mm ← g.withContext do withOptions (fun o => (o.setBool `pp.deepTerms false |>.insert `pp.deepTerms.threshold (6 : Nat))) do return toString (← ppExpr (tg.getAppArgs[9]!))
        out := out ++ s!"\nMEMS ARG ({mm.length} chars): " ++ mm.take 3500
  for gi2 in [8, 12] do
    if let some g := gs[gi2]? then
      let t ← g.withContext do return toString (← ppExpr (← instantiateMVars (← g.getType)))
      out := out ++ s!"\nGOAL{gi2} ({t.length} chars):\n" ++ t.take 1500 ++ "\n.....\n" ++ (t.drop (t.length - 1200)).toString
  if let some g := gs.find? (fun g => true) then
    let _ := g
  for g in gs do
    let tg ← g.withContext do instantiateMVars (← g.getType)
    if (Tools.VedU1WireShare.loopsDag tg).size > 0 then
      let occ := Tools.VedU1WireShare.collectDag (fun x => x.isAppOfArity ``Signal.val 4 && (x.getArg! 2).isAppOfArity ``Signal.loop 4) tg
      let ts ← g.withContext do occ.mapM fun o => do return toString (← ppExpr (o.getArg! 3))
      let lp := Tools.VedU1WireShare.collectDag (fun x => x.isAppOfArity ``Signal.loop 4) tg
      let parents := Tools.VedU1WireShare.collectDag (fun x => x.isApp && x.getAppArgs.any (fun a => a.isAppOfArity ``Signal.loop 4)) tg
      let ps ← g.withContext do parents.mapM fun o => do return (toString (← ppExpr o.getAppFn)).take 60
      let tgtS ← g.withContext do
        let ty ← inferType lp[0]!
        withLocalDeclD `LOOP ty fun lv => do
          let t' := tg.replace fun e => if e.isAppOfArity ``Signal.loop 4 then some lv else none
          return toString (← ppExpr t')
      out := out ++ s!"\nT1 TARGET (loop := LOOP, {tgtS.length} chars): " ++ tgtS.take 1800
      let pe := parents[0]!.replace fun e => if e.isAppOfArity ``Signal.loop 4 then some (mkConst `LOOP) else none
      let pes ← g.withContext <| withOptions (fun o => o.setBool `pp.explicit true) do return toString (← ppExpr pe)
      out := out ++ s!"\nPARENT0 (loop := LOOP): {pes.take 700}"
      out := out ++ s!"\nFIRST T1 GOAL: Signal.val-of-loop occurrences at times {ts}; loops {lp.size}; parents heads {ps}"
      break
  if let some g := gs.head? then
    let hy ← g.withContext do
      let mut o := ""
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          o := o ++ s!"\n  {d.userName} : " ++ (← (do let t := toString (← ppExpr (← instantiateMVars d.type)); pure (if t.length > 700 then (t.take 100).toString ++ s!" ...({t.length} chars)" else t) : MetaM String))
      return o
    out := out ++ "\nHYPS:" ++ hy.take 4500
    let extra ← g.withContext do
      let mut o := ""
      let tl := Tools.VedU1WireShare.loopsDag (← instantiateMVars (← g.getType))
      o := o ++ s!"\nTARGET LOOPS {tl.size}"
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          let hl := Tools.VedU1WireShare.loopsDag (← instantiateMVars d.type)
          if hl.size > 0 then
            o := o ++ s!"\nHYP {d.userName}: loops {hl.size}, in target: {hl.map (fun l => tl.contains l)}"
      return o
    out := out ++ extra
  throwError "DBGSTATE {out}"

/-- close a goal `x.toNat < n` (a bit-vector's range) by `BitVec.isLt` -/
elab "ved_lt_close" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOfArity ``LT.lt 4 do throwError "not <"
  evalTactic (← `(tactic| exact BitVec.isLt _))

/-- `ved_mem_congr s1 s2 h t`: rewrite every `memState` of the goal that mentions the fvar `s1` into the one
with `s2` in its place (`h : ∀ k ≤ t, s1.val k = s2.val k`) -/
elab "ved_mem_congr " s1:ident s2:ident h:ident : tactic => withMainContext do
  let s1E ← elabTerm s1.raw none
  let s2E ← elabTerm s2.raw none
  let tgt ← instantiateMVars (← getMainTarget)
  let isMem := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 8
  let occs := Tools.VedU1WireShare.collectDag isMem tgt
  let mut done : Array Expr := #[]
  for o in occs do
    let args := o.getAppArgs
    let T := mkAppN o.getAppFn (args.extract 0 8)
    if done.contains T || !(T.containsFVar s1E.fvarId!) then continue
    done := done.push T
    let T' := T.replaceFVar s1E s2E
    let Ts ← Term.exprToSyntax T
    let T's ← Term.exprToSyntax T'
    let side ← `(tactic| (intro k hk; simp only [$h:ident k (by omega)]))
    let side2 ← `(tactic| (intro k hk; simp [$h:ident k (by omega), Tools.VedU1Contract.PTy.val, Sparkle.Core.Signal.Signal.map, Functor.map, Seq.seq, Sparkle.Core.Signal.Signal.seq, Sparkle.Core.Signal.Signal.ap, Sparkle.Core.Signal.Signal.mux, Sparkle.Core.Signal.Signal.beq, Sparkle.Core.Signal.bundle2]))
    let side3 ← `(tactic| (intro k hk; (try dsimp only); ved_loop_simp [$h:ident k (by omega), Tools.VedU1Contract.PTy.val, Sparkle.Core.Signal.Signal.memoryComboRead_val, Tools.VedU1Lemmas.add_val_sc, Tools.VedU1Lemmas.add_val_cs, Tools.VedU1Lemmas.sub_val_sc, Tools.VedU1Lemmas.sub_val_cs, Tools.VedU1Lemmas.mul_val_sc, Tools.VedU1Lemmas.mul_val_cs, Tools.VedU1Lemmas.and_val_sc, Tools.VedU1Lemmas.and_val_cs, Tools.VedU1Lemmas.or_val_sc, Tools.VedU1Lemmas.or_val_cs, Tools.VedU1Lemmas.xor_val_sc, Tools.VedU1Lemmas.xor_val_cs, Tools.VedU1Lemmas.shl_val_sc, Tools.VedU1Lemmas.shl_val_cs, Tools.VedU1Lemmas.shr_val_sc, Tools.VedU1Lemmas.shr_val_cs, Tools.VedMemLoop.add_val_bs, Tools.VedMemLoop.add_val_sb, Tools.VedMemLoop.sub_val_bs, Tools.VedMemLoop.sub_val_sb, Tools.VedMemLoop.mul_val_bs, Tools.VedMemLoop.mul_val_sb, Tools.VedMemLoop.and_val_bs, Tools.VedMemLoop.and_val_sb, Tools.VedMemLoop.or_val_bs, Tools.VedMemLoop.or_val_sb, Tools.VedMemLoop.xor_val_bs, Tools.VedMemLoop.xor_val_sb, Tools.VedMemLoop.shl_val_bs, Tools.VedMemLoop.shl_val_sb, Tools.VedMemLoop.shr_val_bs, Tools.VedMemLoop.shr_val_sb, Tools.VedU1Lemmas.pure_val, Tools.VedU1Lemmas.mux_val, Tools.VedU1Lemmas.compl_val, Tools.VedU1Lemmas.bool_and_val, Tools.VedU1Lemmas.bool_or_val, Tools.VedU1Lemmas.bool_xor_val, Tools.VedU1Lemmas.bool_compl_val]))
    evalTactic (← `(tactic|
      (have hc : $Ts = $T's := Tools.VedMem.memState_congr _ _
          (by first | ($side:tactic; done) | ($side2:tactic; done) | ($side3:tactic; done))
          (by first | ($side:tactic; done) | ($side2:tactic; done) | ($side3:tactic; done))
          (by first | ($side:tactic; done) | ($side2:tactic; done) | ($side3:tactic; done))
       rw [hc])))


open Lean Meta in
/-- `BitVec.toNat (x ++ y)` read at either spelling of the width (`4` against `2 + 2`: the pattern of `BitVec.toNat_append`
does not unify the width of a `++` used at a literal width) -/
simproc ved_toNat_append (BitVec.toNat _) := fun e => do
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let a := e.getArg! 1
  unless a.isAppOfArity ``HAppend.hAppend 6 do return .continue
  let x := a.getArg! 4
  let y := a.getArg! 5
  let pf ← mkAppM ``BitVec.toNat_append #[x, y]
  let some (_, l, r) := (← inferType pf).eq? | return .continue
  unless (← isDefEq l e) do return .continue
  return .visit { expr := r, proof? := some pf }

def dbgLog (msg : String) : IO Unit := do
  if let some dir ← IO.getEnv "VED_DUMP_DIR" then
    let h ← IO.FS.Handle.mk s!"{dir}/addr.log" .append
    h.putStrLn msg

/-- `ved_clear_signals`: clear the hypotheses that speak of signals (`MemInv`, the read equations: whole loop bodies, hundreds of
kilobytes): an address equality does not use them, and `omega` / `generalize ... at *` read every hypothesis. -/
elab "ved_clear_signals" : tactic => withMainContext do
  let mut ids : Array FVarId := #[]
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      let t ← instantiateMVars d.type
      if (t.find? fun e => e.isConst && (e.constName!.getPrefix == `Sparkle.Core.Signal.Signal
          || e.constName! == ``Tools.VedMem.MemInv)).isSome then ids := ids.push d.fvarId
  let g ← getMainGoal
  let mut g := g
  for i in ids.reverse do
    g ← g.tryClear i
  replaceMainGoal [g]

/-- `ved_decide_small`: a goal over a few small bit-vector fields (every free variable occurs as `BitVec.toNat v` with `v` a
variable of at most `2^14` values together) is closed by `decide +kernel` after the fields are generalised to bounded
`Nat` variables (`∀ a, a < 2^w → ..`): the case analysis `omega` does by splitting every `if` is one kernel evaluation.
Fails when another free variable remains. -/
def decideSmallCore : Lean.Elab.Tactic.TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let isAtom := fun (e : Expr) => e.isAppOfArity ``BitVec.toNat 2 && (e.getArg! 1).isFVar
  let mut atoms : Array Expr := #[]
  for o in Tools.VedU1WireShare.collectDag isAtom tgt do
    unless atoms.contains o do atoms := atoms.push o
  if atoms.isEmpty then throwError "ved_decide_small: no field"
  -- every free variable of the goal is under a collected atom
  let rest := atoms.foldl (fun (t : Expr) a => t.replace fun e => if e == a then some (mkNatLit 0) else none) tgt
  if rest.hasFVar then throwError "ved_decide_small: other variables"
  let mut cases : Nat := 1
  for a in atoms do
    let ty ← whnf (← inferType (a.getArg! 1))
    let some w := (ty.getArg! 0).nat? | throwError "ved_decide_small: width"
    cases := cases * 2 ^ w
  if cases > 16384 then throwError "ved_decide_small: too many cases"
  let mut names : Array (TSyntax `ident) := #[]
  let mut k := 0
  for a in atoms do
    let nm := mkIdent (Name.mkSimple s!"ved_ds_a{k}")
    let bn := mkIdent (Name.mkSimple s!"ved_ds_b{k}")
    let aS ← Term.exprToSyntax a
    let vS ← Term.exprToSyntax (a.getArg! 1)
    let hk := mkIdent (Name.mkSimple s!"ved_ds_h{k}")
    let ty ← whnf (← inferType (a.getArg! 1))
    let wS := Syntax.mkNumLit (toString ((ty.getArg! 0).nat?.getD 0))
    evalTactic (← `(tactic| generalize $hk:ident : $aS = $nm))
    evalTactic (← `(tactic| have $bn : $nm < 2 ^ $wS := by rw [← $hk:ident]; exact BitVec.isLt $vS))
    evalTactic (← `(tactic| clear $hk:ident))
    names := names.push nm
    k := k + 1
  for nm in names.reverse do
    evalTactic (← `(tactic| revert $nm))
  evalTactic (← `(tactic| decide +kernel))

elab "ved_decide_small" : tactic => do
  try decideSmallCore
  catch e =>
    dbgLog s!"decide_small: {← e.toMessageData.toString}"
    try dbgLog s!"{← Lean.Elab.Tactic.withMainContext (do return (← Lean.Meta.ppGoal (← Lean.Elab.Tactic.getMainGoal)).pretty)}" catch _ => pure ()
    throw e

def dbgT (label : String) : IO Unit := do
  dbgLog s!"T {label} t={← IO.monoMsNow}"

/-- `ved_mem_addr`: the `memState` atoms of the goal that differ only in the ADDRESS (the IR side spells it as `BitVec.ofNat aw`
of `Nat` arithmetic, the declaration side as `BitVec` arithmetic) are made the same atom: each other address is rewritten to
the first one, by an equality proved with `bv_omega` (the branch conditions of the enclosing `if`s are first propagated into the
branches).  Untrusted: the kernel checks the rewrites. -/
elab "ved_mem_addr" : tactic => withMainContext do
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
  dbgT "addr: gate passed"
  let isMem := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 9
  -- one rewrite per round, the atoms collected again after it (an address can contain another one: the rewrite of the
  -- inner one changes the outer one)
  let mut remaining := true
  for pass in [0:2] do
    if !remaining then break
    if pass == 1 then
      try evalTactic (← `(tactic| simp (config := {contextual := true}) only [↓reduceIte, ite_true, ite_false, if_true, if_false])) catch _ => pure ()
      dbgT "addr: contextual simp done"
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
            evalTactic (← `(tactic| (have hmaddr : $aS = $repS := by
                                       first | rfl | (apply BitVec.eq_of_toNat_eq; (try ved_clear_signals); (try ved_pack_simp); (try ved_bit_simp); (try ved_pack_simp); (try simp only [apply_ite BitVec.toNat, ved_toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]); first | ved_decide_small | ((repeat' split); all_goals (try simp only [ved_toNat_append, BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]); all_goals (try ved_pack_simp); all_goals (first | omega | bv_omega))))))
            dbgT "addr: have done"
            evalTactic (← `(tactic| rw [hmaddr]))
            progress := true
            dbgT "addr: rewrite ok"
          catch e => dbgT "addr: equality failed"; dbgLog s!"no equality for {← ppExpr a}: {← e.toMessageData.toString}"
      if !progress then break

/-- `ved_mem_gen`: each `memState` application of the goal (no bound variable) is generalised to a variable `ved_mem_k` (in the
goal and in the hypotheses that mention it).  After `ved_mem_addr` the two sides of a data goal read the same memory atoms and
the rest is arithmetic over the register fields: the atoms (whose write ports are whole loop bodies) only make the goal a
large tree for `ved_wire`.  Untrusted: generalisation of a term by a variable. -/
elab "ved_mem_gen" : tactic => withMainContext do
  dbgT "gen: start"
  let isMem := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 9
  let tgt ← instantiateMVars (← getMainTarget)
  let mut occs : Array Expr := #[]
  for o in Tools.VedU1WireShare.collectDag isMem tgt do
    if o.hasLooseBVars || occs.contains o then continue
    occs := occs.push o
  let mut k := 0
  for o in occs do
    Tools.VedU1WireShare.generalizeDag o (Name.mkSimple s!"ved_mem{k}")
    k := k + 1
  dbgT "gen: done"

/-- `ved_hyp_bits`: the hypotheses with a bit operation (`&&&`, `|||`, `^^^`) on `Nat` (the write enable of a memory
as the module computes it, `c1 &&& c2` of two conditions) are rewritten like the goal by `ved_bit_simp`'s rules and moved
into the goal, where the closing step splits their `if`s (`omega` does not read `if` or `&&&`).  Untrusted: `revert`. -/
elab "ved_hyp_bits" : tactic => withMainContext do
  let mut hs : Array (TSyntax `ident) := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if (Tools.VedU1Loop.natBitOps (← instantiateMVars d.type)).size > 0 then
        hs := hs.push (mkIdent d.userName)
  dbgT s!"hyp: {hs.size} hyps"
  if hs.isEmpty then return
  try evalTactic (← `(tactic| simp (disch := first | ved_omega | (split <;> ved_omega) | fail) only
      [Tools.VedU1Loop.and_lt2_l, Tools.VedU1Loop.and_lt2_r, Tools.VedU1Loop.or_lt2, Tools.VedU1Loop.xor_lt2] at $[$hs]*))
  catch e => dbgLog s!"ved_hyp_bits simp: {← e.toMessageData.toString}"
  let g ← getMainGoal
  try
    let names := hs.map (·.getId)
    let fvs ← g.withContext do
      return (← getLCtx).foldl (init := (#[] : Array FVarId)) fun a d =>
        if !d.isImplementationDetail && names.contains d.userName then a.push d.fvarId else a
    let (_, g') ← g.revert fvs (preserveOrder := true)
    replaceMainGoal [g']
    dbgLog "ved_hyp_bits: reverted"
  catch e => dbgLog s!"ved_hyp_bits revert: {← e.toMessageData.toString}"

/-- `ved_stamp k`: (only with `VED_DUMP_DIR` set) append the time and the number of goals to `addr.log` -/
elab "ved_stamp " k:num : tactic => do
  if (← IO.getEnv "VED_DUMP_DIR").isSome then
    dbgLog s!"STAMP {k.getNat} t={← IO.monoMsNow} goals={(← getGoals).length}"

/-- the side condition `hS` of the strong fixpoint equation -/
syntax "ved_causal " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| ved_causal [$ex,*]) =>
    `(tactic| (intro t s1 s2 h
               -- a registered read's value at `t` unfolds only at `t = n + 1`
               rcases t with _ | t <;>
               (try (ved_loop_simp [Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.memory_val_succ, Sparkle.Core.Signal.Signal.memory_val_zero, Sparkle.Core.Signal.Signal.fst, Sparkle.Core.Signal.Signal.snd, $ex,*]))
               <;> (try ved_mem_congr s1 s2 h)
               <;> (try (ved_loop_simp [Tools.VedU1Lemmas.add_val_sc, Tools.VedU1Lemmas.add_val_cs, Tools.VedU1Lemmas.sub_val_sc, Tools.VedU1Lemmas.sub_val_cs, Tools.VedU1Lemmas.mul_val_sc, Tools.VedU1Lemmas.mul_val_cs, Tools.VedU1Lemmas.and_val_sc, Tools.VedU1Lemmas.and_val_cs, Tools.VedU1Lemmas.or_val_sc, Tools.VedU1Lemmas.or_val_cs, Tools.VedU1Lemmas.xor_val_sc, Tools.VedU1Lemmas.xor_val_cs, Tools.VedU1Lemmas.shl_val_sc, Tools.VedU1Lemmas.shl_val_cs, Tools.VedU1Lemmas.shr_val_sc, Tools.VedU1Lemmas.shr_val_cs, Tools.VedMemLoop.add_val_bs, Tools.VedMemLoop.add_val_sb, Tools.VedMemLoop.sub_val_bs, Tools.VedMemLoop.sub_val_sb, Tools.VedMemLoop.mul_val_bs, Tools.VedMemLoop.mul_val_sb, Tools.VedMemLoop.and_val_bs, Tools.VedMemLoop.and_val_sb, Tools.VedMemLoop.or_val_bs, Tools.VedMemLoop.or_val_sb, Tools.VedMemLoop.xor_val_bs, Tools.VedMemLoop.xor_val_sb, Tools.VedMemLoop.shl_val_bs, Tools.VedMemLoop.shl_val_sb, Tools.VedMemLoop.shr_val_bs, Tools.VedMemLoop.shr_val_sb, Tools.VedU1Lemmas.pure_val, Tools.VedU1Lemmas.mux_val, Tools.VedU1Lemmas.compl_val, Tools.VedU1Lemmas.bool_and_val, Tools.VedU1Lemmas.bool_or_val, Tools.VedU1Lemmas.bool_xor_val, Tools.VedU1Lemmas.bool_compl_val, h, Sparkle.Core.Signal.Signal.fst, Sparkle.Core.Signal.Signal.snd, $ex,*]))))

/-- `runSub` that, when a side condition stays open, says which (the first goal, cut to 2500 characters) -/
def runSubMem (m : MVarId) (tac : TSyntax `tactic) : TacticM Unit := do
  let saved ← getGoals
  setGoals [m]
  evalTactic tac
  let rest ← getGoals
  unless rest.isEmpty do
    let g ← ppGoal rest.head!
    let txt := (toString g).take 2500
    throwError "ved_loop_unfold_mem: a side condition is left open ({rest.length} goals); first:\n{txt}"
  setGoals saved

open Tools.VedU1WireShare in
/-- the loops of one goal (target and hypotheses), each once -/
def goalLoops (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut loops := loopsDag (← instantiateMVars (← g.getType))
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      for l in loopsDag (← instantiateMVars d.type) do
        unless loops.contains l do loops := loops.push l
  return loops

open Tools.VedU1WireShare in
/-- the goal reads `(loop).val s` somewhere (target or hypotheses) -/
def hasValAt (g : MVarId) (loop s : Expr) : MetaM Bool := g.withContext do
  let isV := fun (e : Expr) => e.isAppOfArity ``Signal.val 4 && e.getArg! 2 == loop && e.getArg! 3 == s
  if !(collectDag isV (← instantiateMVars (← g.getType))).isEmpty then return true
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if !(collectDag isV (← instantiateMVars d.type)).isEmpty then return true
  return false

open Tools.VedU1WireShare in
/-- `ved_loop_gen_mem s`: `ved_loop_gen_share s` with the loops of ALL goals (the goals of a memory body differ in the
spelling of the loop after the earlier simp steps; the share version reads the loops of the first goal only), and
each loop generalised (tuple taken apart, `Bool` components split) only in the goals that contain it -/
elab "ved_loop_gen_mem " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let mut loops : Array Expr := #[]
  for g in ← getGoals do
    for l in ← goalLoops g do
      unless loops.contains l do loops := loops.push l
  if loops.isEmpty then
    evalTactic (← `(tactic| ved_loop_gen $s))
    return
  for j in [0:loops.size] do
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_loop_gen_mem: malformed Signal.loop"
    let bare := !(← whnfR α).isAppOf ``Prod
    let n := (← Tools.VedU1Loop.stateComps α).length
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    let xs := (List.range (if bare then 1 else n + 1)).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x{j}_{i}")
    let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
    let mut gsOut : List MVarId := []
    for g in ← getGoals do
      setGoals [g]
      unless (← hasValAt g loops[j]! sE) do
        gsOut := gsOut ++ [g]
        continue
      let v ← g.withContext <| mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE]
      generalizeDag v (if bare then Name.mkSimple s!"ved_x{j}_0" else X.getId)
      unless bare do evalTactic (← `(tactic| all_goals rcases $X:ident with ⟨$pats,*⟩))
      for x in xs do
        let some d := (← withMainContext getLCtx).findFromUserName? x.getId | continue
        if (← whnfR d.type).isConstOf ``Bool then
          evalTactic (← `(tactic| all_goals cases $x:ident))
      gsOut := gsOut ++ (← getGoals)
    setGoals gsOut


open Tools.VedU1WireShare in
/-- `ved_loop_unfold_mem t`: rewrite `(Signal.loop F).val t` by the strong fixpoint equation, for every loop
whose value at `t` occurs in the goal (the walk of `ved_loop_unfold_share`, the lemma and the side
conditions changed) -/
elab "ved_loop_unfold_mem " " [" ex:Lean.Parser.Tactic.simpLemma,* "]" t:term : tactic => withMainContext do
  let tgt0 ← instantiateMVars (← getMainTarget)
  let tE ← instantiateMVars (← Term.elabTerm t (some (mkConst ``Nat)))
  let tE ← instantiateMVars tE
  let isOcc0 := fun (x : Expr) =>
    x.isAppOfArity ``Signal.val 4 && (x.getArg! 2).isAppOfArity ``Signal.loop 4
  let occs := fun (e : Expr) => do
    let mut out : Array Expr := #[]
    for x in collectDag isOcc0 e do
      if x.getArg! 3 == tE || (← withReducible <| isDefEq (x.getArg! 3) tE) then out := out.push x
    pure out
  if (← occs tgt0).isEmpty then return
  for _ in [0:64] do
    let tgt ← instantiateMVars (← getMainTarget)
    let some lhs := (← occs tgt)[0]? | break
    let L := lhs.getArg! 2
    let f4 := mkApp4 (mkConst ``Tools.VedMem.loop_val_unfold_strong) (L.getArg! 0) (L.getArg! 1) (L.getArg! 2) (L.getArg! 3)
    let ty ← whnf (← inferType f4)
    let h0T := ty.bindingDomain!
    let h0 ← mkFreshExprMVar h0T
    let ty ← whnf (ty.bindingBody!.instantiate1 h0)
    let hS ← mkFreshExprMVar ty.bindingDomain!
    runSubMem h0.mvarId! (← `(tactic| (intro _ _; rfl)))
    runSubMem hS.mvarId! (← `(tactic| ved_causal [$ex,*]))
    let lem ← instantiateMVars (mkApp3 f4 h0 hS (lhs.getArg! 3))
    let eqTy ← instantiateMVars (← inferType lem)
    let some (_, l, r) := eqTy.eq? | throwError "ved_loop_unfold_mem: unexpected equation {eqTy}"
    unless l == lhs do throwError "ved_loop_unfold_mem: the occurrence is not the left side of the equation"
    let xTy ← inferType lhs
    let motive ← withLocalDeclD `ved_x xTy fun xv =>
      mkLambdaFVars #[xv] (tgt.replace fun e => if e == lhs then some xv else none)
    let pf ← mkCongrArg motive lem
    let newTgt := tgt.replace fun e => if e == lhs then some r else none
    let g ← getMainGoal
    let g' ← g.replaceTargetEq newTgt pf
    replaceMainGoal [g']

end Tools.VedMemLoop
