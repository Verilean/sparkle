import Lean
import Tools.VedU1Contract
import Tools.VedU1Lemmas
import Tools.VedU1LemmasExt1
import Tools.VedU1Loop
import Tools.VedU1ScriptSeqGen
import Tools.VedU1MultiSeqLemmas

/-!
# Tactics of the structure-with-registers script (`Tools/VedU1StructSeq.lean`)

The tactics `Tools/VedU1MultiSeqLoop.lean` and `Tools/VedU1Entry.lean` give the loop path, repeated here
under the names `ved_ss_*` because the generator has to be imported BY `Tools/VedU1Entry.lean` (the
standard entry dispatches to it), so it cannot import either of them.  Untrusted tactics: the
kernel checks what they build.  The one change from the originals: a loop state that ends in `PUnit`
(`Unit` after `whnfR`, a `circuit do` block's tuple) is read as ending in `Unit`, not as one more
component of unknown width.
-/

namespace Tools.VedU1StructSeqTac

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Loop

syntax (name := vedSsCoreSimp) "ved_ss_core_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| ved_ss_core_simp [$ex,*] $[$loc]?) =>
    `(tactic| simp [stepModule, evalAssigns, regNexts, memNexts, Sparkle.IR.Semantics.evalExpr,
        Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalExpr.go,
        widthOf, seedIn, applyNexts, declWidth, srcOf, contractOf, applyIns, 
        Signal.register, OTy.obs, PTy.obs, PTy.sig, mask, Tools.VedU1ScriptSeq.or_mod _ _ _ _ rfl,
        Nat.shiftRight_eq_div_pow, Tools.VedU1Lemmas.evalOp_not_lit, 
        Tools.VedU1Lemmas.compl_val,
        Tools.VedU1Lemmas.evalOp_and_lit, Tools.VedU1Lemmas.evalOp_or_lit,
        Tools.VedU1Lemmas.evalOp_xor_lit, Tools.VedU1Lemmas.and_val,
        Tools.VedU1Lemmas.or_val, Tools.VedU1Lemmas.xor_val,
        Tools.VedU1Lemmas.evalOp_add_lit, Tools.VedU1Lemmas.add_val, BitVec.toNat_add,
        Tools.VedU1Lemmas.evalOp_sub_lit, Tools.VedU1Lemmas.sub_val, BitVec.toNat_sub,
        Tools.VedU1Lemmas.evalOp_mux_lit, Tools.VedU1Lemmas.mux_val,
        Tools.VedU1Lemmas.evalOp_eq_lit, Tools.VedU1Lemmas.evalOp_mul_lit, Tools.VedU1Lemmas.evalOp_shl_lit, Tools.VedU1Lemmas.evalOp_shr_lit, Tools.VedU1Lemmas.evalOp_lt_u_lit, Tools.VedU1Lemmas.evalOp_le_u_lit, Tools.VedU1Lemmas.evalOp_gt_u_lit, Tools.VedU1Lemmas.evalOp_ge_u_lit, Tools.VedU1Lemmas.evalOp_lt_s_lit, Tools.VedU1Lemmas.mul_val, Tools.VedU1Lemmas.add_val_sc, Tools.VedU1Lemmas.add_val_cs, Tools.VedU1Lemmas.sub_val_sc, Tools.VedU1Lemmas.sub_val_cs, Tools.VedU1Lemmas.mul_val_sc, Tools.VedU1Lemmas.mul_val_cs, Tools.VedU1Lemmas.and_val_sc, Tools.VedU1Lemmas.and_val_cs, Tools.VedU1Lemmas.or_val_sc, Tools.VedU1Lemmas.or_val_cs, Tools.VedU1Lemmas.xor_val_sc, Tools.VedU1Lemmas.xor_val_cs, Tools.VedU1Lemmas.shl_val_sc, Tools.VedU1Lemmas.shl_val_cs, Tools.VedU1Lemmas.shr_val_sc, Tools.VedU1Lemmas.shr_val_cs, Tools.VedU1Lemmas.append_def_sc, Tools.VedU1Lemmas.append_def_cs, Tools.VedU1Lemmas.evalOp_asr_lit, Tools.VedU1Lemmas.toNat_sshiftRight', Tools.VedU1Lemmas.mask_emod, Tools.VedU1Lemmas.slt_eq, Tools.VedU1Lemmas.ult_eq, Signal.slt, Signal.ult, Signal.ule, Signal.ashr, Signal.lt, Signal.le, Tools.VedU1Lemmas.bool_and_val, Tools.VedU1Lemmas.bool_or_val, Tools.VedU1Lemmas.bool_xor_val, Tools.VedU1Lemmas.bool_compl_val, Tools.VedU1Lemmas.evalOp_not_raw, Tools.VedU1Lemmas.evalOp_and_raw, Tools.VedU1Lemmas.evalOp_or_raw, Tools.VedU1Lemmas.evalOp_xor_raw, Tools.VedU1Lemmas.evalOp_sub_raw, Tools.VedU1Lemmas.shl_val, Tools.VedU1Lemmas.shr_val, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', Tools.VedU1Lemmas.pure_val, Tools.VedU1Lemmas.append_def, Tools.VedU1Lemmas.toNat_append', Sparkle.Core.Signal.Signal.map,
        Seq.seq, Signal.beq, Signal.seq, Signal.ap, Sparkle.Core.Signal.bundle2, BitVec.toNat_append,
        BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, Nat.mod_eq_of_lt, Functor.map, Signal.map, BitVec.toNat_not, BitVec.toNat_ofNat,
        List.lookup, Option.getD_some, Option.getD_none, -Nat.reduceAdd, $ex,*] $[$loc]?)


syntax (name := vedSsWideSimp) "ved_ss_wide_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| ved_ss_wide_simp [$ex,*] $[$loc]?) =>
    `(tactic| simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Tools.VedU1Lemmas.bit1_eq, Tools.VedU1Lemmas.toNat_append', BitVec.toNat_neg, BitVec.toInt_eq_toNat_cond, Sparkle.IR.Semantics.toSigned, Tools.VedU1Lemmas.or_hi_8, Tools.VedU1Lemmas.or_hi_16, Tools.VedU1Lemmas.or_hi_24, Tools.VedU1Lemmas.or_hi_32, Tools.VedU1Lemmas.or_hi_40, Tools.VedU1Lemmas.or_hi_48, Tools.VedU1Lemmas.or_hi_64, Tools.VedU1Lemmas.and_mod_r, Tools.VedU1Lemmas.and_mod_l, Tools.VedU1Lemmas.toNat_sshiftRight', Tools.VedU1Lemmas.toInt_ofNat_toSigned, Tools.VedU1Lemmas.beq_ofNat, Tools.VedU1Lemmas.toNat_decide_ite, Tools.VedU1Lemmas.toNat_not_decide_ite, Tools.VedU1Lemmas.toNat_ite_true, Tools.VedU1Lemmas.ofNat_eq_iff, Tools.VedU1Lemmas.ule_decide, Tools.VedU1Lemmas.ult_decide, Tools.VedU1Lemmas.xor_one_one, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, apply_ite BitVec.toNat, -Nat.reduceAdd, $ex,*] $[$loc]?)


syntax (name := vedSsLoopWideSimp) "ved_ss_loopw_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| ved_ss_loopw_simp [$ex,*] $[$loc]?) =>
    `(tactic| simp -implicitDefEqProofs (maxSteps := 4000000) [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Tools.VedU1Lemmas.bit1_eq, Tools.VedU1Lemmas.toNat_append', BitVec.toNat_neg, BitVec.toInt_eq_toNat_cond, Sparkle.IR.Semantics.toSigned, Tools.VedU1Lemmas.or_hi_8, Tools.VedU1Lemmas.or_hi_16, Tools.VedU1Lemmas.or_hi_24, Tools.VedU1Lemmas.or_hi_32, Tools.VedU1Lemmas.or_hi_40, Tools.VedU1Lemmas.or_hi_48, Tools.VedU1Lemmas.or_hi_64, Tools.VedU1Lemmas.and_mod_r, Tools.VedU1Lemmas.and_mod_l, Tools.VedU1Lemmas.toNat_sshiftRight', Tools.VedU1Lemmas.toInt_ofNat_toSigned, Tools.VedU1Lemmas.beq_ofNat, Tools.VedU1Lemmas.toNat_decide_ite, Tools.VedU1Lemmas.toNat_not_decide_ite, Tools.VedU1Lemmas.toNat_ite_true, Tools.VedU1Lemmas.ofNat_eq_iff, Tools.VedU1Lemmas.ule_decide, Tools.VedU1Lemmas.ult_decide, Tools.VedU1Lemmas.xor_one_one, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, apply_ite BitVec.toNat, -Nat.reduceAdd, $ex,*] $[$loc]?)


syntax (name := vedSsLoopClose) "ved_ss_loop_close " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| ved_ss_loop_close [$ex,*]) =>
    `(tactic| ((try ved_ss_loopw_simp [$ex,*]) <;> (first | omega | ((repeat' (split <;> (try simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, Nat.add_zero, Nat.sub_zero, eq_self, ↓reduceIte, Nat.reduceEqDiff, not_true_eq_false, if_true, if_false, true_and, and_true, false_and, and_false, or_false, false_or, or_true, true_or, not_false_eq_true, *]))) <;> (try simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, Nat.reduceDiv, Tools.VedU1Lemmas.xor_one_one, not_true_eq_false, Nat.zero_and, Nat.and_zero, Nat.one_and_eq_mod_two, Nat.and_one_is_mod, Nat.zero_xor, Nat.xor_zero, true_and, and_true, false_and, and_false, or_false, false_or, or_true, true_or, not_false_eq_true, true_iff, iff_true, false_iff, iff_false, Nat.reduceSub, Nat.add_zero, Nat.sub_zero, Nat.zero_add, Int.bmod_def, Int.natCast_zero, Int.add_zero, Int.sub_zero] at *) <;> (try ved_or_lit) <;> (try ved_bit_simp) <;> (try (repeat' split)) <;> (try simp only [Nat.or_zero, Nat.zero_or]) <;> (try ved_bits_facts) <;> omega))))


open Lean Meta Elab Tactic

/-- the component types of a right-nested state tuple, ending in `Unit` or in a last scalar
component; the flag says whether the tuple ends in `Unit` -/
partial def stateComps' (ty : Lean.Expr) : MetaM (List Lean.Expr × Bool) := do
  let ty ← whnfR ty
  match ty.getAppFnArgs with
  | (``Prod, #[a, b]) =>
    let (r, u) ← stateComps' b
    return ((← whnfR a) :: r, u)
  | (``PUnit, _) => return ([], true)
  | (``Unit, #[]) => return ([], true)
  | _ => return ([ty], false)

/-- `i`-th component of a right-nested tuple value of `n` components (`unit` : ends in `Unit`) -/
partial def compProj' (e : Lean.Expr) (i n : Nat) (unit : Bool) : MetaM Lean.Expr := do
  if i + 1 == n && !unit then
    if i == 0 then return e else compProj' (← mkAppM ``Prod.snd #[e]) (i - 1) (n - 1) unit
  else if i == 0 then mkAppM ``Prod.fst #[e]
  else compProj' (← mkAppM ``Prod.snd #[e]) (i - 1) (n - 1) unit

/-- `ved_ss_R`: `ved_loop_R` for tuples that may end in a scalar component. -/
elab "ved_ss_R " ins:ident " [" ns:str,* "]" ws:num,* : tactic => withMainContext do
  let insE ← elabTerm ins.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let loops := loopsOf tgt
  if loops.isEmpty then
    let shown := (← ppExpr tgt).pretty.take 3000
    throwError "ved_ss_R: no Signal.loop in the goal: {shown}"
  let ms ← getMVars tgt
  let mut rId? : Option MVarId := none
  for m in ms do
    if (← m.getTag).eraseMacroScopes == `R then rId? := some m
  let some rId := rId? | throwError "ved_ss_R: no invariant mvar ?R in the goal"
  let regs := (ns.getElems.map (·.getString)).toList.zip (ws.getElems.map (·.getNat)).toList
  let mut compsOf : Array (List Lean.Expr × Bool) := #[]
  for L in loops do
    let some α := L.getAppArgs[1]? | throwError "ved_ss_R: malformed Signal.loop"
    compsOf := compsOf.push (← stateComps' α)
  let widths ← (compsOf.toList.flatMap (·.1)).mapM fun c => compWidth c
  let some names := matchRegs widths regs
    | throwError "ved_ss_R: the state components {widths} of {loops.size} loop(s) {compsOf.map (·.1.length)} do not match the module registers {regs}"
  forallTelescope (← inferType (mkMVar rId)) fun xs _ => do
    unless xs.size == 3 do throwError "ved_ss_R: unexpected invariant type"
    let mut eqs : Array Lean.Expr := #[]
    let mut k := 0
    for j in [0:loops.size] do
      let L' := loops[j]!.replaceFVar insE xs[0]!
      let lv ← mkAppM ``Sparkle.Core.Signal.Signal.val #[L', xs[1]!]
      let (cs, u) := compsOf[j]!
      for i in [0:cs.length] do
        let c ← compToNat (← compProj' lv i cs.length u)
        eqs := eqs.push (← mkEq (mkApp xs[2]! (mkStrLit names[k]!)) c)
        k := k + 1
    let some last := eqs.back? | throwError "ved_ss_R: no registers"
    let body := (eqs.pop).foldr (fun e r => mkAnd e r) last
    rId.assign (← mkLambdaFVars xs body)

/-- `ved_ss_gen s`: `ved_loop_gen` for tuples that may end in a scalar component. -/
elab "ved_ss_gen " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let loops := loopsOf tgt
  if loops.isEmpty then throwError "ved_ss_gen: no Signal.loop in the goal"
  for j in [0:loops.size] do
    let v ← mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE]
    let vs ← Term.exprToSyntax v
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    evalTactic (← `(tactic| all_goals generalize $vs = $X at *))
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_ss_gen: malformed Signal.loop"
    let (cs, u) ← stateComps' α
    let n := cs.length + (if u then 1 else 0)
    let xs := (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x{j}_{i}")
    let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
    evalTactic (← `(tactic| all_goals rcases $X:ident with ⟨$pats,*⟩))
    for x in xs do
      let some d := (← withMainContext getLCtx).findFromUserName? x.getId | continue
      if (← whnfR d.type).isConstOf ``Bool then
        evalTactic (← `(tactic| all_goals cases $x:ident))

/-- The leaf equations of `x₁ + … = y₁ + …` / `c * x = c * y` (same shape on both sides), by structural
descent: each leaf is closed on its own, which avoids splitting every condition of every field of
a packed value at once.  Returns the goal itself when the two sides have no common shape. -/
partial def leafGoals (g : MVarId) : MetaM (List MVarId) := do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some (ty, l, r) := t.eq? | return [g]
  unless ty.isConstOf ``Nat do return [g]
  if l.isAppOfArity ``HAdd.hAdd 6 && r.isAppOfArity ``HAdd.hAdd 6 then
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``Tools.VedU1MultiSeqLemmas.add_congr_nat)
    return (← gs.mapM leafGoals).flatten
  if l.isAppOfArity ``HMul.hMul 6 && r.isAppOfArity ``HMul.hMul 6 && (l.getArg! 4) == (r.getArg! 4)
      && (l.getArg! 4).nat?.isSome then
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``Tools.VedU1MultiSeqLemmas.mul_congr_nat)
    return (← gs.mapM leafGoals).flatten
  return [g]

/-- `ved_leafwise`: replace the main goal by its leaf equations (see `leafGoals`). -/
elab "ved_ss_leafwise" : tactic => do
  let g ← getMainGoal
  let gs ← leafGoals g
  replaceMainGoal gs

/-- `ved_timed tac`: run `tac` on the main goal and print the elapsed milliseconds and the size of
the goal to stderr (debugging the per-goal cost of the closing stage). -/
elab "ved_ss_timed " t:tactic : tactic => do
  let g ← getMainGoal
  let sz := (← instantiateMVars (← g.getType)).approxDepth
  if let some path ← IO.getEnv "VED_MS_LOG" then
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn s!"VED MS start {← IO.monoMsNow} depth={sz}"
    h.flush
  let t0 ← IO.monoMsNow
  let r ← try evalTactic t; pure true catch _ => pure false
  let t1 ← IO.monoMsNow
  let msg := s!"VED MS goal {g.name} depth={sz} {t1 - t0}ms ok={r}"
  match ← IO.getEnv "VED_MS_LOG" with
  | some path =>
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn msg
    h.flush
  | none => IO.eprintln msg
  unless r do throwError "ved_timed: failed"

/-- all `a ^^^ b` on `Nat` with a numeral operand in `e` (each distinct term once) -/
partial def natXorLits (e : Lean.Expr) : Array Lean.Expr := Id.run do
  let mut out : Array Lean.Expr := #[]
  let mut todo : Array Lean.Expr := #[e]
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if x.isAppOfArity ``HXor.hXor 6 && (x.getArg! 0).isConstOf ``Nat
        && ((x.getArg! 4).nat?.isSome || (x.getArg! 5).nat?.isSome) then
      unless out.contains x do out := out.push x
    match x with
    | .app f a => todo := (todo.push a).push f
    | .lam _ t b _ => todo := (todo.push b).push t
    | .forallE _ t b _ => todo := (todo.push b).push t
    | .letE _ t v b _ => todo := ((todo.push b).push v).push t
    | .mdata _ b => todo := todo.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- `ved_xor_ones`: rewrite `x ^^^ c` for a numeral `c = 2^k - 1` as `c - x` when `x < 2^k` (proved by
`omega`): the bit-clear `a &&& ~~~b` of a register update. -/
elab "ved_ss_xor_ones" : tactic => withMainContext do
  let mut skip : Array Lean.Expr := #[]
  for _ in [0:64] do
    let tgt ← instantiateMVars (← getMainTarget)
    let cands := (natXorLits tgt).filter (!skip.contains ·)
    let some t := cands[0]? | break
    let a := t.getArg! 4
    let b := t.getArg! 5
    let mut done := false
    for (x, c, swapped) in [(a, b, false), (b, a, true)] do
      if done then break
      let some cn := c.nat? | continue
      let some k := (List.range 130).find? (fun k => cn + 1 == 2 ^ k) | continue
      let hcP ← mkEq (← mkAppM ``HAdd.hAdd #[c, mkNatLit 1]) (← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit k])
      let hc ← mkDecideProof hcP
      let p ← mkAppM ``LT.lt #[x, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit k]]
      let some hx ← omegaProof? p | continue
      let lem ← mkAppM ``Tools.VedU1MultiSeqLemmas.xor_ones #[x, c, mkNatLit k, hc, hx]
      let lemS ← Term.exprToSyntax lem
      if swapped then
        let cs ← Term.exprToSyntax c
        let xs ← Term.exprToSyntax x
        evalTactic (← `(tactic| rw [Nat.xor_comm $cs $xs, $lemS:term]))
      else
        evalTactic (← `(tactic| rw [$lemS:term]))
      done := true
    unless done do skip := skip.push t

/-- `ved_ss_core_simp_big [lemmas] (at loc)?`: `ved_core_simp` with the simp step budget raised
(`maxSteps`): a packed result with registers unfolds the whole body of every register and every
projection in one `simp`. -/
elab "ved_ss_core_simp_big " "[" ex:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? : tactic => do
  let more : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    #[``Tools.VedU1MultiSeqLemmas.add_val_scI, ``Tools.VedU1MultiSeqLemmas.add_val_csI,
      ``Tools.VedU1MultiSeqLemmas.sub_val_scI, ``Tools.VedU1MultiSeqLemmas.sub_val_csI,
      ``Tools.VedU1MultiSeqLemmas.mul_val_scI, ``Tools.VedU1MultiSeqLemmas.mul_val_csI,
      ``Tools.VedU1MultiSeqLemmas.and_val_scI, ``Tools.VedU1MultiSeqLemmas.and_val_csI,
      ``Tools.VedU1MultiSeqLemmas.or_val_scI, ``Tools.VedU1MultiSeqLemmas.or_val_csI,
      ``Tools.VedU1MultiSeqLemmas.xor_val_scI, ``Tools.VedU1MultiSeqLemmas.xor_val_csI,
      ``Tools.VedU1MultiSeqLemmas.shl_val_scI, ``Tools.VedU1MultiSeqLemmas.shl_val_csI,
      ``Tools.VedU1MultiSeqLemmas.shr_val_scI, ``Tools.VedU1MultiSeqLemmas.shr_val_csI,
      ``Tools.VedU1MultiSeqLemmas.append_val_scI, ``Tools.VedU1MultiSeqLemmas.append_val_csI].mapM
      fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let all : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems (ex.getElems ++ more)
  let base ← match loc with
    | some l => `(tactic| ved_ss_core_simp [$all,*] $l:location)
    | none => `(tactic| ved_ss_core_simp [$all,*])
  let stx ← liftMacroM (expandMacros base)
  let tmpl ← `(tactic| simp (config := { maxSteps := 2000000 }) [Nat.add_zero])
  -- the `simp` node's second argument is its (empty) `optConfig`: put the raised one there
  let stx' := stx.setArg 1 (tmpl.raw.getArg 1)
  evalTactic stx'

/-- `ved_ss_unfold [defs] t`: `ved_loop_unfold` for a loop whose body is a named definition
applied to its inputs (`Signal.loop (dividerLoopBody a b c)`): the step side condition unfolds
`defs` first (the body is not a lambda until then). -/
macro "ved_ss_unfold " "[" hs:Lean.Parser.Tactic.simpLemma,* "]" t:term : tactic =>
  `(tactic| repeat (rw [Tools.VedU1Loop.loop_val_unfold _ ?h0 ?hS $t]
                    case h0 => intro _ _; rfl
                    case hS => intro s1 s2 t h; ved_ss_core_simp_big [Signal.fst, Signal.snd, h, $hs,*]))

/-- `ved_ss_unfold1 t`: one rewrite of `ved_loop_unfold` (debugging: the failure is not hidden
by `repeat`). -/
macro "ved_ss_unfold1 " "[" hs:Lean.Parser.Tactic.simpLemma,* "]" t:term : tactic =>
  `(tactic| (rw [Tools.VedU1Loop.loop_val_unfold _ ?h0 ?hS $t]
             case h0 => intro _ _; rfl
             case hS => intro s1 s2 t h; ved_ss_core_simp_big [Signal.fst, Signal.snd, h, $hs,*]))



end Tools.VedU1StructSeqTac
