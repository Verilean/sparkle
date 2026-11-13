import Tools.VedU1Loop
import Tools.VedU1Entry
import Tools.VedU1MultiSeqLemmas

/-!
# Loop state tuples that do not end in `Unit` (packed result with registers)

`Tools.VedU1Loop.ved_loop_R` / `ved_loop_gen` read a loop state `α × β × … × Unit` (a `circuit do`
block's tuple) and stop at the first non-product: a state whose LAST component is a scalar
(`BitVec 6 × … × Bool`, `IP.RV32.Divider.DivState`) lost that component and the match against the
module's registers failed.  These variants take the last scalar component too.  Untrusted tactics:
the kernel checks the proof they build.
-/

namespace Tools.VedU1MultiSeqLoop

open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Loop
open Lean Meta Elab Tactic

/-- the component types of a right-nested state tuple, ending in `Unit` or in a last scalar
component; the flag says whether the tuple ends in `Unit` -/
partial def stateComps' (ty : Lean.Expr) : MetaM (List Lean.Expr × Bool) := do
  let ty ← whnfR ty
  match ty.getAppFnArgs with
  | (``Prod, #[a, b]) =>
    let (r, u) ← stateComps' b
    return ((← whnfR a) :: r, u)
  | (``Unit, #[]) => return ([], true)
  | _ => return ([ty], false)

/-- `i`-th component of a right-nested tuple value of `n` components (`unit` : ends in `Unit`) -/
partial def compProj' (e : Lean.Expr) (i n : Nat) (unit : Bool) : MetaM Lean.Expr := do
  if i + 1 == n && !unit then
    if i == 0 then return e else compProj' (← mkAppM ``Prod.snd #[e]) (i - 1) (n - 1) unit
  else if i == 0 then mkAppM ``Prod.fst #[e]
  else compProj' (← mkAppM ``Prod.snd #[e]) (i - 1) (n - 1) unit

/-- `ved_loop_R'`: `ved_loop_R` for tuples that may end in a scalar component. -/
elab "ved_loop_R' " ins:ident " [" ns:str,* "]" ws:num,* : tactic => withMainContext do
  let insE ← elabTerm ins.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let loops := loopsOf tgt
  if loops.isEmpty then
    let shown := (← ppExpr tgt).pretty.take 3000
    throwError "ved_loop_R': no Signal.loop in the goal: {shown}"
  let ms ← getMVars tgt
  let mut rId? : Option MVarId := none
  for m in ms do
    if (← m.getTag).eraseMacroScopes == `R then rId? := some m
  let some rId := rId? | throwError "ved_loop_R': no invariant mvar ?R in the goal"
  let regs := (ns.getElems.map (·.getString)).toList.zip (ws.getElems.map (·.getNat)).toList
  let mut compsOf : Array (List Lean.Expr × Bool) := #[]
  for L in loops do
    let some α := L.getAppArgs[1]? | throwError "ved_loop_R': malformed Signal.loop"
    compsOf := compsOf.push (← stateComps' α)
  let widths ← (compsOf.toList.flatMap (·.1)).mapM fun c => compWidth c
  let some names := matchRegs widths regs
    | throwError "ved_loop_R': the state components {widths} of {loops.size} loop(s) {compsOf.map (·.1.length)} do not match the module registers {regs}"
  forallTelescope (← inferType (mkMVar rId)) fun xs _ => do
    unless xs.size == 3 do throwError "ved_loop_R': unexpected invariant type"
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
    let some last := eqs.back? | throwError "ved_loop_R': no registers"
    let body := (eqs.pop).foldr (fun e r => mkAnd e r) last
    rId.assign (← mkLambdaFVars xs body)

/-- `ved_loop_gen' s`: `ved_loop_gen` for tuples that may end in a scalar component. -/
elab "ved_loop_gen' " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let loops := loopsOf tgt
  if loops.isEmpty then throwError "ved_loop_gen': no Signal.loop in the goal"
  for j in [0:loops.size] do
    let v ← mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE]
    let vs ← Term.exprToSyntax v
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    evalTactic (← `(tactic| all_goals generalize $vs = $X at *))
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_loop_gen': malformed Signal.loop"
    let (cs, u) ← stateComps' α
    let n := cs.length + (if u then 1 else 0)
    let xs := (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x{j}_{i}")
    let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
    evalTactic (← `(tactic| all_goals rcases $X:ident with ⟨$pats,*⟩))
    for x in xs do
      let some d := (← withMainContext getLCtx).findFromUserName? x.getId | continue
      if (← whnfR d.type).isConstOf ``Bool then
        evalTactic (← `(tactic| all_goals cases $x:ident))

/-- `ved_core_simp_big [lemmas] (at loc)?`: `ved_core_simp` with the simp step budget raised
(`maxSteps`): a packed result with registers unfolds the whole body of every register and every
projection in one `simp`. -/
elab "ved_core_simp_big " "[" ex:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? : tactic => do
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
    | some l => `(tactic| ved_core_simp [$all,*] $l:location)
    | none => `(tactic| ved_core_simp [$all,*])
  let stx ← liftMacroM (expandMacros base)
  let tmpl ← `(tactic| simp (config := { maxSteps := 2000000 }) [Nat.add_zero])
  -- the `simp` node's second argument is its (empty) `optConfig`: put the raised one there
  let stx' := stx.setArg 1 (tmpl.raw.getArg 1)
  evalTactic stx'

/-- `ved_loop_unfold' [defs] t`: `ved_loop_unfold` for a loop whose body is a named definition
applied to its inputs (`Signal.loop (dividerLoopBody a b c)`): the step side condition unfolds
`defs` first (the body is not a lambda until then). -/
macro "ved_loop_unfold' " "[" hs:Lean.Parser.Tactic.simpLemma,* "]" t:term : tactic =>
  `(tactic| repeat (rw [Tools.VedU1Loop.loop_val_unfold _ ?h0 ?hS $t]
                    case h0 => intro _ _; rfl
                    case hS => intro s1 s2 t h; ved_core_simp_big [$hs,*, Signal.fst, Signal.snd, h]))

/-- `ved_loop_unfold1 t`: one rewrite of `ved_loop_unfold` (debugging: the failure is not hidden
by `repeat`). -/
macro "ved_loop_unfold1 " "[" hs:Lean.Parser.Tactic.simpLemma,* "]" t:term : tactic =>
  `(tactic| (rw [Tools.VedU1Loop.loop_val_unfold _ ?h0 ?hS $t]
             case h0 => intro _ _; rfl
             case hS => intro s1 s2 t h; ved_core_simp_big [$hs,*, Signal.fst, Signal.snd, h]))

end Tools.VedU1MultiSeqLoop
