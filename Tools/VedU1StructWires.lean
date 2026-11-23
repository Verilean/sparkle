import Lean
import Tools.VedU1StructSeqTac

/-!
# Opaque loop for the structure-with-registers script (`ved.sseq.wires`, sparkle-ved-multiout unit 10)

`Tools/VedU1StructSeq.lean` states the invariant `R` as one equation per register against `toNat (proj_k ((Signal.loop F).val t))`:
the loop term `Signal.loop F` (the unfolded body: every register's next-state chain) sits inside EVERY equation, inside every
register hypothesis, and again inside every output wire of the unfolded source value, so the goal read as a tree is
`registers x loop size` per use (measured: the 26-register toy's goal goes from 3757 to 1.84e7 nodes at `ved_ss_R`).

Under the option the loop is named ONCE and used through its value lemma:

* `IsLoop F L` (an opaque wrapper of `L = Signal.loop F`: `simp` does not eliminate the existential);
* `R ins t st := ∃ L, IsLoop F L ∧ ⋀_k st "n_k" = toNat (proj_k (L.val t))` (`ved_ss_R2`): register `k` at cycle `t` is the
  `k`-th component of the NAMED state `L`;
* `ved_ss_wit L hL hvsrc [helpers]`: the loop term of the source value `hvsrc` is replaced by `L`, and the per-cycle
  value lemma `hU : ∀ t, L.val (t + 1) = (F L).val (t + 1)` is stated and proved ONCE (`Tools.VedU1Loop.loop_val_unfold`; the body
  side conditions by the same `ved_ss_core_simp_big` as `ved_ss_unfold`);
* `isLoop_exists`: the existential of `R` at `s + 1` is instantiated with the same `L` (the loop does not depend on the cycle);
* `ved_ss_gen2 L s`: `ved_ss_gen` for the named state (`generalize L.val s = X`, then the components).

Untrusted tactics: the kernel checks what they build.  Default off; one loop only (several loops are refused with a message).
-/

namespace Tools.VedU1StructWires

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Loop Tools.VedU1StructSeqTac
open Lean Meta Elab Tactic

/-- `L` is the loop of `F`, behind a definition so that `simp` keeps `∃ L, IsLoop F L ∧ …` -/
def IsLoop {dom : DomainConfig} {α : Type} [Inhabited α] (F : Signal dom α → Signal dom α) (L : Signal dom α) : Prop :=
  L = Signal.loop F

/-- the existential of the invariant is instantiated by the named loop: `L` is `F`'s loop and there is only one -/
theorem isLoop_exists {dom : DomainConfig} {α : Type} [Inhabited α] {F : Signal dom α → Signal dom α}
    {L : Signal dom α} (h : IsLoop F L) (P : Signal dom α → Prop) : (∃ L', IsLoop F L' ∧ P L') = P L := by
  apply propext
  constructor
  · rintro ⟨L', hL', hP⟩
    have : L' = L := hL'.trans h.symm
    subst this
    exact hP
  · intro hP
    exact ⟨L, h, hP⟩

/-- the first `(applyIns …).val t` in `e` -/
partial def findApplyVal (e : Lean.Expr) : Option Lean.Expr :=
  if e.isApp && e.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal.val && e.getAppNumArgs == 4
      && (e.getArg! 2).getAppFn.isConstOf ``Tools.VedU1Contract.applyIns then some e
  else match e with
    | .app f a => (findApplyVal f).orElse fun _ => findApplyVal a
    | .lam _ t b _ => (findApplyVal t).orElse fun _ => findApplyVal b
    | .forallE _ t b _ => (findApplyVal t).orElse fun _ => findApplyVal b
    | .letE _ t v b _ => ((findApplyVal t).orElse fun _ => findApplyVal v).orElse fun _ => findApplyVal b
    | .mdata _ b => findApplyVal b
    | .proj _ _ b => findApplyVal b
    | _ => none

/-- `ved_ss_vsrc v hv`: the source value `(applyIns … f).val s` of the goal (after `simp only [srcOf]`) is generalised to the
variable `v`, `hv : v = (applyIns … f).val s` (the term as the goal has it, so that nothing has to match syntactically) -/
elab "ved_ss_vsrc " v:ident hv:ident : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := findApplyVal tgt | throwError "ved_ss_vsrc: no (applyIns …).val in the goal"
  let es ← Term.exprToSyntax e
  let hh := mkIdent `hvsrcRev
  evalTactic (← `(tactic| generalize $hh:ident : $es = $v:ident))
  evalTactic (← `(tactic| have $hv:ident := Eq.symm $hh))
  evalTactic (← `(tactic| clear $hh:ident))

/-- `ved_ss_R2 ins ["n₀", …] w₀, …`: assign the invariant `?R` as `∃ L, IsLoop F L ∧ ⋀ st n_k = toNat (proj_k (L.val t))`
(the loop term occurs once in `R`, not once per register) -/
elab "ved_ss_R2 " ins:ident " [" ns:str,* "]" ws:num,* : tactic => withMainContext do
  let insE ← elabTerm ins.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let loops := loopsOf tgt
  if loops.isEmpty then
    let shown := (← ppExpr tgt).pretty.take 3000
    throwError "ved_ss_R2: no Signal.loop in the goal: {shown}"
  unless loops.size == 1 do
    throwError "ved_ss_R2: ved.sseq.wires handles ONE Signal.loop, found {loops.size}"
  let ms ← getMVars tgt
  let mut rId? : Option MVarId := none
  for m in ms do
    if (← m.getTag).eraseMacroScopes == `R then rId? := some m
  let some rId := rId? | throwError "ved_ss_R2: no invariant mvar ?R in the goal"
  let regs := (ns.getElems.map (·.getString)).toList.zip (ws.getElems.map (·.getNat)).toList
  let loop := loops[0]!
  let some α := loop.getAppArgs[1]? | throwError "ved_ss_R2: malformed Signal.loop"
  let (cs, u) ← stateComps' α
  let widths ← cs.mapM fun c => compWidth c
  let some names := matchRegs widths regs
    | throwError "ved_ss_R2: the state components {widths} of the loop do not match the module registers {regs}"
  forallTelescope (← inferType (mkMVar rId)) fun xs _ => do
    unless xs.size == 3 do throwError "ved_ss_R2: unexpected invariant type"
    let L' := loop.replaceFVar insE xs[0]!
    let args := L'.getAppArgs
    unless args.size == 4 do throwError "ved_ss_R2: malformed Signal.loop"
    let sigTy ← inferType L'
    withLocalDeclD `L sigTy fun Lv => do
      let lv ← mkAppM ``Sparkle.Core.Signal.Signal.val #[Lv, xs[1]!]
      let mut eqs : Array Lean.Expr := #[]
      for i in [0:cs.length] do
        let c ← compToNat (← compProj' lv i cs.length u)
        eqs := eqs.push (← mkEq (mkApp xs[2]! (mkStrLit names[i]!)) c)
      let some last := eqs.back? | throwError "ved_ss_R2: no registers"
      let conj := (eqs.pop).foldr (fun e r => mkAnd e r) last
      let isL := mkApp5 (mkConst ``IsLoop) args[0]! args[1]! args[2]! args[3]! Lv
      let ex ← mkAppM ``Exists #[← mkLambdaFVars #[Lv] (mkAnd isL conj)]
      rId.assign (← mkLambdaFVars xs ex)

/-- `ved_ss_wit L hL hv [helpers]`: from `hL : IsLoop F L`, the value lemma `hU : ∀ t, L.val (t+1) = (F L).val (t+1)` (proved
once) and `hv` rewritten with the named loop (`Signal.loop F` replaced by `L`) -/
elab "ved_ss_wit " L:ident hL:ident hv:ident " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let hd ← getLocalDeclFromUserName hL.getId
  let ty ← instantiateMVars hd.type
  unless ty.isAppOfArity ``IsLoop 5 do throwError "ved_ss_wit: {hL} is not an IsLoop hypothesis: {ty}"
  let F := ty.getArg! 3
  let Fs ← Term.exprToSyntax F
  let hU := mkIdent `hU
  let hL' := mkIdent `hLeq
  let loopE := mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.loop) (ty.getArg! 0) (ty.getArg! 1) (ty.getArg! 2) F
  let loopS ← Term.exprToSyntax loopE
  evalTactic (← `(tactic| have $hL':ident : $L = $loopS := $hL))
  evalTactic (← `(tactic| have $hU:ident : ∀ t : Nat, ($L).val (t + 1) = ($Fs $L).val (t + 1) := by
    intro t
    subst $hL':ident
    refine Tools.VedU1Loop.loop_val_unfold $Fs ?h0 ?hS (t + 1)
    case h0 => intro _ _; rfl
    case hS => intro s1 s2 t h; ved_ss_core_simp_big [Signal.fst, Signal.snd, h, $hs,*]))
  evalTactic (← `(tactic| rw [← $hL':ident] at $hv:ident))
  evalTactic (← `(tactic| clear $hL':ident))

/-- `ved_ss_succ L s [helpers]`: the next state `L.val (s+1)` is taken apart ONCE: `y₀, …` generalised for its components, the value
lemma `hU s` expanded once (`F L` with `Prod.mk.injEq`: one equation `yₖ = eₖ` per register, `eₖ` its next-state wire over `L.val s`),
and every use of `L.val (s+1)` in the goal gets the (small) `eₖ`, not the whole tuple of all registers -/
elab "ved_ss_succ " L:ident s:ident " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let LE ← elabTerm L.raw none
  let v ← mkAppM ``Sparkle.Core.Signal.Signal.val #[LE, ← mkAppM ``HAdd.hAdd #[sE, mkNatLit 1]]
  let vs ← Term.exprToSyntax v
  let sigTy ← whnfR (← inferType LE)
  let some α := sigTy.getAppArgs[1]? | throwError "ved_ss_succ: malformed state signal"
  unless (← whnfR α).isAppOf ``Prod do throwError "ved_ss_succ: the state is not a tuple"
  let (cs, u) ← stateComps' α
  let n := cs.length + (if u then 1 else 0)
  let Y := mkIdent `ved_Ys
  let hX := mkIdent `hXs
  let hV := mkIdent `hVs
  let hU := mkIdent `hU
  let ys := (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_y_{i}")
  let pats ← ys.mapM fun y => `(Lean.Parser.Tactic.rcasesPatLo| $y:ident)
  evalTactic (← `(tactic| generalize $hX:ident : $vs = $Y:ident at *))
  evalTactic (← `(tactic| rcases $Y:ident with ⟨$pats,*⟩))
  -- the projections of the explicit tuple `(y₀, …, yₖ)` first (each equation keeps ONE `yₖ`), then the equations are substituted
  evalTactic (← `(tactic| try dsimp only))
  evalTactic (← `(tactic| have $hV:ident := $hU:ident $s))
  evalTactic (← `(tactic| rw [$hX:ident] at $hV:ident))
  evalTactic (← `(tactic| ved_ss_core_simp_big [Signal.fst, Signal.snd, Prod.mk.injEq, $hs,*] at $hV:ident))
  let hps ← (List.range cs.length).toArray.mapM fun i => pure (mkIdent (Name.mkSimple s!"ved_ye_{i}"))
  let hpats ← hps.mapM fun h => `(Lean.Parser.Tactic.rcasesPatLo| $h:ident)
  if cs.length == 1 then
    evalTactic (← `(tactic| have $(hps[0]!):ident := $hV:ident))
  else
    evalTactic (← `(tactic| obtain ⟨$hpats,*⟩ := $hV:ident))
  for h in hps do
    evalTactic (← `(tactic| subst $h:ident))
  evalTactic (← `(tactic| clear $hX:ident $hU:ident))

/-- `ved_ss_gen2 L s`: `ved_ss_gen` for the named state `L` (`generalize L.val s = X at *`, then its components) -/
elab "ved_ss_gen2 " L:ident s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let LE ← elabTerm L.raw none
  let v ← mkAppM ``Sparkle.Core.Signal.Signal.val #[LE, sE]
  let vs ← Term.exprToSyntax v
  let X := mkIdent `ved_X0
  evalTactic (← `(tactic| all_goals generalize $vs = $X at *))
  let sigTy ← whnfR (← inferType LE)
  let some α := sigTy.getAppArgs[1]? | throwError "ved_ss_gen2: malformed state signal"
  let (cs, u) ← stateComps' α
  let n := cs.length + (if u then 1 else 0)
  let xs := (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x0_{i}")
  let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
  if (← whnfR α).isAppOf ``Prod then
    evalTactic (← `(tactic| all_goals rcases $X:ident with ⟨$pats,*⟩))
  else if (← whnfR α).isConstOf ``Bool then
    evalTactic (← `(tactic| all_goals cases $X:ident))
  for x in xs do
    let some d := (← withMainContext getLCtx).findFromUserName? x.getId | continue
    if (← whnfR d.type).isConstOf ``Bool then
      evalTactic (← `(tactic| all_goals cases $x:ident))

end Tools.VedU1StructWires
