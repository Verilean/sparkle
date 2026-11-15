import Tools.VedU1ScriptSeqGen
import Tools.VedU1Packed
import Tools.VedU1MultiSeqLoop
import Tools.VedU1MultiSeqLemmas
import Tools.VedU1WireShare

/-!
# Packed result with registers: the per-statement script (`sparkle-ved-packed-seq2`)

`Tools.VedU1PackedEntry` proved a packed body with registers by the FLAT loop script
(`Tools.VedU1MultiSeq.packedLoopScript`): the loop state is split by `cases` on every `Bool`
component BEFORE the whole body is rewritten, so each rewriting stage runs once per case (16 times
for a controller with four `Bool` registers) and the closing stage repeats the same arithmetic goal
in every case.  This is the script of `Tools.VedU1ScriptSeqGen.seqLoopScript` (one `step_seq`, one
equation per statement, `Bool` state components split LAST and only after the unused hypotheses
are cleared) over the packed statement: the contract is `PContract.core C`, the declaration
`packedF C.tbl f`, and the port's value is read through `srcOf_packed` / `OTy_packNat_pair`.
The contract (`PContract`, ShapeCore, reset held 0, every slice) and the statement are the
packed entry's; only the proof script differs.  Untrusted: the kernel checks the result.
-/

/-- Debugging only: `ved.packedseq2.dbg 1` prints why the per-statement first attempt failed (and its time); 2 also stops after a failed first attempt; 3 adds `VED PKMARK` time/heartbeat marks between the script's phases. -/
register_option ved.packedseq2.dbg : Nat := {
  defValue := 0
  descr := "ved.packedseq2.dbg: 1 = print the failure of the packed per-statement first attempt, 2 = and stop, 3 = timing marks"
}

namespace Tools.VedU1PackedSeq2

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder
open Sparkle.Core.Signal Sparkle.Core.Domain
open Tools.VedU1Contract Tools.VedU1Packed Tools.VedU1ScriptSeq

open Lean Meta Elab Tactic in
/-- `ved_pk_mark "label"`: debugging only (`ved.packedseq2.dbg 3`): print the monotonic milliseconds and the
heartbeat counter (differences of two marks are the cost of the phase between them). -/
elab "ved_pk_mark " l:str : tactic => do
  if ved.packedseq2.dbg.get (← getOptions) < 3 then return
  IO.eprintln s!"VED PKMARK {l.getString} {← IO.monoMsNow} {(← IO.getNumHeartbeats) / 1000000}"


theorem OTy_packNat_pair_mod (a b : OTy) (v : (OTy.pair a b).val) :
    (OTy.pair a b).packNat v =
      a.packNat v.1 % 2 ^ a.width * 2 ^ b.width + b.packNat v.2 % 2 ^ b.width := by
  rw [Tools.VedU1MultiSeqLemmas.OTy_packNat_pair,
    Nat.mod_eq_of_lt (Tools.VedU1MultiSeqLemmas.OTy_packNat_lt a v.1),
    Nat.mod_eq_of_lt (Tools.VedU1MultiSeqLemmas.OTy_packNat_lt b v.2)]

theorem ite_one_mod2_eq_one (p : Prop) [Decidable p] : ((if p then 1 else 0) % 2 = 1) = p := by
  by_cases h : p <;> simp [h]

theorem ite_one_mod2_eq_zero (p : Prop) [Decidable p] : ((if p then 1 else 0) % 2 = 0) = ¬p := by
  by_cases h : p <;> simp [h]

theorem mul_congr_nat_r {a b : Nat} (c : Nat) (h : a = b) : a * c = b * c := by subst h; rfl

theorem mod_congr_nat {a b : Nat} (n : Nat) (h : a = b) : a % n = b % n := by subst h; rfl

open Lean Meta Elab Tactic in
/-- The leaf equations of a packed equation whose two sides are the same concatenation
`x₁ % 2^w₁ * 2^k₁ + (rest₁ % 2^k₁)` / `c * x + y` (the module's nested concatenation against the declaration's
`OTy_packNat_pair_mod`): descent through `+`, `c * _` / `_ * c` (the same literal) and `_ % n` over a sum
(the same literal).  A goal of another shape is a leaf. -/
partial def pkLeafGoals (g : MVarId) : MetaM (List MVarId) := do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some (ty, l, r) := t.eq? | return [g]
  unless ty.isConstOf ``Nat do return [g]
  let isAdd (e : Lean.Expr) := e.isAppOfArity ``HAdd.hAdd 6
  if isAdd l && isAdd r then
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``Tools.VedU1MultiSeqLemmas.add_congr_nat)
    return (← gs.mapM pkLeafGoals).flatten
  if l.isAppOfArity ``HMul.hMul 6 && r.isAppOfArity ``HMul.hMul 6 then
    if (l.getArg! 4) == (r.getArg! 4) && (l.getArg! 4).nat?.isSome then
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``Tools.VedU1MultiSeqLemmas.mul_congr_nat)
      return (← gs.mapM pkLeafGoals).flatten
    if (l.getArg! 5) == (r.getArg! 5) && (l.getArg! 5).nat?.isSome then
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``mul_congr_nat_r)
      return (← gs.mapM pkLeafGoals).flatten
  if l.isAppOfArity ``HMod.hMod 6 && r.isAppOfArity ``HMod.hMod 6 && (l.getArg! 5) == (r.getArg! 5)
      && isAdd (l.getArg! 4) && isAdd (r.getArg! 4) then
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``mod_congr_nat)
    return (← gs.mapM pkLeafGoals).flatten
  return [g]

open Lean Meta Elab Tactic in
/-- `ved_pk_leafwise`: replace every goal by its leaf equations (`pkLeafGoals`). -/
elab "ved_pk_leafwise" : tactic => do
  let gs ← getGoals
  let mut out : Array MVarId := #[]
  for g in gs do out := out ++ (← pkLeafGoals g).toArray
  setGoals out.toList


/-- `ved_pk_simp`: `ved_seq_simp` with the signal-literal lemmas of `ved_core_simp_big` (`x &&& 8#32` where the literal is a
`Signal` by `OfNat`; the loop bodies of a packed result use them). -/
syntax (name := vedPkSimp) "ved_pk_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| ved_pk_simp [$ex,*] $[$loc]?) =>
    `(tactic| ved_seq_simp [Tools.VedU1MultiSeqLemmas.add_val_scI, Tools.VedU1MultiSeqLemmas.add_val_csI,
      Tools.VedU1MultiSeqLemmas.sub_val_scI, Tools.VedU1MultiSeqLemmas.sub_val_csI,
      Tools.VedU1MultiSeqLemmas.mul_val_scI, Tools.VedU1MultiSeqLemmas.mul_val_csI,
      Tools.VedU1MultiSeqLemmas.and_val_scI, Tools.VedU1MultiSeqLemmas.and_val_csI,
      Tools.VedU1MultiSeqLemmas.or_val_scI, Tools.VedU1MultiSeqLemmas.or_val_csI,
      Tools.VedU1MultiSeqLemmas.xor_val_scI, Tools.VedU1MultiSeqLemmas.xor_val_csI,
      Tools.VedU1MultiSeqLemmas.shl_val_scI, Tools.VedU1MultiSeqLemmas.shl_val_csI,
      Tools.VedU1MultiSeqLemmas.shr_val_scI, Tools.VedU1MultiSeqLemmas.shr_val_csI,
      Tools.VedU1MultiSeqLemmas.append_val_scI, Tools.VedU1MultiSeqLemmas.append_val_csI, $ex,*] $[$loc]?)

open Lean Meta Elab Tactic in
/-- `seqNextAt` (`Tools.VedU1ScriptSeqGen`) with `ved_pk_simp`: read every loop of the context and of the goal at
the cycle `tm` off its body. -/
def pkNextAt (tm : Term) (ex : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma ",") : TacticM Unit :=
  withMainContext do
  let mut tgt : Lean.Expr := mkConst ``True
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  tgt := mkApp tgt (← instantiateMVars (← getMainTarget))
  let loops := Tools.VedU1Loop.loopsOf tgt
  for j in [0:loops.size] do
    let L := loops[j]!
    let args := L.getAppArgs
    unless args.size == 4 do throwError "ved_pk_next: malformed Signal.loop"
    let dom ← Term.exprToSyntax args[0]!
    let α ← Term.exprToSyntax args[1]!
    let inst ← Term.exprToSyntax args[2]!
    let F ← Term.exprToSyntax args[3]!
    let hU := mkIdent (Name.mkSimple s!"ved_hU{j}")
    let hL ← `(Lean.Parser.Tactic.simpLemma| h)
    let exh : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
      Syntax.TSepArray.ofElems (#[hL] ++ ex.getElems)
    evalTactic (← `(tactic| have $hU:ident := @Tools.VedU1Loop.loop_val_unfold $dom $α $inst $F
        (fun _ _ => rfl) (fun s1 s2 t h => by ved_pk_simp [$exh,*]) $tm))
    evalTactic (← `(tactic| ved_seq_aux $hU:ident (
      try dsimp only [$ex,*, Sparkle.Core.Signal.Signal.map, Signal.register, Signal.beq, Signal.seq, Signal.ap,
        Sparkle.Core.Signal.bundle2, Functor.map, Seq.seq, Signal.slt, Signal.ult, Signal.ule, Signal.ashr, Signal.lt, Signal.le,
        OTy.obs, PTy.obs, PTy.sig, -Nat.reduceAdd] at $hU:ident
      try ved_pk_simp [$ex,*] at $hU:ident
      try ved_seq_sub at $hU:ident)))

/-- `ved_pk_next s [ex]`: `ved_seq_next` with `ved_pk_simp`. -/
syntax (name := vedPkNext) "ved_pk_next " ident " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

open Lean Meta Elab Tactic in
@[tactic vedPkNext] def evalVedPkNext : Tactic := fun stx => do
  let sI : Ident := ⟨stx[1]⟩
  let sE ← `(term| $sI + 1)
  pkNextAt sE ⟨stx[3].getArgs⟩

/-- `ved_pk_next0 [ex]`: the same at cycle 0. -/
syntax (name := vedPkNext0) "ved_pk_next0 " " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

open Lean Meta Elab Tactic in
@[tactic vedPkNext0] def evalVedPkNext0 : Tactic := fun stx => do
  pkNextAt (← `(term| 0)) ⟨stx[2].getArgs⟩

open Lean Meta Elab Tactic in
/-- `ved_pk_bits_facts`: `ved_bits_facts` with the operations taken innermost first and the context re-read after
every fact (`omegaProof?` works in the context current when it is called; `ved_bits_facts` reads it once, so the
bound of `(x &&& c ||| 8) ||| 128` needed a third call after the bound of `x &&& c ||| 8` was added). -/
elab "ved_pk_bits_facts" : tactic => do
  let tgt ← withMainContext do instantiateMVars (← getMainTarget)
  let cands : List Nat := (List.range 130).tail! ++ (List.range 60).map (fun i => 136 + 8 * i)
  let ops := (Tools.VedU1Loop.natBitOps tgt).qsort (fun a b => a.approxDepth.toNat < b.approxDepth.toNat)
  for t in ops do
    withMainContext do
      let a := t.getArg! 4
      let b := t.getArg! 5
      if t.isAppOfArity ``HAnd.hAnd 6 then
        evalTactic (← `(tactic| have := @Nat.and_le_left $(← Term.exprToSyntax a) $(← Term.exprToSyntax b)))
        evalTactic (← `(tactic| have := @Nat.and_le_right $(← Term.exprToSyntax a) $(← Term.exprToSyntax b)))
    withMainContext do
      let a := t.getArg! 4
      let b := t.getArg! 5
      unless t.isAppOfArity ``HAnd.hAnd 6 do
        let mut done := false
        for n in cands do
          if done then break
          let bound ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit n]
          let some ha ← Tools.VedU1Loop.omegaProof? (← mkAppM ``LT.lt #[a, bound]) | continue
          let some hb ← Tools.VedU1Loop.omegaProof? (← mkAppM ``LT.lt #[b, bound]) | continue
          let lem ← if t.isAppOfArity ``HXor.hXor 6
            then mkAppM ``Nat.xor_lt_two_pow #[ha, hb] else mkAppM ``Nat.or_lt_two_pow #[ha, hb]
          evalTactic (← `(tactic| have := $(← Term.exprToSyntax lem)))
          done := true

open Sparkle.IR.Semantics Tools.VedU1Contract Sparkle.Core.Signal in
/-- The closing tactic of `ved_seq_loop_close` with `ved_pk_bits_facts`. -/
syntax (name := vedPkLoopClose) "ved_pk_loop_close " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| ved_pk_loop_close [$ex,*]) =>
    `(tactic| ((try ved_seq_wide_simp [$ex,*]) <;> (try simp only [Tools.VedU1PackedSeq2.ite_one_mod2_eq_one, Tools.VedU1PackedSeq2.ite_one_mod2_eq_zero]) <;> (first | omega | ((repeat' (split <;> (try simp only [vedToNatAppend, Tools.VedU1Lemmas.toNat_append', BitVec.toNat_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv, eq_self, ↓reduceIte, Nat.reduceEqDiff, not_true_eq_false, if_true, if_false, true_and, and_true, false_and, and_false, or_false, false_or, or_true, true_or, not_false_eq_true, *]))) <;> (try simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq] at *) <;> (try simp only [vedToNatAppend, Tools.VedU1Lemmas.toNat_append', Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, Nat.reduceDiv, Tools.VedU1Lemmas.xor_one_one, not_true_eq_false, Nat.zero_and, Nat.and_zero, Nat.one_and_eq_mod_two, Nat.and_one_is_mod, Nat.zero_xor, Nat.xor_zero, true_and, and_true, false_and, and_false, or_false, false_or, or_true, true_or, not_false_eq_true] at *) <;> (try ved_or_lit) <;> (try simp only [Nat.or_zero, Nat.zero_or]) <;> (try ved_xor_ones) <;> (try ved_pk_bits_facts) <;> omega))))



open Lean Meta Elab Tactic in
/-- `ved_pk_close_each`: `ved_seq_close_each` with `ved_pk_loop_close` (its `ved_bits_facts` reads the context once, so
the bound of a nested `|||` was missing after the case split exposed it). -/
elab "ved_pk_close_each" : tactic => do
  let gs ← getGoals
  for g in gs do
    setGoals [g]
    evalTactic (← `(tactic| ved_seq_unmdata))
    Tactic.withoutRecover
      (evalTactic (← `(tactic| ved_pk_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod, Int.bmod_def, BitVec.toNat_append, BitVec.toNat_ofNat, Tools.VedU1ScriptSeq.or_mod _ _ _ _ rfl])))
  setGoals []

open Lean Meta Elab Tactic in
/-- debugging: size of the type of hypothesis `h` (distinct nodes, depth). -/
elab "ved_pk_size " h:ident : tactic => withMainContext do
  let some d := (← getLCtx).findFromUserName? h.getId | throwError "no {h.getId}"
  let ty ← instantiateMVars d.type
  let nodes := (Tools.VedU1WireShare.collectDag (fun _ => true) ty).size
  IO.eprintln s!"VED PKSIZE {h.getId} dagNodes={nodes} depth={ty.approxDepth} loops={(Tools.VedU1WireShare.loopsDag ty).size}"

/-- `ved_pk_aux h (tacs)`: `ved_seq_aux` (`Tools.VedU1ScriptSeqGen`), printing under `ved.packedseq2.dbg ≥ 3` the DAG size of
the proof and the time of the auxiliary theorem. -/
syntax (name := vedPkAux) "ved_pk_aux " ident " (" tacticSeq ")" : tactic

open Lean Meta Elab Tactic in
@[tactic vedPkAux] def evalVedPkAux : Tactic := fun stx => do
  let h : Ident := ⟨stx[1]⟩
  let tacs := stx[3]
  let dbg := ved.packedseq2.dbg.get (← getOptions) ≥ 3
  let aux ← withMainContext do
    let ty ← mkFreshTypeMVar
    let mv ← mkFreshExprMVar (some ty)
    let saved ← getGoals
    setGoals [mv.mvarId!]
    evalTactic tacs
    evalTactic (← `(tactic| exact $h))
    setGoals saved
    let val ← instantiateMVars mv
    let T1 ← instantiateMVars ty
    if dbg then
      IO.eprintln s!"VED PKAUX {h.getId} proof dagNodes={(Tools.VedU1WireShare.collectDag (fun _ => true) val).size} depth={val.approxDepth} treeSize={val.sizeWithoutSharing} typeTree={T1.sizeWithoutSharing} typeNodes={(Tools.VedU1WireShare.collectDag (fun _ => true) T1).size}"
    if dbg then
      let mut cnt : Std.HashMap Name Nat := {}
      for e in Tools.VedU1WireShare.collectDag (fun e => e.isConst) val do
        cnt := cnt.insert e.constName! (cnt.getD e.constName! 0 + 1)
      let top := (cnt.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 400
      IO.eprintln s!"VED PKAUX consts {top.map fun (n, c) => s!"{n}:{c}"}"
    let t0 ← IO.monoMsNow
    let r ← mkAuxTheorem T1 val (zetaDelta := true)
    if dbg then IO.eprintln s!"VED PKAUX {h.getId} kernel {(← IO.monoMsNow) - t0} ms"
    pure r
  let auxS ← Term.exprToSyntax aux
  evalTactic (← `(tactic| have $h:ident := $auxS))

open Lean Meta Elab Tactic in
/-- `ved_pk_simp_nz [lemmas] (at loc)?`: `ved_seq_simp` with `zeta := false`.  The declaration of a packed result is a
chain of `let`s (`let csrIsRW := …`, `let regs := Signal.loop …`) used by every leaf; `zeta` unfolds them all at once and the
proof of the rewriting then carries the unfolded type at every step (R14: a tree of 2.4·10^7 nodes, the kernel needed 66 s
and ran out of stack).  With the `let`s kept the type is small; `dsimp only` unfolds them afterwards, with no proof term. -/
elab "ved_pk_simp_nz " "[" ex:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? : tactic => do
  let base ← match loc with
    | some l => `(tactic| ved_seq_simp [$ex,*] $l:location)
    | none => `(tactic| ved_seq_simp [$ex,*])
  let stx ← liftMacroM (expandMacros base)
  let tmpl ← `(tactic| simp (config := { zeta := false }) [Nat.add_zero])
  evalTactic (stx.setArg 1 (tmpl.raw.getArg 1))

open Lean Meta Elab Tactic in
/-- `ved_pk_genloops h`: replace every `Signal.loop F` of the type of the hypothesis `h` by a new variable `ved_Lj`, keeping
`ved_hLoopj : Signal.loop F = ved_Lj`.  The body of a loop is not rewritten (`vedLoopFreeze`), but every step of a `simp` proof
carries the type of `h`; a packed result whose declaration is a chain of `let`s mentions the same loop once per leaf (R14: the
type is 692 distinct nodes but a tree of 3.3·10^5, the rewriting proof a tree of 2.4·10^7 that the kernel could not check:
66 s, then deep recursion).  The abstraction is done on the shared term (`Expr.abstract`), not by `generalize` (`kabstract`
walks the tree: more than 8·10^9 heartbeats) and the type is changed by `Eq.mp (congrArg motive hLoop)`.
`ved_pk_unloops` puts the loops back with `subst`. -/
elab "ved_pk_genloops " h:ident : tactic => withMainContext do
  let some d := (← getLCtx).findFromUserName? h.getId | throwError "ved_pk_genloops: no {h.getId}"
  let loops := Tools.VedU1WireShare.loopsDag (← instantiateMVars d.type)
  let mut hId := d.fvarId
  for j in [0:loops.size] do
    let e := loops[j]!
    let eS ← Term.exprToSyntax e
    let hL := mkIdent (Name.mkSimple s!"ved_hLoop{j}")
    let L := mkIdent (Name.mkSimple s!"ved_L{j}")
    evalTactic (← `(tactic| refine (fun ($L : _) ($hL : $eS = $L) => ?_) $eS rfl))
    hId ← withMainContext do
      let some dh := (← getLCtx).find? hId | throwError "ved_pk_genloops: {h.getId} lost"
      let ty ← instantiateMVars dh.type
      let α ← inferType e
      let some dL := (← getLCtx).findFromUserName? L.getId | throwError "ved_pk_genloops: no L"
      let some dE := (← getLCtx).findFromUserName? hL.getId | throwError "ved_pk_genloops: no eq"
      let motive := Lean.mkLambda `l .default α (ty.abstract #[e])
      let tyNew := (ty.abstract #[e]).instantiate1 dL.toExpr
      let eqPf ← mkCongrArg motive dE.toExpr
      let g ← getMainGoal
      let r ← g.replaceLocalDecl hId tyNew eqPf
      replaceMainGoal [r.mvarId]
      pure r.fvarId
  -- the new declaration has a new fvar id: nothing else to do, `h` is found by name

open Lean Meta Elab Tactic in
/-- `ved_pk_unloops`: `subst` every `ved_hLoop…` (the loops of `ved_pk_genloops` go back in place). -/
elab "ved_pk_unloops" : tactic => do
  let names ← withMainContext do
    let mut out : Array Name := #[]
    for d in ← getLCtx do
      if d.userName.toString.startsWith "ved_hLoop" then out := out.push d.userName
    pure out
  for n in names.reverse do
    evalTactic (← `(tactic| subst $(mkIdent n):ident))

open Lean Meta Elab Tactic in
/-- `ved_pk_drop`: the first half of `ved_seq_bools`: drop the hypotheses the rewriting is done with
(nothing reads them any more, and `cases` would revert and re-introduce every one that mentions the
variable). -/
elab "ved_pk_drop" : tactic => do
  let gs ← getGoals
  let mut out : Array MVarId := #[]
  for g0 in gs do
    setGoals [g0]
    let drop ← withMainContext do
      let mut out : Array FVarId := #[]
      for d in ← getLCtx do
        let n := d.userName.toString
        if d.isImplementationDetail then continue
        let mentionsIR := (← instantiateMVars d.type).find? fun e =>
          e.isConst && (e.constName!.toString.startsWith "Sparkle.IR" || e.constName!.toString.startsWith "Tools.VedU1")
        if n.startsWith "ved_hL" || n.startsWith "ved_hU" || n.startsWith "hv" || n.startsWith "hs" || n.startsWith "hEr" || n.startsWith "hEin"
            || n.startsWith "hreg" || n.startsWith "hrg" || n.startsWith "hw" || n == "hfr" || n == "hall"
            || n == "hstep" || n == "key" || (mentionsIR.isSome && (← isProp d.type)) then
          out := out.push d.fvarId
      pure out
    for fv in drop.reverse do
      let g ← getMainGoal
      try
        let g' ← g.clear fv
        replaceMainGoal [g']
      catch _ => pure ()
    out := out ++ (← getGoals).toArray
  setGoals out.toList

open Lean Meta Elab Tactic in
/-- `ved_pk_split`: on EVERY goal, split only the `Bool` loop-state components (`ved_b…` bound facts of
`ved_seq_gen'`) that occur in that goal.  `ved_seq_bools` splits all of them in every goal: `k` `Bool`
registers made `2^k` copies of every goal, also of those that never read a `Bool` (R41: 16 copies of the
fsm goal, 15 s each). -/
elab "ved_pk_split" : tactic => do
  let gs ← getGoals
  let mut out : Array MVarId := #[]
  for g in gs do
    setGoals [g]
    let bs ← withMainContext do
      let mut bs : Array Lean.Expr := #[]
      for d in ← getLCtx do
        if d.userName.toString.startsWith "ved_b" then
          let t ← instantiateMVars d.type
          let a := t.getArg! 2
          if a.isAppOfArity ``Bool.toNat 1 then bs := bs.push (a.getArg! 0)
      pure bs
    for e in bs do
      let occurs ← withMainContext do
        pure ((← instantiateMVars (← getMainTarget)).find? (· == e)).isSome
      if occurs then
        let eS ← Term.exprToSyntax e
        evalTactic (← `(tactic| all_goals (try cases hbool : $eS)))
    out := out ++ (← getGoals).toArray
  setGoals out.toList

open Lean Meta Elab Tactic in
/-- `ved_seq_gen' s`: `ved_seq_gen` for a loop state that may end in a scalar component
(`Tools.VedU1MultiSeqLoop.stateComps'`): the state stays ONE variable, its components are read by
projections, `Bool` components keep their `ved_b` bound facts and are split later by `ved_seq_bools`. -/
elab "ved_seq_gen' " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let loops := Tools.VedU1Loop.loopsOf tgt
  if loops.isEmpty then throwError "ved_seq_gen': no Signal.loop in the goal"
  for j in [0:loops.size] do
    let v ← mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE]
    let vs ← Term.exprToSyntax v
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    let hL := mkIdent (Name.mkSimple s!"ved_hL{j}")
    evalTactic (← `(tactic| generalize $hL:ident : $vs = $X:ident at *))
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_seq_gen': malformed Signal.loop"
    let (cs, u) ← Tools.VedU1MultiSeqLoop.stateComps' α
    let n := cs.length
    for i in [0:n] do
      let (pS, isB, isV) ← withMainContext do
        let some dX := (← getLCtx).findFromUserName? X.getId | throwError "ved_seq_gen': no state variable"
        let proj ← Tools.VedU1MultiSeqLoop.compProj' dX.toExpr i n u
        let ty ← whnfR (← inferType proj)
        pure (← Term.exprToSyntax proj, ty.isConstOf ``Bool, ty.isAppOf ``BitVec)
      if isB then
        evalTactic (← `(tactic| have $(mkIdent (Name.mkSimple s!"ved_b{j}_{i}")):ident := Bool.toNat_le $pS))
      else if isV then
        evalTactic (← `(tactic| have $(mkIdent (Name.mkSimple s!"ved_v{j}_{i}")):ident := BitVec.isLt $pS))

open Lean Elab Term

private def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The script, or `none` when the module is outside its shape (a register whose input is not a
plain wire, a data input that is not scalar, no clock/reset for the registers).
`C M O B` are the checker's constants (contract, module, outputs, body), `F`/`nDom` the
declaration, `b0` the arrangement stored as `B`, `regs` the registers `(name, width)`. -/
def packedSeqScript (C M O B F : Name) (nDom : Nat) (m : Sparkle.IR.AST.Module) (b0 : List Stmt)
    (clkRst : Option (String × String)) (dataPorts : List Port) (regs : List (String × Nat))
    (helpers : Array Name) : TermElabM (Option Syntax) := do
  let some (clkN, rstN) := clkRst | return none
  -- registers: their input must be a plain wire, their reset the module's, their init non-negative
  let mut regInfo : Array (String × Nat × String × String × Int) := #[]
  for (r, w) in regs do
    match b0.find? (fun s => match s with | .register o .. => o == r | _ => false) with
    | some (.register _ _ (rst, _) (.ref wire) init) =>
      if rst != rstN || init < 0 then return none
      regInfo := regInfo.push (r, w, rst, wire, init)
    | _ => return none
  let fI := mkCIdent F
  let mut f0 : Term := fI
  if nDom > 0 then
    f0 ← `(@$fI)
    for _ in [0:nDom] do f0 ← `($f0 Sparkle.Core.Domain.defaultDomain)
  let Cc := mkCIdent C
  let Ci : Term ← `(Tools.VedU1Packed.PContract.core $Cc)
  let f : Term ← `(Tools.VedU1Packed.packedF ($Cc).tbl $f0)
  let Mi := mkCIdent M
  let Oi := mkCIdent O
  let Bi := mkCIdent B
  let hsA : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    helpers.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let insI := mkIdent `ins
  let sI := mkIdent `s
  let hR := mkIdent `hR
  let vI := mkIdent `vsrc
  let hv := mkIdent `hvsrc
  let k := regs.length
  let hregs := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"hreg{i}")
  let rNames := (regs.map fun r => Syntax.mkStrLit r.1).toArray
  let rWidths := (regs.map fun r => Syntax.mkNumLit (toString r.2)).toArray
  -- widths of every name the body mentions
  let names := dedup (b0.flatMap stmtNames ++ dataPorts.map (·.name) ++ [rstN])
  let hws := (List.range names.length).toArray.map fun i => mkIdent (Name.mkSimple s!"hw{i}")
  let mut pre : Array (TSyntax `tactic) := #[]
  for (n, h) in names.zip hws.toList do
    let w := declWidth m n
    pre := pre.push (← `(tactic| have $h:ident : declWidth $Mi $(Syntax.mkStrLit n) = $(Syntax.mkNumLit (toString w)) := by decide +kernel))
  pre := pre.push (← `(tactic| ved_pk_mark "pre-hw"))
  -- data inputs: the range facts, one per input
  let hins := (List.range dataPorts.length).toArray.map fun i => mkIdent (Name.mkSimple s!"hin{i}")
  for (i, p, h) in (List.range dataPorts.length).zip (dataPorts.zip hins.toList) |>.map fun (i, (p, h)) => (i, p, h) do
    let pn := Syntax.mkStrLit p.name
    let hwI := hws[(names.findIdx? (· == p.name)).getD 0]!
    match p.ty with
    | .bit | .bitVector _ => pure ()
    | _ => return none
    let wn := declWidth m p.name
    let iL := Syntax.mkNumLit (toString i)
    pre := pre.push (← `(tactic| have $h:ident : $insI $sI $pn < 2 ^ $(Syntax.mkNumLit (toString wn)) := by
        have h0 := Tools.VedU1ScriptSeq.inputsOk_nth $Ci $Mi $insI hok $sI $iL $pn (by decide +kernel)
        rw [$hwI:ident] at h0
        exact h0))
  pre := pre.push (← `(tactic| ved_pk_mark "pre-hin"))
  -- the reset is held 0
  let hrst := mkIdent `hrst0
  pre := pre.push (← `(tactic| have $hrst:ident : $insI $sI $(Syntax.mkStrLit rstN) = 0 :=
    hok.2 $sI ($(Syntax.mkStrLit clkN), $(Syntax.mkStrLit rstN)) (by decide +kernel)))
  -- the environment E: inputs from the stream, registers from the state
  let hEin := (List.range dataPorts.length).toArray.map fun i => mkIdent (Name.mkSimple s!"hEin{i}")
  let mut postStep : Array (TSyntax `tactic) := #[]
  for (p, h) in dataPorts.zip hEin.toList do
    let pn := Syntax.mkStrLit p.name
    postStep := postStep.push (← `(tactic| have $h:ident : E $pn = $insI $sI $pn :=
      (hfr $pn (by decide +kernel)).trans
        (Tools.VedU1ScriptSeq.seedIn_input $Mi $insI $sI st $pn (by decide +kernel))))
  let hErst := mkIdent `hErst
  postStep := postStep.push (← `(tactic| have $hErst:ident : E $(Syntax.mkStrLit rstN) = 0 :=
    (hfr $(Syntax.mkStrLit rstN) (by decide +kernel)).trans
      ((Tools.VedU1ScriptSeq.seedIn_input $Mi $insI $sI st $(Syntax.mkStrLit rstN) (by decide +kernel)).trans $hrst)))
  let hEr := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"hEr{i}")
  for i in [0:k] do
    let rn := rNames[i]!
    postStep := postStep.push (← `(tactic| have $(hEr[i]!):ident : E $rn = st $rn :=
      (hfr $rn (by decide +kernel)).trans
        (Tools.VedU1ScriptSeq.seedIn_state $Mi $insI $sI st $rn (by decide +kernel))))
    postStep := postStep.push (← `(tactic| rw [$(hregs[i]!):ident] at $(hEr[i]!):ident))
  -- register next values
  let hrgs := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"hrg{i}")
  for i in [0:k] do
    let (r, _, rst, wire, init) := regInfo[i]!
    postStep := postStep.push (← `(tactic| have $(hrgs[i]!):ident :
      Tools.VedU1ScriptSeq.regOf $Bi $(Syntax.mkStrLit r) =
        some ($(Syntax.mkStrLit rst), Sparkle.IR.AST.Expr.ref $(Syntax.mkStrLit wire),
          ($(Syntax.mkNumLit (toString init.toNat)) : Int)) := rfl))
  -- one equation per assignment
  let nS := b0.length
  let hss := (List.range nS).toArray.map fun i => mkIdent (Name.mkSimple s!"hs{i}")
  let mut pats : Array (TSyntax `Lean.Parser.Tactic.rcasesPatLo) := #[]
  let mut assignIdx : Array Nat := #[]
  for i in [0:nS] do
    match b0[i]? with
    | some (.assign ..) =>
      pats := pats.push (← `(Lean.Parser.Tactic.rcasesPatLo| $(hss[i]!):ident))
      assignIdx := assignIdx.push i
    | _ => pats := pats.push (← `(Lean.Parser.Tactic.rcasesPatLo| _))
  pats := pats.push (← `(Lean.Parser.Tactic.rcasesPatLo| _))
  let allPat : TSyntax `rcasesPat ← `(rcasesPat| ⟨$[$pats],*⟩)
  let hwL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    hws.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let hEinL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    hEin.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let hErL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    hEr.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let hrgL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    hrgs.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let hErstL ← `(Lean.Parser.Tactic.simpLemma| $hErst:ident)
  let mk (xs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :
      Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems xs
  -- the statements, in order, each on its own: the equations of the earlier statements are
  -- substituted (they are already small) and a packed word read back by `ved_seq_unpack`
  let hsL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    (assignIdx.map fun i => hss[i]!).mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let mut perStmt : Array (TSyntax `tactic) := #[]
  for k in [0:assignIdx.size] do
    let i := assignIdx[k]!
    perStmt := perStmt.push (← `(tactic| ved_pk_aux $(hss[i]!):ident (
      ved_seq_simp_nd [$(mk (hwL ++ hEinL ++ hErL ++ #[hErstL] ++ hsL.extract 0 k)),*] at $(hss[i]!):ident
      try ved_seq_unpack at $(hss[i]!):ident)))
  let applyL ← `(Lean.Parser.Tactic.simpLemma| Tools.VedU1ScriptSeq.applyNexts_nextsOf)
  let sigBase := #[← `(Lean.Parser.Tactic.simpLemma| srcOf), ← `(Lean.Parser.Tactic.simpLemma| $Cc:ident), ← `(Lean.Parser.Tactic.simpLemma| Tools.VedU1Packed.PContract.core), ← `(Lean.Parser.Tactic.simpLemma| Tools.VedU1Packed.collapse),
    ← `(Lean.Parser.Tactic.simpLemma| contractOf), ← `(Lean.Parser.Tactic.simpLemma| applyIns),
    ← `(Lean.Parser.Tactic.simpLemma| $fI:ident)] ++ hsA
  let exReg := mk (#[applyL] ++ sigBase ++ hrgL ++ hwL ++ hEinL ++ hErL ++ #[hErstL] ++ hsL)
  let closeTacs : Array (TSyntax `tactic) := #[
    ← `(tactic| ved_seq_unmdata),
    ← `(tactic| all_goals (try simp only [vedToNatAppend, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq])),
    ← `(tactic| all_goals (try simp only [Nat.reduceAdd, Nat.reducePow])),
    ← `(tactic| all_goals (try simp (disch := first | ved_omega | decide) only [Nat.mod_mod_of_dvd])),
    ← `(tactic| all_goals (try ved_seq_wide_simp [BitVec.toNat_eq, Nat.and_one_is_mod, Int.bmod_def, Tools.VedU1Loop.ved_mul_lit_bv])),
    ← `(tactic| all_goals (try ved_bit_simp)),
    ← `(tactic| all_goals (try ved_or_lit)),
    ← `(tactic| all_goals (try ved_pack_simp)),
    ← `(tactic| all_goals (try ved_xor_ones)),
    ← `(tactic| all_goals (try ved_pk_bits_facts)),
    ← `(tactic| all_goals (try ved_mul_facts)),
    ← `(tactic| all_goals (try ved_pack_simp)),
    ← `(tactic| all_goals (try simp only [Nat.mod_mul_mod, Nat.mul_mod_mod])),
    ← `(tactic| all_goals (try simp only [Tools.VedU1Loop.ved_mul_lit_nat])),
    ← `(tactic| ved_pk_close_each)]
  let pats2 ← (hregs.toList).mapM fun h => `(Lean.Parser.Tactic.rcasesPatLo| $h:ident)
  let hPat : TSyntax `rcasesPat ← match pats2 with
    | [] => `(rcasesPat| _)
    | _ => `(rcasesPat| ⟨$[$(pats2.toArray)],*⟩)
  let mut tacs : Array (TSyntax `tactic) := #[]
  let marks := ved.packedseq2.dbg.get (← getOptions) ≥ 3
  let dbgN := ved.packedseq2.dbg.get (← getOptions)
  let mark (n : String) : TermElabM (Array (TSyntax `tactic)) :=
    if dbgN == 4 && n == "reg-split" then do pure #[← `(tactic| (trace_state; fail "stopped at reg-split"))]
    else if dbgN == 5 && n == "out-split" then do pure #[← `(tactic| (trace_state; fail "stopped at out-split"))]
    else do pure #[← `(tactic| ved_pk_mark $(Syntax.mkStrLit n))]
  tacs := tacs.push (← `(tactic| intro $insI hok $sI st mems $hR))
  tacs := tacs ++ pre
  tacs := tacs ++ (← mark "pre")
  let hv0 := mkIdent `hv0
  tacs := tacs.push (← `(tactic| obtain ⟨$vI, $hv0⟩ : ∃ v, v = srcOf $Ci $f $insI "out" $sI := ⟨_, rfl⟩))
  tacs := tacs.push (← `(tactic| have $hv := $hv0))
  tacs := tacs.push (← `(tactic| have key : ∀ t, srcOf $Ci $f $insI "out" t =
      OTy.packNat ($Cc).tbl.out ((applyIns ($Cc).tbl.ins ($Cc).inNames $insI $f0).val t) :=
        fun t => Tools.VedU1Packed.srcOf_packed $Cc $f0 $insI t))
  tacs := tacs.push (← `(tactic| rw [key] at $hv:ident))
  let hvDs ← `(tactic| try dsimp only [$Oi:ident, $Mi:ident, $Bi:ident, Tools.VedU1Contract.declWidth, srcOf, $Cc:ident, Tools.VedU1Packed.PContract.core, Tools.VedU1Packed.collapse, contractOf, applyIns, $fI:ident,
        Signal.fst, Signal.snd, Sparkle.Core.Signal.Signal.map, Signal.register, Signal.beq, Signal.seq, Signal.ap, Sparkle.Core.Signal.bundle2, Functor.map, Seq.seq,
        Signal.slt, Signal.ult, Signal.ule, Signal.ashr, Signal.lt, Signal.le, OTy.obs, PTy.obs, PTy.sig, -Nat.reduceAdd, $(mk hsA),*] at $hv:ident)
  let hvSimp ← `(tactic| ved_seq_simp [$Oi:ident, $Mi:ident, $Bi:ident, declWidth, srcOf, $Cc:ident, Tools.VedU1Packed.PContract.core, Tools.VedU1Packed.collapse, contractOf, applyIns, $fI:ident, Tools.VedU1PackedSeq2.OTy_packNat_pair_mod, Tools.VedU1MultiSeqLemmas.OTy_packNat_leaf, OTy.width, PTy.width, Signal.fst, Signal.snd, $(mk hsA),*] at $hv:ident)
  if dbgN == 7 then
    tacs := tacs ++ #[hvDs, hvSimp, ← `(tactic| ved_pk_size $hv), ← `(tactic| (fail "stopped at hv"))]
  else
    if dbgN == 8 then
      tacs := tacs.push (← `(tactic| ved_pk_aux $hv:ident ($hvDs:tactic; ved_pk_mark "hv-dsimp"; $hvSimp:tactic; ved_pk_mark "hv-simp")))
    else
      tacs := tacs.push (← `(tactic| ved_pk_aux $hv:ident ($hvDs:tactic; ved_pk_mark "hv-dsimp"; $hvSimp:tactic; ved_pk_mark "hv-simp")))
  tacs := tacs ++ (← mark "hv")
  tacs := tacs.push (← `(tactic| ved_loop_R' $insI [$rNames,*] $rWidths,*))
  tacs := tacs.push (← `(tactic| obtain $hPat := $hR))
  tacs := tacs.push (← `(tactic| ved_seq_gen' $sI))
  tacs := tacs ++ (← mark "R+gen")
  tacs := tacs.push (← `(tactic| ved_pk_next $sI [$(mk (#[← `(Lean.Parser.Tactic.simpLemma| Signal.fst), ← `(Lean.Parser.Tactic.simpLemma| Signal.snd), ← `(Lean.Parser.Tactic.simpLemma| $fI:ident)] ++ hsA)),*]))
  tacs := tacs ++ (← mark "next")
  tacs := tacs.push (← `(tactic| obtain ⟨E, hstep, hfr, hall⟩ := Tools.VedU1ScriptSeq.step_seq (declWidth $Mi) mems $Bi
    (Tools.VedU1Contract.seedIn $Mi $insI $sI st) (by decide +kernel) (by decide +kernel)))
  tacs := tacs ++ postStep
  tacs := tacs.push (← `(tactic| obtain $allPat := hall))
  tacs := tacs ++ (← mark "step_seq+post")
  tacs := tacs ++ perStmt
  tacs := tacs ++ (← mark "perStmt")
  tacs := tacs.push (← `(tactic| refine ⟨E, Tools.VedU1ScriptSeq.nextsOf (declWidth $Mi) E $Bi, mems, hstep, ?_, ?_⟩))
  -- outputs
  let outTacs : Array (TSyntax `tactic) := #[
    ← `(tactic| intro o ho),
    ← `(tactic| simp only [$Oi:ident, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho),
    ← `(tactic| subst ho),
    ← `(tactic| try dsimp only),
    ← `(tactic| rw [← $hv0:ident]),
    ← `(tactic| rw [$hv:ident]),
    ← `(tactic| simp only [$(mk hsL),*, -Nat.reduceAdd]),
    ← `(tactic| try simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul]),
    ← `(tactic| ved_pk_drop),
    ← `(tactic| ved_pk_leafwise)] ++ (← mark "out-simp") ++ #[
    ← `(tactic| all_goals try (repeat' apply And.intro)),
    ← `(tactic| ved_pk_split)] ++ (← mark "out-split") ++ closeTacs ++ (← mark "out-close")
  let regTacs : Array (TSyntax `tactic) := #[
    ← `(tactic| ved_seq_sub),
    ← `(tactic| ved_seq_simp [$exReg,*])] ++ (← mark "reg-simp") ++ #[
    ← `(tactic| ved_pk_drop),
    ← `(tactic| all_goals try (repeat' apply And.intro)),
    ← `(tactic| ved_pk_split)] ++ (← mark "reg-split") ++ closeTacs ++ (← mark "reg-close")
  let stopH0 ← `(tactic| (trace_state; fail "stopped at h0"))
  let h0tacs : Array (TSyntax `tactic) := #[
    ← `(tactic| intro $insI hok),
    ← `(tactic| ved_pk_next0 [$(mk (#[← `(Lean.Parser.Tactic.simpLemma| Signal.fst), ← `(Lean.Parser.Tactic.simpLemma| Signal.snd), ← `(Lean.Parser.Tactic.simpLemma| $fI:ident)] ++ hsA)),*]),
    ← `(tactic| ved_seq_sub)] ++ (if dbgN == 6 then #[stopH0] else #[]) ++ #[
    ← `(tactic| simp [Signal.fst, Signal.snd, Tools.VedU1Contract.st0, $Cc:ident, Tools.VedU1Packed.PContract.core, Tools.VedU1Packed.collapse, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.regsOf, $Mi:ident, Sparkle.IR.Semantics.encodeInit, Sparkle.IR.Semantics.mask, Tools.VedU1Contract.declWidth]),
    ← `(tactic| all_goals decide +kernel)]
  let oos := mkCIdent `Tools.VedU1Entry.outputs_of_step
  let b1 ← `(tactic| · $outTacs*)
  let b2 ← `(tactic| · $regTacs*)
  let hblock : Array (TSyntax `tactic) := tacs ++ #[b1, b2]
  let Mi' := Mi
  let stx ← `(by
      have hP : Tools.VedU1Packed.PackCover $Cc := by decide
      have hU : U1Stmt $Ci $Mi' $f := by
        have hord : OrderOk $Mi $Bi = true := by decide +kernel
        refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨$Bi, hord⟩, ?_⟩
        apply Tools.VedU1Contract.outputs_of_order $Bi hord
        refine $oos $Ci $Mi $Bi $f $Oi (by decide +kernel) ?R ?h0 ?hstep
        case hstep =>
          $hblock*
        case h0 =>
          $h0tacs*
      exact ⟨hP, hU, Tools.VedU1Packed.slices_of_outputs hP.1 hU.2.2.2.2⟩)
  return some stx

end Tools.VedU1PackedSeq2
