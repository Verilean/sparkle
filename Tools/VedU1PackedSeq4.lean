import Tools.VedU1PackedSeq2
import Tools.VedU1PackedSeq4Unpack

/-!
# Packed result with registers: the packed-seq4 script (`sparkle-ved-packed-seq4`)
-/

register_option ved.packedseq4.on : Bool := {
  defValue := true
  descr := "ved.packedseq4.on: use the packed-seq4 script (otherwise the packed-seq2 script)"
}

namespace Tools.VedU1PackedSeq4

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder
open Sparkle.Core.Signal Sparkle.Core.Domain
open Tools.VedU1Contract Tools.VedU1Packed Tools.VedU1ScriptSeq Tools.VedU1PackedSeq2

/-- `ved_pk4_aux h (tacs)`: `ved_pk_aux` (`Tools.VedU1PackedSeq2`), and under `ved.packedseq2.dbg = 9` the type of the auxiliary theorem is printed. -/
syntax (name := vedPk4Aux) "ved_pk4_aux " ident " (" tacticSeq ")" : tactic

open Lean Meta Elab Tactic in
@[tactic vedPk4Aux] def evalVedPk4Aux : Tactic := fun stx => do
  let h : Ident := ⟨stx[1]⟩
  let tacs := stx[3]
  let dbg := ved.packedseq2.dbg.get (← getOptions)
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
    if dbg ≥ 3 then
      IO.eprintln s!"VED PKAUX {h.getId} proof depth={val.approxDepth} treeSize={val.sizeWithoutSharing} typeTree={T1.sizeWithoutSharing}"
    if dbg == 9 then
      IO.eprintln s!"VED PKTYPE {h.getId} {← ppExpr T1}"
    let t0 ← IO.monoMsNow
    let r ← mkAuxTheorem T1 val (zetaDelta := true)
    if dbg ≥ 3 then IO.eprintln s!"VED PKAUX {h.getId} kernel {(← IO.monoMsNow) - t0} ms"
    pure r
  let auxS ← Term.exprToSyntax aux
  evalTactic (← `(tactic| have $h:ident := $auxS))

open Lean Meta Elab Tactic in
/-- `ved_pk4_show h`: debugging only (`ved.packedseq2.dbg = 10`): print the type of the hypothesis `h`. -/
elab "ved_pk4_show " h:ident : tactic => withMainContext do
  if ved.packedseq2.dbg.get (← getOptions) != 10 then return
  let some d := (← getLCtx).findFromUserName? h.getId | return
  IO.eprintln s!"VED PKRAW {h.getId} {← ppExpr (← instantiateMVars d.type)}"

open Lean Elab Term

private def dedup4 (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The script, or `none` when the module is outside its shape (a register whose input is not a
plain wire, a data input that is not scalar, no clock/reset for the registers).
`C M O B` are the checker's constants (contract, module, outputs, body), `F`/`nDom` the
declaration, `b0` the arrangement stored as `B`, `regs` the registers `(name, width)`. -/
def packedSeqScript4 (C M O B F : Name) (nDom : Nat) (m : Sparkle.IR.AST.Module) (b0 : List Stmt)
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
  let names := dedup4 (b0.flatMap stmtNames ++ dataPorts.map (·.name) ++ [rstN])
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
  -- the unpacking chain of the loop words: `_tmp_loop_k = ref body` and every `slice` of a chain name
  let mut chain : List String := []
  for s in b0 do
    match s with
    | .assign x (.ref _) => if x.startsWith "_tmp_loop_" && !x.startsWith "_tmp_loop_body" then chain := x :: chain
    | .assign x (.slice (.ref y) ..) => if chain.contains y then chain := x :: chain
    | _ => pure ()
  let mut perStmt : Array (TSyntax `tactic) := #[]
  for k in [0:assignIdx.size] do
    let i := assignIdx[k]!
    let inChain := match b0[i]? with
      | some (.assign x _) => chain.contains x
      | _ => false
    perStmt := perStmt.push (← `(tactic| ved_pk4_show $(hss[i]!):ident))
    if inChain then
      perStmt := perStmt.push (← `(tactic| ved_pk4_aux $(hss[i]!):ident (
        ved_seq_simp_nd [$(mk (hwL ++ hEinL ++ hErL ++ #[hErstL] ++ hsL.extract 0 k)),*] at $(hss[i]!):ident
        ved_pk4_show $(hss[i]!):ident
        try ved_pk4_unpack at $(hss[i]!):ident
        try ved_seq_unpack at $(hss[i]!):ident)))
    else
      perStmt := perStmt.push (← `(tactic| ved_pk4_aux $(hss[i]!):ident (
        ved_seq_simp_nd [$(mk (hwL ++ hEinL ++ hErL ++ #[hErstL] ++ hsL.extract 0 k)),*] at $(hss[i]!):ident
        ved_pk4_show $(hss[i]!):ident
        try ved_seq_unpack at $(hss[i]!):ident)))
    perStmt := perStmt.push (← `(tactic| ved_pk_mark $(Syntax.mkStrLit s!"stmt{i}")))
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
  let dbgN := ved.packedseq2.dbg.get (← getOptions)
  let mark (n : String) : TermElabM (Array (TSyntax `tactic)) :=
    if dbgN == 4 && n == "reg-split" then do pure #[← `(tactic| (trace_state; fail "stopped at reg-split"))]
    else if dbgN == 8 && n == "pre" then do pure #[← `(tactic| (ved_pk_mark "pre"; fail "stopped at pre"))]
    else if dbgN == 5 && n == "out-split" then do pure #[← `(tactic| (trace_state; fail "stopped at out-split"))]
    else do pure #[← `(tactic| ved_pk_mark $(Syntax.mkStrLit n))]
  tacs := tacs.push (← `(tactic| intro $insI hok $sI st mems $hR))
  tacs := tacs ++ (← mark "intro")
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
  tacs := tacs.push (← `(tactic| ved_pk4_aux $hv:ident ($hvDs:tactic; ved_pk_mark "hv-dsimp"; $hvSimp:tactic; ved_pk_mark "hv-simp")))
  tacs := tacs ++ (← mark "hv")
  tacs := tacs.push (← `(tactic| ved_loop_R' $insI [$rNames,*] $rWidths,*))
  tacs := tacs.push (← `(tactic| obtain $hPat := $hR))
  tacs := tacs.push (← `(tactic| ved_seq_gen' $sI))
  tacs := tacs ++ (← mark "R+gen")
  tacs := tacs.push (← `(tactic| ved_pk_next $sI [$(mk (#[← `(Lean.Parser.Tactic.simpLemma| Signal.fst), ← `(Lean.Parser.Tactic.simpLemma| Signal.snd), ← `(Lean.Parser.Tactic.simpLemma| $fI:ident)] ++ hsA)),*]))
  tacs := tacs ++ (← mark "next")
  tacs := tacs.push (← `(tactic| obtain ⟨E, hstep, hfr, hall⟩ := Tools.VedU1ScriptSeq.step_seq (declWidth $Mi) mems $Bi
    (Tools.VedU1Contract.seedIn $Mi $insI $sI st) (by decide +kernel) (by decide +kernel)))
  tacs := tacs ++ (← mark "step_seq")
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
      ved_pk_mark "start4"
      have hP : Tools.VedU1Packed.PackCover $Cc := by decide
      ved_pk_mark "hP"
      have hU : U1Stmt $Ci $Mi' $f := by
        have hord : OrderOk $Mi $Bi = true := by decide +kernel
        ved_pk_mark "hord"
        refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨$Bi, hord⟩, ?_⟩
        ved_pk_mark "u1parts"
        apply Tools.VedU1Contract.outputs_of_order $Bi hord
        refine $oos $Ci $Mi $Bi $f $Oi (by decide +kernel) ?R ?h0 ?hstep
        case hstep =>
          $hblock*
        case h0 =>
          $h0tacs*
      exact ⟨hP, hU, Tools.VedU1Packed.slices_of_outputs hP.1 hU.2.2.2.2⟩)
  return some stx

end Tools.VedU1PackedSeq4
