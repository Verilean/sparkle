import Lean
import Tools.VedU1Contract
import Tools.VedU1Loop
import Tools.VedU1StructSeqTac
import Tools.VedU1StructWires
import Tools.VedU1StructSlice
import Tools.VedU1StructWireEqs
import Tools.VedU1OrderFast
import Tools.VedMemWidth
import Tools.VedU1WireShare

/-!
# Structure result with registers (`Signal.loop`), several output ports

Generated (untrusted) proof script for `U1Stmt C M f` when `f` is a statement TERM (the bundled lambda
of `Tools/VedU1StructOut.lean` / the product entry) rather than a constant, and the module has registers.
Not packed: the contract keeps one output port per field (docs: reviewer conditions of
`sparkle-ved-struct-seq`); `outputs_of_step` quantifies over ALL ports, so the proof is

* one loop invariant `R` (the loop path's: register `n` of the module is the `toNat` of the loop-state
  component it implements, by induction on the cycle; the loop is read off the value of the whole
  bundled tuple `(applyIns … f).val s`, in which every field's projection of the loop occurs);
* the step: the module's next registers satisfy `R` at `s + 1`, and EVERY port's value equals
  `srcOf C f ins port s`, one conjunct per port (`List.mem_cons` over the port list), closed by the
  same closing tactics as the packed script (`Tools/VedU1MultiSeq.lean`).

It lives below `Tools/VedU1Entry.lean` (which imports it, for the standard entry's dispatch), so it takes
the five names the checker registers as plain `Name`s and uses the `ved_ss_*` tactics.
-/

namespace Tools.VedU1StructSeq

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Loop Tools.VedU1StructSeqTac
open Lean Meta Elab Term

/-- `ved_ss_pack_share`: the packing stage under `ved.sseq.share`.  `ved_pack_wire` on each goal (as `ved_pack_wire_all`), but
with a heartbeat budget of its own per goal (`packGoalHb`, never above what is left of the ambient one: no raise); a goal that
exhausts it is restored and given `ved_wire_bits` (the sharing-aware wiring, any size) with the same budget, and is left as
it was when that fails too.  With `VED_MS_LOG` one line per goal before and after (tree size, bit operations, DAG size,
milliseconds, heartbeats, which tactic took it), so the cost of the stage is named per goal. -/
def packGoalHb : Nat := 400000 * 1000

/-- tree >= `packRatio` x DAG and tree >= `packRatioMin`: `ved_wire_bits` before the packing step -/
def packRatio : Nat := 20
def packRatioMin : Nat := 20000

elab "ved_ss_pack_share" : tactic => do
  let gs ← Tactic.getGoals
  let log : String → Tactic.TacticM Unit := fun m => do
    if let some path ← IO.getEnv "VED_MS_LOG" then
      let h ← IO.FS.Handle.mk path .append
      h.putStrLn m
      h.flush
  let local' : Nat → Tactic.TacticM Bool → Tactic.TacticM Bool := fun n x => do
    let hb ← IO.getNumHeartbeats
    withTheReader Core.Context (fun c =>
        let left := c.maxHeartbeats - (hb - c.initHeartbeats)
        { c with maxHeartbeats := if c.maxHeartbeats == 0 then n else max 1 (min left n), initHeartbeats := hb }) x
  let mut rest : List MVarId := []
  let mut i := 0
  for g in gs do
    Tactic.setGoals [g]
    let (sz, nb, dag) ← g.withContext do
      let t ← instantiateMVars (← g.getType)
      pure (Tools.VedU1Loop.treeSizeVal t, (Tools.VedU1Loop.natBitOps t).size, (Tools.VedU1WireShare.collectDag (fun _ => true) t).size)
    log s!"VED PK goal {i} start tree={sz} bitops={nb} dag={dag}"
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoMsNow
    let st ← saveState
    let step : String → Tactic.TacticM Unit → Tactic.TacticM Bool := fun _ tac => do
      tryCatchRuntimeEx
        (local' packGoalHb (do Tactic.withoutRecover tac; pure true))
        fun e => if e.isRuntime then pure false else throw e
    let mut how := "pack_wire"
    -- a goal whose tree is at least `packRatio` times its DAG (and `packRatioMin` nodes): the unfolded register/output value
    -- is read as a tree by `ved_pack_simp` (measured, wScalarMul: tree up to ~150 x DAG); `ved_wire_bits` (equalities per
    -- shared wire) first, its failure message logged (it names the missing proposition), then the ordinary route
    let ratioRoute := (← getOptions).getBool `ved.sseq.ratio true && sz ≥ packRatioMin && sz ≥ packRatio * dag
    let mut done := false
    if ratioRoute then
      let ok0 ← try
          tryCatchRuntimeEx
            (local' packGoalHb (do Tactic.withoutRecover (Tactic.evalTactic (← `(tactic| ved_wire_bits))); pure true))
            fun e => do
              log s!"VED PK goal {i} wire_bits-first runtime failure after {(← IO.monoMsNow) - t0}ms: {(← e.toMessageData.toString).take 600}"
              if e.isRuntime then pure false else throw e
        catch e =>
          log s!"VED PK goal {i} wire_bits-first failed after {(← IO.monoMsNow) - t0}ms: {(← e.toMessageData.toString).take 600}"
          pure false
      if ok0 then
        how := "ratio:wire_bits"
        done := true
      else
        st.restore
        how := "ratio:wire_bits:failed,pack_wire"
    unless done do
      let ok1 ← step "pack_wire" (Tactic.evalTactic (← `(tactic| ved_pack_wire)))
      unless ok1 do
        st.restore
        how := how ++ ":budget,wire_bits"
        let ok2 ← try step "wire_bits" (Tactic.evalTactic (← `(tactic| ved_wire_bits)))
          catch _ => pure false
        unless ok2 do
          st.restore
          how := how ++ ":failed,left"
    log s!"VED PK goal {i} done {how} tree={sz} {(← IO.monoMsNow) - t0}ms hb={((← IO.getNumHeartbeats) - h0) / 1000}"
    i := i + 1
    rest := rest ++ (← Tactic.getGoals)
  Tactic.setGoals rest

/-- Debugging/controls only: stop the generated script after stage `k` and print the goals. -/
register_option ved.sseq.dbg : Nat := {
  defValue := 0
  descr := "ved.sseq.dbg: stop the structure-with-registers script after stage k (0: off)"
}

/-- Default off: prove the script's `OrderOk M B` through the one-pass hashed check `OrderOkLeafFast`
(`Tools/VedU1OrderFast.lean`, `orderOkLeafFast_sound`) instead of the quadratic `decide +kernel` of `OrderOk` itself
(the 560 statements of R184's `wPointOp` exceed 23 GB there), and `WidthStmt` through `WidthStmt_of_parts`
(`Tools/VedMemWidth.lean`).  Set by the multi-output child loop. -/
register_option ved.sseq.fastOrder : Bool := {
  defValue := false
  descr := "ved.sseq.fastOrder: struct script proves OrderOk via orderOkLeafFast_sound (default off)"
}

/-- Debugging/controls only (default off): the debug stop (`ved.sseq.dbg` k) ends the script with `sorry` (kernel runs on the
partial proof; the entry's strict audit then refuses) instead of failing, so the KERNEL cost of the stages up to `k` can be measured. -/
register_option ved.sseq.dbgSorry : Bool := {
  defValue := false
  descr := "ved.sseq.dbgSorry: the debug stop closes the goals with sorry (kernel cost of the partial proof; debugging only)"
}

/-- Default off: the packing stage (`all_goals (try ved_pack_simp)`) is `ved_pack_wire_all` as in the single-register loop
script (`Tools/VedU1Entry.lean`, `Tools/VedU1Wire.lean`): a goal below `shareMinTree` nodes read as a TREE keeps
`try ved_pack_simp`, a larger one is wired (`ved_wire`, equalities per shared wire) and its failure is the failure of the
step (not a budget exhaustion).  Candidate for `wScalarMul` (R184), whose `ved_pack_simp` stage exhausts the heartbeats. -/
register_option ved.sseq.share : Bool := {
  defValue := false
  descr := "ved.sseq.share: struct script packs with ved_pack_wire_all (sharing-aware for large goals), default off"
}

/-- Default off: the widths of the data inputs for `hin` by a closed `decide +kernel` (`declWidth M n = PTy.width`), then `simp`
without `M` / `declWidth` at `hin hrst` (class (a): the unsupplied local fact about the input widths). -/
register_option ved.sseq.dwLemma : Bool := {
  defValue := false
  descr := "ved.sseq.dwLemma: input widths of the module by a kernel check, not by simp at hin/hrst (default off)"
}

/-- Default off: the loop is NAMED once (`Tools/VedU1StructWires.lean`): the invariant states register `k` as the `k`-th component of
the named state `L` (`∃ L, IsLoop F L ∧ …`), the per-cycle value lemma `hU : ∀ t, L.val (t+1) = (F L).val (t+1)` is proved once, the
source value is read through `vsrc` (`srcOf` unfolded, `applyIns … f` generalised) and every later goal mentions `L.val s`, not the loop
term.  One `Signal.loop` only. -/
register_option ved.sseq.wires : Bool := {
  defValue := false
  descr := "ved.sseq.wires: struct script names the loop once (opaque L, value lemma), default off"
}

/-- Default TRUE (unchanged behaviour): under `ved.sseq.share` a packing goal with tree >= `packRatio` x DAG goes through `ved_wire_bits`
first.  Set to false to skip that attempt (measured, wScalarMul with `ved.sseq.slice`: it fails on all 66 high-ratio goals, 5-8 s and
about half of each goal's heartbeats before `ved_pack_wire` runs anyway). -/
register_option ved.sseq.ratio : Bool := {
  defValue := true
  descr := "ved.sseq.ratio: ved_ss_pack_share tries ved_wire_bits first on high tree/DAG goals (default true)"
}

/-- Default off: the three local slice facts of the packed register file (`Tools/VedU1StructSlice.lean`: `ved_slice_div`,
`ved_slice_mod`, `ved_slice_modM`) join the simp sets of every stage, so a read of register `k` becomes `x_k % 2^w_k` where the
pack is first formed, instead of the whole `K`-register pack inlined at every read. -/
register_option ved.sseq.slice : Bool := {
  defValue := false
  descr := "ved.sseq.slice: slice lemmas of the packed register file in the stage simp sets, default off"
}

/-- Default off: the let/have chain of the source value `hvsrc` is reduced by an explicit loop (`ved_ss_zeta`, sharing kept) and the
user's definition unfolded there, before the first `simp at hvsrc` (whose recursive zeta stops with "maximum recursion depth" on
R184's `wPointOp`). -/
register_option ved.sseq.zeta : Bool := {
  defValue := false
  descr := "ved.sseq.zeta: non-recursive zeta of the source value before simp (default off)"
}

/-- Default off: the closing stage first tries the NORMAL FORM of the conditional-subtract helpers (`faddMod`/`fsubMod`: `mux (ule p s) (s - p) s`): `p ≤ t` as
`¬ t < p`, `ite_not`, `Nat.add_comm` (ordered), then `done`; a leaf goal whose two sides are the same chain up to these is closed by `rfl` of the
normalised sides instead of a case split per `ite` (4-level chain: `2^k` cases of `omega` over 257-bit literals, 8M hb on the 256-bit field toy). -/
register_option ved.sseq.iteNorm : Bool := {
  defValue := false
  descr := "ved.sseq.iteNorm: closing stage tries the ite normal form (¬ t < p, ite_not, add_comm) first (default off)"
}

/-- The generated (untrusted) script for `U1Stmt C M f` where `f` is the statement TERM (the bundled
lambda `fun xs => bundle2 (D xs).f₁ (bundle2 …)` of a structure / product result, or any term of the
table's type) and `C`'s module has the registers `regs` (name, width) of `Signal.loop`s.  Every output
port of the contract is closed: ONE loop invariant ("register n = toNat of the loop-state component"), and
the module's value of EACH port is compared with `srcOf C f ins <port> s` (one conjunct per port). -/
def structLoopScript (contractN modN outsN bodyN : Name) (F : Name) (fStx : Term) (regs : List (String × Nat))
    (helpers : Array Name) : TermElabM Syntax := do
  let helpers := if ved.sseq.slice.get (← getOptions)
    then helpers ++ #[``Tools.VedU1StructSlice.ved_slice_div, ``Tools.VedU1StructSlice.ved_slice_mod,
      ``Tools.VedU1StructSlice.ved_slice_modM] else helpers
  let hsA : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    helpers.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  -- `ved.sseq.kshape`: the wrappers of core's `rfl` lemmas are added/swapped in `ved_ss_core_simp_big` (`Tools/VedU1StructSeqTac.lean`)
  let C := mkCIdent contractN
  let M := mkCIdent modN
  let O := mkCIdent outsN
  let B := mkCIdent bodyN
  let fI := mkCIdent F
  -- defined in `Tools.VedU1Entry` (which imports this file): named, not quoted
  let oStep := mkCIdent `Tools.VedU1Entry.outputs_of_step
  let f : Term := fStx
  let k := regs.length
  let hs := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"hreg{i}")
  let rNames := (regs.map fun r => Syntax.mkStrLit r.1).toArray
  let rWidths := (regs.map fun r => Syntax.mkNumLit (toString r.2)).toArray
  let insI := mkIdent `ins
  let sI := mkIdent `s
  let hinI := mkIdent `hin
  let hrstI := mkIdent `hrst
  let hR := mkIdent `hR
  let vI := mkIdent `vsrc
  let hv := mkIdent `hvsrc
  let hsAll : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    hs.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let ex1 : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems (hsA ++ hsAll)
  let ex2 : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems (hsA ++ hsAll.push (← `(Lean.Parser.Tactic.simpLemma| $hrstI:ident)))
  let exHelp : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems hsA
  let pats ← (hs.toList).mapM fun h => `(Lean.Parser.Tactic.rcasesPatLo| $h:ident)
  let hPat : TSyntax `rcasesPat ← match pats with
    | [] => `(rcasesPat| _)
    | _ => `(rcasesPat| ⟨$[$(pats.toArray)],*⟩)
  let mut tacs : Array (TSyntax `tactic) := #[]
  let timed := ved.sseq.dbg.get (← getOptions) == 97
  let wrap (t : TSyntax `tactic) : TermElabM (TSyntax `tactic) :=
    if timed then `(tactic| ved_ss_timed $t) else pure t
  tacs := tacs.push (← wrap (← `(tactic| intro $insI hok $sI st mems $hR)))
  tacs := tacs.push (← wrap (← `(tactic| have $hinI := hok.1 $sI)))
  tacs := tacs.push (← wrap (← `(tactic| have $hrstI := hok.2 $sI)))
  if ved.sseq.dwLemma.get (← getOptions) then
    let hdwI := mkIdent `hdw
    -- the widths of the data inputs by ONE closed kernel check (`declWidth M n` is a `find?` over the module's wires: `simp`
    -- unfolding `M` (every wire, every statement) and `declWidth` at `hin` costs 82 s on R184's `wPointOp`, 563 wires)
    tacs := tacs.push (← wrap (← `(tactic| have $hdwI : ∀ q ∈ ($C).inNames.zip ($C).table.ins, declWidth $M q.1 = q.2.width := by decide +kernel)))
    tacs := tacs.push (← wrap (← `(tactic| replace $hinI : ∀ q ∈ ($C).inNames.zip ($C).table.ins, $insI $sI q.1 < 2 ^ q.2.width := fun q hq => by
      have h := $hinI ⟨q.1, q.2.hw⟩ (List.mem_map.2 ⟨q, hq, rfl⟩)
      change $insI $sI q.1 < 2 ^ declWidth $M q.1 at h
      rwa [$hdwI q hq] at h)))
    tacs := tacs.push (← wrap (← `(tactic| clear $hdwI)))
    tacs := tacs.push (← wrap (← `(tactic| simp (config := { maxSteps := 2000000 }) [$C:ident, contractOf, PTy.width] at $hinI:ident $hrstI:ident)))
  else
    tacs := tacs.push (← wrap (← `(tactic| simp (config := { maxSteps := 2000000 }) [$C:ident, contractOf, Contract.dataInputs, $M:ident, declWidth] at $hinI:ident $hrstI:ident)))
  tacs := tacs.push (← wrap (← `(tactic| simp only [$O:ident, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq])))
  let wires := ved.sseq.wires.get (← getOptions)
  let LI := mkIdent `L
  let hLI := mkIdent `hL
  let hUI := mkIdent `hU
  if wires then
    -- the goal reads the source value through `vsrc` (the one `applyIns … f` value), not through its own unfolding
    tacs := tacs.push (← wrap (← `(tactic| simp only [srcOf])))
    tacs := tacs.push (← wrap (← `(tactic| ved_ss_vsrc $vI $hv)))
  else
    tacs := tacs.push (← wrap (← `(tactic| obtain ⟨$vI, $hv⟩ : ∃ v, v = (applyIns ($C).table.ins ($C).inNames $insI $f).val $sI := ⟨_, rfl⟩)))
  if ved.sseq.zeta.get (← getOptions) then
    tacs := tacs.push (← wrap (← `(tactic| ved_ss_zeta $hv [$fI:ident, $(helpers.map mkCIdent),*])))
  if Tools.VedU1StructWireEqs.ved.sseq.wireEqs.get (← getOptions) then
    -- per-wire value lemmas (`Tools/VedU1StructWireEqs.lean`): the same simp set, chunk by chunk
    tacs := tacs.push (← wrap (← `(tactic| ved_ss_wiresimp $hv:ident [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident, Signal.fst, Signal.snd, $exHelp,*])))
  else
    tacs := tacs.push (← wrap (← `(tactic| ved_ss_core_simp_big [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident, Signal.fst, Signal.snd, $exHelp,*] at $hv:ident)))
  if wires then
    let rPats ← (hs.toList).mapM fun h => `(Lean.Parser.Tactic.rcasesPatLo| $h:ident)
    let wPat : TSyntax `rcasesPat ← `(rcasesPat| ⟨$LI:ident, $hLI:ident, $[$(rPats.toArray)],*⟩)
    tacs := tacs.push (← wrap (← `(tactic| ved_ss_R2 $insI [$rNames,*] $rWidths,*)))
    tacs := tacs.push (← wrap (← `(tactic| obtain $wPat := $hR)))
    tacs := tacs.push (← wrap (← `(tactic| ved_ss_wit $LI $hLI $hv [$exHelp,*])))
    tacs := tacs.push (← wrap (← `(tactic| simp only [Tools.VedU1StructWires.isLoop_exists $hLI])))
    tacs := tacs.push (← wrap (← `(tactic| clear $hLI)))
  else
    tacs := tacs.push (← wrap (← `(tactic| ved_ss_R $insI [$rNames,*] $rWidths,*)))
    tacs := tacs.push (← wrap (← `(tactic| clear $hv)))
    -- ONE register: the invariant is the equation itself (no conjunction to take apart)
    if hs.size == 1 then
      tacs := tacs ++ #[← wrap (← `(tactic| have $(hs[0]!):ident := $hR)), ← wrap (← `(tactic| clear $hR))]
    else
      tacs := tacs.push (← wrap (← `(tactic| obtain $hPat := $hR)))
  let closing ← if ved.sseq.dbg.get (← getOptions) == 96
    then `(tactic| all_goals (ved_ss_leafwise <;> (first | ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod] | fail "leaf failed here")))
    else if ved.sseq.dbg.get (← getOptions) == 98
    then `(tactic| all_goals (ved_ss_timed (first
        | (ved_ss_leafwise <;> ved_ss_timed (ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod]))
        | ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod])))
    else if ved.sseq.dbg.get (← getOptions) == 99
    then `(tactic| all_goals (first | ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod] | fail "ved_ss_loop_close failed here"))
    else if ved.sseq.iteNorm.get (← getOptions)
    then `(tactic| all_goals (first
        | (simp only [← Nat.not_lt, ite_not, Nat.add_comm]; done)
        | (ved_ss_leafwise <;> ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod])
        | ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod]))
    else `(tactic| all_goals (first
        | (ved_ss_leafwise <;> ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod])
        | ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod]))
  let packT : TSyntax `tactic ←
    if ved.sseq.share.get (← getOptions) then `(tactic| ved_ss_pack_share)
    else `(tactic| all_goals (try ved_pack_simp))
  let stages : Array (Array (TSyntax `tactic)) := #[
    #[← `(tactic| ved_ss_unfold [$exHelp,*] ($sI + 1))],
    #[← `(tactic| ved_ss_core_simp_big [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident, Signal.fst, Signal.snd, $ex1,*])],
    #[← `(tactic| ved_ss_gen $sI)],
    #[← `(tactic| all_goals refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩),
      ← `(tactic| all_goals ved_ss_core_simp_big [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident, Signal.fst, Signal.snd, $ex2,*]),
      ← `(tactic| all_goals try (repeat' apply And.intro))],
    #[← `(tactic| all_goals (try ved_ss_wide_simp [BitVec.toNat_eq, Nat.and_one_is_mod, Tools.VedU1Loop.ved_mul_lit_bv]))],
    #[← `(tactic| all_goals (try ved_bit_simp))],
    #[← `(tactic| all_goals (try ved_or_lit))],
    #[packT],
    #[← `(tactic| all_goals (try ved_ss_xor_ones))],
    #[← `(tactic| all_goals (try ved_bits_facts)), ← `(tactic| all_goals (try ved_mul_facts)),
      ← `(tactic| all_goals (try ved_pack_simp)),
      ← `(tactic| all_goals (try simp only [Nat.mod_mul_mod, Nat.mul_mod_mod])),
      ← `(tactic| all_goals (try simp only [Tools.VedU1Loop.ved_mul_lit_nat]))],
    -- the one-bit logic again: the register fields are now plain values, so `x < 2` side conditions of
    -- `a ||| b` / `a &&& b` between comparisons (`inHdr := is1 ||| is2 ||| …`) are provable
    #[← `(tactic| all_goals (try ved_bit_simp))],
    -- a goal comparing a narrow state value with several literals is split on the state value
    #[← `(tactic| all_goals (try ved_ss_state_split))],
    #[closing]]
  let ex1w : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems (hsA ++ hsAll.push (← `(Lean.Parser.Tactic.simpLemma| $hv:ident)))
  -- the named loop: `hU` once instead of the unfolded loop in every equation / output wire; `vsrc` is replaced by its value
  -- (over `L.val s`) in the first simp
  let wStages : Array (Array (TSyntax `tactic)) := #[
    #[← `(tactic| ved_ss_succ $LI $sI [$exHelp,*])],
    #[← `(tactic| ved_ss_core_simp_big [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident, Signal.fst, Signal.snd, $ex1w,*]),
      ← `(tactic| clear $hv)],
    #[← `(tactic| ved_ss_gen2 $LI $sI)]]
  let stages := if wires then wStages ++ stages.extract 3 stages.size else stages
  let dbg := ved.sseq.dbg.get (← getOptions)
  if dbg == 50 then
    tacs := tacs.push (← `(tactic| ved_ss_unfold1 [$exHelp,*] ($sI + 1)))
  let stop ← if ved.sseq.dbgSorry.get (← getOptions) then `(tactic| all_goals sorry)
    else `(tactic| (trace_state; fail "stopped at debug stage"))
  if dbg == 1 || (dbg ≥ 50 && dbg < 96 && !(dbg ≥ 91 && dbg ≤ 94)) then tacs := tacs.push stop
  else
    for k in [0:stages.size] do
      if dbg == 0 || dbg == 96 || dbg == 97 || dbg == 98 || dbg > k + 1 then
        if dbg == 97 then
          for t in stages[k]! do tacs := tacs.push (← `(tactic| ved_ss_timed $t))
        else tacs := tacs ++ stages[k]!
      if dbg == k + 2 then tacs := tacs.push stop
  let h0wit : Array (TSyntax `tactic) ←
    if wires then pure #[← `(tactic| refine ⟨_, rfl, ?_⟩)] else pure #[]
  let h0tacs : Array (TSyntax `tactic) := #[← `(tactic| intro $insI hok)] ++ h0wit ++ #[
    ← `(tactic| ved_ss_unfold [$exHelp,*] 0),
    ← `(tactic| ved_ss_core_simp_big [st0, $C:ident, contractOf, regsOf, $M:ident, encodeInit, mask, declWidth, Signal.fst, Signal.snd, $exHelp,*]),
    ← `(tactic| all_goals decide +kernel)]
  let dbgS := ved.sseq.dbg.get (← getOptions)
  let stopT ← `(tactic| fail "stopped at debug stage")
  let skipT ← `(tactic| skip)
  let sa : TSyntax `tactic := if dbgS == 91 then stopT else skipT
  let sb : TSyntax `tactic := if dbgS == 92 then stopT else skipT
  let sc : TSyntax `tactic := if dbgS == 93 then stopT else skipT
  let sd : TSyntax `tactic := if dbgS == 94 then stopT else skipT
  let hordT : TSyntax `tactic ←
    if ved.sseq.fastOrder.get (← getOptions) then
      `(tactic| have hord : OrderOk $M $B = true := Tools.VedU1OrderFast.orderOkLeafFast_sound (by decide +kernel))
    else `(tactic| have hord : OrderOk $M $B = true := (by decide +kernel))
  -- the same option: `WidthStmt`'s wire-name `Nodup` is String-quadratic in the kernel too (563 wires of `wPointOp`:
  -- killed at 23 GB), `Tools.VedMemWidth.WidthStmt_of_parts` is the one-pass table form (sound, std3)
  let widT : TSyntax `term ←
    if ved.sseq.fastOrder.get (← getOptions) then
      `(Tools.VedMemWidth.WidthStmt_of_parts _ _ (by decide +kernel) (by decide +kernel))
    else `(by decide +kernel)
  `(by
      $sa
      $hordT
      $sb
      refine ⟨by decide +kernel, by decide +kernel, $widT, ⟨$B, hord⟩, ?_⟩
      $sc
      apply outputs_of_order $B hord
      refine $oStep $C $M $B $f $O (by decide +kernel) ?R ?h0 ?hstep
      $sd
      case hstep =>
        $tacs*
      case h0 =>
        $h0tacs*)

/-- The leaves of the result tree: statement (bundled signal) and port names,
left-first.  `pre?` is the compiler's name prefix (`splitReturnLeaves`). -/
partial def bundleTree (ty e : Lean.Expr) (pre? : Option String) :
    MetaM (Lean.Expr × List String) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFn with
  | .const ``Sparkle.Core.Signal.Signal _ => pure (e, [pre?.getD "out"])
  | .const ``Prod _ =>
    let some (a, b) := (match ty.getAppArgs with | #[a, b] => some (a, b) | _ => none)
      | throwError "ved_struct%: malformed product {ty}"
    let p := pre?.getD "out"
    let (l, ln) ← bundleTree a (← mkAppM ``Prod.fst #[e]) (some (p ++ "_0"))
    let (r, rn) ← bundleTree b (← mkAppM ``Prod.snd #[e]) (some (p ++ "_1"))
    return (← mkAppM ``Sparkle.Core.Signal.bundle2 #[l, r], ln ++ rn)
  | .const ind _ =>
    let some (.inductInfo iv) := (← getEnv).find? ind
      | throwError "ved_struct%: {ty} is not a structure of signals"
    unless iv.ctors.length == 1 && !iv.isRec && iv.numIndices == 0 do
      throwError "ved_struct%: {ind} is not a single-constructor structure"
    let some sinfo := getStructureInfo? (← getEnv) ind
      | throwError "ved_struct%: {ind} is not a structure"
    if sinfo.fieldNames.isEmpty then throwError "ved_struct%: {ind} has no fields"
    -- fields, constructor order (the compiler's order: the ctor's binder names)
    let mut leaves : Array (Lean.Expr × List String) := #[]
    for f in sinfo.fieldNames do
      let pj ← mkProjection e f
      let fty ← inferType pj
      let nm := match pre? with | none => f.toString | some p => p ++ "_" ++ f.toString
      leaves := leaves.push (← bundleTree fty pj (some nm))
    -- right-nested pairs: f₁, (f₂, (… fₙ))
    let mut acc := leaves.back!
    for i in (List.range (leaves.size - 1)).reverse do
      let (l, ln) := leaves[i]!
      acc := (← mkAppM ``Sparkle.Core.Signal.bundle2 #[l, acc.1], ln ++ acc.2)
    return acc
  | _ => throwError "ved_struct%: {ty} is not a signal, a product or a structure"

open Lean Meta in
/-- `fun xs => bundle2 …` over the declaration's own projections, with the port names: the statement
term and the output names of a result that is a `×` / structure of signals (`bundleTree`). -/
def bundledStmtT (stmt : Lean.Expr) : MetaM (Lean.Expr × List String) := do
  forallTelescopeReducing (← inferType stmt) fun xs res => do
    let (bt, ns) ← bundleTree res (mkAppN stmt xs) none
    return (← mkLambdaFVars xs bt, ns)


end Tools.VedU1StructSeq
