import Lean
import Sparkle.Compiler.Elab
import Tools.VedU1Entry
import Tools.VedMem
import Tools.VedStrictAudit
import Tools.VedU1Uns
import Tools.VedMemLoop
import Tools.VedMemS94Prof
import Tools.VedMemS94Fix
import Tools.VedMemPack
import Tools.VedMemShape
import Tools.VedMemOrder
import Tools.VedMemWidth
import Tools.VedU1Loop
import Tools.VedU1WireShare
import Tools.VedU1Wire
import Tools.VedU1LemmasExt1
import Tools.VedU1PackedEntry
import Tools.VedU1MultiSeq

/-!
# `#ved_u1_mem decl`: the U1 entry for modules with memories, with or without `Signal.loop` registers (`sparkle-ved-memory`)

Same path as `#ved_u1` (`Tools/VedU1Entry.lean`, not changed): specialise a leading `DomainConfig` binder, read
the table from the declaration's type, `synthesizeCombinational` ONCE, register `ved_mod` / `ved_contract` /
`ved_outs` / `ved_body`, elaborate a generated script against the expected statement, add the theorem with
exactly that type, strict audit.  The statement is `Tools.VedMem.MemStmt c m stmt`: the U1 statement with the
memory-free shape clause replaced by "no instances", the order clause `OrderOkM`, and the SAME
`OutputsStmt` (every output port, every cycle, every run from the initial state, all memories 0).

What the generated script proves, per memory statement `k` of the returned module (matched by let name,
`x` to the statement `_gen_x`, to the `Signal.memory` / `Signal.memoryComboRead` calls of the declaration):

* `MemInv`: the IR array `mems name_k` is, at every cycle, the contents `memState` of the declaration's
  memory (the write port's address / data / enable signals), read through `toNat`;
* for a registered read (`Signal.memory`): the data latch `st rd_k` is the declaration's registered read.

The state induction is `Tools.VedMem.outputs_of_step_mem` (the old `outputs_of_step` quantifies the memory
freely).  Everything is untrusted generation; the kernel checks the result against the stored statement.

Scope of this slice: register-free bodies (no `register` statement), no instances, every memory with one
write port and one read port whose ports are plain names, no memory read inside a write payload.  Other
shapes are refused at stage `shape` BEFORE the proof is tried; they are not accepted by a weaker statement.
-/

namespace Tools.VedMemEntry

open Lean Meta Elab Term
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedMem

/-- `(clock, reset)` of a module for the statement: as the registers use them, else, for a register-free
module with memories, the memory clock and `rst`.  Only chooses the names; `ShapeCore` checks them. -/
def clkRstOfM (m : Sparkle.IR.AST.Module) : Option (String × String) :=
  match clkRstOf m with
  | some kr => some kr
  | none =>
    match m.body.findSome? (fun s => match s with | .memory _ _ _ clk .. => some clk | _ => none) with
    | some clk => some (clk, "rst")
    | none => none

/-- one memory call of the declaration -/
structure MemCall where
  sync : Bool
  call : Lean.Expr
  aw : Nat
  dw : Nat
  wa : Lean.Expr
  wd : Lean.Expr
  we : Lean.Expr
  ra : Lean.Expr

/-- Marker for the value of a dead `let` (never type-checked, only traversed by `collectCalls`): `deadSeq b v`
keeps `v`, the value of an unused `let` of `b`, visible after the zeta step, AFTER the reachable calls of `b`.  The
synthesis emits a memory statement for such a call too (its write is a state change the module has), so the
module's memory statements and the declaration's calls match only if the dead call is counted. -/
def deadSeqName : Name := `Tools.VedMemEntry.deadSeq

/-- Marker `memTag "x" v` around the value `v` of a `let x` that binds a memory call (traversal only): the module's memory
statement for the call is `_gen_x`, and the statements come in the order of the `let`s -/
def memTagName : Name := `Tools.VedMemEntry.memTag

/-- zeta-reduce every `let` of `e`, keeping the value of a `let` that nothing uses (marked by `deadSeqName`) and
tagging the values that are memory calls (`memTagName`); the reachable part is zeta-reduced as before -/
def zetaKeepDead (e : Lean.Expr) : MetaM Lean.Expr :=
  Core.transform e (pre := fun e => do
    match e with
    | .letE n _ v b _ =>
      let v := if v.isAppOf ``Sparkle.Core.Signal.Signal.memory || v.isAppOf ``Sparkle.Core.Signal.Signal.memoryComboRead then
          mkApp2 (Lean.mkConst memTagName) (mkStrLit n.toString) v else v
      if b.hasLooseBVar 0 then return .visit (b.instantiate1 v)
      else return .visit (mkApp2 (Lean.mkConst deadSeqName) (b.lowerLooseBVars 1 1) v)
    | _ => return .continue)

/-- `deadSeq b v` ↦ `b` and `memTag x v` ↦ `v`, everywhere -/
partial def stripDead (x : Lean.Expr) : Lean.Expr :=
  x.replace fun y =>
    if y.isAppOfArity deadSeqName 2 then some (stripDead y.appFn!.appArg!)
    else if y.isAppOfArity memTagName 2 then some (stripDead y.appArg!)
    else none

/-- the memory calls of an expression, in order of first occurrence (arguments left to right), each
distinct call once -/
partial def collectCalls (unf : Name → Bool) (e : Lean.Expr) : MetaM (Array MemCall × Array (Lean.Expr × String)) := do
  let tags ← IO.mkRef (#[] : Array (Lean.Expr × String))
  let r ← IO.mkRef (#[] : Array MemCall)
  let seen ← IO.mkRef (∅ : Std.HashSet Lean.Expr)
  let rec go (e : Lean.Expr) : MetaM Unit := do
    if (← seen.get).contains e then return
    seen.modify (·.insert e)
    match e with
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if e.isAppOfArity memTagName 2 then
        go e.appArg!
        if let .lit (.strVal nm) := e.appFn!.appArg! then tags.modify (·.push (e.appArg!, nm))
        return
      if let .const n _ := fn then
        let sync := n == ``Sparkle.Core.Signal.Signal.memory
        let combo := n == ``Sparkle.Core.Signal.Signal.memoryComboRead
        if (sync || combo) && args.size ≥ 6 then
          let k := args.size
          let some aw ← evalNat (← whnf args[k-6]!) | pure ()
          let some dw ← evalNat (← whnf args[k-5]!) | pure ()
          -- the arguments first (a call inside an argument comes earlier)
          for a in args do go a
          r.modify (·.push { sync, call := e, aw, dw, wa := args[k-4]!, wd := args[k-3]!, we := args[k-2]!, ra := args[k-1]! })
          return
      if let .const n _ := fn then
        -- a loop: its body with the state variable replaced by the loop itself (the form the calls take
        -- after the fixpoint equation is applied)
        if n == ``Sparkle.Core.Signal.Signal.loop && args.size == 4 then
          let body := match args[3]! with
            | .lam _ _ b _ => b.instantiate1 e
            | f => (mkApp f e).headBeta
          go (← instantiateMVars (← zetaKeepDead body))
          return
        if unf n then
          if let some u ← unfoldDefinition? e then
            go (← instantiateMVars (← zetaKeepDead u.headBeta))
            return
      go fn
      for a in args do go a
    | .lam _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  return (← r.get, ← tags.get)

/-- The declaration's body applied to one input signal per table port (`PTy.sig`), `ins` a free variable:
unfolded, beta- and zeta-reduced. -/
def declBody (stmt : Lean.Expr) (tbl : DeclTable) (names : List String) (ins : Lean.Expr) (keepDead : Bool := false) : MetaM Lean.Expr := do
  let mut e := stmt
  for (p, n) in tbl.ins.zip names do
    e := mkApp e (mkApp3 (Lean.mkConst ``PTy.sig) (toExpr p) ins (mkStrLit n))
  let cur := (← unfoldDefinition? e).getD e
  if keepDead then instantiateMVars (← zetaKeepDead cur.headBeta) else instantiateMVars (← zetaReduce cur.headBeta)

/-- the memory calls of the declaration, each component a closed `fun ins => …`.  `order`: the names of the module's
memory statements, `dims` their (address, data) widths; the calls are put in that order when every statement
`_gen_<let name>` (or `_gen_<let name>_k`, a name the synthesizer numbered) finds a call among the `let`s of the
declaration (the module lists its memory statements in the order of the `let`s, the traversal finds the calls in the
order of their uses; among calls of one name the dimensions decide), else they stay in the order of the traversal -/
def collectAll (stmt : Lean.Expr) (tbl : DeclTable) (names : List String) (unf : Name → Bool)
    (order : List String := []) (dims : List (Nat × Nat) := []) : MetaM (Array MemCall) := do
  let insTy ← mkArrow (Lean.mkConst ``Nat) (← mkArrow (Lean.mkConst ``String) (Lean.mkConst ``Nat))
  withLocalDeclD `ins insTy fun ins => do
    let body ← declBody stmt tbl names ins (keepDead := true)
    let (cs, tags) ← collectCalls unf body
    let nameOf := fun (c : MemCall) => (tags.find? (fun (v, _) => v == c.call)).map fun (_, n) => "_gen_" ++ n
    let cs := if order.isEmpty || cs.size != order.length then cs else
      -- a `let` name used twice in the declaration is numbered by the synthesizer (`_gen_x`, `_gen_x_1`, ..) in an
      -- order that is not the traversal's: the statement `_gen_x_k` takes a call tagged `x` of its own dimensions
      -- (the first one in the traversal when several agree; the proof compares the memory itself)
      let group := fun (o : String) => cs.filter fun c => nameOf c == some o
      let baseOf := fun (o : String) =>
        if !(group o).isEmpty then o else
        match o.splitOn "_" |>.reverse with
        | k :: rest@(_ :: _) => if k.toNat?.isSome then "_".intercalate rest.reverse else o
        | _ => o
      let step := fun (st : Option (List MemCall)) (x : String × Nat × Nat) => do
        let acc ← st
        let cands := (group (baseOf x.1)).filter fun c => !(acc.any (·.call == c.call))
        let c ← (cands.find? fun c => c.aw == x.2.1 && c.dw == x.2.2) <|> cands[0]?
        pure (c :: acc)
      match (order.zip dims).foldl step (some []) with
      | some l => if l.length == order.length then l.reverse.toArray else cs
      | none => cs
    cs.mapM fun c => do
      -- the marker is for the traversal only: the pieces handed to the proof carry the reachable part
      pure { c with call := ← mkLambdaFVars #[ins] (stripDead c.call), wa := ← mkLambdaFVars #[ins] (stripDead c.wa),
                    wd := ← mkLambdaFVars #[ins] (stripDead c.wd), we := ← mkLambdaFVars #[ins] (stripDead c.we),
                    ra := ← mkLambdaFVars #[ins] (stripDead c.ra) }

/-- the proof script's pieces for one module: which memory statements are present -/
def memStmts (m : Sparkle.IR.AST.Module) : List (String × Nat × Nat × Bool × String × String × String × String × String) :=
  m.body.filterMap fun s => match s with
    | .memory name aw dw _ (.ref wa) (.ref wd) (.ref we) (.ref ra) rd cr _ _ => some (name, aw, dw, cr, wa, wd, we, ra, rd)
    | _ => none

/-- the shape this slice handles, or the reason it does not -/
def shapeProblem (m : Sparkle.IR.AST.Module) : Option String :=
  if !(instFree m.body) then
    some "the body has a submodule instance (instances belong to the hierarchy units)"
  else if m.body.all (fun s => match s with | .memory .. => false | _ => true) then
    some "the body has no memory (use #ved_u1)"
  else if m.body.any (fun s => match s with
      | .memory _ _ _ _ (.ref _) (.ref _) (.ref _) (.ref _) _ _ [] [] => false
      | .memory .. => true
      | _ => false) then
    some "a memory has extra ports or a port that is not a plain name"
  else none

syntax (name := vedMemSimp) "ved_mem_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| ved_mem_simp [$ex,*] $[$loc]?) =>
    `(tactic| ved_core_simp [comboReads, syncReadLatches, Tools.VedMem.memWritePorts_ref_one,
        Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.memory_val_succ,
        Sparkle.Core.Signal.Signal.memory_val_zero, $ex,*] $[$loc]?)

syntax (name := vedMemPeel) "ved_mem_peel " ident : tactic

/-- close `MemInv name .. (s+1) mems'` for the memory whose current invariant is `h`: peel the writes of the
other memories (`MemInv.other'`) and apply the write of this one (`MemInv.write'`); the side goals
(`hev` `hav` `hdv`) are left to the caller -/
macro_rules
  | `(tactic| ved_mem_peel $h:ident) =>
    `(tactic| first
      | exact $h
      | (ved_mem_shape ite; refine Tools.VedMem.MemInv.ite (fun _ => ?_) (fun _ => ?_) <;> ved_mem_peel $h)
      | (ved_mem_shape lam; refine Tools.VedMem.MemInv.other_leaf ?_ (by decide) _ _; ved_mem_peel $h)
      | (ved_mem_shape lam; refine Tools.VedMem.MemInv.write_leaf ?_ ?_ ?_ ?_; ved_mem_peel $h)
      | (ved_mem_shape fvar; refine Tools.VedMem.MemInv.hold_leaf ?_ ?_; ved_mem_peel $h))

/-- print the generated script before elaborating it (debugging only) -/
register_option ved.mem.debugStage : Nat := {
  defValue := 0
  descr := "insert trace_state after stage k of the hstep script (debugging only)"
}

/-- the goal-count gate after the memory loop's case split -/
register_option ved.mem.goalGate : Nat := {
  defValue := 512
  descr := "refuse (stage proof) when the memory loop's case split leaves more than this many goals; 0 disables the gate (heuristic limit)"
}

register_option ved.mem.showScript : Bool := {
  defValue := false
  descr := "print the script `#ved_u1_mem` generated"
}

/-- debugging (`ved.mem.showScript`): the resident set size, from `/proc/self/status` -/
def rssNote (tag : String) : MetaM Unit := do
  if (← IO.getEnv "VED_DUMP_DIR").isSome then
    let t ← try IO.FS.readFile "/proc/self/status" catch _ => pure ""
    let l := (t.splitOn "\n").filter (·.startsWith "VmRSS")
    Tools.VedMemLoop.dbgLog s!"RSS {tag}: {l.headD ""} t={← IO.monoMsNow}"
  if ved.mem.showScript.get (← getOptions) then
    let t ← try IO.FS.readFile "/proc/self/status" catch _ => pure ""
    let l := (t.splitOn "\n").filter (·.startsWith "VmRSS")
    IO.eprintln s!"VED MEM RSS {tag}: {l.headD ""} t={← IO.monoMsNow}"

def refuseM {α} (decl : Name) (stage : String) (msg : MessageData) : MetaM α :=
  throwError m!"VED U1 REFUSED {decl} [{stage}]: {msg}"

/-- The statement for a packed result `Signal d (A × B × ..)`: `Tools.VedU1Packed.PackedStmt` with the memory-free shape
clause replaced as in `MemStmt` (`MemStmt` of the collapsed contract; the slices follow from its outputs). -/
def MemPackedStmt (pc : Tools.VedU1Packed.PContract) (m : Sparkle.IR.AST.Module) (f : pc.tbl.Ty) : Prop :=
  Tools.VedU1Packed.PackCover pc ∧ MemStmt pc.core m (Tools.VedU1Packed.packedF pc.tbl f) ∧
    Tools.VedU1Packed.SlicesStmt pc m f

/-- The invariant `R ins s st mems` as a closed lambda: one `MemInv` per memory statement then one latch
equation per registered read. -/
def buildR (regs : List (String × Nat)) (stmts : List (String × Nat × Nat × Bool × String × String × String × String × String))
    (stmt : Lean.Expr) (tbl : DeclTable) (names : List String) (unf : Name → Bool) : MetaM Lean.Expr := do
  let strNat ← mkArrow (Lean.mkConst ``String) (Lean.mkConst ``Nat)
  let insTy ← mkArrow (Lean.mkConst ``Nat) strNat
  withLocalDeclD `ins insTy fun ins =>
  withLocalDeclD `s (Lean.mkConst ``Nat) fun s =>
  withLocalDeclD `st strNat fun st =>
  withLocalDeclD `mems (Lean.mkConst ``Sparkle.IR.Semantics.MEnv) fun mems => do
    let calls ← collectAll stmt tbl names unf (stmts.map (·.1)) (stmts.map fun x => (x.2.1, x.2.2.1))
    let inst := fun (x : Lean.Expr) => (mkApp x ins).headBeta
    -- the registers of the loops: `st name = toNat (component of the loop state at s)`
    let mut regEqs : Array Lean.Expr := #[]
    unless regs.isEmpty do
      let body ← declBody stmt tbl names ins
      let loops ← Tools.VedMemShape.nestedLoops unf body
      if loops.isEmpty then refuseM `mem "shape" m!"registers but no Signal.loop in the declaration"
      let mut compsOf : Array (List Lean.Expr) := #[]
      for L in loops do
        let some α := L.getAppArgs[1]? | refuseM `mem "shape" m!"malformed Signal.loop"
        compsOf := compsOf.push (← Tools.VedU1Loop.stateComps α)
      let widths ← (compsOf.toList.flatten).mapM fun c => Tools.VedU1Loop.compWidth c
      let some rnames := Tools.VedU1Loop.matchRegs widths regs <|> Tools.VedMemShape.matchRegsShared widths regs
        | refuseM `mem "shape" m!"the loop state components {widths} do not match the registers {regs}"
      let mut k := 0
      for j in [0:loops.size] do
        let lv ← mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, s]
        for i in [0:compsOf[j]!.length] do
          let c ← Tools.VedU1Loop.compToNat (← Tools.VedU1Loop.compProj lv i)
          regEqs := regEqs.push (← mkEq (mkApp st (mkStrLit rnames[k]!)) c)
          k := k + 1
    let mut invs : Array Lean.Expr := #[]
    let mut latches : Array Lean.Expr := #[]
    for ((name, aw, dw, cr, _, _, _, _, rd), c) in stmts.zip calls.toList do
      unless aw == c.aw && dw == c.dw && cr == !c.sync do
        refuseM `mem "shape" m!"memory statement {name} ({aw}x{dw}) does not match the declaration's memory call ({c.aw}x{c.dw}); statements {stmts.map fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1)}, calls (aw, dw, sync) {calls.toList.map fun c => (c.aw, c.dw, c.sync)}"
      let zero ← mkAppM ``BitVec.ofNat #[toExpr c.dw, toExpr 0]
      let init := Lean.mkLambda `a .default (← mkAppM ``BitVec #[toExpr c.aw]) zero
      invs := invs.push (← mkAppM ``Tools.VedMem.MemInv #[mkStrLit name, init, inst c.wa, inst c.wd, inst c.we, s, mems])
      unless cr do
        latches := latches.push (← mkEq (mkApp st (mkStrLit rd))
          (← mkAppM ``BitVec.toNat #[← mkAppM ``Sparkle.Core.Signal.Signal.val #[inst c.call, s]]))
    let all := regEqs ++ invs ++ latches
    let some last := all.back? | refuseM `mem "shape" m!"no memory"
    let mut conj := last
    for x in all.pop.reverse do conj ← mkAppM ``And #[x, conj]
    mkLambdaFVars #[ins, s, st, mems] conj

/-- the simp lemmas about the bodies' operators and address conversions, for both scripts: `.val` of an operator applied
directly through the `BitVec`-`Signal` / `Signal`-`BitVec` instances (`Tools.VedMemLoop`), the `Signal.pure` spelling
(`Tools.VedU1Lemmas`), `BitVec.ofNat w (x.toNat % 2^w) = extractLsb' 0 w x` -/
def memHelperNames : Array Name := #[``Tools.VedMem.ofNat_mod_eq_extract, ``Tools.VedMem.ofNat_mod_eq_extract', ``Tools.VedMemLoop.add_val_bs, ``Tools.VedMemLoop.add_val_sb, ``Tools.VedMemLoop.sub_val_bs, ``Tools.VedMemLoop.sub_val_sb, ``Tools.VedMemLoop.mul_val_bs, ``Tools.VedMemLoop.mul_val_sb, ``Tools.VedMemLoop.and_val_bs, ``Tools.VedMemLoop.and_val_sb, ``Tools.VedMemLoop.or_val_bs, ``Tools.VedMemLoop.or_val_sb, ``Tools.VedMemLoop.xor_val_bs, ``Tools.VedMemLoop.xor_val_sb, ``Tools.VedMemLoop.shl_val_bs, ``Tools.VedMemLoop.shl_val_sb, ``Tools.VedMemLoop.shr_val_bs, ``Tools.VedMemLoop.shr_val_sb, ``Tools.VedU1Lemmas.add_val_sc, ``Tools.VedU1Lemmas.add_val_cs, ``Tools.VedU1Lemmas.sub_val_sc, ``Tools.VedU1Lemmas.sub_val_cs, ``Tools.VedU1Lemmas.mul_val_sc, ``Tools.VedU1Lemmas.mul_val_cs, ``Tools.VedU1Lemmas.and_val_sc, ``Tools.VedU1Lemmas.and_val_cs, ``Tools.VedU1Lemmas.or_val_sc, ``Tools.VedU1Lemmas.or_val_cs, ``Tools.VedU1Lemmas.xor_val_sc, ``Tools.VedU1Lemmas.xor_val_cs, ``Tools.VedU1Lemmas.shl_val_sc, ``Tools.VedU1Lemmas.shl_val_cs, ``Tools.VedU1Lemmas.shr_val_sc, ``Tools.VedU1Lemmas.shr_val_cs]

/-- the generated script for `MemStmt C M stmt`; `R` the closed invariant -/
def memScript (dbg : Nat) (nm : Names) (F : Name) (nDom : Nat)
    (stmts : List (String × Nat × Nat × Bool × String × String × String × String × String))
    (calls : Array MemCall) (R : Lean.Expr) (helpers : Array Name) : TermElabM Syntax := do
  let helpers := helpers ++ memHelperNames
  let hsA : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    helpers.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let C := mkCIdent nm.contract
  let M := mkCIdent nm.mod
  let O := mkCIdent nm.outs
  let B := mkCIdent nm.body
  let fI := mkCIdent F
  let mut f : Term := fI
  if nDom > 0 then
    f ← `(@$fI)
    for _ in [0:nDom] do f ← `($f Sparkle.Core.Domain.defaultDomain)
  let Rstx ← Term.exprToSyntax R
  let n := stmts.length
  let nSync := (stmts.filter fun x => !x.2.2.2.1).length
  let hM := (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"hM{i}")
  let hL := (List.range nSync).toArray.map fun i => mkIdent (Name.mkSimple s!"hL{i}")
  let hD := (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"hD{i}")
  let hPatArr ← (hM ++ hL).mapM fun h => `(Lean.Parser.Tactic.rcasesPatLo| $h:ident)
  let hPat : TSyntax `rcasesPat ← if hM.size + hL.size == 1 then `(rcasesPat| _)
    else `(rcasesPat| ⟨$[$hPatArr],*⟩)
  -- one read rule per memory, in the form `simp` leaves the IR read in
  let mut rdTacs : Array (TSyntax `tactic) := #[]
  let mut rdLemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  let insI := mkIdent `ins
  let sI := mkIdent `s
  for (i, ((name, aw, dw, _, _, _, _, _, _), c)) in (List.range stmts.length).zip (stmts.zip calls.toList) |>.map (fun (i, (x, c)) => (i, (x, c))) do
    let waL ← Term.exprToSyntax c.wa
    let wdL ← Term.exprToSyntax c.wd
    let weL ← Term.exprToSyntax c.we
    let waS ← `(($waL $insI))
    let wdS ← `(($wdL $insI))
    let weS ← `(($weL $insI))
    let nameS := Syntax.mkStrLit name
    let awN := Syntax.mkNumLit (toString (2 ^ aw))
    let dwN := Syntax.mkNumLit (toString (2 ^ dw))
    let awL := Syntax.mkNumLit (toString aw)
    let dwL := Syntax.mkNumLit (toString dw)
    let hd : TSyntax `ident := hD[i]!
    let hmi : TSyntax `ident := hM[i]!
    rdTacs := rdTacs.push (← `(tactic| have $hd : ∀ a, mems $nameS (a % $awN) % $dwN =
        (Sparkle.Core.Signal.Signal.memState (fun _ => 0#$dwL) $waS $wdS $weS $sI (BitVec.ofNat $awL a)).toNat :=
      fun a => ($hmi).read' a))
    rdLemmas := rdLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $hd:ident))
  for h in hL do rdLemmas := rdLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $h:ident))
  let exAll : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems (hsA ++ rdLemmas)
  let obtainTac : TSyntax `tactic ← if hM.size + hL.size == 1 then `(tactic| have $(hM[0]!):ident := hR)
    else `(tactic| obtain $hPat := hR)
  let hin := mkIdent `hin
  let hrst := mkIdent `hrst
  let simpAll ← `(tactic| ved_mem_simp [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf,
      applyIns, $fI:ident, $hin:ident, $exAll,*])
  -- the side goals of a write: the port wires carry the declaration's enable / address / data
  let side ← `(tactic| first | (simp [PTy.sig] <;> omega) | (($simpAll:tactic) <;> omega) | (($simpAll:tactic) <;> first | omega | (split <;> simp <;> omega) | ved_wide_close [$hin:ident]) | (trace_state; fail "ved_mem: a goal is not closed"))
  let mut closers : Array (TSyntax `tactic) := #[]
  for i in [0:n] do
    let hmi : TSyntax `ident := hM[i]!
    closers := closers.push (← `(tactic| (ved_mem_peel $hmi:ident; all_goals ($side:tactic))))
  let mut firstAlt : TSyntax `tactic := closers[0]!
  for c in closers.toList.drop 1 do
    firstAlt ← `(tactic| first | ($firstAlt:tactic) | ($c:tactic))
  let stopT ← `(tactic| ved_dbg_state)
  let skipT ← `(tactic| skip)
  let dbg1 := if dbg == 1 then stopT else skipT
  let dbg2 := if dbg == 2 then stopT else skipT
  let dbg3 := if dbg == 3 then stopT else skipT
  let mut peelOnly : TSyntax `tactic := ← `(tactic| fail "no memory")
  for i in [0:n] do
    let hmi : TSyntax `ident := hM[i]!
    peelOnly ← `(tactic| first | ($peelOnly:tactic) | (ved_mem_peel $hmi:ident))
  let stop4T ← `(tactic| ((all_goals (first | (ved_mem_peel hM1) | skip)); trace_state; fail "stop4"))
  let stop5T ← `(tactic| ((case right.right.left => refine Tools.VedMem.MemInv.write'' ?_ ?_ ?_ ?_); trace_state; fail "stop5"))
  let stop6T ← `(tactic| (rotate_left 2; refine Tools.VedMem.MemInv.write'' ?_ ?_ ?_ ?_; refine Tools.VedMem.MemInv.other'' ?_ (by decide) _ _ _; trace_state; fail "stop6"))
  let stop7T ← `(tactic| ((simp [PTy.sig]); trace_state; fail "stop7"))
  let dbg4 := if dbg == 4 then stop4T else if dbg == 5 then stop5T else if dbg == 6 then stop6T else if dbg == 7 then stop7T else skipT
  let zeroTerms ← (List.range n).mapM fun _ => `(Tools.VedMem.MemInv.zero _ _ _ _)
  let h0Elems : Array Term ← do
    let mut a : Array Term := zeroTerms.toArray
    for _ in [0:nSync] do a := a.push (← `(?_))
    pure a
  let h0Term : Term ← if h0Elems.size == 1 then pure h0Elems[0]! else `(⟨$[$h0Elems],*⟩)
  `(by
      have hord : OrderOkM $M $B = true := by
        first
          | exact Tools.VedMemOrder.OrderOkM_of_parts _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
          | decide +kernel
      refine ⟨by decide +kernel, ⟨by decide +kernel, by decide +kernel⟩,
        by first
          | exact Tools.VedMemWidth.WidthStmt_of_parts _ _ (by decide +kernel) (by decide +kernel)
          | decide +kernel, ⟨$B, hord⟩, ?_⟩
      apply outputs_of_orderM $B hord
      refine outputs_of_step_mem $C $M $B $f $O (by decide +kernel) $Rstx ?h0 ?hstep
      case h0 =>
        intro $insI hok
        refine $h0Term
        all_goals simp [st0, $C:ident, contractOf, regsOf, $M:ident, encodeInit, mask, declWidth,
          Sparkle.Core.Signal.Signal.memory_val_zero]
      case hstep =>
        intro $insI hok $sI st mems hR
        have $hin := hok.1 $sI
        have $hrst := hok.2 $sI
        simp [$C:ident, contractOf, Contract.dataInputs, $M:ident, declWidth] at $hin:ident $hrst:ident
        $obtainTac
        $rdTacs*
        $dbg1
        $simpAll:tactic
        $dbg2
        refine ⟨_, _, _, ⟨rfl, rfl, rfl⟩, ?_⟩
        all_goals (try (repeat' apply And.intro))
        $dbg3
        $dbg4
        all_goals first | ($firstAlt:tactic) | ($side:tactic))

/-- the conjuncts of a right-nested `And` -/
partial def conjCount (e : Lean.Expr) : Nat :=
  match e.getAppFnArgs with
  | (``And, #[_, b]) => 1 + conjCount b
  | _ => 1

/-- The generated script when the module has registers (`Signal.loop`): `Tools/VedU1Entry.lean`'s `loopScriptFor`
with the invariant extended by the memories.  The invariant is `R` (registers first, then one `MemInv` per
memory, then one latch equation per registered read), given in full: the loop-state tactics (`ved_loop_unfold_share`,
`ved_loop_gen_share`, the closing stages) are those of `loopScriptFor`, run after the memory parts of the next
state are peeled (their side conditions are goals of the same kind as the registers'). -/
def memLoopScript (dbg gate loopGate h0Budget : Nat) (nm : Names) (F : Name) (nDom : Nat) (regs : List (String × Nat))
    (stmts : List (String × Nat × Nat × Bool × String × String × String × String × String))
    (calls : Array MemCall) (R : Lean.Expr) (helpers : Array Name) (pk : Bool := false) : TermElabM Syntax := do
  -- the state projections `Signal.fst` / `Signal.snd` of a loop's state signal are unfolded with the helpers
  let helpers := helpers ++ #[``Sparkle.Core.Signal.Signal.fst, ``Sparkle.Core.Signal.Signal.snd, ``Sparkle.Core.Signal.Signal.memoryComboRead_val]
  let helpers := helpers ++ memHelperNames
  -- a packed result (`Tools/VedU1Packed.lean`): the contract is the collapsed `PContract.core`, the declaration its `packedF`
  let helpers := if pk then helpers ++ #[``Tools.VedU1Packed.PContract.core, ``Tools.VedU1Packed.collapse, ``Tools.VedU1MultiSeqLemmas.OTy_packNat_pair, ``Tools.VedU1MultiSeqLemmas.OTy_packNat_leaf, ``Tools.VedU1Contract.OTy.width, ``Tools.VedU1Contract.PTy.width] else helpers
  let hsA : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    helpers.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let C := mkCIdent nm.contract
  let M := mkCIdent nm.mod
  let O := mkCIdent nm.outs
  let B := mkCIdent nm.body
  let fI := mkCIdent F
  let gateN := Lean.Syntax.mkNumLit (toString gate)
  let loopGateN := Lean.Syntax.mkNumLit (toString loopGate)
  let h0BudgetN := Lean.Syntax.mkNumLit (toString h0Budget)
  let mut f : Term := fI
  if nDom > 0 then
    f ← `(@$fI)
    for _ in [0:nDom] do f ← `($f Sparkle.Core.Domain.defaultDomain)
  let Cx : Term ← if pk then `(Tools.VedU1Packed.PContract.core $C) else `($C)
  let fx : Term ← if pk then `(Tools.VedU1Packed.packedF ($C).tbl $f) else `($f)
  let Rstx ← Term.exprToSyntax R
  let hsSep : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems hsA
  let n := stmts.length
  let nSync := (stmts.filter fun x => !x.2.2.2.1).length
  -- one equation per loop state component (a component sharing a register, `matchRegsShared`, has its own)
  let k := (conjCount (R.bindingBody!.bindingBody!.bindingBody!.bindingBody!)) - n - nSync
  let _ := regs
  let hR' := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"hreg{i}")
  let hM := (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"hM{i}")
  let hL := (List.range nSync).toArray.map fun i => mkIdent (Name.mkSimple s!"hL{i}")
  let hD := (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"hD{i}")
  let hAll : Array (TSyntax `ident) := hR' ++ hM ++ hL
  let hNorm : Array (TSyntax `ident) := hAll ++ hD
  let hPatArr ← hAll.mapM fun h => `(Lean.Parser.Tactic.rcasesPatLo| $h:ident)
  -- option `ved.mem.hstepDag`: `hR` taken apart by projections (`ved_obtain_dag`); the `obtain` is the fallback
  let obtainTac : TSyntax `tactic ← if hAll.size == 1 then `(tactic| have $(hAll[0]!):ident := hR)
    else `(tactic| first
      | (ved_hstep_dag_on
         ved_obtain_dag hR [$hAll,*])
      | obtain ⟨$[$hPatArr],*⟩ := hR)
  let insI := mkIdent `ins
  let sI := mkIdent `s
  let hinI := mkIdent `hin
  let hrstI := mkIdent `hrst
  let mut rdTacs : Array (TSyntax `tactic) := #[]
  let mut rdLemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for (i, ((name, aw, dw, _, _, _, _, _, _), c)) in (List.range stmts.length).zip (stmts.zip calls.toList) |>.map (fun (i, (x, c)) => (i, (x, c))) do
    let waL ← Term.exprToSyntax c.wa
    let wdL ← Term.exprToSyntax c.wd
    let weL ← Term.exprToSyntax c.we
    let waS ← `(($waL $insI))
    let wdS ← `(($wdL $insI))
    let weS ← `(($weL $insI))
    let nameS := Syntax.mkStrLit name
    let awN := Syntax.mkNumLit (toString (2 ^ aw))
    let dwN := Syntax.mkNumLit (toString (2 ^ dw))
    let awL := Syntax.mkNumLit (toString aw)
    let dwL := Syntax.mkNumLit (toString dw)
    let hd : TSyntax `ident := hD[i]!
    let hmi : TSyntax `ident := hM[i]!
    rdTacs := rdTacs.push (← `(tactic| have $hd : ∀ a, mems $nameS (a % $awN) % $dwN =
        (Sparkle.Core.Signal.Signal.memState (fun _ => 0#$dwL) $waS $wdS $weS $sI (BitVec.ofNat $awL a)).toNat :=
      fun a => ($hmi).read' a))
    rdLemmas := rdLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $hd:ident))
  for h in hL do rdLemmas := rdLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $h:ident))
  for h in hR' do rdLemmas := rdLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $h:ident))
  let ex1 : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems (hsA ++ rdLemmas)
  let ex2 : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems (hsA ++ rdLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $hrstI:ident)))
  -- option `ved.mem.hstepNorm`: the simps after the invariant do not enter `Signal.loop` (`vedMemLoopFreeze`, `↓`)
  let fzL ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedMemLoopFreeze):term)
  let dwL ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedDeclWidth):term)
  let dw1L ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedDeclWidth1):term)
  let bsO ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedBindStrictO):term)
  let bsB ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedBindStrictB):term)
  -- `VED_S94_NOBIND` (diagnosis only): the new branch without the in-order `Option.bind` simprocs
  let efL ← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedEnvFreeze):term)
  let fzs0 := if (← IO.getEnv "VED_S94_NOBIND").isSome then #[fzL, dwL, dw1L] else #[fzL, dwL, dw1L, bsO, bsB]
  -- option `ved.mem.s94EnvFreeze` (new branch only): the environment functions of the module semantics are not entered
  let fzs := if Tools.VedMemLoop.ved.mem.s94EnvFreeze.get (← getOptions) then fzs0.push efL else fzs0
  -- diagnosis only (`VED_PROBE_S94` and `VED_DUMP_DIR`): the counting simproc of stage 94
  let probeL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    if (← IO.getEnv "VED_PROBE_S94").isSome && (← IO.getEnv "VED_DUMP_DIR").isSome && (← IO.getEnv "VED_S94_PROF").isNone then
      pure #[← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkCIdent ``Tools.VedMemLoop.vedMemProbe):term)]
    else pure #[]
  let ex1F : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems (probeL ++ fzs ++ (hsA ++ rdLemmas))
  let ex2F : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems (fzs ++ (hsA ++ rdLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $hrstI:ident))))
  let hsSepF : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems (fzs ++ hsA)
  let memSimpLemmas ← `(Lean.Parser.Tactic.simpLemma| comboReads)
  let _ := memSimpLemmas
  -- the memory parts of the next state: peel (the side conditions stay as goals)
  let mut peels : Array (TSyntax `tactic) := #[]
  for i in [0:n] do
    let hmi : TSyntax `ident := hM[i]!
    peels := peels.push (← `(tactic| (ved_mem_peel $hmi:ident)))
  let mut peelAlt : TSyntax `tactic := peels[0]!
  for c in peels.toList.drop 1 do
    peelAlt ← `(tactic| first | ($peelAlt:tactic) | ($c:tactic))
  let zeroTerms ← (List.range n).mapM fun _ => `(Tools.VedMem.MemInv.zero _ _ _ _)
  let h0Elems : Array Term ← do
    let mut a : Array Term := #[]
    for _ in [0:k] do a := a.push (← `(?_))
    a := a ++ zeroTerms.toArray
    for _ in [0:nSync] do a := a.push (← `(?_))
    pure a
  let h0Term : Term ← if h0Elems.size == 1 then pure h0Elems[0]! else `(⟨$[$h0Elems],*⟩)
  let closing ← `(tactic| all_goals (first | ved_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod, Tools.VedU1Loop.ved_mul_lit_nat, Tools.VedU1LemmasExt1.beq_eq_bne, Nat.add_zero, Nat.sub_zero, Nat.zero_add, Int.bmod_def, Int.natCast_zero, Int.add_zero, Int.sub_zero] | ved_bmod_close | ((try ved_bits_facts) <;> (repeat' split) <;> (try simp (disch := omega) only [Nat.mod_eq_of_lt]) <;> (try ved_bits_facts) <;> omega) | (have hb1 : Bool.toNat true = 1 := rfl; have hb0 : Bool.toNat false = 0 := rfl; omega)))
  let closing ← if pk then `(tactic| ved_all_goals_log ((ved_clear_sig_big; first | ved_decide_small2 | ved_ctrl_cases | ved_leaf_gate (first | (ved_leafwise <;> (first | ved_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod, Tools.VedU1Loop.ved_mul_lit_nat, Tools.VedU1LemmasExt1.beq_eq_bne, Nat.add_zero, Nat.sub_zero, Nat.zero_add, Int.bmod_def, Int.natCast_zero, Int.add_zero, Int.sub_zero] | ved_bmod_close | ((try ved_bits_facts) <;> (repeat' split) <;> (try simp (disch := omega) only [Nat.mod_eq_of_lt]) <;> (try ved_bits_facts) <;> omega) | (have hb1 : Bool.toNat true = 1 := rfl; have hb0 : Bool.toNat false = 0 := rfl; omega))) | (first | ved_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod, Tools.VedU1Loop.ved_mul_lit_nat, Tools.VedU1LemmasExt1.beq_eq_bne, Nat.add_zero, Nat.sub_zero, Nat.zero_add, Int.bmod_def, Int.natCast_zero, Int.add_zero, Int.sub_zero] | ved_bmod_close | ((try ved_bits_facts) <;> (repeat' split) <;> (try simp (disch := omega) only [Nat.mod_eq_of_lt]) <;> (try ved_bits_facts) <;> omega) | (have hb1 : Bool.toNat true = 1 := rfl; have hb0 : Bool.toNat false = 0 := rfl; omega)))))) else pure closing
  let closingDbg ← `(tactic| all_goals (first | ved_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod, Tools.VedU1Loop.ved_mul_lit_nat, Tools.VedU1LemmasExt1.beq_eq_bne, Nat.add_zero, Nat.sub_zero, Nat.zero_add, Int.bmod_def, Int.natCast_zero, Int.add_zero, Int.sub_zero] | ved_bmod_close | ((try ved_bits_facts) <;> (repeat' split) <;> (try simp (disch := omega) only [Nat.mod_eq_of_lt]) <;> (try ved_bits_facts) <;> omega) | (have hb1 : Bool.toNat true = 1 := rfl; have hb0 : Bool.toNat false = 0 := rfl; omega) | ved_dbg_state))
  let closing := if dbg == 17 then closingDbg else closing
  let mkStages := fun (fz : Bool) => do
   let ex2 := if fz then ex2F else ex2
   let lw : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
     Syntax.TSepArray.ofElems ((if fz then fzs else #[]) ++ #[← `(Lean.Parser.Tactic.simpLemma| BitVec.toNat_eq),
       ← `(Lean.Parser.Tactic.simpLemma| Nat.and_one_is_mod), ← `(Lean.Parser.Tactic.simpLemma| Tools.VedU1Loop.ved_mul_lit_bv)])
   let stages : Array (Array (TSyntax `tactic)) := #[
    #[← `(tactic| all_goals (try ved_lt_close)),
      ← `(tactic| all_goals (try ved_loop_simp [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident, $ex2,*])),
      ← `(tactic| all_goals try (repeat' apply And.intro)),
      ← `(tactic| all_goals (try ved_lt_close))],
    #[← `(tactic| all_goals (try ved_loopw_simp [$lw,*]))],
    #[← `(tactic| ved_bit_simp_share_m)],
    #[← `(tactic| all_goals (try ved_or_lit_g))],
    #[← `(tactic| all_goals (try ved_mem_addr)), ← `(tactic| all_goals (try ved_addr_post_g))],
    #[← `(tactic| ved_pack_dag_wire_all), ← `(tactic| ved_stamp 51), ← `(tactic| ved_all_goals_log (try ved_bit_simp_g)), ← `(tactic| ved_stamp 52), ← `(tactic| ved_all_goals_log (try (first | (ved_dag_only; ved_pack_dag) | skip))), ← `(tactic| ved_stamp 53), ← `(tactic| ved_all_goals_log (try ved_or_lit_post))],
    #[← `(tactic| ved_all_goals_log (try ved_bits_facts)), ← `(tactic| ved_stamp 61), ← `(tactic| ved_all_goals_log (try ved_mul_facts)), ← `(tactic| ved_stamp 62),
      ← `(tactic| ved_all_goals_log (try ved_pack_simp_g)), ← `(tactic| ved_stamp 63),
      ← `(tactic| all_goals (try simp only [Nat.mod_mul_mod, Nat.mul_mod_mod])), ← `(tactic| ved_stamp 64),
      ← `(tactic| all_goals (try simp only [Tools.VedU1Loop.ved_mul_lit_nat])), ← `(tactic| ved_stamp 65),
      ← `(tactic| all_goals (try simp only [Tools.VedU1Loop.ved_mul_lit_nat] at *))],
    #[← `(tactic| all_goals (try simp only [Tools.VedMem.ofNat_mod_eq_extract'])), closing]]
   let stopStage ← `(tactic| ved_dbg_state)
   let tail ← (stages.zipIdx.mapM fun (st, k) => do
     let stamp ← `(tactic| ved_stamp $(Syntax.mkNumLit (toString k)))
     pure (if dbg == 20 + k then (#[stamp] ++ st).push stopStage else #[stamp] ++ st))
   pure tail.flatten
  let stopStage ← `(tactic| ved_dbg_state)
  let tail ← mkStages false
  let tailF ← mkStages true
  -- the declaration's loops in the hypotheses take the simp normal form of the goal's (the invariant was
  -- built from the declaration as written; `loopScriptFor` builds it from the normalised source instead)
  -- option `ved.mem.hstepDag`: the same simp, each distinct loop of the hypotheses simplified once (`ved_hnorm_dag`); the old step is the fallback
  let normHyps ← `(tactic| try (first
    | (ved_hstep_dag_on
       ved_hnorm_dag [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf,
         applyIns, $fI:ident, comboReads, syncReadLatches, Tools.VedMem.memWritePorts_ref_one,
         Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.memory_val_succ,
         Sparkle.Core.Signal.Signal.memory_val_zero, $hsSep,*] at $[$hNorm]*)
    | (ved_loop_simp [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf,
         applyIns, $fI:ident, comboReads, syncReadLatches, Tools.VedMem.memWritePorts_ref_one,
         Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.memory_val_succ,
         Sparkle.Core.Signal.Signal.memory_val_zero, $hsSep,*] at $[$hNorm]*)))
  let stopT := stopStage
  let skipT ← `(tactic| skip)
  let d := fun (k : Nat) => if dbg == k then stopT else skipT
  let d1 := d 11
  let d2 := d 12
  let d3 := d 13
  let d4 := d 14
  let d5 := d 15
  let d6 := d 16
  let d18 ← if dbg == 18 then `(tactic| (rotate_left 4; ved_mem_shape ite; refine Tools.VedMem.MemInv.ite (fun _ => ?_) (fun _ => ?_); ved_dbg_state)) else `(tactic| skip)
  let d10 := d 10
  let hinSimp : TSyntax `tactic ←
    if pk then `(tactic| ved_hin_simp $M:ident)
    else `(tactic| simp [$C:ident, contractOf, Contract.dataInputs, $M:ident, declWidth] at $hinI:ident $hrstI:ident)
  let keyTacs : Array (TSyntax `tactic) ← if pk then pure #[
      ← `(tactic| have key : ∀ t, Tools.VedU1Contract.srcOf (Tools.VedU1Packed.PContract.core $C) (Tools.VedU1Packed.packedF ($C).tbl $f) $insI "out" t =
          Tools.VedU1Contract.OTy.packNat ($C).tbl.out ((Tools.VedU1Contract.applyIns ($C).tbl.ins ($C).inNames $insI $f).val t) := fun t => Tools.VedU1Packed.srcOf_packed $C $f $insI t),
      ← `(tactic| simp only [$O:ident, List.mem_singleton, forall_eq, key])] else pure #[← `(tactic| skip)]
  -- the step case from the hypotheses' normalisation to the end; `fz`: the simps do not enter `Signal.loop` (option `ved.mem.hstepNorm`)
  let prof := (← IO.getEnv "VED_S94_PROF").isSome
  let mkSeg := fun (nh : TSyntax `tactic) (e1 : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma ",") (tl : Array (TSyntax `tactic)) (r99 : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma ",") (un : TSyntax `tactic) (dg : Bool) (atm : Bool) (nic : Bool) => do
    let dgT : TSyntax `tactic ← if dg && prof then `(tactic| all_goals (ved_s94_prof [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident,
            comboReads, syncReadLatches, Tools.VedMem.memWritePorts_ref_one,
            Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.memory_val_succ,
            Sparkle.Core.Signal.Signal.memory_val_zero, $e1,*]))
        else if dg then `(tactic| all_goals (ved_s94_diag [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident,
            comboReads, syncReadLatches, Tools.VedMem.memWritePorts_ref_one,
            Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.memory_val_succ,
            Sparkle.Core.Signal.Signal.memory_val_zero, $e1,*])) else `(tactic| skip)
    let simpT : TSyntax `tactic ← `(tactic| all_goals (ved_loop_simp [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident,
            comboReads, syncReadLatches, Tools.VedMem.memWritePorts_ref_one,
            Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.memory_val_succ,
            Sparkle.Core.Signal.Signal.memory_val_zero, $e1,*]))
    -- option `ved.mem.s94LoopAtom` (new branch only): the stage-94 simp runs on a goal whose loops are atoms; the plain simp is the fallback
    let s94T0 : TSyntax `tactic ← if atm then `(tactic| first | ved_s94_atom ($dgT:tactic; $simpT:tactic) | ($dgT:tactic; $simpT:tactic)) else `(tactic| ($dgT:tactic; $simpT:tactic))
    -- option `ved.mem.s94NoIteCongr` (new branch only): the stage-94 simp without the congruence theorem `ite_congr`; the old simp is the fallback
    let s94T : TSyntax `tactic ← if nic then `(tactic| first | ved_s94_noitecongr ($s94T0:tactic) | $s94T0:tactic) else pure s94T0
    `(tactic| (
          $nh
          ved_stamp 93
          $d1
          ved_loop_unfold_mem (limit := $loopGateN) [$hsSep,*] ($sI + 1)
          $d2
          ved_stamp 94
          ved_s94_probe_start
          $s94T
          ved_s94_probe_stop
          $un
          ved_stamp 95
          $d3
          all_goals refine ⟨_, _, _, ⟨rfl, rfl, rfl⟩, ?_⟩
          ved_stamp 96
          all_goals (try (repeat' apply And.intro))
          ved_stamp 97
          $d4
          $d18
          all_goals (try $peelAlt:tactic)
          ved_stamp 98
          ved_goal_gate $gateN
          $d5
          ved_if_read (ved_loop_simp [$r99,*])
          ved_stamp 99
          ved_dsimp_goals
          ved_stamp 100
          ved_loop_gen_mem $sI
          $d6
          $tl*))
  let normHypsF ← `(tactic| (ved_hstep_loops_clear; try (ved_loop_simp [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf,
         applyIns, $fI:ident, comboReads, syncReadLatches, Tools.VedMem.memWritePorts_ref_one,
         Sparkle.Core.Signal.Signal.memoryComboRead_val, Sparkle.Core.Signal.Signal.memory_val_succ,
         Sparkle.Core.Signal.Signal.memory_val_zero, $hsSepF,*] at $[$hNorm]*); ved_hstep_loops))
  let mcr ← `(Lean.Parser.Tactic.simpLemma| Sparkle.Core.Signal.Signal.memoryComboRead_val)
  let segOld ← mkSeg normHyps ex1 tail (Syntax.TSepArray.ofElems #[mcr]) (← `(tactic| skip)) false false false
  let segNew ← mkSeg normHypsF ex1F tailF (Syntax.TSepArray.ofElems (fzs.push mcr)) (← `(tactic| ved_hstep_unify)) ((← IO.getEnv "VED_S94_DIAG").isSome || prof) (Tools.VedMemLoop.ved.mem.s94LoopAtom.get (← getOptions)) (Tools.VedMemS94Fix.ved.mem.s94NoIteCongr.get (← getOptions))
  let core ← `(by
    ved_no_recover (
        ved_stamp 80
        have hord : OrderOkM $M $B = true := by
          first
            | exact Tools.VedMemOrder.OrderOkM_of_parts _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
            | decide +kernel
        ved_stamp 81
        refine ⟨by decide +kernel, ⟨by decide +kernel, by decide +kernel⟩,
          by first
            | exact Tools.VedMemWidth.WidthStmt_of_parts _ _ (by decide +kernel) (by decide +kernel)
            | decide +kernel, ⟨$B, hord⟩, ?_⟩
        ved_stamp 82
        apply outputs_of_orderM $B hord
        ved_stamp 83
        refine outputs_of_step_mem $Cx $M $B $fx $O (by decide +kernel) $Rstx ?h0 ?hstep
        case h0 =>
          ved_h0_mark 0
          ved_stamp 84
          intro $insI hok
          ved_loop_unfold_mem (limit := $loopGateN) [$hsSep,*] 0
          ved_stamp 85
          ved_h0_mark 1
          ved_h0_budget $h0BudgetN (
            first
              | (ved_h0_dag_on
                 refine $h0Term
                 all_goals ved_h0_dag_close)
              | (refine $h0Term
                 $d10
                 all_goals ved_loop_simp [st0, $C:ident, contractOf, regsOf, $M:ident, encodeInit, mask, declWidth,
                   Sparkle.Core.Signal.Signal.memory_val_zero, $hsSep,*]))
          ved_h0_done
          ved_stamp 86
          all_goals (try decide +kernel)
          ved_stamp 87
        case hstep =>
          ved_stamp 88
          intro $insI hok $sI st mems hR
          have $hinI := hok.1 $sI
          have $hrstI := hok.2 $sI
          ved_stamp 90
          $hinSimp
          ved_stamp 91
          $keyTacs*
          ved_stamp 911
          $obtainTac
          ved_stamp 92
          $rdTacs*
          ved_stamp 921
          first
            | (ved_hstep_norm_on
               ved_hstep_logfail $segNew
               ved_hstep_loops_clear
               ved_hstep_norm_ran)
            | (ved_hstep_fallback_reset
               $segOld:tactic)
          ))
  if pk then
    `(by
        have hP : Tools.VedU1Packed.PackCover $C := by decide
        have hU : MemStmt (Tools.VedU1Packed.PContract.core $C) $M (Tools.VedU1Packed.packedF ($C).tbl $f) := $core
        exact ⟨hP, hU, Tools.VedU1Packed.slices_of_outputs hP.1 hU.2.2.2.2⟩)
  else pure core

/-! ## The checker -/

/-- The checker below the entry (the copy of `checkU1E`'s steps for the memory statement).  `m` is the module
the synthesis returned, `stmt` the statement's term. -/
def checkMemE (decl : Name) (base : Name) (stmt : Lean.Expr) (m : Sparkle.IR.AST.Module)
    (outNames : List String := ["out"]) (packed : Bool := false) : TermElabM Name := do
  let nm : Names := { (Names.ofBase base) with thm := base ++ `ved_mem }
  let saved ← saveState
  tryCatchRuntimeEx (do
    let tbl ← try readTableOfType decl (← inferType stmt) catch e => refuse decl "table" e.toMessageData
    if packed then
      unless tbl.out.flat.length ≥ 2 do
        refuse decl "packed" m!"the result is not a product inside one `Signal`"
      unless m.outputs.map (·.name) == ["out"] do
        refuse decl "packed" m!"the module's output ports {m.outputs.map (·.name)} are not the one packed port `out`"
    else
      unless tbl.out.flat.length == 1 && outNames.length == 1 do
        refuse decl "multi-output" m!"{tbl.out.flat.length} output projections (this slice: one output; `#ved_u1_mem_packed` takes a product)"
    if let some why := shapeProblem m then refuse decl "shape" m!"{why}"
    let mE := toExpr m
    let back ← withEvalBudget (evalModule mE)
    unless decide (back = m) do
      refuse decl "artifact" m!"toExpr of the returned module does not evaluate back to it"
    addDefn nm.mod (Lean.mkConst ``Sparkle.IR.AST.Module) mE
    let clkRst := clkRstOfM m
    let pc : Tools.VedU1Packed.PContract :=
      { modName := m.name, tbl, port := "out", slices := tbl.out.slices,
        inNames := tbl.binders.map ("_gen_" ++ ·), wires := m.wires,
        clkRst := clkRstOf m, inits := (regsOf m.body).map (fun r => (r.1, r.2.2.2)) }
    if packed then
      unless decide (Tools.VedU1Packed.PackCover pc) do
        refuse decl "packed" m!"the slice map is not the packing rule's map for the declaration's result"
      addDefn nm.contract (Lean.mkConst ``Tools.VedU1Packed.PContract) (toExpr pc)
      addDefn nm.outs (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Port))
        (toExpr pc.core.outputs)
    else
      let cE := mkAppN (Lean.mkConst ``contractOf)
        #[toExpr tbl, toExpr outNames, toExpr clkRst, Lean.mkConst nm.mod]
      addDefn nm.contract (Lean.mkConst ``Contract) cE
      let c := contractOf tbl outNames clkRst m
      addDefn nm.outs (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Port))
        (toExpr c.outputs)
    let b0 := orderBody m.body
    unless OrderOkM m b0 do
      refuse decl "order"
        m!"no arrangement of the body assigns every wire before it is read (combinational cycle, self-read, undriven net or duplicate update)"
    addDefn nm.body (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Stmt))
      (toExpr b0)
    let expected := mkAppN (Lean.mkConst (if packed then ``MemPackedStmt else ``MemStmt)) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
    try check expected catch e => refuse decl "type" e.toMessageData
    unless ← isProp expected do refuse decl "type" m!"expected statement is not a Prop"
    let stmts := memStmts m
    let helpers ← helperConsts stmt.getAppFn.constName!
    let unf : Name → Bool := fun n => n == stmt.getAppFn.constName! || helpers.contains n
    let inNames := tbl.binders.map ("_gen_" ++ ·)
    let calls ← try collectAll stmt tbl inNames unf (memStmts m |>.map (·.1)) (memStmts m |>.map fun x => (x.2.1, x.2.2.1)) catch e => refuse decl "shape" e.toMessageData
    let regsL := (regsOf m.body).map fun r => (r.1, declWidth m r.1)
    let R ← try buildR regsL stmts stmt tbl inNames unf catch e => refuse decl "shape" e.toMessageData
    unless calls.size == stmts.length do
      refuse decl "shape"
        m!"the module has {stmts.length} memory statements, the declaration {calls.size} memory calls (cannot match them)"
    let nDom := stmt.getAppNumArgs
    let regsL := (regsOf m.body).map fun r => (r.1, declWidth m r.1)
    let stx ← if regsL.isEmpty then
        if packed then refuse decl "shape" m!"register-free packed modules with memories: not in this slice" else
        memScript (ved.mem.debugStage.get (← getOptions)) nm stmt.getAppFn.constName! nDom stmts calls R helpers
      else do
        unless ← Tools.VedU1Uns.usesLoop stmt.getAppFn.constName! helpers do
          refuse decl "shape" m!"the body has registers that do not come from a `Signal.loop` (this slice: loops)"
        memLoopScript (ved.mem.debugStage.get (← getOptions)) (ved.mem.goalGate.get (← getOptions)) (Tools.VedMemLoop.ved.mem.loopGate.get (← getOptions)) (Tools.VedMemLoop.ved.mem.h0Budget.get (← getOptions)) nm stmt.getAppFn.constName! nDom regsL stmts calls R helpers packed
    let scriptTxt ← PrettyPrinter.ppTerm ⟨stx⟩
    if ved.mem.showScript.get (← getOptions) then IO.eprintln s!"VED MEM SCRIPT {scriptTxt}"
    let errsBefore := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
    -- option `ved.mem.hstepNorm`: `declWidth M "wire"` is answered from this table in the new branch's simps (`Tools.VedMemLoop.vedDeclWidth`)
    if Tools.VedMemLoop.ved.mem.hstepNorm.get (← getOptions) then
      let tab : Std.HashMap String Nat := m.wires.foldl (fun t p =>
        if t.contains p.name then t else t.insert p.name (Tools.VedU1Contract.declWidth m p.name)) {}
      Tools.VedMemLoop.declWidthTab.set (some (nm.mod, tab))
    let pf ← try (tryCatchRuntimeEx
      (withProofBudget do
        withoutErrToSorry do
          rssNote "before elab"
          let e ← elabTermEnsuringType stx expected
          rssNote "elabTermEnsuringType done"
          synthesizeSyntheticMVarsNoPostponing
          rssNote "synthesize done"
          let e ← instantiateMVars e
          if ved.mem.showScript.get (← getOptions) then
            IO.eprintln s!"VED MEM proof dag size {(Tools.VedU1WireShare.collectDag (fun _ => true) e).size}"
          rssNote "instantiateMVars done"
          return e)
      fun e => do
        if ved.mem.showScript.get (← getOptions) then
          for msg in (← Core.getMessageLog).toList do IO.eprintln s!"VED MEM MSG {← msg.data.toString}"
        refuse decl "proof" e.toMessageData)
      finally Tools.VedMemLoop.declWidthTab.set none
    if ved.mem.showScript.get (← getOptions) then IO.eprintln s!"VED MEM elaborated, proof term size {pf.approxDepth}"
    let errs := (← Core.getMessageLog).toList.filter (·.severity == .error)
    if errs.length != errsBefore then
      let new := errs.drop errsBefore
      let first ← match new with
        | msg :: _ => msg.data.toString
        | [] => pure ""
      if ved.mem.showScript.get (← getOptions) then
        for msg in (← Core.getMessageLog).toList do IO.eprintln s!"VED MEM MSG {← msg.data.toString}"
      refuse decl "proof" m!"errors were logged while elaborating the proof; first: {first}"
    rssNote "proof elaborated"
    if pf.hasMVar || pf.hasFVar then refuse decl "proof" m!"proof term is not closed"
    if ved.mem.showScript.get (← getOptions) then IO.eprintln s!"VED MEM kernel check starts"
    tryCatchRuntimeEx
      (withProofBudget <| withOptions (fun o => o.setBool `Elab.async false) do
        addDecl (.thmDecl { name := nm.thm, levelParams := [], type := expected, value := pf }))
      fun e => refuse decl "kernel" e.toMessageData
    rssNote "kernel done"
    let some (.thmInfo ti) := (← getEnv).find? nm.thm
      | refuse decl "kernel" m!"{nm.thm} is not a theorem in the environment"
    unless ti.type == expected do refuse decl "type" m!"stored type differs from the expected statement"
    try discard <| Tools.VedStrictAudit.strictAudit nm.thm
    catch e => refuse decl "audit" e.toMessageData
    return nm.thm) fun e => do
    saved.restore (restoreInfo := true)
    if ← isRefusal e then throw e
    refuse decl "checker" e.toMessageData

/-- the entry: `synthesizeCombinational` ONCE, the statement over the returned module and the declaration -/
def vedMemEntryS (declName : Name) (packed : Bool := false) :
    TermElabM (Sparkle.IR.AST.Module × Design × Name × Nat) := do
  let (stmt, nDom) ← try specialiseDomain declName catch e => refuse declName "table" e.toMessageData
  let tbl ← try readTableOfType declName (← inferType stmt) catch e => refuse declName "table" e.toMessageData
  if packed then
    unless tbl.out.flat.length ≥ 2 do
      refuse declName "packed" m!"the result is not a product inside one `Signal` (use `#ved_u1_mem`)"
  else
    unless tbl.out.flat.length == 1 do
      refuse declName "multi-output" m!"{tbl.out.flat.length} output projections (use `#ved_u1_mem_packed`)"
  let (m, d) ← try Sparkle.Compiler.Elab.synthesizeCombinational declName
    catch e => refuse declName "synthesis" e.toMessageData
  let thm ← checkMemE declName declName stmt m (packed := packed)
  return (m, d, thm, nDom)

open Lean Elab Command in
elab "#ved_u1_mem " id:ident : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  Command.liftTermElabM do
    let (m, _, thm, nDom) ← vedMemEntryS decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U1 MEM OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}\n{repr m}"

open Lean Elab Command in
/-- `#ved_u1_mem_packed decl`: `#ved_u1_mem` for a result `Signal d (A × B × ..)` (statement `MemPackedStmt`) -/
elab "#ved_u1_mem_packed " id:ident : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  Command.liftTermElabM do
    let (m, _, thm, nDom) ← vedMemEntryS decl (packed := true)
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U1 MEM PACKED OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}"

end Tools.VedMemEntry
