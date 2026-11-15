import Lean
import Sparkle.Compiler.Elab
import Tools.VedU1Entry
import Tools.VedMem
import Tools.VedStrictAudit

/-!
# `#ved_u1_mem decl`: the U1 entry for register-free modules with memories (`sparkle-ved-memory`)

Same path as `#ved_u1` (`Tools/VedU1Entry.lean`, not changed): specialise a leading `DomainConfig` binder, read
the table from the declaration's type, `synthesizeCombinational` ONCE, register `ved_mod` / `ved_contract` /
`ved_outs` / `ved_body`, elaborate a generated script against the expected statement, add the theorem with
exactly that type, strict audit.  The statement is `Tools.VedMem.MemStmt c m stmt`: the U1 statement with the
memory-free shape clause replaced by "no instances", the order clause `OrderOkM`, and the SAME
`OutputsStmt` (every output port, every cycle, every run from the initial state, all memories 0).

What the generated script proves, per memory statement `k` of the returned module (matched, in the order of
the module's memory statements, to the `Signal.memory` / `Signal.memoryComboRead` calls of the declaration):

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

/-- the memory calls of an expression, in order of first occurrence (arguments left to right), each
distinct call once -/
partial def collectCalls (unf : Name → Bool) (e : Lean.Expr) : MetaM (Array MemCall) := do
  let r ← IO.mkRef (#[] : Array MemCall)
  let seen ← IO.mkRef (∅ : Std.HashSet Lean.Expr)
  let rec go (e : Lean.Expr) : MetaM Unit := do
    if (← seen.get).contains e then return
    seen.modify (·.insert e)
    match e with
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
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
        if unf n then
          if let some u ← unfoldDefinition? e then
            go (← instantiateMVars (← zetaReduce u.headBeta))
            return
      go fn
      for a in args do go a
    | .lam _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  r.get

/-- The declaration's body applied to one input signal per table port (`PTy.sig`), `ins` a free variable:
unfolded, beta- and zeta-reduced. -/
def declBody (stmt : Lean.Expr) (tbl : DeclTable) (names : List String) (ins : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := stmt
  for (p, n) in tbl.ins.zip names do
    e := mkApp e (mkApp3 (Lean.mkConst ``PTy.sig) (toExpr p) ins (mkStrLit n))
  let cur := (← unfoldDefinition? e).getD e
  instantiateMVars (← zetaReduce cur.headBeta)

/-- the memory calls of the declaration, each component a closed `fun ins => …` -/
def collectAll (stmt : Lean.Expr) (tbl : DeclTable) (names : List String) (unf : Name → Bool) :
    MetaM (Array MemCall) := do
  let insTy ← mkArrow (Lean.mkConst ``Nat) (← mkArrow (Lean.mkConst ``String) (Lean.mkConst ``Nat))
  withLocalDeclD `ins insTy fun ins => do
    let body ← declBody stmt tbl names ins
    let cs ← collectCalls unf body
    cs.mapM fun c => do
      pure { c with call := ← mkLambdaFVars #[ins] c.call, wa := ← mkLambdaFVars #[ins] c.wa,
                    wd := ← mkLambdaFVars #[ins] c.wd, we := ← mkLambdaFVars #[ins] c.we,
                    ra := ← mkLambdaFVars #[ins] c.ra }

/-- the proof script's pieces for one module: which memory statements are present -/
def memStmts (m : Sparkle.IR.AST.Module) : List (String × Nat × Nat × Bool × String × String × String × String × String) :=
  m.body.filterMap fun s => match s with
    | .memory name aw dw _ (.ref wa) (.ref wd) (.ref we) (.ref ra) rd cr _ _ => some (name, aw, dw, cr, wa, wd, we, ra, rd)
    | _ => none

/-- the shape this slice handles, or the reason it does not -/
def shapeProblem (m : Sparkle.IR.AST.Module) : Option String :=
  if !(instFree m.body) then
    some "the body has a submodule instance (instances belong to the hierarchy units)"
  else if !(regsOf m.body).isEmpty then
    some "the body has registers (this slice: register-free bodies with memories)"
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
      | (refine Tools.VedMem.MemInv.write' ?_ ?_ ?_ ?_; ved_mem_peel $h)
      | (refine Tools.VedMem.MemInv.write'' ?_ ?_ ?_ ?_; ved_mem_peel $h)
      | (refine Tools.VedMem.MemInv.other' ?_ (by decide) _ _ _ _ _; ved_mem_peel $h)
      | (refine Tools.VedMem.MemInv.other'' ?_ (by decide) _ _ _; ved_mem_peel $h))

/-- print the generated script before elaborating it (debugging only) -/
register_option ved.mem.debugStage : Nat := {
  defValue := 0
  descr := "insert trace_state after stage k of the hstep script (debugging only)"
}

register_option ved.mem.showScript : Bool := {
  defValue := false
  descr := "print the script `#ved_u1_mem` generated"
}

def refuseM {α} (decl : Name) (stage : String) (msg : MessageData) : MetaM α :=
  throwError m!"VED U1 REFUSED {decl} [{stage}]: {msg}"

/-- The invariant `R ins s st mems` as a closed lambda: one `MemInv` per memory statement then one latch
equation per registered read. -/
def buildR (calls : Array MemCall) (stmts : List (String × Nat × Nat × Bool × String × String × String × String × String))
    (stmt : Lean.Expr) (tbl : DeclTable) (names : List String) (unf : Name → Bool) : MetaM Lean.Expr := do
  let strNat ← mkArrow (Lean.mkConst ``String) (Lean.mkConst ``Nat)
  let insTy ← mkArrow (Lean.mkConst ``Nat) strNat
  withLocalDeclD `ins insTy fun ins =>
  withLocalDeclD `s (Lean.mkConst ``Nat) fun s =>
  withLocalDeclD `st strNat fun st =>
  withLocalDeclD `mems (Lean.mkConst ``Sparkle.IR.Semantics.MEnv) fun mems => do
    let calls ← collectAll stmt tbl names unf
    let inst := fun (x : Lean.Expr) => (mkApp x ins).headBeta
    let mut invs : Array Lean.Expr := #[]
    let mut latches : Array Lean.Expr := #[]
    for ((name, aw, dw, cr, _, _, _, _, rd), c) in stmts.zip calls.toList do
      unless aw == c.aw && dw == c.dw && cr == !c.sync do
        refuseM `mem "shape" m!"memory statement {name} ({aw}x{dw}) does not match the declaration's memory call ({c.aw}x{c.dw})"
      let zero ← mkAppM ``BitVec.ofNat #[toExpr c.dw, toExpr 0]
      let init := Lean.mkLambda `a .default (← mkAppM ``BitVec #[toExpr c.aw]) zero
      invs := invs.push (← mkAppM ``Tools.VedMem.MemInv #[mkStrLit name, init, inst c.wa, inst c.wd, inst c.we, s, mems])
      unless cr do
        latches := latches.push (← mkEq (mkApp st (mkStrLit rd))
          (← mkAppM ``BitVec.toNat #[← mkAppM ``Sparkle.Core.Signal.Signal.val #[inst c.call, s]]))
    let all := invs ++ latches
    let some last := all.back? | refuseM `mem "shape" m!"no memory"
    let mut conj := last
    for x in all.pop.reverse do conj ← mkAppM ``And #[x, conj]
    mkLambdaFVars #[ins, s, st, mems] conj

/-- the generated script for `MemStmt C M stmt`; `R` the closed invariant -/
def memScript (dbg : Nat) (nm : Names) (F : Name) (nDom : Nat)
    (stmts : List (String × Nat × Nat × Bool × String × String × String × String × String))
    (calls : Array MemCall) (R : Lean.Expr) (helpers : Array Name) : TermElabM Syntax := do
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
  let stopT ← `(tactic| (trace_state; fail "ved_mem debug stop"))
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
  let dbg4 := if dbg == 4 then stop4T else if dbg == 5 then stop5T else if dbg == 6 then stop6T else skipT
  let zeroTerms ← (List.range n).mapM fun _ => `(Tools.VedMem.MemInv.zero _ _ _ _)
  let h0Elems : Array Term ← do
    let mut a : Array Term := zeroTerms.toArray
    for _ in [0:nSync] do a := a.push (← `(?_))
    pure a
  let h0Term : Term ← if h0Elems.size == 1 then pure h0Elems[0]! else `(⟨$[$h0Elems],*⟩)
  `(by
      have hord : OrderOkM $M $B = true := by decide +kernel
      refine ⟨by decide +kernel, ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, ⟨$B, hord⟩, ?_⟩
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

/-! ## The checker -/

/-- The checker below the entry (the copy of `checkU1E`'s steps for the memory statement).  `m` is the module
the synthesis returned, `stmt` the statement's term. -/
def checkMemE (decl : Name) (base : Name) (stmt : Lean.Expr) (m : Sparkle.IR.AST.Module)
    (outNames : List String := ["out"]) : TermElabM Name := do
  let nm : Names := { (Names.ofBase base) with thm := base ++ `ved_mem }
  let saved ← saveState
  tryCatchRuntimeEx (do
    let tbl ← try readTableOfType decl (← inferType stmt) catch e => refuse decl "table" e.toMessageData
    unless tbl.out.flat.length == 1 && outNames.length == 1 do
      refuse decl "multi-output" m!"{tbl.out.flat.length} output projections (this slice: one output)"
    if let some why := shapeProblem m then refuse decl "shape" m!"{why}"
    let mE := toExpr m
    let back ← withEvalBudget (evalModule mE)
    unless decide (back = m) do
      refuse decl "artifact" m!"toExpr of the returned module does not evaluate back to it"
    addDefn nm.mod (Lean.mkConst ``Sparkle.IR.AST.Module) mE
    let clkRst := clkRstOfM m
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
    let expected := mkAppN (Lean.mkConst ``MemStmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
    try check expected catch e => refuse decl "type" e.toMessageData
    unless ← isProp expected do refuse decl "type" m!"expected statement is not a Prop"
    let stmts := memStmts m
    let helpers ← helperConsts stmt.getAppFn.constName!
    let unf : Name → Bool := fun n => n == stmt.getAppFn.constName! || helpers.contains n
    let inNames := tbl.binders.map ("_gen_" ++ ·)
    let calls ← try collectAll stmt tbl inNames unf catch e => refuse decl "shape" e.toMessageData
    let R ← try buildR calls stmts stmt tbl inNames unf catch e => refuse decl "shape" e.toMessageData
    unless calls.size == stmts.length do
      refuse decl "shape"
        m!"the module has {stmts.length} memory statements, the declaration {calls.size} memory calls (cannot match them)"
    let nDom := stmt.getAppNumArgs
    let stx ← memScript (ved.mem.debugStage.get (← getOptions)) nm stmt.getAppFn.constName! nDom stmts calls R helpers
    if ved.mem.showScript.get (← getOptions) then IO.eprintln s!"VED MEM SCRIPT {← PrettyPrinter.ppTerm ⟨stx⟩}"
    let errsBefore := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
    let pf ← tryCatchRuntimeEx
      (withProofBudget do
        withoutErrToSorry do
          let e ← elabTermEnsuringType stx expected
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e)
      fun e => do
        if ved.mem.showScript.get (← getOptions) then
          for msg in (← Core.getMessageLog).toList do IO.eprintln s!"VED MEM MSG {← msg.data.toString}"
        refuse decl "proof" e.toMessageData
    let errs := (← Core.getMessageLog).toList.filter (·.severity == .error)
    if errs.length != errsBefore then
      let new := errs.drop errsBefore
      let first ← match new with
        | msg :: _ => msg.data.toString
        | [] => pure ""
      if ved.mem.showScript.get (← getOptions) then
        for msg in (← Core.getMessageLog).toList do IO.eprintln s!"VED MEM MSG {← msg.data.toString}"
      refuse decl "proof" m!"errors were logged while elaborating the proof; first: {first}"
    if pf.hasMVar || pf.hasFVar then refuse decl "proof" m!"proof term is not closed"
    tryCatchRuntimeEx
      (withProofBudget <| withOptions (fun o => o.setBool `Elab.async false) do
        addDecl (.thmDecl { name := nm.thm, levelParams := [], type := expected, value := pf }))
      fun e => refuse decl "kernel" e.toMessageData
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
def vedMemEntryS (declName : Name) : TermElabM (Sparkle.IR.AST.Module × Design × Name × Nat) := do
  let (stmt, nDom) ← try specialiseDomain declName catch e => refuse declName "table" e.toMessageData
  let tbl ← try readTableOfType declName (← inferType stmt) catch e => refuse declName "table" e.toMessageData
  unless tbl.out.flat.length == 1 do
    refuse declName "multi-output" m!"{tbl.out.flat.length} output projections (this slice: one output)"
  let (m, d) ← try Sparkle.Compiler.Elab.synthesizeCombinational declName
    catch e => refuse declName "synthesis" e.toMessageData
  let thm ← checkMemE declName declName stmt m
  return (m, d, thm, nDom)

open Lean Elab Command in
elab "#ved_u1_mem " id:ident : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  Command.liftTermElabM do
    let (m, _, thm, nDom) ← vedMemEntryS decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U1 MEM OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}\n{repr m}"

end Tools.VedMemEntry
