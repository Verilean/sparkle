import Tools.VedU1Entry
import Tools.DeepElab

/-!
# U1 entry with the DeepElab generator (`#ved_u1_deep decl`)

Issue sparkle-ved-gen1.  Design: docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md
§11 (route 1–4, reviewer ruling 6).  Nothing in `Sparkle/` or
`Tools/DeepElab.lean` is changed.

`vedU1DeepEntry declName` is `vedU1Entry` (`synthesizeCombinational` exactly ONCE, the
full `U1Stmt` over the returned module `m` and the declaration constant
itself, kernel, strict audit; `m` is returned only on success) with a
different proof source: a script built from what `#verify_elab_deep` has
already generated for the declaration, of which it uses ONLY

* `{f}_deep : Cdo Γr Γi w` (the reified circuit), `{f}_nm` (its names),
  `{f}_inp` (its input map),
* `{f}_deep_trace` (Signal = `Cdo.irState` / compiled output, via
  `Cdo.elab_general`), `{f}_deep_next`, `{f}_deep_inits`, `{f}_deep_out`.

These are standard-axiom theorems.  The cone constants, `_deep_fidelity_*`,
DeepElab's re-synthesised IR, and every `native_decide`-dependent theorem
(`_deep_coneEval_*`, `_deep_regstep`, `_deep_signal_run`, …) are NOT used.
They may exist in the environment; the final theorem's axiom closure is
checked by the strict audit, and its constant-dependency closure by the
Check file.

The step obligation is discharged on the checked arrangement `nm.body`
(`OrderOk m nm.body`, a well-ordered permutation of `m.body`): one cycle of
it is evaluated by the kernel (`simp` over `stepModule`) and compared with
one step of `Cdo.irState` (the compiled `next`, evaluated the same way);
`outputs_of_order` then carries the result to EVERY well-ordered arrangement
of `m.body` (`runModule_perm`).  This is not a statement about running the
returned list `m.body` in its own order with `runModule`, nor about the C
simulator.  The invariant is "the register of `m` = `Cdo.irState` at the
same cycle".  Name/slot correspondence, widths (`declWidth` / `weOfC`), the
mask, the initial value (`st0` / `_deep_inits`) and the time direction
(`outputs_of_step`, `seedFwd_time`) are all closed inside that kernel proof;
nothing is observed, and the two synthesis runs are not assumed equal.

Scope of this slice (the script fails, and the entry refuses, outside it):
one register, data inputs of bit-vector type, one output, no memory.  The
builder refuses up front when `#verify_elab_deep` has not produced the
constants above, or the shape is outside the slice.
-/

namespace Tools.VedU1Deep

open Lean Meta Elab Term
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

/-- `{prefix}.{last}{suffix}`: the names `#verify_elab_deep` gives its
constants (in the declaration's namespace). -/
def deepName (decl : Name) (suffix : String) : Name :=
  match decl with
  | .str p s => .str p (s ++ suffix)
  | _ => .str decl suffix

/-- The DeepElab constants the script reads (and nothing else). -/
def deepParts : List String :=
  ["_deep", "_nm", "_inp", "_deep_trace", "_deep_next", "_deep_inits", "_deep_out"]

/-- Auxiliary definitions the builder registers (inside the checker's scope). -/
def auxNames (base : Name) : List Name :=
  [base ++ `ved_inpU, base ++ `ved_irS]

/-- A definition with ordinary (not `abbrev`) reducibility, so `simp`/`omega`
see `ved_irS ins s` as one atom until it is unfolded on purpose. -/
def addDefnRegular (n : Name) (ty val : Lean.Expr) : MetaM Unit := do
  addDecl (.defnDecl (mkDefinitionValEx n [] ty val (.regular 1) .safe []))
  enableRealizationsForConst n

/-- Elaborate a closed term (no expected type) and register it as `n`. -/
def addTermDef (n : Name) (stx : Term) : TermElabM Unit := do
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar || e.hasFVar then throwError "auxiliary {n} is not closed"
  addDefnRegular n (← inferType e) e

/-- A closed `Nat` expression to its value. -/
def natLit? (e : Lean.Expr) : MetaM (Option Nat) := do
  let r ← reduce (← instantiateMVars e)
  if let some v := r.rawNatLit? then return some v
  (evalNat r).run

/-- `Fin.val` of a numeral: core has `Fin.val_zero/one/two` only, so the context
lookups `[w₀, …][↑3]` of a four-register circuit would stay stuck. -/
simproc reduceFinVal (Fin.val _) := fun e => do
  let_expr Fin.val n x := e | return .continue
  let x ← instantiateMVars x
  unless x.isAppOfArity ``OfNat.ofNat 3 do return .continue
  -- the bound is often `List.length [..]`, not a numeral
  let some nv ← natLit? n | return .continue
  let some k := (x.getArg! 1).rawNatLit? | return .continue
  if nv == 0 then return .continue
  return .done { expr := toExpr (k % nv) }

/-- The register widths `Γr` of a `Cdo Γr Γi w` type (a list literal). -/
partial def readWidths (e : Lean.Expr) : MetaM (List Nat) := do
  let e ← whnfR (← instantiateMVars e)
  match e.getAppFnArgs with
  | (``List.nil, _) => pure []
  | (``List.cons, #[_, h, t]) =>
    let some n ← evalNat (← instantiateMVars h) | throwError "register width {h} is not a literal"
    return n :: (← readWidths t)
  | _ => throwError "register context {e} is not a list literal"

/-- A fresh, macro-scoped identifier (never capturable by a user name). -/
def freshId (base : String) : MetaM Ident := do
  return mkIdent (← mkFreshUserName (Name.mkSimple base))

/-- Right-nested `∧` projection `i` of `k`. -/
def conjProj (h : Ident) (i k : Nat) : TermElabM Term := do
  let mut t : Term := h
  for _ in [0:i] do t ← `($t.2)
  if i + 1 < k then `($t.1) else pure t

/-- The script builder: registers `ved_inpU` / `ved_irS` (under the checker's
base) and returns the proof script of `U1Stmt C M stmtDecl`, built from the
DeepElab constants of `decl`.  The entry passes the same declaration for
both; the controls pass another declaration's DeepElab constants. -/
def buildDeepWith (stmtDecl decl : Name) (tbl : DeclTable) (nm : Names) (m : Sparkle.IR.AST.Module) :
    TermElabM Syntax := do
  for s in deepParts do
    unless (← getEnv).contains (deepName decl s) do
      throwError "{deepName decl s} missing (run #verify_elab_deep {decl} first)"
  let deepC ← getConstInfo (deepName decl "_deep")
  unless deepC.type.getAppFn.constName? == some ``Cdo do
    throwError "{deepName decl "_deep"} is not a Cdo (memories are outside this slice)"
  let widths ← readWidths (deepC.type.getAppArgs[0]!)
  let k := widths.length
  if k == 0 then throwError "no register (outside this slice)"
  unless (regsOf m.body).length == k do
    throwError "module has {(regsOf m.body).length} registers, {deepName decl "_deep"} has {k}"
  unless tbl.out.flat.length == 1 do throwError "not one output"
  let mut sigs : Array Term := #[]
  for (p, b) in tbl.ins.zip tbl.binders do
    match p with
    | .bv pw =>
      sigs := sigs.push (← `(PTy.sig (.bv $(quote pw)) ins $(quote ("_gen_" ++ b))))
    | .bit =>
      sigs := sigs.push (← `(PTy.sig .bit ins $(quote ("_gen_" ++ b))))
  let base := nm.mod.getPrefix
  let inpU := mkCIdent (base ++ `ved_inpU)
  let irS := mkCIdent (base ++ `ved_irS)
  let inpC := mkCIdent (deepName decl "_inp")
  let deep := mkCIdent (deepName decl "_deep")
  let nmC := mkCIdent (deepName decl "_nm")
  addTermDef (base ++ `ved_inpU)
    (← `(fun (ins : Nat → String → Nat) (t : Nat) j => ($inpC $sigs* j).val t))
  addTermDef (base ++ `ved_irS)
    (← `(fun (ins : Nat → String → Nat) (t : Nat) =>
          Cdo.irState $deep $nmC ($inpU ins) t))
  let C := mkCIdent nm.contract
  let M := mkCIdent nm.mod
  let O := mkCIdent nm.outs
  let f := mkCIdent stmtDecl
  let B := mkCIdent nm.body
  let trace := mkCIdent (deepName decl "_deep_trace")
  let next := mkCIdent (deepName decl "_deep_next")
  let inits := mkCIdent (deepName decl "_deep_inits")
  let out := mkCIdent (deepName decl "_deep_out")
  let idx (i : Nat) : TermElabM Term := `((⟨$(quote i), by decide⟩ : Fin _))
  -- per register: its slot name (through `_nm`), its bound, its invariant hypothesis
  let mut slotN : Array Term := #[]
  let mut slotV : Array Term := #[]
  for i in [0:k] do
    slotN := slotN.push (← `($nmC ⟨$(quote i), by decide⟩))
    slotV := slotV.push (← `($irS ins s ⟨$(quote i), by decide⟩))
  let mut inv : Term ← `(st $(slotN[k-1]!) = $(slotV[k-1]!))
  for i in (List.range (k - 1)).reverse do
    inv ← `(st $(slotN[i]!) = $(slotV[i]!) ∧ $inv)
  let hltIds ← (List.range k).toArray.mapM fun i => freshId s!"hlt{i}"
  let hRId ← freshId "hR"
  let hRIds ← (List.range k).toArray.mapM fun i => freshId s!"hR{i}"
  let hltTacs ← (List.range k).toArray.mapM fun i => do
    let h := hltIds[i]!
    let wS := Syntax.mkNumLit (toString widths[i]!)
    `(tactic| have $h:ident : ∀ ins t, $irS ins t ⟨$(quote i), by decide⟩ < 2 ^ $wS := by
        intro ins t
        unfold $irS:ident
        rw [Cdo.irState_eq $deep $nmC hinj]
        exact BitVec.isLt _)
  let hlIds ← (List.range k).toArray.mapM fun i => freshId s!"hl{i}"
  let hlTacs ← (List.range k).toArray.mapM fun i => do
    let h : Ident := hltIds[i]!
    `(tactic| have $(hlIds[i]!):ident := $h ins s)
  let locs : Array (TSyntax `ident) := hRIds ++ hlIds
  let hMods : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← hlIds.mapM fun h => `(Lean.Parser.Tactic.simpLemma| Nat.mod_eq_of_lt $h:ident)
  let hRs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← hRIds.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let hRTacs ← (List.range k).toArray.mapM fun i => do
    `(tactic| have $(hRIds[i]!):ident := $(← conjProj hRId i k))
  let holes : Array Term ← (List.range k).toArray.mapM fun _ => `(?_)
  let mut inpAts : Array Ident := #[]
  for j in [0:tbl.ins.length] do
    for sfx in [s!"_inp_at_{j}", s!"_inp_at_mk_{j}"] do
      if (← getEnv).contains (deepName decl sfx) then
        inpAts := inpAts.push (mkCIdent (deepName decl sfx))
  let mut inpL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for i in inpAts do inpL := inpL.push (← `(Lean.Parser.Tactic.simpLemma| $i:ident))
  inpL := inpL.push (← `(Lean.Parser.Tactic.simpLemma| PTy.sig))
  let splitK : Lean.TSyntax `tactic ← if k == 1 then `(tactic| skip) else `(tactic| refine ⟨$[$holes],*⟩)
  let pre ← `(tactic| have hinj : ∀ i j, $nmC i = $nmC j → i = j := by decide)
  let mainTac ← `(tactic| (
      refine ⟨by decide, by decide, by decide, ⟨$B, by decide⟩, ?_⟩
      apply outputs_of_order $B (by decide)
      apply outputs_of_step $C $M $B $f $O (by decide) (fun ins s st => $inv)
      · intro ins hok
        simp [st0, $C:ident, contractOf, regsOf, $M:ident, encodeInit, mask, declWidth,
          $irS:ident, Cdo.irState, $inits:ident, $nmC:ident, List.lookup, -Fin.isValue]
      · intro ins hok s st mems $hRId
        have hin := hok.1 s
        have hrst := hok.2 s
        $hRTacs*
        $hlTacs*
        simp [$C:ident, contractOf, Contract.dataInputs, $M:ident, declWidth] at hin hrst
        simp [stepModule, evalAssigns, regNexts, memNexts, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList,
          Sparkle.IR.Semantics.evalExpr.go, Sparkle.IR.Semantics.evalOp,
          widthOf, seedIn, applyNexts, $O:ident, $M:ident, $B:ident, declWidth,
          mask, hrst, or_mod _ _ _ _ rfl, Nat.shiftRight_eq_div_pow]
        refine ⟨_, _, ⟨rfl, rfl⟩, ?_, ?_⟩
        · try rw [if_pos rfl]
          all_goals simp [srcOf, $C:ident, contractOf, applyIns, OTy.obs, PTy.obs, $nmC:ident]
          all_goals rw [$trace:ident]
          all_goals unfold $irS:ident $inpU:ident at $locs*
          all_goals simp only [CExpr.compile, $out:ident]
          all_goals simp [Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalExpr.go,
            Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalOp, envOfC, weOfC, chainMap, List.finRange,
            $nmC:ident, -Fin.isValue, -Fin.reduceFinMk, -Fin.reduceSucc, -Fin.reduceOfNat, reduceFinVal, natJoin, widthOf, mask, Nat.shiftRight_eq_div_pow, or_mod _ _ _ _ rfl,
            $[$inpL],*] at $locs* ⊢
          all_goals try simp only [$[$hRs],*]
          all_goals try simp only [$[$hMods],*]
          all_goals (first | omega | ((repeat' split) <;> omega) | ((repeat' split) <;> simp_all <;> omega))
        · $splitK:tactic
          all_goals simp only [List.find?, $nmC:ident]
          all_goals simp [-Fin.isValue]
          all_goals unfold $irS:ident at *
          all_goals simp only [Cdo.irState, $next:ident, CExpr.compile]
          all_goals unfold $inpU:ident at *
          all_goals simp [Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalExpr.go,
            Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalOp, envOfC, weOfC, chainMap, List.finRange,
            $nmC:ident, -Fin.isValue, -Fin.reduceFinMk, -Fin.reduceSucc, -Fin.reduceOfNat, reduceFinVal, natJoin, widthOf, mask, Nat.shiftRight_eq_div_pow, or_mod _ _ _ _ rfl,
            $[$inpL],*, Signal.map, cond_eq_ite, bne_iff_ne, ne_eq] at $locs* ⊢
          all_goals (try simp only [$[$hRs],*])
          all_goals (first | omega | ((repeat' split) <;> omega) | ((repeat' split) <;> simp_all <;> omega))))
  let tacs := #[pre] ++ hltTacs ++ #[mainTac]
  `(by $[$tacs]*)

/-- The entry: as `vedU1Entry` (one `synthesizeCombinational`, the same `m` checked
and returned), with the DeepElab-built script. -/
def vedU1DeepEntry (declName : Name) : TermElabM (Sparkle.IR.AST.Module × Design × Name) := do
  let tbl ← try readTable declName catch e => refuse declName "table" e.toMessageData
  unless tbl.out.flat.length == 1 do
    refuse declName "multi-output"
      m!"{tbl.out.flat.length} output projections; the synthesizer's multi-output port naming is unconfirmed, refused (v1: one output)"
  let (m, d) ← try Sparkle.Compiler.Elab.synthesizeCombinational declName
    catch e => refuse declName "synthesis" e.toMessageData
  let thm ← checkU1 declName declName declName m (.built (buildDeepWith declName declName tbl))
  return (m, d, thm)

/-- `#ved_u1_deep decl`: run the entry (after `#verify_elab_deep decl`); on
success print the theorem, its audit and the returned module. -/
elab "#ved_u1_deep " id:ident : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  Command.liftTermElabM do
    let (m, _, thm) ← vedU1DeepEntry decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    logInfo m!"VED U1 OK {thm}: {Tools.VedStrictAudit.showNames r.axioms}\n{repr m}"

end Tools.VedU1Deep
