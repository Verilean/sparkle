import Tools.VedU1Entry
import Tools.DeepElab

/-!
# U1 entry with the DeepElab generator (`#ved_u1_deep decl`)

Issue sparkle-ved-gen1.  Design: docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md
§11 (route 1–4, reviewer ruling 6).  Nothing in `Sparkle/` or
`Tools/DeepElab.lean` is changed.

`vedU1DeepEntry declName` is `vedU1Entry` (`synthesizeEntry` exactly ONCE, the
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

The step obligation is discharged on `m.body` ITSELF: one cycle of the
returned module is evaluated by the kernel (`simp` over `stepModule`) and
compared with one step of `Cdo.irState` (the compiled `next`, evaluated the
same way).  The invariant is "the register of `m` = `Cdo.irState` at the
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
  let some (r, w) := regShape m
    | throwError "not one register (outside this slice)"
  unless tbl.out.flat.length == 1 do throwError "not one output"
  let mut sigs : Array Term := #[]
  for (p, b) in tbl.ins.zip tbl.binders do
    match p with
    | .bv pw =>
      sigs := sigs.push (← `(PTy.sig (.bv $(quote pw)) ins $(quote ("_gen_" ++ b))))
    | _ => throwError "input {b} is not a bit vector (outside this slice)"
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
          Cdo.irState $deep $nmC ($inpU ins) t ⟨0, by decide⟩))
  let C := mkCIdent nm.contract
  let M := mkCIdent nm.mod
  let O := mkCIdent nm.outs
  let f := mkCIdent stmtDecl
  let trace := mkCIdent (deepName decl "_deep_trace")
  let next := mkCIdent (deepName decl "_deep_next")
  let inits := mkCIdent (deepName decl "_deep_inits")
  let out := mkCIdent (deepName decl "_deep_out")
  let rS := Syntax.mkStrLit r
  let wS := Syntax.mkNumLit (toString w)
  `(by
      have hinj : ∀ i j, $nmC i = $nmC j → i = j := by decide
      have hlt : ∀ ins t, $irS ins t < 2 ^ $wS := by
        intro ins t
        unfold $irS:ident
        rw [Cdo.irState_eq $deep $nmC hinj]
        exact BitVec.isLt _
      have hSI : ∀ ins t, srcOf $C $f ins "out" t = $irS ins t := by
        intro ins t
        have hl := hlt ins t
        simp [srcOf, $C:ident, contractOf, applyIns, OTy.obs, PTy.obs]
        rw [$trace:ident]
        unfold $irS:ident $inpU:ident at hl ⊢
        simp only [CExpr.compile, $out:ident]
        simp [Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalExpr.go,
          Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalOp, envOfC, weOfC, chainMap, List.finRange,
          $nmC:ident, natJoin, widthOf, mask, Nat.shiftRight_eq_div_pow, or_mod _ _ _ _ rfl] at hl ⊢
        omega
      refine ⟨by decide, by decide, by decide, ?_⟩
      apply outputs_of_step $C $M $f $O (by decide) (fun ins s st => st $rS = $irS ins s)
      · intro ins hok
        simp [st0, $C:ident, contractOf, regsOf, $M:ident, encodeInit, mask, declWidth,
          Sparkle.IR.RegDedup.declWidth, $irS:ident, Cdo.irState, $inits:ident]
      · intro ins hok s st mems hR
        have hin := hok.1 s
        have hrst := hok.2 s
        have hl := hlt ins s
        have e1 := hSI ins s
        simp [$C:ident, contractOf, Contract.dataInputs, $M:ident, declWidth,
          Sparkle.IR.RegDedup.declWidth] at hin hrst
        simp [stepModule, evalAssigns, regNexts, memNexts, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList,
          Sparkle.IR.Semantics.evalExpr.go, Sparkle.IR.Semantics.evalOp,
          widthOf, seedIn, applyNexts, $O:ident, $M:ident, declWidth,
          Sparkle.IR.RegDedup.declWidth, mask, hrst, or_mod _ _ _ _ rfl, Nat.shiftRight_eq_div_pow]
        refine ⟨_, _, ⟨rfl, rfl⟩, ?_, ?_⟩
        · simp only [ite_true]
          rw [e1, hR]
          generalize $irS ins s = x at hl ⊢
          omega
        · simp only [List.find?, beq_self_eq_true]
          rw [hR]
          unfold $irS:ident at hl ⊢
          simp only [Cdo.irState, $next:ident, CExpr.compile]
          unfold $inpU:ident at hl ⊢
          simp [Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalExpr.go,
          Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalOp, envOfC, weOfC, chainMap, List.finRange,
            $nmC:ident, natJoin, widthOf, mask, Nat.shiftRight_eq_div_pow, or_mod _ _ _ _ rfl,
            $inpC:ident, PTy.sig] at hl hin ⊢
          omega)

/-- The entry: as `vedU1Entry` (one `synthesizeEntry`, the same `m` checked
and returned), with the DeepElab-built script. -/
def vedU1DeepEntry (declName : Name) : TermElabM (Sparkle.IR.AST.Module × Design × Name) := do
  let tbl ← try readTable declName catch e => refuse declName "table" e.toMessageData
  unless tbl.out.flat.length == 1 do
    refuse declName "multi-output"
      m!"{tbl.out.flat.length} output projections; the synthesizer's multi-output port naming is unconfirmed, refused (v1: one output)"
  try Sparkle.Compiler.Elab.inlinerFuelGuard declName
  catch e => refuse declName "inliner" e.toMessageData
  let (m, d) ← try Sparkle.Compiler.Elab.synthesizeEntry declName
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
