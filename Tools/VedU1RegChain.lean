import Lean
import Sparkle.Core.Signal
import Sparkle.IR.AST
import Tools.VedU1Contract
import Sparkle.IR.Semantics

/-!
# Register chains without `Signal.loop` (U1 generated proof script)

A declaration whose body is `register c₁ (register c₂ (… (register cₖ x)))` over ONE data input `x`
(a shift register / delay line, no feedback).  The module has `k` registers, each fed by a plain wire
(the input port, or the previous register).  Invariant of the induction on the cycle `s`:
register `j` (counted from the input) holds `(register cⱼ (… (register c₁ x))).val s`.
The invariant terms are read off the declaration (`chainSubs`); the kernel checks the proof, the
dispatch and the gate here are untrusted routing.
-/

namespace Tools.VedU1RegChain

open Lean Meta Elab Term Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder Tools.VedU1Contract

/-- For `F` (specialised at `nDom` domains) with ONE explicit `Signal (BitVec w)` binder: the closed
lambdas `fun x => register c_j (… (register c_1 x))`, `j = 1 … k` (innermost first), or `none` when
the body is not a pure register chain over that binder (a `Signal.loop`, an operator, …). -/
def chainSubs (F : Name) (nDom : Nat) : MetaM (Option (Array Lean.Expr)) := do
  let mut e : Lean.Expr := Lean.mkConst F (← (← getConstInfo F).levelParams.mapM fun _ => mkFreshLevelMVar)
  for _ in [0:nDom] do e := mkApp e (Lean.mkConst `Sparkle.Core.Domain.defaultDomain)
  forallTelescopeReducing (← inferType e) fun xs _ => do
    unless xs.size == 1 do return none
    let some body ← unfoldDefinition? (mkAppN e xs) | return none
    let mut cur := body.headBeta
    let mut subs : Array Lean.Expr := #[]
    repeat
      cur ← whnfCore cur
      if cur.isAppOf ``Sparkle.Core.Signal.Signal.register then
        subs := subs.push (← mkLambdaFVars xs cur)
        cur := cur.appArg!
      else break
    unless cur == xs[0]! && subs.size ≥ 2 do return none
    return some subs.reverse

/-- the registers of `b0` in chain order from the input port `inp`, or `none` when they are not one
chain (each fed by a plain wire: the port, then the previous register's output) -/
def chainOrder (b0 : List Stmt) (inp : String) (rstN : String) : Option (List (String × Int)) := Id.run do
  let regs := b0.filterMap fun
    | .register o _ (rst, _) (.ref w) init => if rst == rstN then some (o, w, init) else none
    | _ => none
  unless regs.length == (b0.filter fun | .register .. => true | _ => false).length do return none
  let mut cur := inp
  let mut out : List (String × Int) := []
  for _ in regs do
    match regs.find? (fun r => r.2.1 == cur) with
    | some (o, _, init) => out := out ++ [(o, init)]; cur := o
    | none => return none
  return some out

/-- The script, or `none` outside the shape (see the module doc).  `C M O B` are the checker's constants,
`F`/`nDom` the declaration, `b0` the stored arrangement. -/
def regChainScript (C M O B F : Name) (nDom : Nat) (b0 : List Stmt)
    (clkRst : Option (String × String)) (dataPorts : List Port) : TermElabM (Option Syntax) := do
  let some (_, rstN) := clkRst | return none
  let [p] := dataPorts | return none
  let .bitVector w := p.ty | return none
  let some order := chainOrder b0 p.name rstN | return none
  let some subs ← chainSubs F nDom | return none
  unless subs.size == order.length do return none
  let fI := mkCIdent F
  let mut f : Term := fI
  if nDom > 0 then
    f ← `(@$fI)
    for _ in [0:nDom] do f ← `($f Sparkle.Core.Domain.defaultDomain)
  let Ci := mkCIdent C
  let Mi := mkCIdent M
  let Oi := mkCIdent O
  let Bi := mkCIdent B
  let insI := mkIdent `ins
  let sI := mkIdent `s
  let wS := Syntax.mkNumLit (toString w)
  let pS := Syntax.mkStrLit p.name
  let sig ← `(PTy.sig (PTy.bv $wS) $insI $pS)
  -- the invariant, one conjunct per register
  let mut conj : Array Term := #[]
  for ((r, _), sub) in order.zip subs.toList do
    let subS ← Term.exprToSyntax sub
    conj := conj.push (← `(st $(Syntax.mkStrLit r) = (($subS $sig).val $sI).toNat))
  let some lastC := conj.back? | return none
  let inv ← conj.pop.foldrM (fun c acc => `($c ∧ $acc)) lastC
  let oos := mkCIdent `Tools.VedU1Entry.outputs_of_step
  let hrs : Array (TSyntax `Lean.Parser.Tactic.rcasesPatLo) ← (List.range order.length).toArray.mapM fun i =>
    `(Lean.Parser.Tactic.rcasesPatLo| $(mkIdent (Name.mkSimple s!"hr{i}"))) 
  let rLam ← `(fun $insI $sI st => $inv)
  let stx ← `(by
      have hord : OrderOk $Mi $Bi = true := by decide +kernel
      refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨$Bi, hord⟩, ?_⟩
      apply outputs_of_order $Bi hord
      apply $oos $Ci $Mi $Bi $f $Oi (by decide +kernel) $rLam
      · intro ins hok
        simp [st0, $Ci:ident, contractOf, regsOf,
          $Mi:ident, declWidth, Sparkle.Core.Signal.Signal.register, PTy.sig,
          encodeInit, mask]
        all_goals decide +kernel
      · intro ins hok s st mems hR
        have hin := hok.1 s
        have hrst := hok.2 s
        simp [$Ci:ident, contractOf, Contract.dataInputs, $Mi:ident,
          declWidth] at hin hrst
        simp [stepModule, evalAssigns, regNexts,
          memNexts, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList,
          Sparkle.IR.Semantics.evalExpr.go, widthOf, seedIn,
          applyNexts, $Oi:ident, $Mi:ident, $Bi:ident, declWidth,
          srcOf, $Ci:ident, contractOf, applyIns, $fI:ident,
          Sparkle.Core.Signal.Signal.register, OTy.obs, PTy.obs,
          PTy.sig, mask, hrst] at hR ⊢
        refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
        obtain ⟨$[$hrs],*⟩ := hR
        simp [*, mask]
        all_goals omega)
  return some stx

end Tools.VedU1RegChain
