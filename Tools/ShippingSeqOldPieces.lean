import Lean
-- BUILT (unit SR3t): t2 exit 0 (module); used by the typed re-derivation in Tests.Compiler.SeqDeepGrandEndpointTest and by Tools.ShippingSeqParentGenD2.
/-! # Typed extraction of PC-free subterms of an OLD generated proof term

Unit SR3t, step 1.  The depth-2 endpoint of `grand` (SR3s) reuses subterms of the OLD generated composed theorem
(`grand.machine_composedNR2`) that mention neither the laws `O` nor the old child predicate.  SR3s extracted them by POSITION
(`oldArgOf% thm 15 4`).  The helpers here extract them by BINDER NAME of the consumer head constant and carry an EXPLICIT
expected type:

* `oldNamed% (Ty) thm Head binder`: in the value of the theorem `thm`, the first application of the constant `Head`; its argument
  at the binder named `binder` (a binder name occurring TWICE or not at all is an error);
* `oldGroupFact% (Ty) thm Head binder fact`: as `oldNamed%`, but the argument is the generator's `hcalls` lambda whose body is the
  beta-redex `(fun gfB0 gfL0 gfR0 gfHb0 gfHv0 => …) B L R Hb Hv`; the redex argument paired with the lambda binder named `fact`;
* `oldInst% (Ty) thm Head`: the (unique) instance-implicit argument of `Head` (found by BINDER KIND, not position).

Each helper elaborates `Ty` in the CURRENT local context, matches the free variables of the old term to the locals by user name
(a stray free variable is an error) and THROWS unless `inferType r` is `isDefEq` to `Ty`.  `Ty` may be `_` when the consumer's
expected type is known (then the consumer's type is the check).  Nothing is assumed: a wrong subterm is rejected loudly. -/
namespace Tools.ShippingSeqOldPieces
open Lean Elab Term Meta

/-- The arguments of `app` paired with the binder names of the head constant's type. -/
def namedArgs (app : Expr) : MetaM (Array (Name × Expr)) := do
  let .const nm us := app.getAppFn | throwError "namedArgs: not a constant application"
  let ci ← getConstInfo nm
  let ty := ci.type.instantiateLevelParams ci.levelParams us
  forallTelescope ty fun xs _ => do
    let args := app.getAppArgs
    let mut r := #[]
    for i in [0:min xs.size args.size] do
      r := r.push ((← xs[i]!.fvarId!.getUserName), args[i]!)
    return r

/-- Replace the old binders `ys` occurring in `r` by the locals of the same user name; reject stray free variables. -/
def rebind (who : String) (ys : Array Expr) (r : Expr) : MetaM Expr := do
  let lctx0 ← getLCtx
  let mut r := r
  for y in ys do
    if r.containsFVar y.fvarId! then
      let un ← y.fvarId!.getUserName
      match lctx0.findFromUserName? un with
      | some l => r := r.replaceFVar y l.toExpr
      | none => throwError "{who}: no local named {un}"
  for f in (Lean.collectFVars {} r).fvarIds do
    unless lctx0.contains f do
      let d ← f.getDecl
      throwError "{who}: stray fvar {d.userName} : {d.type} in the extracted term"
  return r

/-- The check: `r : Ty` up to `isDefEq` (when `Ty` is given). -/
def checkTyped (who : String) (r : Expr) (ty? : Option Expr) : MetaM Unit := do
  if let some ty := ty? then
    let rt ← inferType r
    unless ← isDefEq rt ty do
      throwError "{who}: the extracted subterm has type{indentExpr rt}\nbut the expected type is{indentExpr ty}"

def elabTy? (ty : Syntax) : TermElabM (Option Expr) := do
  if ty.isOfKind ``Lean.Parser.Term.hole then return none
  let t ← elabType ty
  synthesizeSyntheticMVarsNoPostponing
  return some (← instantiateMVars t)

def getThm (who : String) (id : Ident) : TermElabM ConstantVal := do
  let nm ← realizeGlobalConstNoOverload id
  let some (.thmInfo ti) := (← getEnv).find? nm | throwError "{who}: {nm} is not a theorem"
  return ti.toConstantVal

def getThmValue (who : String) (id : Ident) : TermElabM Expr := do
  let nm ← realizeGlobalConstNoOverload id
  let some (.thmInfo ti) := (← getEnv).find? nm | throwError "{who}: {nm} is not a theorem"
  return ti.value

/-- The first application of the constant `head` inside `e`. -/
def findHeadApp? (e : Expr) (head : Name) : Option Expr :=
  e.find? fun x => x.isApp && x.getAppFn.isConstOf head

/-- The argument of the binder `bn` of the first application of `head` in the value of `thm`. -/
def namedArgOf (who : String) (thm : Ident) (head : Ident) (bn : Name) (k : Array Expr → Expr → MetaM Expr) : TermElabM Expr := do
  let hd ← realizeGlobalConstNoOverload head
  let v ← getThmValue who thm
  lambdaTelescope v fun ys body => do
    let some app := findHeadApp? body hd | throwError "{who}: {hd} does not occur in the value of {thm.getId}"
    let tbl ← namedArgs app
    let hits := tbl.filter (·.1 == bn)
    unless hits.size == 1 do throwError "{who}: the binder `{bn}` of {hd} occurs {hits.size} times (expected exactly 1)"
    k ys hits[0]!.2

elab "oldNamed% " "(" ty:term ")" thm:ident head:ident bn:ident : term => do
  let ty? ← elabTy? ty
  let r ← namedArgOf "oldNamed%" thm head bn.getId fun ys a => do
    let r ← rebind "oldNamed%" ys a
    return r
  checkTyped "oldNamed%" r ty?
  return r

/-- The binder names of the leading lambdas of `e`. -/
def lamNames : Expr → List Name
  | .lam n _ b _ => n :: lamNames b
  | _ => []

/-- A GROUP FACT of the old generated `hcalls`: `hcalls := fun i bools bits k c hk => (fun gfB0 gfL0 gfR0 gfHb0 gfHv0 => …) B L R Hb Hv`;
the argument of the beta-redex whose LAMBDA BINDER is named `fact` (no position is chosen by the caller). -/
elab "oldGroupFact% " "(" ty:term ")" thm:ident head:ident bn:ident fact:ident : term => do
  let ty? ← elabTy? ty
  let r ← namedArgOf "oldGroupFact%" thm head bn.getId fun ys a => do
    lambdaTelescope a fun zs inner => do
      let f := inner.getAppFn
      unless f.isLambda do throwError "oldGroupFact%: the body of `{bn.getId}` is not a beta-redex: {f}"
      let names := lamNames f
      let hits := (names.zip inner.getAppArgs.toList).filter (·.1 == fact.getId)
      unless hits.length == 1 do
        throwError "oldGroupFact%: the redex binders are {names}; `{fact.getId}` occurs {hits.length} times (expected exactly 1)"
      rebind "oldGroupFact%" (ys ++ zs) hits.head!.2
  checkTyped "oldGroupFact%" r ty?
  return r

/-- The instance-implicit argument of the first application of `head` in the value of `thm` (exactly one such binder). -/
elab "oldInst% " "(" ty:term ")" thm:ident head:ident : term => do
  let ty? ← elabTy? ty
  let hd ← realizeGlobalConstNoOverload head
  let v ← getThmValue "oldInst%" thm
  let r ← lambdaTelescope v fun ys body => do
    let some app := findHeadApp? body hd | throwError "oldInst%: {hd} does not occur in the value of {thm.getId}"
    let ci ← getConstInfo hd
    let ty := ci.type.instantiateLevelParams ci.levelParams (match app.getAppFn with | .const _ us => us | _ => [])
    let insts ← forallTelescope ty fun xs _ => do
      let mut r := #[]
      for i in [0:min xs.size app.getAppNumArgs] do
        if (← xs[i]!.fvarId!.getDecl).binderInfo == BinderInfo.instImplicit then r := r.push app.getAppArgs[i]!
      return r
    unless insts.size == 1 do throwError "oldInst%: expected exactly one instance-implicit binder of {hd}, found {insts.size}"
    rebind "oldInst%" ys insts[0]!
  checkTyped "oldInst%" r ty?
  return r

end Tools.ShippingSeqOldPieces
