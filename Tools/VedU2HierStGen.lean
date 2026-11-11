import Tools.VedU2HierEntry

/-!
# H2c-state: the open parent of a declaration whose child call reads the parent's REGISTERS

`genOpen` (H2a/H2b/H2c) abstracts each child call `g args` of the declaration's body into a free signal
with `kabstract`; that needs the call to be a closed term occurring in the body.  In a real row
(`(burstEmit trigger 18 httpGetByte).byte`) the call is passed to a helper as a FUNCTION and applied
to the loop's register inside `circuit do`'s lambda, so no closed call occurs in the body.

`genOpenSt` builds, from the declaration alone (no assumption about the child's meaning):

* the OUTER call: the declaration's value, reduced by `whnfCore` and definition unfolding until a call of
  the child is at the head (`decl xs ≡ g a`).  Its argument `a` is a closed term over the inputs (it
  contains the parent's own loop: a `Signal.loop` over the registers);
* the open parent `decl.ved_open_…` (struct-valued when the declaration projects a field of a circuit's
  struct result): the declaration's body with the user definitions that reach the child unfolded, the
  child (passed as a function) replaced by the constant function `fun _ => o` of a free signal `o`.
  Its registers are the parent's, its output the call's value `o`;
* the equation `decl xs = π (open xs (g a))` in the KERNEL (`Eq.refl`: it is a delta/beta/projection
  conversion plus the child call at the position the replaced function was applied; the kernel decides).

The deep facts of the open parent (`#verify_elab_deep`, run by the checker) tie its registers to the
IR registers (the invariant of `outputsOnHS_of_stepRK`); the closed argument `a` is tied to the same
registers by the exported STATE theorem of that deep run (`ved_have_export` in DeepElab), and the
child's output at the same cycle by `kid_step`.
-/

namespace Tools.VedU2HierStGen

open Lean Meta Elab Term
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1HierEntry Tools.VedU2HierEntry Tools.VedU1Deep

/-- A module that is part of the user's design, not of the library the circuits are built from. -/
def userModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true
  | some i =>
    let s := (env.header.moduleNames[i.toNat]!).toString
    !(s.startsWith "Init" || s.startsWith "Std" || s.startsWith "Lean" || s.startsWith "Sparkle.Core" ||
      s.startsWith "Sparkle.IR" || s.startsWith "Sparkle.Compiler" || s.startsWith "Sparkle.Utils" ||
      s == "Sparkle" || s.startsWith "Tools")

/-- Does `v` mention the child constant, directly or through user definitions (bounded depth)? -/
partial def mentionsKid (env : Environment) (kid : Name) (v : Lean.Expr) : Nat → Bool
  | 0 => false
  | f + 1 =>
    (v.find? fun x => x.isConstOf kid).isSome ||
      (v.foldConsts ([] : List Name) (fun c acc => c :: acc)).any fun c =>
        c != kid && userModule env c && match env.find? c with
          | some (.defnInfo ci2) => mentionsKid env kid ci2.value f
          | _ => false

/-- Unfold the user definitions whose body (transitively) mentions the child constant; everything else
(the circuit's own plumbing) is left as the user wrote it. -/
def unfoldReaching (kid : Name) (e : Lean.Expr) : MetaM Lean.Expr := do
  let env ← getEnv
  Meta.transform e (pre := fun x => do
    if x.isApp || x.isConst then
      if let .const n _ := x.getAppFn then
        if n != kid && userModule env n then
          if let some (.defnInfo ci) := env.find? n then
            if mentionsKid env kid ci.value 6 then
              if let some y ← unfoldDefinition? x then
                return .visit y.headBeta
    return .continue)

/-- The outer call: reduce the declaration's value until an application of the child is at its head. -/
partial def outerCall (kid : Name) (e : Lean.Expr) (fuel : Nat) : MetaM (Option Lean.Expr) := do
  match fuel with
  | 0 => return none
  | f + 1 =>
    let e ← zetaReduce (← whnfCore e)
    if e.isApp && e.getAppFn.isConstOf kid then return some e
    match ← unfoldDefinition? e with
    | some e' => outerCall kid e' f
    | none => return none

/-- Applications in `e` (whole spines) one of whose arguments is the child function (the child constant with
exactly its domain arguments, or the bare constant), outermost first. -/
partial def kidArgApps (kid : Name) (nDom : Nat) (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  let isKidFn (a : Lean.Expr) : Bool :=
    a.getAppFn.isConstOf kid && a.getAppNumArgs == nDom
  let acc :=
    if e.isApp && !isKidFn e && (e.getAppArgs.any isKidFn) then acc.push e else acc
  match e with
  | .app f a => kidArgApps kid nDom a (kidArgApps kid nDom f acc)
  | .lam _ t b _ => kidArgApps kid nDom b (kidArgApps kid nDom t acc)
  | .letE _ t v b _ => kidArgApps kid nDom b (kidArgApps kid nDom v (kidArgApps kid nDom t acc))
  | .mdata _ b => kidArgApps kid nDom b acc
  | .proj _ _ b => kidArgApps kid nDom b acc
  | _ => acc

/-- `genOpenSt`: see the file header.  `kid` is the single child (the slice: one child, one call). -/
def genOpenSt (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (tbl : DeclTable) (kid : Kid)
    (base : Name) (openSuf : String) : TermElabM OpenInfo := do
  let openName := base ++ Name.mkSimple openSuf
  let eqName := base ++ Name.mkSimple (openSuf ++ "_eq")
  let ty ← inferType stmt
  forallTelescope ty fun xs _ => do
    let some (.defnInfo ci) := (← getEnv).find? decl
      | refuse decl "open" m!"{decl} is not a definition"
    let dflt := Lean.mkConst ``Sparkle.Core.Domain.defaultDomain
    let args : Array Lean.Expr := (Array.replicate nDom dflt) ++ xs
    let body0 := (mkAppN ci.value args).headBeta
    let nIns := kid.tbl.ins.length
    -- the outer call
    let some call ← outerCall kid.decl body0 12
      | refuse decl "open"
          m!"the declaration's value does not reduce to a call of {kid.decl} (the child's output must be the declaration's output: H2c-state covers a declaration that is one call of the child on a closed argument)"
    let cargs := call.getAppArgs
    unless cargs.size == kid.nDom + nIns do
      refuse decl "open" m!"child call {call} is not fully applied"
    let dargs := cargs.extract kid.nDom cargs.size
    for a in dargs do
      if a.hasLooseBVars then
        refuse decl "open" m!"the argument {a} of the child call has loose bound variables"
      unless (Lean.collectFVars {} a).fvarIds.all (fun v => xs.any (·.fvarId! == v)) do
        refuse decl "open" m!"the argument {a} of the child call mentions a variable that is not a parameter of the declaration"
    -- the closed argument definitions `fun ins => argument[inputs := input streams]`
    let sigs : Array Lean.Expr := (tbl.ins.zip tbl.binders).toArray.map fun (pt, bn) =>
      mkAppN (Lean.mkConst ``PTy.sig) #[toExpr pt, Lean.mkBVar 0, toExpr ("_gen_" ++ bn)]
    let _ := sigs
    let insTy := Lean.mkForall `n .default (Lean.mkConst ``Nat)
      (Lean.mkForall `s .default (Lean.mkConst ``String) (Lean.mkConst ``Nat))
    let defs ← withLocalDeclD `ins insTy fun insFv => do
      let mut ds : List Name := []
      let sigsF : Array Lean.Expr := (tbl.ins.zip tbl.binders).toArray.map fun (pt, bn) =>
        mkAppN (Lean.mkConst ``PTy.sig) #[toExpr pt, insFv, toExpr ("_gen_" ++ bn)]
      for (a, kk) in dargs.toList.zipIdx do
        let v := a.replaceFVars xs sigsF
        let lam ← mkLambdaFVars #[insFv] v
        let nmA := base ++ Name.mkSimple (openSuf ++ s!"_arg0_{kk}")
        addDefnRegular nmA (← inferType lam) lam
        ds := ds ++ [nmA]
      return ds
    -- the open parent
    let e1 ← zetaReduce (← unfoldReaching kid.decl body0)
    let env ← getEnv
    let (headFn, headArgs, S0) :=
      match e1.getAppFn with
      | .const n _ =>
        if env.isProjectionFn n && e1.getAppNumArgs > 0 then
          (some e1.getAppFn, e1.getAppArgs.pop, e1.appArg!)
        else (none, #[], e1)
      | _ => (none, #[], e1)
    -- the circuit the child is passed to: the smallest application taking the child function as an
    -- argument (the burst emitter, with its trigger), when it is smaller than the whole value
    let sCands := (kidArgApps kid.decl kid.nDom e1 #[]).filter fun x =>
      !x.hasLooseBVars && (Lean.collectFVars {} x).fvarIds.all (fun v => xs.any (·.fvarId! == v))
    let S := match sCands.foldl (fun (best : Option Lean.Expr) x =>
        match best with
        | none => some x
        | some b => if x.approxDepth < b.approxDepth then some x else some b) none with
      | some x => x
      | none => S0
    let whole := S == S0
    let callTy ← inferType call
    let argTys ← dargs.mapM (fun a => inferType a)
    withLocalDeclD `ved_o callTy fun o => do
      -- The child is replaced by the free signal `o`, but kept READING its argument (`mux (x === x) o o`):
      -- the registers the argument depends on stay alive in the synthesised open parent (a register that
      -- nothing reads is dropped by the synthesiser, and then there is nothing to tie the state to).
      let keepAlive (as : Array Lean.Expr) : MetaM Lean.Expr :=
        as.foldrM (fun a acc => do
          let c ← mkAppM ``Sparkle.Core.Signal.Signal.beq #[a, a]
          mkAppM ``Sparkle.Core.Signal.Signal.mux #[c, acc, o]) o
      let nIns' := nIns
      let S' ← Meta.transform S (pre := fun x => do
        if x.isApp && x.getAppFn.isConstOf kid.decl then
          if x.getAppNumArgs == kid.nDom + nIns' then
            return .done (← keepAlive (x.getAppArgs.extract kid.nDom x.getAppNumArgs))
          if x.getAppNumArgs == kid.nDom then
            let fnTy ← inferType x
            return .done (← forallBoundedTelescope fnTy (some nIns') fun vs _ => do
              mkLambdaFVars vs (← keepAlive vs))
        else if x.isConst && x.constName! == kid.decl && kid.nDom == 0 then
          let fnTy ← inferType x
          return .done (← forallBoundedTelescope fnTy (some nIns') fun vs _ => do
            mkLambdaFVars vs (← keepAlive vs))
        return .continue)
      if (S'.find? fun x => x.isConstOf kid.decl).isSome then
        refuse decl "open" m!"a call of {kid.decl} remains in the open parent after the replacement of the child function"
      let openVal ← mkLambdaFVars (xs ++ #[o]) S'
      let openTy ← inferType openVal
      addDefnRegular openName openTy openVal
      let lhs := mkAppN stmt xs
      let pf ← mkLambdaFVars xs (← mkEqRefl lhs)
      -- (No equation between the declaration and the open parent is claimed: the open parent only ever supplies
      -- the registers' state; the declaration itself is the outer call, below.)
      -- the declaration IS the outer call on its closed argument (also kernel-checked)
      let callEqName := base ++ Name.mkSimple (openSuf ++ "_ceq")
      let ceqTy ← mkForallFVars xs (← mkEq lhs call)
      try
        withOptions (fun o => o.setBool `Elab.async false) do
          addDecl (.thmDecl { name := callEqName, levelParams := [], type := ceqTy, value := pf })
      catch e => refuse decl "open" m!"the kernel refused the equation of the declaration with its call: {e.toMessageData}"
      let port : Option String := if !whole then none else match headFn with
        | some f => match f.constName? with | some n => some n.getString! | none => none
        | none => none
      -- the ports of the open parent: the fields of its struct result
      let ports : List String ← do
        let st ← whnf (← inferType S)
        match st.getAppFn.constName? with
        | some sn =>
          if sn == ``Sparkle.Core.Signal.Signal then pure []
          else pure ((getStructureFields (← getEnv) sn).toList.map (·.toString))
        | none => pure []
      let info : CallInfo := { kid := 0, args := dargs.toList.map (fun _ => "?"), derived := true,
                               argDefs := defs, stateArg := true }
      return { openName, eqName, calls := #[info], port, ports, callEqName := some callEqName }

end Tools.VedU2HierStGen
