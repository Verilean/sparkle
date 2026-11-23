import Tools.VedU2HierStGen
import Tools.VedU2HierMultiLoop
import Tools.VedComposeMultiCircuit
import Tools.VerifyElab

/-!
# H3-open (generation): child calls INSIDE the parent's register loop, on arguments computed from its state

`genOpenSt` (H2c-state) needs the declaration to BE one call of the child (the call sits where the loop
body's `.snd` does not read it).  In `sha512BlockHW` the child (`kMux`) is called inside the loop body on
the counter register and its output feeds the registers' next values: the call is live in the feedback path
and the declaration's output is not the call.

`genOpenMulti` builds, from the declaration alone:

* the loop body with every child call REPLACED by an oracle: the open parent `decl.ved_open_…` is
  `runCircuitH inits body_O` with the oracle signals `os` as parameters (one per DISTINCT call, closed over the
  loop's state `live`: the calls are found by reducing `body regs holds` for a free `live`);
* `F xs os x = loopFOf inits body_O x`, the oracle `Os xs live = (G e₁[live], …, G e_N[live])` the real children
  give, and the relation `E` (oracles agree below `t`);
* the theorem `decl.ved_open_…_eq : decl xs = ved_open xs (Os xs Q)` with `Q` the declaration's own loop: from
  `loop_knot` (`Tools.VedU2HierMulti`) and three facts about the body proved by the generated script
  (`hcF` causal in the state, `hcO` reads the oracle only in the past, `hOs` the oracle reads the state at the
  same cycle only).  The child's output signal at the argument `e_j[Q]` is the declaration's call, closed over
  the inputs, exactly as in H2b (`genOpen`) — the equation is a theorem, not `rfl`.

Nothing is assumed about the child: the child's meaning comes from its own U1 theorem, as before.
-/

namespace Tools.VedU2HierMultiGen

open Lean Meta Elab Term
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1HierEntry Tools.VedU2HierEntry Tools.VedU1Deep

/-- Head normal form of a declaration's value for the pure-wiring top (VED compose multiCircuit, connect17): the user's own
definitions at the head are unfolded and a projection of a structure constructor is reduced; nothing below the head is touched.
The children's calls are left alone. -/
partial def normTop (kids : Array Kid) (e : Lean.Expr) (fuel : Nat) : MetaM Lean.Expr := do
  match fuel with
  | 0 => return e
  | f + 1 =>
    let e ← zetaReduce (← whnfCore e)
    let env ← getEnv
    match e.getAppFn with
    | .const n _ =>
      if kids.any (·.decl == n) then return e
      if let some pi := env.getProjectionFnInfo? n then
        if e.getAppNumArgs == pi.numParams + 1 then
          let s ← normTop kids e.appArg! f
          if s.getAppFn.isConstOf pi.ctorName && s.getAppNumArgs > pi.numParams + pi.i then
            return ← normTop kids (s.getArg! (pi.numParams + pi.i)) f
          else return mkApp e.appFn! s
        else return e
      else if Tools.VedU2HierStGen.userModule env n && (env.find? n).any (·.isDefinition) then
        match ← unfoldDefinition? e with
        | some e' => normTop kids e' f
        | none => return e
      else return e
    | _ => return e

/-- The `runCircuitH` application a declaration's value reduces to, with the projection (if any) wrapped around it.  With `ctor`
(option `ved.compose.multiCircuit`), a projection of a structure constructor (the wiring top `{ out := tx.txLine }.out`) is also
reduced, which the default path refuses. -/
partial def findRun (e : Lean.Expr) (fuel : Nat) (ctor : Bool := false) : MetaM (Option (Lean.Expr × (Lean.Expr → Lean.Expr))) := do
  match fuel with
  | 0 => return none
  | f + 1 =>
    let e ← zetaReduce (← whnfCore e)
    if e.getAppFn.isConstOf ``Sparkle.Core.runCircuitH then return some (e, id)
    let env ← getEnv
    match e.getAppFn with
    | .const n _ =>
      if env.isProjectionFn n && e.getAppNumArgs > 0 then
        match ← findRun e.appArg! f ctor with
        | some (r, w) => return some (r, fun x => mkApp e.appFn! (w x))
        | none =>
          if ctor then
            if let some pi := env.getProjectionFnInfo? n then
              if e.getAppNumArgs == pi.numParams + 1 then
                let s ← normTop #[] e.appArg! 24
                if s.getAppFn.isConstOf pi.ctorName && s.getAppNumArgs > pi.numParams + pi.i then
                  return ← findRun (s.getArg! (pi.numParams + pi.i)) f ctor
            return none
          else return none
      else match ← unfoldDefinition? e with
        | some e' => findRun e' f ctor
        | none => return none
    | _ => return none

/-- Is `x` a saturated call of one of the children? Its kid index. -/
def kidOfCall (kids : Array Kid) (x : Lean.Expr) : Option Nat :=
  match x.getAppFn with
  | .const n _ =>
    match kids.findIdx? (fun k => k.decl == n) with
    | some i => if x.getAppNumArgs == kids[i]!.nDom + kids[i]!.tbl.ins.length then some i else none
    | none => none
  | _ => none

/-- Replace every saturated child call in `e` (under binders, identical subterms once) by
`f occurrence kidIndex callFunction domainArgs dataArgs`.  With `nested` (VED compose connect, chained instances) the data
arguments of a call are processed first (a call inside a call's argument is replaced too, innermost first) and `f` receives
the processed arguments. -/
partial def replaceCalls (kids : Array Kid) (e : Lean.Expr)
    (f : Nat → Nat → Lean.Expr → Array Lean.Expr → Array Lean.Expr → MetaM Lean.Expr) (nested : Bool := false) : MetaM Lean.Expr := do
  let cnt ← IO.mkRef 0
  let rec go (e : Lean.Expr) : MetaM Lean.Expr :=
    Meta.transform e (pre := fun x => do
      if x.isApp then
        if let some ki := kidOfCall kids x then
          let k := kids[ki]!
          let as := x.getAppArgs
          let das ← if nested then (as.extract k.nDom as.size).mapM go else pure (as.extract k.nDom as.size)
          let idx ← cnt.modifyGet fun n => (n, n + 1)
          return .done (← f idx ki x.getAppFn (as.extract 0 k.nDom) das)
      return .continue)
  go e

/-- Applications `Gs_k args` of the marker variables in `e`. -/
partial def collectMarks (ids : Array FVarId) (e : Lean.Expr) (acc : Array (Nat × Array Lean.Expr)) :
    Array (Nat × Array Lean.Expr) :=
  match e with
  | .app .. =>
    let acc := e.getAppArgs.foldl (fun a x => collectMarks ids x a) acc
    match e.getAppFn with
    | .fvar v =>
      match ids.findIdx? (· == v) with
      | some k => if acc.contains (k, e.getAppArgs) then acc else acc.push (k, e.getAppArgs)
      | none => acc
    | f => collectMarks ids f acc
  | .lam _ t b _ | .forallE _ t b _ => collectMarks ids b (collectMarks ids t acc)
  | .letE _ t v b _ => collectMarks ids b (collectMarks ids v (collectMarks ids t acc))
  | .mdata _ b | .proj _ _ b => collectMarks ids b acc
  | _ => acc

/-- The marker applications `Gs_k as` in `e` replaced by the real calls `fns[k] as` (innermost arguments too). -/
partial def substMarks (ids : Array FVarId) (fns : Array Lean.Expr) (e : Lean.Expr) : Lean.Expr :=
  e.replace fun x =>
    if x.isApp then
      match x.getAppFn with
      | .fvar v =>
        match ids.findIdx? (· == v) with
        | some k => some (mkAppN fns[k]! (x.getAppArgs.map (substMarks ids fns)))
        | none => none
      | _ => none
    else none

def mkTuple (es : Array Lean.Expr) : MetaM Lean.Expr := do
  let mut r := Lean.mkConst ``PUnit.unit [levelOne]
  for e in es.reverse do
    r ← mkAppM ``Prod.mk #[e, r]
  return r

def tupleTy (ts : Array Lean.Expr) : MetaM Lean.Expr := do
  let mut r := Lean.mkConst ``PUnit [levelOne]
  for t in ts.reverse do
    r ← mkAppM ``Prod #[t, r]
  return r

/-- The `j`-th component of an oracle tuple. -/
def tupleGet (o : Lean.Expr) (j : Nat) : MetaM Lean.Expr := do
  let mut r := o
  for _ in List.range j do r ← mkAppM ``Prod.snd #[r]
  mkAppM ``Prod.fst #[r]

/-- Nested `withLocalDeclD`. -/
partial def withFVars {α} (names : Array Name) (tys : Array Lean.Expr) (k : Array Lean.Expr → TermElabM α) : TermElabM α :=
  let rec go (i : Nat) (acc : Array Lean.Expr) : TermElabM α :=
    if h : i < tys.size then
      withLocalDeclD names[i]! tys[i] fun v => go (i + 1) (acc.push v)
    else k acc
  go 0 #[]

/-- `Signal.val s t` -/
def valAt (s t : Lean.Expr) : MetaM Lean.Expr := mkAppM ``Sparkle.Core.Signal.Signal.val #[s, t]

/-- `∀ i < t, x.val i = y.val i` -/
def agreeBelow (x y t : Lean.Expr) : MetaM Lean.Expr :=
  withLocalDeclD `i (Lean.mkConst ``Nat) fun i => do
    let lt ← mkAppM ``LT.lt #[i, t]
    let eq ← mkEq (← valAt x i) (← valAt y i)
    mkForallFVars #[i] (← mkArrow lt eq)

/-- Unfold the user's own definitions (the circuit's helper functions) except the children; non-recursive ones only. -/
def unfoldUser (kids : Array Kid) (e : Lean.Expr) : MetaM Lean.Expr := do
  let env ← getEnv
  let r ← Meta.transform e (pre := fun x => do
    if x.isApp || x.isConst then
      if let .const n _ := x.getAppFn then
        if !(kids.any (·.decl == n)) && Tools.VedU2HierStGen.userModule env n then
          if let some (.defnInfo _) := env.find? n then
            if let some y ← unfoldDefinition? x then
              return .visit y.headBeta
    return .continue)
  zetaReduce r

/-- The user's definitions a child's value reaches (names a script can unfold), bounded depth. -/
partial def reachDefs (env : Environment) (n : Name) (fuel : Nat) (acc : Array Name) : Array Name :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    if acc.contains n then acc
    else match env.find? n with
      | some (.defnInfo ci) =>
        let acc := acc.push n
        ci.value.foldConsts acc fun c a =>
          if Tools.VedU2HierStGen.userModule env c && (env.find? c).any (·.isDefinition) then reachDefs env c f a else a
      | _ => acc

def plumbingL : String :=
  "packRegister, Signal.register, Signal.memStep, Circuit.next, Circuit.pure', Circuit.bind, mkHolds, Signal.map, Signal.mux, bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq"

def sigvalL : String :=
  "sigval_add, sigval_sub, sigval_mul, sigval_and, sigval_or, sigval_xor, sigval_shl, sigval_shr, sigval_append, sigval_add_c, sigval_sub_c, sigval_mul_c, sigval_and_c, sigval_or_c, sigval_xor_c, sigval_shl_c, sigval_shr_c, sigval_append_c, sigval_c_add, sigval_c_sub, sigval_c_mul, sigval_c_and, sigval_c_or, sigval_c_xor, sigval_c_shl, sigval_c_shr, sigval_c_append, sigval_and_b, sigval_or_b, sigval_xor_b, sigval_not, sigval_not_b, sigval_neg, sigval_mux, sigval_beq, sigval_pure"

/-- Elaborate the tactic script `text` against `ty` and add the theorem `n` (kernel-checked). -/
def proveByScript (decl : Name) (n : Name) (ty : Lean.Expr) (text : String) : TermElabM Unit := do
  let stx ← match Lean.Parser.runParserCategory (← getEnv) `term text "<ved_u2_hier_multi>" with
    | .ok s => pure s
    | .error e => refuse decl "open" m!"generated script for {n} does not parse: {e}\n{text}"
  let errsBefore := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
  let pf ← try
      withOptions (fun o => ((o.setBool `linter.unusedSimpArgs false).setBool `linter.unusedTactic false).setBool
          `linter.unreachableTactic false) <| withoutErrToSorry <| withEnableInfoTree false do
        let e ← elabTermEnsuringType stx ty
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
    catch e => refuse decl "open" m!"the proof of {n} failed: {e.toMessageData}"
  let errs := (← Core.getMessageLog).toList.filter (·.severity == .error)
  if errs.length != errsBefore then
    let first ← match errs.drop errsBefore with
      | msg :: _ => msg.data.toString
      | [] => pure ""
    refuse decl "open" m!"errors were logged while elaborating the proof of {n}; first: {first}"
  if pf.hasMVar || pf.hasFVar then refuse decl "open" m!"the proof of {n} is not closed"
  try
    withOptions (fun o => o.setBool `Elab.async false) do
      addDecl (.thmDecl { name := n, levelParams := [], type := ty, value := pf })
  catch e => refuse decl "open" m!"the kernel refused {n}: {e.toMessageData}"

/-- VED compose (`pw`): the pointwise lemma of a combinational child call `fn` (of type `fnTy`, a function of signals):
`G v1 .. vn := (fn (pure v1) .. (pure vn)).val 0` and `pw : ∀ As i, (fn As).val i = G (As_1.val i) .. (As_n.val i)`, the
latter a kernel `Eq.refl` (the kernel refuses a child that is not pointwise; then `false`).  With `pw` the proof of `hOs`
rewrites a call by this lemma instead of unfolding the child's definitions on both sides.  `false` also when an argument
is not a signal.  Nothing about the child is assumed: the lemma is checked by the kernel. -/
def mkPointwise (gName pwName : Name) (fn fnTy : Lean.Expr) : TermElabM Bool := do
  forallTelescope fnTy fun As _ => do
    let sigArgs ← As.mapM fun a => do
      let t ← whnf (← inferType a)
      pure (if t.isAppOf ``Sparkle.Core.Signal.Signal && t.getAppNumArgs == 2 then some t.getAppArgs else none)
    if As.isEmpty || sigArgs.any (·.isNone) then return false
    let sa := sigArgs.map (·.get!)
    withFVars (sa.mapIdx fun i _ => Name.mkSimple s!"ved_v{i}") (sa.map (·[1]!)) fun vs => do
      let ps ← (vs.zip sa).mapM fun (v, a) =>
        mkAppOptM ``Sparkle.Core.Signal.Signal.pure #[some a[0]!, some a[1]!, some v]
      let gVal ← mkLambdaFVars vs (← valAt (mkAppN fn ps) (mkNatLit 0))
      addDefnRegular gName (← inferType gVal) gVal
    withLocalDeclD `i (Lean.mkConst ``Nat) fun i => do
      let lhs ← valAt (mkAppN fn As) i
      let rhs := mkAppN (Lean.mkConst gName) (← As.mapM fun a => valAt a i)
      let ty ← mkForallFVars (As.push i) (← mkEq lhs rhs)
      let val ← mkLambdaFVars (As.push i) (← mkEqRefl lhs)
      try
        withOptions (fun o => o.setBool `Elab.async false) do
          addDecl (.thmDecl { name := pwName, levelParams := [], type := ty, value := val })
        return true
      catch _ => return false

/-- Closed subterms of `e` (not under a bound variable of `e`) that reduce to a `runCircuitH`: `(subterm, run, projection wrapper)`.
The result of a subterm is remembered (`memo`): a fused body is a DAG whose tree is exponentially large (connect17); the order and
the multiplicity of the result are those of the plain traversal. -/
partial def innerRunsM (skip : Array Name) (memo : IO.Ref (Std.HashMap Lean.Expr (Array (Lean.Expr × Lean.Expr × (Lean.Expr → Lean.Expr)))))
    (e : Lean.Expr) (acc : Array (Lean.Expr × Lean.Expr × (Lean.Expr → Lean.Expr))) :
    MetaM (Array (Lean.Expr × Lean.Expr × (Lean.Expr → Lean.Expr))) := do
  if let some r := (← memo.get)[e]? then return acc ++ r
  let env ← getEnv
  let here : MetaM (Option (Lean.Expr × Lean.Expr × (Lean.Expr → Lean.Expr))) := do
    if e.isApp && !e.hasLooseBVars then
      match e.getAppFn with
      | .const n _ =>
        if skip.contains n then return none
        if !(env.isProjectionFn n || Tools.VedU2HierStGen.userModule env n) then return none
        match ← (try findRun e 16 catch _ => pure none) with
        -- the circuit's own result (no projection around it): a field read of it contains it as the argument
        | some (r, w) => if r.getAppNumArgs == 8 && w r == r then return some (e, r, w) else return none
        | none => return none
      | _ => return none
    else return none
  let res ← match ← here with
    | some c => pure #[c]
    | none =>
      match e with
      | .app f a => do innerRunsM skip memo a (← innerRunsM skip memo f #[])
      | .lam _ _ b _ => innerRunsM skip memo b #[]
      | .letE _ _ v b _ => do innerRunsM skip memo b (← innerRunsM skip memo v #[])
      | .mdata _ b => innerRunsM skip memo b #[]
      | .proj _ _ b => innerRunsM skip memo b #[]
      | _ => pure #[]
  memo.modify (·.insert e res)
  return acc ++ res

def innerRuns (skip : Array Name) (e : Lean.Expr) (acc : Array (Lean.Expr × Lean.Expr × (Lean.Expr → Lean.Expr))) :
    MetaM (Array (Lean.Expr × Lean.Expr × (Lean.Expr → Lean.Expr))) := do
  innerRunsM skip (← IO.mkRef {}) e acc

/-- `Prod.mk _ _ out writes` of a reduced circuit result. -/
def splitResult (decl : Name) (r : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  unless r.isAppOfArity ``Prod.mk 4 do refuse decl "open" m!"multiCircuit: the reduced circuit body is not a pair (output, writes): {r}"
  return (r.getArg! 2, r.getArg! 3)

/-- VED compose multiCircuit, one step: the closed circuit `run` (circuit B) reads, through the closed subterm `x`, the result of a
second circuit A = `runA` (a closed `runCircuitH`, itself with no closed circuit inside).  Returns the fused run (one `runCircuitH`
over `αA ++ αB`) and a proof of `fused = run`.  Calls of children inside either body are marked during the reduction. -/
def fuseOne (decl : Name) (kids : Array Kid) (pw : Bool) (xs : Array Lean.Expr) (run : Lean.Expr)
    (x runA : Lean.Expr) (wrapA : Lean.Expr → Lean.Expr) (base : Name) (sfx : String) (prodRed : Bool := false) :
    TermElabM (Lean.Expr × Lean.Expr) := do
  let rargs := run.getAppArgs
  let aargs := runA.getAppArgs
  let dom := rargs[0]!; let αB := rargs[1]!; let ρB := rargs[2]!
  let αA := aargs[1]!; let ρA := aargs[2]!
  unless aargs[0]! == dom do refuse decl "open" m!"multiCircuit: the two circuits are in different domains"
  let τ ← inferType x
  let wA ← withLocalDeclD `r ρA fun r => mkLambdaFVars #[r] (wrapA r)
  let bodyA := aargs[7]!
  let abs ← kabstract rargs[7]! x
  let bodyB := Lean.mkLambda `z .default τ abs
  let iA := aargs[6]!; let iB := rargs[6]!
  let αF ← reduce (← mkAppM ``HAppend.hAppend #[αA, αB])
  let iF ← reduce (← mkAppOptM ``Tools.VedComposeMultiCircuit.happend #[some αA, some αB, some iA, some iB])
  let hl (a : Lean.Expr) : MetaM Lean.Expr := mkAppM ``Sparkle.Core.HList #[a]
  let sigTy (a : Lean.Expr) : MetaM Lean.Expr := do mkAppM ``Sparkle.Core.Signal.Signal #[dom, ← hl a]
  let liveATy ← sigTy αA
  let liveBTy ← sigTy αB
  let natTy := Lean.mkConst ``Nat
  let reduceRun (bd : Lean.Expr) (αs : Lean.Expr) (live : Lean.Expr) : TermElabM Lean.Expr := do
    let liveTy ← sigTy αs
    let idRead ← withLocalDeclD `s liveTy fun s => mkLambdaFVars #[s] s
    let sigListTy := mkApp2 (Lean.mkConst ``Sparkle.Core.Circuit.SigList) dom αs
    let idLift ← withLocalDeclD `f (← mkArrow sigListTy sigListTy) fun f => mkLambdaFVars #[f] f
    let regs ← mkAppM ``Sparkle.Core.mkRegList #[live, αs, idRead, idLift]
    let holds ← mkAppM ``Sparkle.Core.mkHolds #[αs, live]
    let r0 ← withTransparency .reducible <| reduce (mkApp (mkApp bd regs) holds) (skipTypes := true) (skipProofs := true)
    unfoldUser kids r0
  -- the child calls of both bodies as markers (the reduction must not unfold a child), with their pointwise lemmas;
  -- A's sites first, then B's (B's body with the closed reader subterm `x` replaced by a variable: the calls inside `x` are A's)
  let siteKid ← IO.mkRef (#[] : Array Nat)
  let siteFn ← IO.mkRef (#[] : Array Lean.Expr)
  let siteTy ← IO.mkRef (#[] : Array Lean.Expr)
  let collect (e : Lean.Expr) : MetaM Unit :=
    discard <| replaceCalls kids e fun _ ki fn dargs _ => do
      siteKid.modify (·.push ki)
      siteFn.modify (·.push (mkAppN fn dargs))
      siteTy.modify (·.push (← inferType (mkAppN fn dargs)))
      return Lean.mkConst ``True
  collect bodyA
  let nSitesA := (← siteKid.get).size
  withLocalDeclD `xz τ fun xz => collect (abs.instantiate1 xz)
  let siteKid ← siteKid.get; let siteFn ← siteFn.get; let siteTy ← siteTy.get
  let envNow ← getEnv
  let reachL := if Tools.VedComposeMultiCircuit.ved.compose.noReach.get (← getOptions) then "" else ", ".intercalate ((kids.toList.flatMap fun k => (reachDefs envNow k.decl 6 #[]).toList.map fun c => toString (userName c)).eraseDups)
  let mut pwNames : Array Name := #[]
  if pw then
    let kidsUsed := siteKid.toList.eraseDups
    for ki in kidsUsed do
      let some j0 := siteKid.findIdx? (· == ki) | pure ()
      let pwName := base ++ Name.mkSimple (sfx ++ s!"_pw{ki}")
      let ok ← try mkPointwise (base ++ Name.mkSimple (sfx ++ s!"_G{ki}")) pwName siteFn[j0]! siteTy[j0]! catch _ => pure false
      if ok then pwNames := pwNames.push pwName
    if pwNames.size != kidsUsed.length then pwNames := #[]
  let waName := base ++ Name.mkSimple (sfx ++ "_WA")
  let wbName := base ++ Name.mkSimple (sfx ++ "_WB")
  -- reduced write functions
  let (waE, wbE) ← withLocalDeclD `x liveATy fun xv => withLocalDeclD `y liveBTy fun yv => do
    withFVars (siteKid.mapIdx fun i _ => Name.mkSimple s!"ved_G{i}") siteTy fun gs => do
      let ids := gs.map (·.fvarId!)
      let bodyAM ← replaceCalls kids bodyA fun idx _ _ _ das => pure (mkAppN gs[idx]! das)
      let rA ← substMarks ids siteFn <$> reduceRun bodyAM αA xv
      let (outA, wA') ← splitResult decl rA
      let zA ← withTransparency .reducible <| reduce (mkApp wA outA) (skipTypes := true) (skipProofs := true)
      let rB ← withLocalDeclD `xz τ fun xz => do
        let bodyM ← replaceCalls kids (abs.instantiate1 xz) fun idx _ _ _ das => pure (mkAppN gs[nSitesA + idx]! das)
        let bodyBM ← mkLambdaFVars #[xz] bodyM
        let r ← reduceRun (mkApp bodyBM zA) αB yv
        pure (substMarks ids siteFn r)
      let (_, wB') ← splitResult decl rB
      pure (← mkLambdaFVars (xs ++ #[xv]) wA', ← mkLambdaFVars (xs ++ #[xv, yv]) wB')
  addDefnRegular waName (← inferType waE) waE
  addDefnRegular wbName (← inferType wbE) wbE
  let waC := Lean.mkConst waName; let wbC := Lean.mkConst wbName
  let satOf (αs w t : Lean.Expr) : MetaM Lean.Expr := mkAppOptM ``Tools.VedComposeMultiCircuit.sat #[some dom, some αs, some w, some t]
  let names := (List.range xs.size).map fun i => s!"a{i}"
  let intros := " ".intercalate names
  let OPEN := "open Sparkle.Core Sparkle.Core.Signal in"
  let plain := "simp only"
  let _ := plain
  let hWAty ← mkForallFVars xs (← withLocalDeclD `t natTy fun t => withLocalDeclD `x liveATy fun xv => withLocalDeclD `y liveATy fun yv => do
    let hyp ← mkEq (← valAt xv t) (← valAt yv t)
    let c ← mkEq (← satOf αA (mkAppN waC (xs ++ #[xv])) t) (← satOf αA (mkAppN waC (xs ++ #[yv])) t)
    mkForallFVars #[t, xv, yv] (← mkArrow hyp c))
  let hWAn := base ++ Name.mkSimple (sfx ++ "_hWA")
  let reachPart := if reachL.isEmpty then "" else reachL ++ ", "
  let pwPart := if pwNames.isEmpty then "" else ", ".intercalate (pwNames.toList.map fun n => toString (userName n)) ++ ", "
  proveByScript decl hWAn hWAty s!"by
  intro {intros} t x y h
  {OPEN} first | (simp only [{toString (userName waName)}, Tools.VedComposeMultiCircuit.sat, {plumbingL}, {sigvalL}, h]; done) | (simp only [{toString (userName waName)}, Tools.VedComposeMultiCircuit.sat, {pwPart}{plumbingL}, {sigvalL}, h]; done) | (simp only [{toString (userName waName)}, Tools.VedComposeMultiCircuit.sat, {reachPart}{plumbingL}, {sigvalL}, h])"
  let hWBty ← mkForallFVars xs (← withLocalDeclD `t natTy fun t => withLocalDeclD `x liveATy fun xv => withLocalDeclD `x' liveATy fun xv' =>
      withLocalDeclD `y liveBTy fun yv => withLocalDeclD `y' liveBTy fun yv' => do
    let hx ← mkEq (← valAt xv t) (← valAt xv' t)
    let hy ← mkEq (← valAt yv t) (← valAt yv' t)
    let c ← mkEq (← satOf αB (mkAppN wbC (xs ++ #[xv, yv])) t) (← satOf αB (mkAppN wbC (xs ++ #[xv', yv'])) t)
    mkForallFVars #[t, xv, xv', yv, yv'] (← mkArrow hx (← mkArrow hy c)))
  let hWBn := base ++ Name.mkSimple (sfx ++ "_hWB")
  proveByScript decl hWBn hWBty s!"by
  intro {intros} t x x' y y' hx hy
  {OPEN} first | (simp only [{toString (userName wbName)}, Tools.VedComposeMultiCircuit.sat, {pwPart}{plumbingL}, {sigvalL}, hx, hy]; done) | (simp only [{toString (userName wbName)}, Tools.VedComposeMultiCircuit.sat, {reachPart}{plumbingL}, {sigvalL}, hx, hy])"
  -- the fused run and the equation
  let some (.defnInfo _) := (← getEnv).find? ``Sparkle.Core.runCircuitH | refuse decl "open" m!"no runCircuitH"
  let instF1 ← mkAppOptM ``Sparkle.Core.HListWireable #[some αF] >>= fun t => synthInstance t
  let instF2 ← synthInstance (← mkAppM ``Inhabited #[← hl αF])
  let fuseT := Lean.mkConst ``Tools.VedComposeMultiCircuit.fuse_run
  let fuseApp ← mkAppOptM ``Tools.VedComposeMultiCircuit.fuse_run
    #[some dom, some αA, some αB, some ρA, some ρB, some τ, some aargs[3]!, some rargs[3]!, some aargs[4]!, some rargs[4]!,
      some instF1, some aargs[5]!, some rargs[5]!, some instF2, some iA, some iB, some bodyA, some wA, some bodyB,
      some (mkAppN (Lean.mkConst hWAn) xs), some (mkAppN (Lean.mkConst hWBn) xs)]
  let _ := fuseT
  let bodyF ← mkAppM ``Tools.VedComposeMultiCircuit.fuseBody #[bodyA, wA, bodyB]
  -- the body handed on is `fuseBody` with the append helpers unfolded (plain `circuit do` plumbing for the later stages)
  let mine : Array Name := #[``Tools.VedComposeMultiCircuit.fuseBody, ``Tools.VedComposeMultiCircuit.liveOfSigs,
    ``Tools.VedComposeMultiCircuit.stake, ``Tools.VedComposeMultiCircuit.sdrop, ``Tools.VedComposeMultiCircuit.sappend,
    ``Sparkle.Core.mkRegList, ``Sparkle.Core.mkHolds]
  let rawRef ← IO.mkRef (Lean.mkConst ``True)
  let bodyFN ← forallTelescopeReducing (← inferType bodyF) fun vs _ => do
    let e ← Meta.transform (mkAppN bodyF vs) (pre := fun x => do
      if let .const n _ := x.getAppFn then
        if mine.contains n then
          if let some y ← unfoldDefinition? x then return .visit y.headBeta
      return .continue)
    rawRef.set (← mkLambdaFVars vs e)
    -- `Signal.map fst (bundle2 a b)` is `a` and `Signal.map snd (bundle2 a b)` is `b` (definitionally; the later stages
    -- evaluate plain reads, not a bundle of the seed)
    let isProj (f : Lean.Expr) : Option Bool :=
      match f with
      | .lam _ _ b _ =>
        if b.isAppOfArity ``Prod.fst 3 && b.appArg!.isBVar then some true
        else if b.isAppOfArity ``Prod.snd 3 && b.appArg!.isBVar then some false
        else match b with
          | .proj ``Prod 0 (.bvar 0) => some true
          | .proj ``Prod 1 (.bvar 0) => some false
          | _ => none
      | _ => if f.isAppOfArity ``Prod.fst 2 then some true else if f.isAppOfArity ``Prod.snd 2 then some false else none
    let e ← Meta.transform (← zetaReduce e) (post := fun x0 => do
      let x := x0.headBeta
      if x.isAppOfArity ``Sparkle.Core.Signal.Signal.map 5 then
        let s := x.getArg! 4
        if s.isAppOfArity ``Sparkle.Core.Signal.bundle2 5 then
          match isProj (x.getArg! 3) with
          | some true => return .done (s.getArg! 3)
          | some false => return .done (s.getArg! 4)
          | none => return .done x
      -- shared-circuit fusion: the pair outputs of the earlier circuits are read by projections (a projection of a pair is the component)
      if prodRed then
        if x.isAppOfArity ``Prod.fst 3 && (x.getArg! 2).isAppOfArity ``Prod.mk 4 then return .done ((x.getArg! 2).getArg! 2)
        if x.isAppOfArity ``Prod.snd 3 && (x.getArg! 2).isAppOfArity ``Prod.mk 4 then return .done ((x.getArg! 2).getArg! 3)
        if let .proj ``Prod i s := x then
          if s.isAppOfArity ``Prod.mk 4 then return .done (s.getArg! (2 + i))
      return .done x)
    mkLambdaFVars vs e
  let fusedRun ← mkAppOptM ``Sparkle.Core.runCircuitH
    #[some dom, some αF, some ρB, some rargs[3]!, some instF1, some instF2, some iF, some bodyFN]
  let stepPf ← mkExpectedTypeHint fuseApp (← mkEq fusedRun run)
  -- measurement only (`VED_OPEN_TICK`): the kernel time of this one fusion step (the whole fuseEq is checked once more at the end)
  if ← Tools.VedU2HierDbg.openTickOn then
    let t0 ← IO.monoMsNow
    let chk (nm : String) (lhs rhs : Lean.Expr) : TermElabM Unit := do
      let t1 ← IO.monoMsNow
      let ty ← mkForallFVars xs (← mkEq lhs rhs)
      let v ← mkLambdaFVars xs (← mkEqRefl lhs)
      try
        withOptions (fun o => o.setBool `Elab.async false) do
          addDecl (.thmDecl { name := base ++ Name.mkSimple (sfx ++ nm), levelParams := [], type := ty, value := v })
      catch e => Tools.VedU2HierDbg.openTick s!"fuseOne {sfx}: {nm} refused: {(← e.toMessageData.toString).take 200}"
      Tools.VedU2HierDbg.openTick s!"fuseOne {sfx}: {nm} kernel {(← IO.monoMsNow) - t1} ms"
    -- (a) the fused run against `fuseBody` unfolded (bodyFN); (b) the reader with the circuit read substituted against `run`
    let fuseRunRaw ← mkAppOptM ``Sparkle.Core.runCircuitH
      #[some dom, some αF, some ρB, some rargs[3]!, some instF1, some instF2, some iF, some bodyF]
    chk "_chkA" fuseRunRaw fusedRun
    let rawRun ← mkAppOptM ``Sparkle.Core.runCircuitH
      #[some dom, some αF, some ρB, some rargs[3]!, some instF1, some instF2, some iF, some (← rawRef.get)]
    chk "_chkA1" fuseRunRaw rawRun
    chk "_chkA2" rawRun fusedRun
    let rhsB ← mkAppOptM ``Sparkle.Core.runCircuitH
      #[some dom, some αB, some ρB, some rargs[3]!, some rargs[4]!, some rargs[5]!, some iB, some (mkApp bodyB (mkApp wA runA))]
    chk "_chkB" rhsB run
    let stepTy ← mkForallFVars xs (← mkEq fusedRun run)
    let stepVal ← mkLambdaFVars xs stepPf
    try
      withOptions (fun o => o.setBool `Elab.async false) do
        addDecl (.thmDecl { name := base ++ Name.mkSimple (sfx ++ "_stepchk"), levelParams := [], type := stepTy, value := stepVal })
    catch e => Tools.VedU2HierDbg.openTick s!"fuseOne {sfx}: step kernel check refused: {← e.toMessageData.toString}"
    Tools.VedU2HierDbg.openTick s!"fuseOne {sfx}: step kernel check {(← IO.monoMsNow) - t0} ms"
  return (fusedRun, stepPf)

/-- VED compose multiCircuit, K circuits: fuse every closed circuit read inside `run`, innermost first (a circuit read by a
circuit that is itself read is fused with its own readers first), and of several circuits read by one body the LAST one first
(the registers of the earlier let-bound circuits then come first).  Returns the fused run and a proof of `fused = run`;
`none` when `run` contains no closed circuit. -/
partial def fuseAll (decl : Name) (kids : Array Kid) (pw : Bool) (xs : Array Lean.Expr) (run : Lean.Expr)
    (base : Name) (sfx : String) (ctr : IO.Ref Nat) : TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  let skip := kids.map (·.decl)
  Tools.VedU2HierDbg.openTick s!"fuseAll {sfx}: innerRuns begin"
  let cs ← innerRuns skip run.getAppArgs[7]! #[]
  Tools.VedU2HierDbg.openTick s!"fuseAll {sfx}: {cs.size} readers"
  if cs.isEmpty then return none
  let (x, runA, wrapA) := cs.back!
  -- the circuit read is itself fused with the circuits it reads first
  let (runA', pf1?) ← match ← fuseAll decl kids pw xs runA base sfx ctr with
    | some (r, pf) => pure (r, some pf)
    | none => pure (runA, none)
  let (cur, pfC?) ← match pf1? with
    | none => pure (run, none)
    | some pfA => do
      -- `run` with `x` replaced by the fused run, and `cur = run` from `runA' = runA`
      let ty ← inferType runA
      let absRun ← kabstract run x
      let f := Lean.mkLambda `r .default ty absRun
      let pf ← mkAppM ``congrArg #[f, pfA]
      pure (absRun.instantiate1 runA', some pf)
  let k ← ctr.modifyGet fun n => (n, n + 1)
  Tools.VedU2HierDbg.openTick s!"fuseOne {k} begin"
  let (fused, pf2) ← fuseOne decl kids pw xs cur (if pf1?.isSome then runA' else x) runA' wrapA base (sfx ++ s!"_{k}")
  Tools.VedU2HierDbg.openTickE s!"fuseOne {k} end" fused
  let pfD ← match pfC? with
    | some pfC => mkAppM ``Eq.trans #[pf2, pfC]
    | none => pure pf2
  -- further readers of the body
  match ← fuseAll decl kids pw xs fused base sfx ctr with
  | some (r, pf3) => return some (r, ← mkAppM ``Eq.trans #[pf3, pfD])
  | none => return some (fused, pfD)

/-- The closed circuits a body reads (innerRuns), each circuit once. -/
def readsOf (skip : Array Name) (body : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let cs ← innerRuns skip body #[]
  let mut out : Array (Lean.Expr × Lean.Expr) := #[]
  for (x, r, _) in cs do
    unless out.any (·.1 == x) do out := out.push (x, r)
  return out

/-- Shared-circuit fusion, the read graph: the circuits `x` (closed calls) reachable from a body in post-order (a circuit after
every circuit it reads, readers in occurrence order), each ONCE, with the circuits each reads, and how many readers each has. -/
partial def sharedVisit (skip : Array Name) (ord : IO.Ref (Array (Lean.Expr × Lean.Expr × Array Lean.Expr)))
    (cnt : IO.Ref (Std.HashMap Lean.Expr Nat)) (x r : Lean.Expr) : MetaM Unit := do
  let ds ← readsOf skip r.getAppArgs[7]!
  for (dx, dr) in ds do
    cnt.modify fun m => m.insert dx (m.getD dx 0 + 1)
    unless (← ord.get).any (·.1 == dx) do sharedVisit skip ord cnt dx dr
  ord.modify (·.push (x, r, ds.map (·.1)))

/-- Component `i` of the left-nested tuple `tup` of `m` circuit values (`tup_1 = e_0`, `tup_m = (tup_{m-1}, e_{m-1})`). -/
partial def projOfTup (tup : Lean.Expr) (m i : Nat) : MetaM Lean.Expr := do
  if m ≤ 1 then return tup
  else if i == m - 1 then mkAppM ``Prod.snd #[tup]
  else projOfTup (← mkAppM ``Prod.fst #[tup]) (m - 1) i

/-- VED compose multiCircuit, shared circuits (unit 19): when a closed circuit is read by SEVERAL readers (a diamond: `D` reads `A` and
`S`, `S` reads `A`), every circuit is fused ONCE.  The circuits are taken in post-order of the read graph; the fusion of the first `j`
carries the tuple of their outputs (`tup_j`, left-nested), so a later reader reads a shared circuit by a projection of the fused
output (not by a second copy).  Step `j`: the reader `B` with its reads replaced by projections of `tup_{j-1}`, whose output is the
pair `(tup_{j-1}, out B)` (not for the last step, the declaration's own run), is fused with the run so far by `fuseOne`; the proof of
`F_j = tup_j` is the fusion equation, `congrArg` of the claim `F_{j-1} = tup_{j-1}`, and a definitional step.  `none` when no
circuit has two readers (the usual chain fusion `fuseAll` then applies). -/
def fuseShared (decl : Name) (kids : Array Kid) (pw : Bool) (xs : Array Lean.Expr) (run : Lean.Expr)
    (base : Name) (sfx : String) (ctr : IO.Ref Nat) : TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  let skip := kids.map (·.decl)
  let ord ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr × Array Lean.Expr))
  let cnt ← IO.mkRef ({} : Std.HashMap Lean.Expr Nat)
  let topDs ← readsOf skip run.getAppArgs[7]!
  for (dx, dr) in topDs do
    cnt.modify fun m => m.insert dx (m.getD dx 0 + 1)
    unless (← ord.get).any (·.1 == dx) do sharedVisit skip ord cnt dx dr
  Tools.VedU2HierDbg.openTick s!"fuseShared: read graph {(← ord.get).size} circuits, {topDs.size} read by the top, readers per circuit {(← cnt.get).toList.map (·.2)}"
  unless (← cnt.get).toList.any (·.2 ≥ 2) do return none
  let ord ← ord.get
  Tools.VedU2HierDbg.openTick s!"fuseShared: {ord.size} circuits, one fusion each"
  let mut F := ord[0]!.2.1
  let mut tup := ord[0]!.1
  let mut claim ← mkExpectedTypeHint (← mkEqRefl F) (← mkEq F tup)
  for j in [1:ord.size + 1] do
    let isTop := j == ord.size
    let (xB, B, deps) := if isTop then (run, run, topDs.map (·.1)) else ord[j]!
    let bargs := B.getAppArgs
    -- the reads of the earlier circuits replaced by projections of the tuple (all at once: the tuple itself contains them)
    let tys ← deps.mapM fun d => inferType d
    let bodyS ← withFVars (deps.mapIdx fun i _ => Name.mkSimple s!"ved_d{i}") tys fun fvs => do
      let mut b := bargs[7]!
      -- syntactic replacement, one pass from the top (a circuit that reads another contains it, and is replaced whole): `kabstract`
      -- compares candidates by `isDefEq`, which unfolds the circuits of two different calls of one definition
      for d in deps do
        unless (b.find? (· == d)).isSome do throwError "multiCircuit shared: a read circuit does not occur in the reader's body"
      b := b.replace fun x => match deps.findIdx? (· == x) with | some i => some fvs[i]! | none => none
      let prs ← deps.mapM fun d => do
        let some i := ord.findIdx? (·.1 == d) | throwError "multiCircuit shared: a read circuit is not in the read graph"
        projOfTup tup j i
      pure ((b.abstract fvs).instantiateRev prs)
    Tools.VedU2HierDbg.openTickE s!"fuseShared step {j}: reads replaced by projections" bodyS
    let Bt ← if isTop then pure (mkAppN B.getAppFn (bargs.set! 7 bodyS)) else do
      let .forallE _ regsTy circ _ ← whnf (← inferType bodyS) | throwError "multiCircuit shared: the body of runCircuitH has an unexpected type"
      let .forallE _ wTy _ _ ← whnf circ | throwError "multiCircuit shared: the Circuit type has an unexpected shape"
      let body' ← withLocalDeclD `regs regsTy fun r => withLocalDeclD `h wTy fun h => do
        let rr := mkApp2 bodyS r h
        let out ← mkAppM ``Prod.fst #[rr]
        let wr ← mkAppM ``Prod.snd #[rr]
        mkLambdaFVars #[r, h] (← mkAppM ``Prod.mk #[← mkAppM ``Prod.mk #[tup, out], wr])
      let ρ'' ← mkAppM ``Prod #[← inferType tup, bargs[2]!]
      let inst ← synthInstance (← mkAppM ``Sparkle.Core.HasDomain #[ρ'', bargs[0]!])
      pure (mkAppN B.getAppFn ((bargs.set! 2 ρ'').set! 3 inst |>.set! 7 body'))
    Tools.VedU2HierDbg.openTickE s!"fuseShared step {j}: reader built" Bt
    let ty ← inferType tup
    let f ← withLocalDeclD `r ty fun r => mkLambdaFVars #[r] (Bt.replace fun x => if x == tup then some r else none)
    let cur := Bt.replace fun x => if x == tup then some F else none
    Tools.VedU2HierDbg.openTick s!"fuseShared step {j}: kabstract done"
    let pfC ← mkAppM ``congrArg #[f, claim]
    Tools.VedU2HierDbg.openTick s!"fuseShared step {j}: congrArg built"
    let k ← ctr.modifyGet fun n => (n, n + 1)
    Tools.VedU2HierDbg.openTick s!"fuseShared {k} begin (circuit {j + 1} of {ord.size + 1})"
    let (Fj, pf2) ← fuseOne decl kids pw xs cur F F id base (sfx ++ s!"_{k}") true
    Tools.VedU2HierDbg.openTickE s!"fuseShared {k} end" Fj
    let pfD ← mkAppM ``Eq.trans #[pf2, pfC]
    Tools.VedU2HierDbg.openTick s!"fuseShared step {j}: Eq.trans built"
    F := Fj
    if isTop then claim ← mkExpectedTypeHint pfD (← mkEq Fj run)
    else
      tup ← mkAppM ``Prod.mk #[tup, xB]
      claim ← mkExpectedTypeHint pfD (← mkEq Fj tup)
  return some (F, claim)

/-- VED compose multiCircuit (unit 15, K circuits since connect16): the declaration's `run` reads closed circuits (closed
`runCircuitH` subterms).  Returns the fused run (one `runCircuitH` over the appended registers) and the name of
`fuseEq : ∀ xs, stmt xs = wrap fusedRun`. -/
def fuseTwo (decl : Name) (kids : Array Kid) (pw : Bool) (stmt : Lean.Expr) (xs : Array Lean.Expr) (run : Lean.Expr)
    (wrap : Lean.Expr → Lean.Expr) (base : Name) (sfx : String) : TermElabM (Option (Lean.Expr × Name)) := do
  let ctr ← IO.mkRef 0
  let r? ← match ← fuseShared decl kids pw xs run base sfx ctr with
    | some r => pure (some r)
    | none => fuseAll decl kids pw xs run base sfx ctr
  let some (fusedRun, pfEq) := r? | return none
  Tools.VedU2HierDbg.openTickE "fuseTwo: fuseAll done (fused run)" fusedRun
  let fuseEqName := base ++ Name.mkSimple (sfx ++ "_fuse")
  let eqTy ← mkForallFVars xs (← mkEq (mkAppN stmt xs) (wrap fusedRun))
  let wrapL ← do
    let ty ← inferType run
    withLocalDeclD `r ty fun r => mkLambdaFVars #[r] (wrap r)
  let pf ← mkLambdaFVars xs (← mkAppM ``congrArg #[wrapL, ← mkEqSymm pfEq])
  Tools.VedU2HierDbg.openTickE "fuseTwo: fuseEq proof built" pf
  try
    withOptions (fun o => o.setBool `Elab.async false) do
      addDecl (.thmDecl { name := fuseEqName, levelParams := [], type := eqTy, value := pf })
  catch e => refuse decl "open" m!"the kernel refused the fused-circuit equation: {e.toMessageData}"
  Tools.VedU2HierDbg.openTick "fuseTwo: fuseEq added"
  return some (fusedRun, fuseEqName)

/-- VED compose multiCircuit, pure-wiring top (connect17): a declaration whose value has no circuit of its own but is an output
function of closed circuits (`f (stageA ..).x (stageB ..).y`, after unfolding the user's wiring definitions and reducing
projections of constructors).  The value `V` is the output of a circuit with NO registers, `runCircuitH (αs := []) () (fun _ h => (V, h))`
(the equation `V = outer` is definitional), so the fusion of the circuits it reads is the same as for a circuit with an outer run.
`none` when the value contains no closed circuit. -/
def outerRun (kids : Array Kid) (dom body0 : Lean.Expr) : MetaM (Option (Lean.Expr × (Lean.Expr → Lean.Expr))) := do
  let v ← normTop kids body0 24
  let cs ← innerRuns (kids.map (·.decl)) v #[]
  if cs.isEmpty then return none
  let ρ ← inferType v
  let nilL := mkApp (Lean.mkConst ``List.nil [levelOne]) (mkSort levelOne)
  let lbl {α} (what : String) (x : MetaM α) : MetaM α := try x catch e => throwError "multiCircuit outer run ({what}): {e.toMessageData}"
  let instH ← lbl "HasDomain" <| synthInstance (← mkAppM ``Sparkle.Core.HasDomain #[ρ, dom])
  let instW ← lbl "HListWireable" <| synthInstance (← mkAppOptM ``Sparkle.Core.HListWireable #[some nilL])
  let instI ← lbl "Inhabited" <| synthInstance (← mkAppM ``Inhabited #[← mkAppM ``Sparkle.Core.HList #[nilL]])
  let unit ← mkAppOptM ``Unit.unit #[]
  let proto ← lbl "runCircuitH" <| mkAppOptM ``Sparkle.Core.runCircuitH #[some dom, some nilL, some ρ, some instH, some instW, some instI, some unit]
  let .forallE _ bodyTy _ _ ← whnf (← inferType proto) | throwError "multiCircuit: runCircuitH has an unexpected type"
  let .forallE _ regsTy circ _ ← whnf bodyTy | throwError "multiCircuit: the body of runCircuitH has an unexpected type"
  let .forallE _ wTy _ _ ← whnf circ | throwError "multiCircuit: the Circuit type has an unexpected shape"
  let body ← withLocalDeclD `regs regsTy fun r => withLocalDeclD `h wTy fun h => do
    mkLambdaFVars #[r, h] (← mkAppM ``Prod.mk #[v, h])
  return some (mkApp proto body, id)

/-- The analysis and the generated constants.  `pw` (option `ved.compose.step`): the proof of `hOs` uses the children's
pointwise lemmas (`mkPointwise`) instead of unfolding them; the produced definitions are the same. -/
def genOpenMulti (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (tbl : DeclTable) (kids : Array Kid)
    (base : Name) (openSuf : String) (pw : Bool := false) (chain : Bool := false) : TermElabM OpenInfo := do
  let openName := base ++ Name.mkSimple openSuf
  Tools.VedU2HierDbg.openTick "genOpenMulti begin"
  let ty ← inferType stmt
  forallTelescope ty fun xs _ => do
    let some (.defnInfo ci) := (← getEnv).find? decl
      | refuse decl "open" m!"{decl} is not a definition"
    let dflt := Lean.mkConst ``Sparkle.Core.Domain.defaultDomain
    let args : Array Lean.Expr := (Array.replicate nDom dflt) ++ xs
    let body0 := (mkAppN ci.value args).headBeta
    let multi := Tools.VedComposeMultiCircuit.ved.compose.multiCircuit.get (← getOptions)
    let some (run, wrap) ← (do
        match ← findRun body0 24 multi with
        | some (r, w) =>
          -- a wrapper that itself holds closed circuits (`a.x + b.y`: only the last operand was found) is a wiring top
          if multi && !(← innerRuns (kids.map (·.decl)) (w (mkSort levelZero)) #[]).isEmpty then
            pure ((← outerRun kids dflt body0).orElse fun _ => some (r, w))
          else pure (some (r, w))
        | none => if multi then outerRun kids dflt body0 else pure none)
      | refuse decl "open" m!"the declaration's value does not reduce to a `circuit do` (runCircuitH)"
    Tools.VedU2HierDbg.openTickE "findRun end" body0
    -- VED compose multiCircuit (option, default off): two wired closed circuits are one circuit over the appended registers
    let (run, fuseEq?) ←
      if Tools.VedComposeMultiCircuit.ved.compose.multiCircuit.get (← getOptions) then
        match ← fuseTwo decl kids pw stmt xs run wrap base (openSuf ++ "_fz") with
        | some (fr, nm) => pure (fr, some nm)
        | none => pure (run, none)
      else pure (run, none)
    Tools.VedU2HierDbg.openTick "genOpenMulti: fuseTwo end"
    let rargs := run.getAppArgs
    unless rargs.size == 8 do refuse decl "open" m!"runCircuitH is not fully applied"
    let dom := rargs[0]!; let αs := rargs[1]!; let rhoTy := rargs[2]!; let inits := rargs[6]!; let body := rargs[7]!
    -- the declaration is a field of the circuit's struct result, or the result itself
    let (headFn?, portName) :=
      match wrap run with
      | w => if w == run then (none, none) else
          match w.getAppFn.constName? with
          | some n => (some n, some n.getString!)
          | none => (none, none)
    let _ := headFn?
    -- call occurrences: the child, the call's function and domain arguments
    let siteKid ← IO.mkRef (#[] : Array Nat)
    let siteFn ← IO.mkRef (#[] : Array Lean.Expr)
    let siteTy ← IO.mkRef (#[] : Array Lean.Expr)
    Tools.VedU2HierDbg.openTick "genOpenMulti: replaceCalls #1 begin"
    discard <| replaceCalls (nested := chain) kids body fun _ ki fn dargs _ => do
      siteKid.modify (·.push ki)
      siteFn.modify (·.push (mkAppN fn dargs))
      siteTy.modify (·.push (← inferType (mkAppN fn dargs)))
      return Lean.mkConst ``True
    let siteKid ← siteKid.get; let siteFn ← siteFn.get; let siteTy ← siteTy.get
    Tools.VedU2HierDbg.openTickE s!"replaceCalls #1 (site collection) end, sites={siteKid.size}" body
    if siteKid.isEmpty then refuse decl "open" m!"no call of a child in the circuit body"
    let liveTy := (← inferType (← mkAppOptM ``Sparkle.Core.packRegister #[some dom, some αs, some inits])).bindingBody!
    let natTy := Lean.mkConst ``Nat
    withFVars (siteKid.mapIdx fun i _ => Name.mkSimple s!"ved_G{i}") siteTy fun gs => do
      let bodyM ← replaceCalls (nested := chain) kids body fun idx _ _ _ das => pure (mkAppN gs[idx]! das)
      Tools.VedU2HierDbg.openTickE "replaceCalls #2 (marker variables) end" bodyM
      withLocalDeclD `live liveTy fun live => do
        let idRead ← withLocalDeclD `s liveTy fun s => mkLambdaFVars #[s] s
        let sigListTy := mkApp2 (Lean.mkConst ``Sparkle.Core.Circuit.SigList) dom αs
        let idLift ← withLocalDeclD `f (← mkArrow sigListTy sigListTy) fun f => mkLambdaFVars #[f] f
        let regs ← mkAppM ``Sparkle.Core.mkRegList #[live, αs, idRead, idLift]
        let holds ← mkAppM ``Sparkle.Core.mkHolds #[αs, live]
        let r0 ← withTransparency .reducible <|
          reduce (mkApp (mkApp bodyM regs) holds) (skipTypes := true) (skipProofs := true)
        Tools.VedU2HierDbg.openTickE "reduce end" r0
        let r ← unfoldUser kids r0
        Tools.VedU2HierDbg.openTickE "unfoldUser end" r
        let marks := collectMarks (gs.map (·.fvarId!)) r #[]
        let realCalls : Lean.Expr → Lean.Expr := if chain then substMarks (gs.map (·.fvarId!)) siteFn else id
        Tools.VedU2HierDbg.openTick s!"collectMarks end, marks={marks.size}"
        -- distinct calls: (child, arguments over `live`)
        let mut orcKey : Array (Nat × Array Lean.Expr) := #[]
        let mut orcSite : Array Nat := #[]
        let mut kToJ : Array (Option Nat) := Array.replicate siteKid.size none
        for (k, as) in marks do
          let key := (siteKid[k]!, as)
          match orcKey.findIdx? (fun q => q.1 == key.1 && q.2 == key.2) with
          | some j => kToJ := kToJ.set! k (some j)
          | none =>
            kToJ := kToJ.set! k (some orcKey.size)
            orcKey := orcKey.push key
            orcSite := orcSite.push k
        if orcKey.isEmpty then refuse decl "open" m!"no live call of a child in the circuit body (every call is dead code)"
        -- a call that is dead code gets the oracle of a live call of the same child (never read)
        for k in List.range siteKid.size do
          if (kToJ[k]!).isNone then
            let ki := siteKid[k]!
            match orcKey.findIdx? (fun q => q.1 == ki) with
            | some j => kToJ := kToJ.set! k (some j)
            | none => refuse decl "open" m!"child {kids[ki]!.decl} is called only in dead code"
        let n := orcKey.size
        Tools.VedU2HierDbg.openTick s!"oracle dedup end, distinct calls={n}"
        let mut orcTys : Array Lean.Expr := #[]
        for (key, k) in orcKey.zip orcSite do
          orcTys := orcTys.push (← inferType (mkAppN siteFn[k]! (key.2.map realCalls)))
        let osTy ← tupleTy orcTys
        withFVars (orcTys.mapIdx fun i _ => Name.mkSimple s!"ved_o{i}") orcTys fun os => do
          let bodyO ← replaceCalls (nested := chain) kids body fun idx _ _ _ _ => pure os[(kToJ[idx]!).get!]!
          if (bodyO.find? fun x => kids.any (fun k => x.isConstOf k.decl)).isSome then
            refuse decl "open" m!"a call of a child remains in the open parent's body (a call nested in another call's argument?)"
          -- the open parent: the struct result (the declaration's field is the port)
          let runO := mkAppN run.getAppFn (rargs.set! 7 bodyO)
          let openVal ← mkLambdaFVars (xs ++ os) runO
          let openTy ← inferType openVal
          Tools.VedU2HierDbg.openTickE "replaceCalls #3 (oracle variables) end" bodyO
          addDefnRegular openName openTy openVal
          Tools.VedU2HierDbg.openTick "open definition added"
          let pre := rargs.extract 0 6
          let loopFOfOf (b : Lean.Expr) : MetaM Lean.Expr :=
            mkAppOptM ``loopFOf ((pre.map some) ++ #[some inits, some b])
          -- F xs o x = packRegister inits (the reduced writes over the state x and the oracle tuple o)
          let some wtup := (if r.isAppOfArity ``Prod.mk 4 then some r.appArg! else none)
            | refuse decl "open" m!"the reduced loop body is not a pair (output, writes): {r}"
          let f2Name := base ++ Name.mkSimple (openSuf ++ (if chain then "_FL" else "_F2"))  -- chain: `_F{j}` of the third call would clash with `_F2`
          let wO := wtup.replace fun e =>
            if e.isApp then
              match e.getAppFn with
              | .fvar v =>
                match gs.findIdx? (·.fvarId! == v) with
                | some k => (kToJ[k]!).bind fun j => some os[j]!
                | none => none
              | _ => none
            else none
          let f2Const := Lean.mkConst f2Name
          withLocalDeclD `o osTy fun ot => withLocalDeclD `x liveTy fun x => do
            let projs ← (List.range n).toArray.mapM (tupleGet ot ·)
            let w := (wO.replaceFVars os projs).replaceFVar live x
            let f2Val ← mkLambdaFVars (xs ++ #[ot, x]) (← mkAppOptM ``Sparkle.Core.packRegister #[some dom, some αs, some inits, some w])
            addDefnRegular f2Name (← inferType f2Val) f2Val
            Tools.VedU2HierDbg.openTickE "F2 definition added" f2Val
          -- Os xs live = the oracle values the real children give
          let osComps : Array Lean.Expr := (orcKey.zip orcSite).map fun (key, k) => mkAppN siteFn[k]! (key.2.map realCalls)
          let osName := base ++ Name.mkSimple (openSuf ++ "_Os")
          let osVal ← mkLambdaFVars (xs ++ #[live]) (← mkTuple osComps)
          addDefnRegular osName (← inferType osVal) osVal
          Tools.VedU2HierDbg.openTick "Os definition added"
          -- the declaration's own loop
          -- the declaration's own loop, as a CONSTANT (the proof's `simp` must not unfold the 34-register body)
          let qName := base ++ Name.mkSimple (openSuf ++ "_Q")
          let qVal ← mkLambdaFVars xs (← mkAppM ``Sparkle.Core.Signal.Signal.loop #[← loopFOfOf body])
          addDefnRegular qName (← inferType qVal) qVal
          Tools.VedU2HierDbg.openTick "Q definition added"
          let qBody := mkAppN (Lean.mkConst qName) xs
          -- E: the oracle tuples agree below t
          let eName := base ++ Name.mkSimple (openSuf ++ "_E")
          withLocalDeclD `o osTy fun o => withLocalDeclD `o' osTy fun o' => withLocalDeclD `t natTy fun t => do
            let conj ← withLocalDeclD `i natTy fun i => do
              let mut c := Lean.mkConst ``True
              for j in (List.range n).reverse do
                let eq ← mkEq (← valAt (← tupleGet o j) i) (← valAt (← tupleGet o' j) i)
                c := mkApp2 (Lean.mkConst ``And) eq c
              mkForallFVars #[i] (← mkArrow (← mkAppM ``LT.lt #[i, t]) c)
            let eVal ← mkLambdaFVars #[o, o', t] conj
            addDefnRegular eName (← inferType eVal) eVal
          let eConst := Lean.mkConst eName
          let osConst := Lean.mkConst osName
          -- the obligations
          let xsN ← xs.mapM fun x => do pure (← x.fvarId!.getUserName)
          let names := (List.range xs.size).map fun i => s!"a{i}"
          let intros := " ".intercalate names
          let eU := toString (userName eName)
          let fU := toString (userName f2Name)
          let osU := toString (userName osName)
          let _ := xsN
          let OPEN := "open Sparkle.Core Sparkle.Core.Signal in"
          let envNow ← getEnv
          let reach := (kids.toList.flatMap fun k => (reachDefs envNow k.decl 6 #[]).toList.map fun c => toString (userName c))
          -- option `ved.compose.noReach`: no unfolding candidates of the children's bodies in `hOs`
          let noReach := Tools.VedComposeMultiCircuit.ved.compose.noReach.get (← getOptions)
          let reachL := if noReach then "" else ", ".intercalate reach.eraseDups
          let reachOs := if reachL.isEmpty then "" else reachL ++ ", "
          -- hcF
          let hcFName := base ++ Name.mkSimple (openSuf ++ "_hcF")
          let hcFTy ← mkForallFVars xs (← withLocalDeclD `o osTy fun o => withLocalDeclD `t natTy fun t =>
              withLocalDeclD `x liveTy fun x => withLocalDeclD `y liveTy fun y => do
            let hyp ← agreeBelow x y t
            let lhs ← valAt (mkAppN (mkConst f2Name) (xs ++ #[o, x])) t
            let rhs ← valAt (mkAppN (mkConst f2Name) (xs ++ #[o, y])) t
            mkForallFVars #[o, t, x, y] (← mkArrow hyp (← mkEq lhs rhs)))
          Tools.VedU2HierDbg.openTick "obligation setup end, hcF begin"
          proveByScript decl hcFName hcFTy s!"by
  intro {intros} o t x y h
  cases t with
  | zero =>
    {OPEN} simp only [{fU}, {plumbingL}]
  | succ s =>
    have hs := h s (Nat.lt_succ_self s)
    {OPEN} simp only [{fU}, {plumbingL}, {sigvalL}, hs]"
          Tools.VedU2HierDbg.openTick "hcF end"
          -- hcO
          let hcOName := base ++ Name.mkSimple (openSuf ++ "_hcO")
          let hcOTy ← mkForallFVars xs (← withLocalDeclD `o osTy fun o => withLocalDeclD `o' osTy fun o' =>
              withLocalDeclD `x liveTy fun x => withLocalDeclD `t natTy fun t => do
            let hyp := mkAppN eConst #[o, o', t]
            let lhs ← valAt (mkAppN (mkConst f2Name) (xs ++ #[o, x])) t
            let rhs ← valAt (mkAppN (mkConst f2Name) (xs ++ #[o', x])) t
            mkForallFVars #[o, o', x, t] (← mkArrow hyp (← mkEq lhs rhs)))
          let hn := (List.range n).map fun j => s!"e{j}"
          let pat := ", ".intercalate (hn ++ ["_"])
          proveByScript decl hcOName hcOTy s!"by
  intro {intros} o o' x t h
  cases t with
  | zero =>
    {OPEN} simp only [{fU}, {plumbingL}]
  | succ s =>
    have hs := h s (Nat.lt_succ_self s)
    obtain ⟨{pat}⟩ := hs
    {OPEN} simp only [{fU}, {plumbingL}, {sigvalL}, {", ".intercalate hn}]"
          Tools.VedU2HierDbg.openTick "hcO end"
          -- the children's pointwise lemmas (option `pw`; none when a child is not pointwise or not a function of signals)
          let mut pwNames : Array Name := #[]
          if pw then
            let kidsUsed := (orcKey.map (·.1)).toList.eraseDups
            for ki in kidsUsed do
              let some j0 := orcKey.findIdx? (fun q => q.1 == ki) | pure ()
              let k0 := orcSite[j0]!
              let pwName := base ++ Name.mkSimple (openSuf ++ s!"_pw{ki}")
              let ok ← try mkPointwise (base ++ Name.mkSimple (openSuf ++ s!"_G{ki}")) pwName siteFn[k0]! siteTy[k0]! catch _ => pure false
              if ok then pwNames := pwNames.push pwName
            if pwNames.size != kidsUsed.length then pwNames := #[]
          Tools.VedU2HierDbg.openTick s!"pointwise lemmas end, {pwNames.size}"
          -- hOs
          let hOsName := base ++ Name.mkSimple (openSuf ++ "_hOs")
          let hOsTy ← mkForallFVars xs (← withLocalDeclD `t natTy fun t => withLocalDeclD `x liveTy fun x =>
              withLocalDeclD `y liveTy fun y => do
            let hyp ← agreeBelow x y t
            let c := mkAppN eConst #[mkAppN osConst (xs ++ #[x]), mkAppN osConst (xs ++ #[y]), t]
            mkForallFVars #[t, x, y] (← mkArrow hyp c))
          let hOsOld := s!"simp only [{osU}, {reachOs}{plumbingL}, {sigvalL}, hx, and_self, and_true]"
          let hOsClose := if pwNames.isEmpty then hOsOld else
            s!"first | (simp only [{osU}, {", ".intercalate (pwNames.toList.map fun n => toString (userName n))}, {plumbingL}, {sigvalL}, hx, and_self, and_true]; done) | ({hOsOld})"
          proveByScript decl hOsName hOsTy s!"by
  intro {intros} t x y h
  unfold {eU}
  intro i hi
  have hx := h i hi
  {OPEN} {hOsClose}"
          Tools.VedU2HierDbg.openTick "hOs end"
          -- the knot: the declaration's loop IS the open loop with the oracle fixed along it
          let Qx := qBody
          let osQ := osComps.map fun c => c.replaceFVar live Qx
          let bodyStar := bodyO.replaceFVars os osQ
          let F2x := mkAppN f2Const xs
          let Osx := mkAppN osConst xs
          let hknot ← mkAppM ``Tools.VedU2HierMulti.loop_knot
            #[F2x, Osx, eConst, mkAppN (Lean.mkConst hcFName) xs,
              mkAppN (Lean.mkConst hcOName) xs, mkAppN (Lean.mkConst hOsName) xs]
          let knotName := base ++ Name.mkSimple (openSuf ++ "_knot")
          let knotTy ← mkForallFVars xs (← withLocalDeclD `t natTy fun t => do
            let rhs ← valAt (← mkAppM ``Sparkle.Core.Signal.Signal.loop #[← loopFOfOf bodyStar]) t
            mkForallFVars #[t] (← mkEq (← valAt Qx t) rhs))
          try
            withOptions (fun o => o.setBool `Elab.async false) do
              addDecl (.thmDecl { name := knotName, levelParams := [], type := knotTy, value := ← mkLambdaFVars xs hknot })
          catch e => refuse decl "open" m!"the kernel refused the loop knot: {e.toMessageData}"
          Tools.VedU2HierDbg.openTick "knot end"
          -- the equation: the declaration is the open parent at the oracle the real children give along its own loop
          let lhs := mkAppN stmt xs
          let openApp := wrap (mkAppN (Lean.mkConst openName) (xs ++ osQ))
          let eqTy ← mkForallFVars xs (← mkEq lhs openApp)
          let A ← withLocalDeclD `L liveTy fun L => do
            mkLambdaFVars #[L] (wrap (← mkAppOptM ``outFOf ((pre.map some) ++ #[some inits, some bodyStar, some L])))
          let hQP ← mkAppM ``Tools.VedU2HierMulti.signal_ext #[hknot]
          let pfBody ← mkAppM ``congrArg #[A, hQP]
          let pf ← match fuseEq? with
            | none => mkLambdaFVars xs pfBody
            | some fe => mkLambdaFVars xs (← mkAppM ``Eq.trans #[mkAppN (Lean.mkConst fe) xs, pfBody])
          let eqName := base ++ Name.mkSimple (openSuf ++ "_eq")
          try
            withOptions (fun o => o.setBool `Elab.async false) do
              addDecl (.thmDecl { name := eqName, levelParams := [], type := eqTy, value := pf })
          catch e => refuse decl "open" m!"the kernel refused the open-parent equation: {e.toMessageData}"
          Tools.VedU2HierDbg.openTick "eq end"
          -- the closed argument definitions `fun ins => argument[state := the declaration's loop][inputs := input streams]`
          let insTy := Lean.mkForall `n .default (Lean.mkConst ``Nat)
            (Lean.mkForall `s .default (Lean.mkConst ``String) (Lean.mkConst ``Nat))
          let mut infos : Array CallInfo := #[]
          for ((key, _), j) in (orcKey.zip orcSite).zipIdx do
            let defs ← withLocalDeclD `ins insTy fun insFv => do
              let sigsF : Array Lean.Expr := (tbl.ins.zip tbl.binders).toArray.map fun (pt, bn) =>
                mkAppN (Lean.mkConst ``PTy.sig) #[toExpr pt, insFv, toExpr ("_gen_" ++ bn)]
              let mut ds : List Name := []
              for (a, kk) in key.2.toList.zipIdx do
                let v := ((realCalls a).replaceFVar live Qx).replaceFVars xs sigsF
                let lam ← mkLambdaFVars #[insFv] v
                let nmA := base ++ Name.mkSimple (openSuf ++ s!"_arg{j}_{kk}")
                addDefnRegular nmA (← inferType lam) lam
                ds := ds ++ [nmA]
              return ds
            infos := infos.push { kid := key.1, args := defs.map fun _ => "?", derived := true, argDefs := defs, stateArg := true }
          Tools.VedU2HierDbg.openTick "arg definitions end"
          -- the ports of the open parent: the fields of its struct result
          let ports : List String ← do
            let st ← whnf rhoTy
            match st.getAppFn.constName? with
            | some sn =>
              if sn == ``Sparkle.Core.Signal.Signal then pure []
              else pure ((getStructureFields (← getEnv) sn).toList.map (·.toString))
            | none => pure []
          let _ := ports
          return { openName, eqName, calls := infos, port := portName, ports, knot := some knotName }

end Tools.VedU2HierMultiGen
