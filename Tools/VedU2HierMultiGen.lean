import Tools.VedU2HierStGen
import Tools.VedU2HierMultiLoop
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

/-- The `runCircuitH` application a declaration's value reduces to, with the projection (if any) wrapped around it. -/
partial def findRun (e : Lean.Expr) (fuel : Nat) : MetaM (Option (Lean.Expr × (Lean.Expr → Lean.Expr))) := do
  match fuel with
  | 0 => return none
  | f + 1 =>
    let e ← zetaReduce (← whnfCore e)
    if e.getAppFn.isConstOf ``Sparkle.Core.runCircuitH then return some (e, id)
    let env ← getEnv
    match e.getAppFn with
    | .const n _ =>
      if env.isProjectionFn n && e.getAppNumArgs > 0 then
        match ← findRun e.appArg! f with
        | some (r, w) => return some (r, fun x => mkApp e.appFn! (w x))
        | none => return none
      else match ← unfoldDefinition? e with
        | some e' => findRun e' f
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

/-- Option `ved.compose.multiOut`: a call whose value is a structure of signals (a child with several output ports).  Its oracle is one
free signal PER FIELD (the open parent keeps Signal parameters only); the call's occurrence in the body is the constructor
applied to those signals.  `none` for a call that is itself a `Signal`. -/
def structCallOf (ty : Lean.Expr) : MetaM (Option (Lean.Expr × Array Name)) := do
  let ty ← whnf ty
  match ty.getAppFn with
  | .const sn us =>
    if sn == ``Sparkle.Core.Signal.Signal then return none
    let env ← getEnv
    unless isStructure env sn do return none
    let fs := getStructureFields env sn
    let ctor := mkAppN (Lean.mkConst (getStructureCtor env sn).name us) ty.getAppArgs
    return some (ctor, fs.map (sn ++ ·))
  | _ => return none

/-- Projections of constructor applications reduced (`P2.s (P2.mk a b)` to `a`), under binders: what the oracle replacement of a
structure-valued call leaves in the open parent's body (the synthesizer has no rule for `P2.mk`/`P2.s`). -/
def reduceCtorProjs (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun x => do
    if let .const n _ := x.getAppFn then
      if (← getEnv).isProjectionFn n && x.getAppNumArgs > 0 then
        if (← whnfCore x.appArg!).getAppFn.isConst then
          if let some x' ← unfoldDefinition? x then
            let r ← whnfCore x'
            if !r.isProj then return .done r
    return .continue)

/-- The analysis and the generated constants.  `pw` (option `ved.compose.step`): the proof of `hOs` uses the children's
pointwise lemmas (`mkPointwise`) instead of unfolding them; the produced definitions are the same. -/
def genOpenMulti (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (tbl : DeclTable) (kids : Array Kid)
    (base : Name) (openSuf : String) (pw : Bool := false) (chain : Bool := false) (multiOutOn : Bool := false) : TermElabM OpenInfo := do
  let openName := base ++ Name.mkSimple openSuf
  Tools.VedU2HierDbg.openTick "genOpenMulti begin"
  let ty ← inferType stmt
  forallTelescope ty fun xs _ => do
    let some (.defnInfo ci) := (← getEnv).find? decl
      | refuse decl "open" m!"{decl} is not a definition"
    let dflt := Lean.mkConst ``Sparkle.Core.Domain.defaultDomain
    let args : Array Lean.Expr := (Array.replicate nDom dflt) ++ xs
    let body0 := (mkAppN ci.value args).headBeta
    let some (run, wrap) ← findRun body0 24
      | refuse decl "open" m!"the declaration's value does not reduce to a `circuit do` (runCircuitH)"
    Tools.VedU2HierDbg.openTickE "findRun end" body0
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
        -- the oracle signals: one per call, or one per field of a structure-valued call (option `ved.compose.multiOut`)
        let mut structs : Array (Option (Lean.Expr × Array Name)) := #[]
        let mut leafTerms : Array (Array Lean.Expr) := #[]
        let mut leafBase : Array Nat := #[]
        let mut leafTys : Array Lean.Expr := #[]
        for ((key, k), j) in (orcKey.zip orcSite).zipIdx do
          let callE := mkAppN siteFn[k]! (key.2.map realCalls)
          let st ← if multiOutOn then structCallOf orcTys[j]! else pure none
          structs := structs.push st
          leafBase := leafBase.push leafTys.size
          let ls : Array Lean.Expr ← match st with
            | some (_, fns) => fns.mapM fun f => mkAppM f #[callE]
            | none => pure #[callE]
          leafTerms := leafTerms.push ls
          for l in ls do leafTys := leafTys.push (← inferType l)
        let nL := leafTys.size
        let osTy ← tupleTy leafTys
        withFVars (leafTys.mapIdx fun i _ => Name.mkSimple s!"ved_o{i}") leafTys fun os => do
          let callVal (j : Nat) : Lean.Expr :=
            match structs[j]! with
            | some (ctor, fns) => mkAppN ctor (os.extract leafBase[j]! (leafBase[j]! + fns.size))
            | none => os[leafBase[j]!]!
          let bodyO0 ← replaceCalls (nested := chain) kids body fun idx _ _ _ _ => pure (callVal (kToJ[idx]!).get!)
          let bodyO ← if multiOutOn then reduceCtorProjs bodyO0 else pure bodyO0
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
          let f2Name := base ++ Name.mkSimple (openSuf ++ (if chain || multiOutOn then "_FL" else "_F2"))  -- chain: `_F{j}` of the third call would clash with `_F2`
          let wO := wtup.replace fun e =>
            if e.isApp then
              match e.getAppFn with
              | .fvar v =>
                match gs.findIdx? (·.fvarId! == v) with
                | some k => (kToJ[k]!).bind fun j => some (callVal j)
                | none => none
              | _ => none
            else none
          let f2Const := Lean.mkConst f2Name
          withLocalDeclD `o osTy fun ot => withLocalDeclD `x liveTy fun x => do
            let projs ← (List.range nL).toArray.mapM (tupleGet ot ·)
            let w := (wO.replaceFVars os projs).replaceFVar live x
            let f2Val ← mkLambdaFVars (xs ++ #[ot, x]) (← mkAppOptM ``Sparkle.Core.packRegister #[some dom, some αs, some inits, some w])
            addDefnRegular f2Name (← inferType f2Val) f2Val
            Tools.VedU2HierDbg.openTickE "F2 definition added" f2Val
          -- Os xs live = the oracle values the real children give
          let osComps : Array Lean.Expr := leafTerms.flatten
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
              for j in (List.range nL).reverse do
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
          let reachL := ", ".intercalate reach.eraseDups
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
          let hn := (List.range nL).map fun j => s!"e{j}"
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
          let hOsOld := s!"simp only [{osU}, {reachL}, {plumbingL}, {sigvalL}, hx, and_self, and_true]"
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
          let pf ← mkLambdaFVars xs pfBody
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
            match structs[j]! with
            | some (_, fns) =>
              for (f, l) in fns.toList.zipIdx do
                infos := infos.push { kid := key.1, args := defs.map fun _ => "?", derived := true, argDefs := defs, stateArg := true,
                                      leaf := l, proj := some (f.getString!) }
            | none =>
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
