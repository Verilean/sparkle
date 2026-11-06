import Tools.ShippingFGCircuitS2bShare
set_option autoImplicit false
-- FG circuit pilot S1w: the metaprogram that builds the `DW` derivation term (docs/FG-CIRCUIT-PILOT.md §26).
-- Nothing here is trusted: the term it emits is checked by the kernel (`addDecl`); a wrong term is rejected, a wrong generator can only fail.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # the generator

`derive` walks an `Expr` exactly as the SNAPSHOT recognizer of Check17 does and returns a proof term of `DW env ρ e r` built from the constructors of `DW` and the table
versions of Tools/ShippingFGCircuitS1wTbl. The environment-reading side conditions are `Eq.refl` proofs of the environment-free evaluators (`unfoldL`, `recStepL`, …) over the lookup
`lookOf ΔW ΓW`; the tables `ΔW`/`ΓW` are built from the names the evaluators actually queried (recorded while the term is built). -/
namespace Tools.ShippingFGCircuitS2bGen
open Lean Meta Elab Command Term
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD
open Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1sCD Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS2bShare

/-- one entry of the valuation: the quoted syntactic type, the Lean type, the value (as `Expr`s of the term) -/
structure CEntry where
  tau : Lean.Expr
  ty : Lean.Expr
  val : Lean.Expr

structure St where
  q : Std.HashMap Lean.Expr Lean.Expr := {}
  memo : Std.HashMap (Bool × Lean.Expr × Lean.Expr) Lean.Expr := {}
  defs : Array (Name × List Name × Lean.Expr) := #[]
  ctors : Array (Name × Name × Nat × Nat) := #[]
  hasRec : Bool := false
  seen : Std.HashSet Name := {}
  misses : Array Name := #[]
  nodes : Nat := 0
  steps : Array (String × Nat) := #[]
  probe : Bool := false
  stops : Array String := #[]
  cap : Nat := 0
  heavy : Array (Nat × Nat × Lean.Expr × Lean.Expr) := #[]
  log : Array String := #[]

abbrev G := StateRefT St MetaM

/-- (DAG size, tree size) of an `Expr` (instrumentation only) -/
partial def dagTree (e : Lean.Expr) : Nat × Nat := Id.run do
  let rec go (e : Lean.Expr) (m : Std.HashMap Lean.Expr Nat) : Nat × Std.HashMap Lean.Expr Nat :=
    match m[e]? with
    | some n => (n, m)
    | none =>
      let (n, m) := match e with
        | .app f a => let (x, m) := go f m; let (y, m) := go a m; (x + y + 1, m)
        | .lam _ t b _ => let (x, m) := go t m; let (y, m) := go b m; (x + y + 1, m)
        | .forallE _ t b _ => let (x, m) := go t m; let (y, m) := go b m; (x + y + 1, m)
        | .letE _ t v b _ => let (x, m) := go t m; let (y, m) := go v m; let (z, m) := go b m; (x + y + z + 1, m)
        | .proj _ _ y => let (x, m) := go y m; (x + 1, m)
        | .mdata _ y => let (x, m) := go y m; (x + 1, m)
        | _ => (1, m)
      (n, m.insert e n)
  let (t, m) := go e {}
  (m.size, t)

def logSz (k : String) (e : Lean.Expr) : G Unit := do
  let (d, t) := dagTree e
  let n := (← get).nodes
  modify fun s => { s with log := s.log.push s!"{n} {k} dag={d} tree={t}" }

def bump (k : String) : G Unit := modify fun s =>
  match s.steps.findIdx? (·.1 == k) with
  | some i => { s with steps := s.steps.modify i fun (a, n) => (a, n + 1) }
  | none => { s with steps := s.steps.push (k, 1) }

/-! ## quoting an `Expr` as a term of type `Expr` (shared: equal sub-expressions are quoted once) -/

def qL : Level → Lean.Expr
  | .zero => mkConst ``Level.zero
  | .succ l => mkApp (mkConst ``Level.succ) (qL l)
  | .max a b => mkApp2 (mkConst ``Level.max) (qL a) (qL b)
  | .imax a b => mkApp2 (mkConst ``Level.imax) (qL a) (qL b)
  | .param n => mkApp (mkConst ``Level.param) (toExpr n)
  | .mvar _ => mkConst ``Level.zero

def qLs (ls : List Level) : Lean.Expr :=
  ls.foldr (fun l acc => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Level) (qL l) acc) (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Level))

def biE (bi : BinderInfo) : Lean.Expr :=
  match bi with
  | .default => mkConst ``BinderInfo.default
  | .implicit => mkConst ``BinderInfo.implicit
  | .strictImplicit => mkConst ``BinderInfo.strictImplicit
  | .instImplicit => mkConst ``BinderInfo.instImplicit

partial def qE (e : Lean.Expr) : G Lean.Expr := do
  if let some r := (← get).q[e]? then return r
  let r ← match e with
    | .bvar i => pure (mkApp (mkConst ``Lean.Expr.bvar) (toExpr i))
    | .const n ls => pure (mkApp2 (mkConst ``Lean.Expr.const) (toExpr n) (qLs ls))
    | .app f a => pure (mkApp2 (mkConst ``Lean.Expr.app) (← qE f) (← qE a))
    | .lam n t b bi => pure (mkApp4 (mkConst ``Lean.Expr.lam) (toExpr n) (← qE t) (← qE b) (biE bi))
    | .forallE n t b bi => pure (mkApp4 (mkConst ``Lean.Expr.forallE) (toExpr n) (← qE t) (← qE b) (biE bi))
    | .letE n t v b nd => pure (mkApp5 (mkConst ``Lean.Expr.letE) (toExpr n) (← qE t) (← qE v) (← qE b) (toExpr nd))
    | .lit (.natVal k) => pure (mkApp (mkConst ``Lean.Expr.lit) (mkApp (mkConst ``Lean.Literal.natVal) (toExpr k)))
    | .lit (.strVal s) => pure (mkApp (mkConst ``Lean.Expr.lit) (mkApp (mkConst ``Lean.Literal.strVal) (toExpr s)))
    | .proj s i x => pure (mkApp3 (mkConst ``Lean.Expr.proj) (toExpr s) (toExpr i) (← qE x))
    | .sort l => pure (mkApp (mkConst ``Lean.Expr.sort) (qL l))
    | .mdata .. => throwError "quote: mdata"
    | .fvar .. => throwError "quote: fvar"
    | .mvar .. => throwError "quote: mvar"
  modify fun s => { s with q := s.q.insert e r }
  pure r

/-! ## the lookup, recording what the evaluators ask -/

def classify (env : Environment) (c : Name) : Option Lk :=
  match env.find? c with
  | some (.defnInfo d) => some (.defn ⟨d.levelParams, d.value⟩)
  | some (.ctorInfo cv) => some (.ctor ⟨cv.induct, cv.numParams, cv.numFields⟩)
  | some (.recInfo _) => if c == ``List.rec then some .recl else none
  | _ => none

/-- the recording lookup (effects hidden behind `unsafeBaseIO`; the recorded set only widens, so duplicated or reordered calls are harmless) -/
unsafe def recLook (env : Environment) (ref : IO.Ref (Array (Name × Option Lk))) : Look := fun c =>
  unsafeBaseIO (do
    let r := classify env c
    ref.modify fun a => if a.any (·.1 == c) then a else a.push (c, r)
    pure r)

def record (qs : Array (Name × Option Lk)) : G Unit := do
  for (c, k) in qs do
    unless (← get).seen.contains c do
      modify fun s => { s with seen := s.seen.insert c }
      match k with
      | some (.defn r) => modify fun s => { s with defs := s.defs.push (c, r.lps, r.value) }
      | some (.ctor r) => modify fun s => { s with ctors := s.ctors.push (c, r.induct, r.numParams, r.numFields) }
      | some .recl => modify fun s => { s with hasRec := true }
      | none => modify fun s => { s with misses := s.misses.push c }

/-- an evaluation `f lk`; the queried names go to the tables. `some x`: the function returns `some x`; `none`: it returns `none`. A name outside the tables is an error. -/
unsafe def ev (f : Look → Option (Option Lean.Expr)) (what : String) : G (Option Lean.Expr) := do
  let env ← getEnv
  let ref ← IO.mkRef (#[] : Array (Name × Option Lk))
  let r ← IO.lazyPure fun _ => f (recLook env ref)
  let r ← match r with
    | some (some x) => pure (some (some x))
    | some none => pure (some none)
    | none => pure none
  let qs ← ref.get
  record qs
  match r with
  | some (some x) => pure (some x)
  | some none => pure none
  | none => throwError "evaluator {what}: a name outside the tables was queried: {(qs.filter (·.2.isNone)).map (·.1)}"

/-! ## building rule applications by binder name -/

partial def piNames : Lean.Expr → List Name
  | .forallE n _ b _ => n :: piNames b
  | _ => []

def nm (s : String) : Name := Name.mkSimple s

/-- the application of the constant `c` whose arguments are given by binder name (all of them, implicit ones included) -/
def mkN (c : Name) (args : List (String × Lean.Expr)) : MetaM Lean.Expr := do
  let ci ← getConstInfo c
  let names := piNames ci.type
  let mut out : Array Lean.Expr := #[]
  for n in names do
    match args.find? (fun (k, _) => nm k == n) with
    | some (_, v) => out := out.push v
    | none => throwError "mkN {c}: no argument for the binder {n}"
  for (k, _) in args do
    unless names.contains (nm k) do throwError "mkN {c}: the binder {k} does not exist"
  pure (mkAppN (mkConst c) out)

/-- `DW env ρ e r` of a proof -/
def dwOf (pf : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let t ← whnfR (← inferType pf)
  unless t.getAppFn.isConstOf ``DS do throwError "not a DW proof: {t}"
  let a := t.getAppArgs
  unless a.size == 4 do throwError "DW arity"
  pure (a[2]!, a[3]!)

def valOf (pf : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let (_, r) ← dwOf pf
  unless r.getAppFn.isConstOf ``Res.val do throwError "expected a value judgement, got {r}"
  pure (r.getAppArgs[0]!, r.getAppArgs[1]!)

def tyOf (pf : Lean.Expr) : MetaM Lean.Expr := do
  let (_, r) ← dwOf pf
  unless r.getAppFn.isConstOf ``Res.ty do throwError "expected a type judgement, got {r}"
  pure r.getAppArgs[0]!

def lvl1 : Level := .succ .zero
def reflT (α x : Lean.Expr) : Lean.Expr := mkApp2 (mkConst ``Eq.refl [lvl1]) α x
def exprT : Lean.Expr := mkConst ``Lean.Expr
def boolT : Lean.Expr := mkConst ``Bool
def natT : Lean.Expr := mkConst ``Nat
def nameT : Lean.Expr := mkConst ``Lean.Name
def optT (α : Lean.Expr) : Lean.Expr := mkApp (mkConst ``Option [Level.zero]) α
def someE (α x : Lean.Expr) : Lean.Expr := mkApp2 (mkConst ``Option.some [Level.zero]) α x
def lkT : Lean.Expr := mkConst ``Lk

def entryE (c : CEntry) : Lean.Expr :=
  mkApp2 (mkConst ``Entry.mk) c.tau (mkApp2 (mkConst ``Dyn.mk) c.ty c.val)

def entryT : Lean.Expr := mkConst ``Entry

def ctxE : List CEntry → Lean.Expr
  | [] => mkApp (mkConst ``List.nil [lvl1]) entryT
  | c :: cs => mkApp3 (mkConst ``List.cons [lvl1]) entryT (entryE c) (ctxE cs)


/-- what the derivation needs from the surroundings -/
structure Kx where
  env : Lean.Expr      -- the free variable `env`
  hlk : Lean.Expr      -- `EnvLk env (lookOf ΔW ΓW)`
  lk : Lean.Expr       -- `lookOf ΔW ΓW`

def ctorRowE (induct : Name) (np nf : Nat) : Lean.Expr := mkApp3 (mkConst ``CtorRow.mk) (toExpr induct) (toExpr np) (toExpr nf)

def nth {α : Type} (l : List α) (i : Nat) : Option α := l[i]?

/-- `Eq.refl` of the table fact `lk c = some (.ctor row)` -/
def ctorFact (K : Kx) (c : Name) : G Lean.Expr := do
  let env ← getEnv
  match classify env c with
  | some (.ctor r) =>
    record #[(c, some (.ctor r))]
    pure (reflT (optT lkT) (someE lkT (mkApp (mkConst ``Lk.ctor) (ctorRowE r.induct r.numParams r.numFields))))
  | _ => throwError "{c} is not a constructor of the environment"

def ctorRowOf (c : Name) : G CtorRow := do
  match classify (← getEnv) c with
  | some (.ctor r) => pure r
  | _ => throwError "{c} is not a constructor"

def recFact : Lean.Expr := reflT (optT lkT) (someE lkT (mkConst ``Lk.recl))

/-- `Prod.fst`/`Prod.snd` as the function argument of `Signal.map` -/
def projFnG (f : Lean.Expr) : Option (Bool × Lean.Expr × Lean.Expr) :=
  match appFn f, appArgs f with
  | .const c [.zero, .zero], [a, b] => if c == ``Prod.fst then some (true, a, b) else if c == ``Prod.snd then some (false, a, b) else none
  | _, _ => none

mutual
unsafe def derive (K : Kx) (ty : Bool) (cx : List CEntry) (e : Lean.Expr) : G Lean.Expr := do
  let ρE := ctxE cx
  let key := (ty, ρE, e)
  if let some p := (← get).memo[key]? then return p
  modify fun s => { s with nodes := s.nodes + 1 }
  if (← get).cap > 0 && (← get).nodes > (← get).cap then throwError "CAPHIT"
  let p ← if (← get).probe then
      try deriveCore K ty cx ρE e
      catch ex =>
        let msg ← ex.toMessageData.toString
        if msg.startsWith "CAPHIT" then throw ex
        modify fun s => { s with stops := s.stops.push msg }
        -- probe only: a metavariable stands for the stuck sub-derivation (never added to the environment)
        let tv ← mkFreshExprMVar (some (mkSort (.succ .zero)))
        let r ← if ty then pure (mkApp (mkConst ``Res.ty) tv)
          else do
            let vv ← mkFreshExprMVar (some tv)
            pure (mkApp2 (mkConst ``Res.val) tv vv)
        mkFreshExprMVar (some (mkAppN (mkConst ``DS) #[K.env, ρE, ← qE e, r]))
    else deriveCore K ty cx ρE e
  modify fun s => { s with memo := s.memo.insert key p }
  pure p

unsafe def deriveCore (K : Kx) (ty : Bool) (cx : List CEntry) (ρE : Lean.Expr) (e : Lean.Expr) : G Lean.Expr := do
  match e with
  | .bvar i =>
    if ty then throwError "bvar {i} judged as a type"
    let some c := nth cx i | throwError "bvar {i} is not bound (context has {cx.length})"
    bump "bvar"
    mkN ``DS.bvar [("env", K.env), ("ρ", ρE), ("i", toExpr i), ("τ", c.tau), ("T", c.ty), ("a", c.val),
      ("h", mkApp2 (mkConst ``Eq.refl [.succ (.succ .zero)]) (mkApp (mkConst ``Option [lvl1]) entryT) (mkApp2 (mkConst ``Option.some [lvl1]) entryT (entryE c)))]
  | .lam n A b bi =>
    if ty then throwError "lam judged as a type"
    let eQ ← qE e
    let hA ← derive K true cx A
    let TA ← tyOf hA
    bump "lam"
    withLocalDeclD `a TA fun av => do
      let c : CEntry := { tau := ← qE A, ty := TA, val := av }
      let hb ← derive K false (c :: cx) b
      let (αb, vb) ← valOf hb
      let TB ← mkLambdaFVars #[av] αb
      let f ← mkLambdaFVars #[av] vb
      let hbL ← mkLambdaFVars #[av] hb
      mkN ``DS.lam [("env", K.env), ("ρ", ρE), ("e", eQ), ("A", ← qE A), ("body", ← qE b), ("n", toExpr n), ("bi", biE bi),
        ("TA", TA), ("TB", TB), ("f", f), ("he", reflT exprT eQ), ("hA", hA), ("hb", hbL)]
  | .letE n A v b nd =>
    if ty then throwError "let judged as a type"
    let eQ ← qE e
    if coreHead A then
      let hA ← derive K true cx A
      let TA ← tyOf hA
      let hv ← derive K false cx v
      let (_, a) ← valOf hv
      let c : CEntry := { tau := ← qE A, ty := TA, val := a }
      let hb ← derive K false (c :: cx) b
      let (T, r) ← valOf hb
      logSz "letE" e; bump "letE"
      mkN ``DS.letE [("env", K.env), ("ρ", ρE), ("e", eQ), ("A", ← qE A), ("v", ← qE v), ("body", ← qE b), ("n", toExpr n), ("nd", toExpr nd),
        ("TA", TA), ("T", T), ("a", a), ("r", r), ("he", reflT exprT eQ), ("hA", hA), ("hc", reflT boolT (mkConst ``true)), ("hv", hv), ("hb", hb)]
    else
      let h ← derive K false cx (instE b v 0)
      let (α, r) ← valOf h
      logSz "zeta" e; bump "zeta"
      mkN ``DS.zeta [("env", K.env), ("ρ", ρE), ("e", eQ), ("A", ← qE A), ("v", ← qE v), ("body", ← qE b), ("n", toExpr n), ("nd", toExpr nd),
        ("α", α), ("r", r), ("he", reflT exprT eQ), ("hA", reflT boolT (mkConst ``false)), ("h", h)]
  | .proj S i x => deriveProj K ty cx ρE e S i x
  | .mdata .. => throwError "mdata"
  | _ =>
    match appFn e with
    | .lam .. | .letE .. | .proj .. =>
      let some e' ← ev (fun lk => headRedexRL lk e) "headRedexRL" | throwError "beta: no redex"
      let h ← derive K ty cx e'
      let (_, r) ← dwOf h
      logSz "beta" e; bump "beta"
      mkN ``ds_beta_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρE), ("e", ← qE e), ("e'", ← qE e'), ("r", r),
        ("hb", reflT (optT (optT exprT)) (someE (optT exprT) (someE exprT (← qE e')))), ("h", h)]
    | .const c ls => deriveConst K ty cx ρE e c ls
    | h => throwError "head {h.ctorName} application"

unsafe def deriveProj (K : Kx) (ty : Bool) (cx : List CEntry) (ρE : Lean.Expr) (e : Lean.Expr) (S : Name) (i : Nat) (x : Lean.Expr) : G Lean.Expr := do
  let eQ ← qE e
  let xQ ← qE x
  let recCase : G (Option Lean.Expr) := do
    match appFn x with
    | .const ctor ls =>
      if ctor == ``List.rec then
        match ← ev (fun lk => recStepL lk x) "recStepL(proj)" with
        | some x' =>
          let h ← derive K ty cx (.proj S i x')
          let (_, r) ← dwOf h
          logSz "projRec" e; bump "projRec"
          return some (← mkN ``ds_projRec_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρE), ("e", eQ), ("x", xQ), ("x'", ← qE x'), ("S", toExpr S),
            ("i", toExpr i), ("ls", qLs ls), ("r", r), ("he", reflT exprT eQ), ("hf", reflT exprT (← qE (appFn x))), ("hrec", recFact),
            ("hr", reflT (optT (optT exprT)) (someE (optT exprT) (someE exprT (← qE x')))), ("h", h)])
        | none => pure none
      else pure none
    | _ => pure none
  if let some p ← recCase then return p
  let ctorCase : G (Option Lean.Expr) := do
    match appFn x with
    | .const ctor ls =>
      match classify (← getEnv) ctor with
      | some (.ctor r) =>
        if r.induct == S && (appArgs x).length == r.numParams + r.numFields then
          match (appArgs x)[r.numParams + i]? with
          | some fld =>
            let h ← derive K ty cx fld
            let (_, res) ← dwOf h
            let hr ← ctorFact K ctor
            logSz "projCtor" e; bump "projCtor"
            return some (← mkN ``ds_projCtor_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρE), ("e", eQ), ("x", xQ), ("fld", ← qE fld), ("S", toExpr S),
              ("ctor", toExpr ctor), ("ls", qLs ls), ("cw", ctorRowE r.induct r.numParams r.numFields), ("i", toExpr i), ("r", res),
              ("he", reflT exprT eQ), ("hh", reflT exprT (← qE (appFn x))), ("hr", hr), ("hS", reflT nameT (toExpr S)),
              ("hn", reflT natT (toExpr (appArgs x).length)), ("hf", reflT (optT exprT) (someE exprT (← qE fld))), ("h", h)])
          | none => pure none
        else pure none
      | _ => pure none
    | _ => pure none
  if let some p ← ctorCase then return p
  match ← ev (fun lk => whStepRL lk x) "whStepRL(proj)" with
  | some x' =>
    if (← get).cap > 0 then
      let (d, t) := dagTree x
      do
        modify fun st => { st with heavy := ((st.heavy.push (t, d, x, x')).qsort (fun a b => a.1 > b.1)).extract 0 3 }
    let h ← derive K ty cx (.proj S i x')
    let (_, r) ← dwOf h
    logSz "projStep" e; bump "projStep"
    mkN ``ds_projStep_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρE), ("e", eQ), ("x", xQ), ("x'", ← qE x'), ("S", toExpr S), ("i", toExpr i), ("r", r),
      ("he", reflT exprT eQ), ("hx", reflT (optT (optT exprT)) (someE (optT exprT) (someE exprT (← qE x')))), ("h", h)]
  | none => throwError "proj {S}#{i}: stuck on {repr (appFn x).ctorName} {(appFn x)}"

unsafe def deriveConst (K : Kx) (ty : Bool) (cx : List CEntry) (ρE : Lean.Expr) (e : Lean.Expr) (c : Name) (ls : List Level) : G Lean.Expr := do
  let eQ ← qE e
  let args := appArgs e
  let a (i : Nat) : G Lean.Expr := do
    let some x := args[i]? | throwError "{c}: argument {i} missing"
    pure x
  let q (i : Nat) : G Lean.Expr := do qE (← a i)
  let heE := reflT exprT eQ
  let v (i : Nat) : G Lean.Expr := do derive K false cx (← a i)
  let t (i : Nat) : G Lean.Expr := do derive K true cx (← a i)
  let env0 : List (String × Lean.Expr) := [("env", K.env), ("ρ", ρE), ("e", eQ), ("he", heE)]
  let generic : G Lean.Expr := do
    if c == ``List.rec then
      match ← ev (fun lk => recStepL lk e) "recStepL" with
      | some e' =>
        let h ← derive K ty cx e'
        let (_, r) ← dwOf h
        logSz "recIota" e; bump "recIota"
        mkN ``ds_recIota_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρE), ("e", eQ), ("e'", ← qE e'), ("ls", qLs ls), ("r", r),
          ("hf", reflT exprT (← qE (appFn e))), ("hrec", recFact), ("hr", reflT (optT (optT exprT)) (someE (optT exprT) (someE exprT (← qE e')))), ("h", h)]
      | none => throwError "List.rec: no step"
    else
      match ← ev (fun lk => unfoldL lk e) "unfoldL" with
      | some e' =>
        let h ← derive K ty cx e'
        let (_, r) ← dwOf h
        logSz s!"unf {c}" e; bump s!"unf"
        mkN ``ds_unf_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρE), ("e", eQ), ("e'", ← qE e'), ("r", r),
          ("hs", reflT boolT (mkConst ``false)), ("hu", reflT (optT (optT exprT)) (someE (optT exprT) (someE exprT (← qE e')))), ("h", h)]
      | none => throwError "{c}: stuck ({if ty then "type" else "value"}): not unfoldable (head {c}, levels {ls}, {args.length} args)"
  if ty then
    if c == ``Nat then bump "nat"; mkN ``DS.nat [("env", K.env), ("ρ", ρE), ("e", eQ), ("he", heE)]
    else if c == ``Bool then bump "bool"; mkN ``DS.bool [("env", K.env), ("ρ", ρE), ("e", eQ), ("he", heE)]
    else if c == ``Sparkle.Core.Domain.DomainConfig then bump "domainConfig"; mkN ``DS.domainConfig [("env", K.env), ("ρ", ρE), ("e", eQ), ("he", heE)]
    else if c == ``BitVec then
      let hw ← v 0
      let (_, n) ← valOf hw
      bump "bitvec"
      mkN ``DS.bitvec (env0 ++ [("w", ← q 0), ("n", n), ("hw", hw)])
    else if c == ``Signal then
      let hd ← v 0
      let ht ← t 1
      let (_, D) ← valOf hd
      bump "signal"
      mkN ``DS.signal (env0 ++ [("d", ← q 0), ("t", ← q 1), ("D", D), ("T", ← tyOf ht), ("hd", hd), ("ht", ht)])
    else if c == ``Prod && ls == [.zero, .zero] && args.length == 2 then
      let ha ← t 0
      let hb ← t 1
      bump "prodTy"
      mkN ``DS.prodTy (env0 ++ [("a", ← q 0), ("b", ← q 1), ("A", ← tyOf ha), ("B", ← tyOf hb), ("ha", ha), ("hb", hb)])
    else if c == ``PUnit && ls == [.succ .zero] && args.length == 0 then
      bump "punitTy"
      mkN ``DS.punitTy [("env", K.env), ("ρ", ρE), ("e", eQ), ("he", heE)]
    else generic
  else
    if c == ``OfNat.ofNat then
      match args[1]? with
      | some (Lean.Expr.lit (.natVal n)) => bump "natLit"; mkN ``DS.natLit (env0 ++ [("n", toExpr n)])
      | _ => throwError "OfNat.ofNat: not a literal"
    else if c == ``Sparkle.Core.Domain.defaultDomain then bump "domDefault"; mkN ``DS.domDefault [("env", K.env), ("ρ", ρE), ("e", eQ), ("he", heE)]
    else if c == ``instInhabitedBool then bump "boolInhabited"; mkN ``DS.boolInhabited [("env", K.env), ("ρ", ρE), ("e", eQ), ("he", heE)]
    else if c == ``BitVec.ofNat then
      let hw ← v 0
      let hk ← v 1
      let (_, W) ← valOf hw
      let (_, Kk) ← valOf hk
      bump "bvOfNat"
      mkN ``DS.bvOfNat (env0 ++ [("w", ← q 0), ("k", ← q 1), ("W", W), ("K", Kk), ("hw", hw), ("hk", hk)])
    else if c == ``BitVec.instInhabited then
      let hw ← v 0
      let (_, W) ← valOf hw
      bump "bvInhabited"
      mkN ``DS.bvInhabited (env0 ++ [("w", ← q 0), ("W", W), ("hw", hw)])
    else if c == ``Signal.pure then
      let hd ← v 0
      let ht ← t 1
      let hx ← v 2
      let (_, D) ← valOf hd
      let (_, av) ← valOf hx
      bump "sigPure"
      mkN ``DS.sigPure (env0 ++ [("d", ← q 0), ("t", ← q 1), ("x", ← q 2), ("D", D), ("T", ← tyOf ht), ("a", av), ("hd", hd), ("ht", ht), ("hx", hx)])
    else if c == ``Signal.register then
      let hd ← v 0
      let ht ← t 1
      let hi ← v 2
      let hs ← v 3
      let (_, D) ← valOf hd
      let (_, av) ← valOf hi
      let (_, sv) ← valOf hs
      bump "sigRegister"
      mkN ``DS.sigRegister (env0 ++ [("d", ← q 0), ("t", ← q 1), ("i", ← q 2), ("s", ← q 3), ("D", D), ("T", ← tyOf ht), ("a", av), ("sv", sv),
        ("hd", hd), ("ht", ht), ("hi", hi), ("hs", hs)])
    else if c == ``Signal.mux then
      let hd ← v 0
      let ht ← t 1
      let hc ← v 2
      let ha ← v 3
      let hb ← v 4
      let (_, D) ← valOf hd
      let (_, cv) ← valOf hc
      let (_, av) ← valOf ha
      let (_, bv) ← valOf hb
      bump "sigMux"
      mkN ``DS.sigMux (env0 ++ [("d", ← q 0), ("t", ← q 1), ("c", ← q 2), ("a", ← q 3), ("b", ← q 4), ("D", D), ("T", ← tyOf ht), ("cv", cv), ("av", av), ("bv", bv),
        ("hd", hd), ("ht", ht), ("hc", hc), ("ha", ha), ("hb", hb)])
    else if c == ``Signal.loop then
      let hd ← v 0
      let ht ← t 1
      let hi ← v 2
      let hf ← v 3
      let (_, D) ← valOf hd
      let (_, iv) ← valOf hi
      let (_, g) ← valOf hf
      bump "sigLoop"
      mkN ``DS.sigLoop (env0 ++ [("d", ← q 0), ("t", ← q 1), ("inst", ← q 2), ("f", ← q 3), ("D", D), ("T", ← tyOf ht), ("iv", iv), ("g", g),
        ("hd", hd), ("ht", ht), ("hi", hi), ("hf", hf)])
    else if c == ``HAdd.hAdd then
      let inst ← a 3
      let ia := appArgs inst
      let some dq := ia[0]? | throwError "HAdd: instance args"
      let some wq := ia[1]? | throwError "HAdd: instance args"
      let hd ← derive K false cx dq
      let hw ← derive K false cx wq
      let ha ← v 4
      let hb ← v 5
      let (_, D) ← valOf hd
      let (_, W) ← valOf hw
      let (_, av) ← valOf ha
      let (_, bv) ← valOf hb
      bump "sigAddBV"
      mkN ``DS.sigAddBV (env0 ++ [("d", ← qE dq), ("w", ← qE wq), ("a", ← q 4), ("b", ← q 5), ("D", D), ("W", W), ("av", av), ("bv", bv),
        ("hd", hd), ("hw", hw), ("ha", ha), ("hb", hb)])
    else if c == ``HAnd.hAnd || c == ``HOr.hOr then
      let inst ← a 3
      let some dq := (appArgs inst)[0]? | throwError "HAnd/HOr: instance args"
      let hd ← derive K false cx dq
      let ha ← v 4
      let hb ← v 5
      let (_, D) ← valOf hd
      let (_, av) ← valOf ha
      let (_, bv) ← valOf hb
      bump (if c == ``HAnd.hAnd then "sigAndBool" else "sigOrBool")
      mkN (if c == ``HAnd.hAnd then ``DS.sigAndBool else ``DS.sigOrBool) (env0 ++ [("d", ← qE dq), ("a", ← q 4), ("b", ← q 5), ("D", D), ("av", av), ("bv", bv),
        ("hd", hd), ("ha", ha), ("hb", hb)])
    else if c == ``Complement.complement then
      let inst ← a 1
      let some dq := (appArgs inst)[0]? | throwError "Complement: instance args"
      let hd ← derive K false cx dq
      let ha ← v 2
      let (_, D) ← valOf hd
      let (_, av) ← valOf ha
      bump "sigNotBool"
      mkN ``DS.sigNotBool (env0 ++ [("d", ← qE dq), ("a", ← q 2), ("D", D), ("av", av), ("hd", hd), ("ha", ha)])
    else if c == ``Sparkle.Core.Signal.Signal.beq then
      let bvT ← a 0
      let some wq := (appArgs bvT)[0]? | throwError "beq: BitVec arg"
      let hd ← v 1
      let hw ← derive K false cx wq
      let ha ← v 3
      let hb ← v 4
      let (_, D) ← valOf hd
      let (_, W) ← valOf hw
      let (_, av) ← valOf ha
      let (_, bv) ← valOf hb
      bump "sigBeqBV"
      mkN ``DS.sigBeqBV (env0 ++ [("d", ← q 1), ("w", ← qE wq), ("a", ← q 3), ("b", ← q 4), ("D", D), ("W", W), ("av", av), ("bv", bv),
        ("hd", hd), ("hw", hw), ("ha", ha), ("hb", hb)])
    else if (bvAbbrevRow c).isSome then throwError "bvAbbrev {c}: not supported by the generator"
    else if c == ``Signal.map && ls == [.zero] && args.length == 5 && (projFnG (args[3]!)).isSome then
      let some (isFst, pa, pb) := projFnG (args[3]!) | throwError "unreachable"
      match ← ev (fun lk => unfoldL lk e) "unfoldL(map)" with
      | some u =>
        let some ls' := (match appFn u with | .const k l => if k == ``Signal.mk then some l else none | _ => none) | throwError "Signal.map: the unfolding is not a Signal.mk (stuck rule missing)"
        let hd ← v 0
        let hp ← t 1
        let ht ← t 2
        let ha ← derive K true cx pa
        let hb ← derive K true cx pb
        let hs ← v 4
        let (_, D) ← valOf hd
        let (_, sv) ← valOf hs
        let hr ← ctorFact K ``Signal.mk
        let cw ← ctorRowOf ``Signal.mk
        let tyArg := if isFst then "ta" else "tb"
        bump (if isFst then "mapFst" else "mapSnd")
        mkN (if isFst then ``ds_mapFst_t else ``ds_mapSnd_t) [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρE), ("e", eQ), ("d", ← q 0), ("tp", ← q 1),
          (tyArg, ← q 2), ("a", ← qE pa), ("b", ← qE pb), ("s", ← q 4), ("u", ← qE u), ("D", D), ("A", ← tyOf (if isFst then ht else ha)), ("B", ← tyOf hb), ("sv", sv),
          ("ls'", qLs ls'), ("cw", ctorRowE cw.induct cw.numParams cw.numFields), ("he", heE), ("hd", hd), ("hp", hp), ("ht", ht), ("ha", ha), ("hb", hb), ("hs", hs),
          ("hu", reflT (optT (optT exprT)) (someE (optT exprT) (someE exprT (← qE u)))), ("hm", reflT exprT (← qE (appFn u))), ("hr", hr)]
      | none => throwError "Signal.map: not unfoldable"
    else if c == ``Sparkle.Core.Signal.bundle2 && ls == [.zero] && args.length == 5 then
      let hd ← v 0
      let hta ← t 1
      let htb ← t 2
      let ha ← v 3
      let hb ← v 4
      let (_, D) ← valOf hd
      let (_, av) ← valOf ha
      let (_, bv) ← valOf hb
      bump "bundle2"
      mkN ``DS.bundle2 (env0 ++ [("d", ← q 0), ("ta", ← q 1), ("tb", ← q 2), ("a", ← q 3), ("b", ← q 4), ("D", D), ("A", ← tyOf hta), ("B", ← tyOf htb),
        ("av", av), ("bv", bv), ("hd", hd), ("hta", hta), ("htb", htb), ("ha", ha), ("hb", hb)])
    else if c == ``Inhabited.mk && ls.length == 1 && args.length == 2 && lvlNat (ls.head!) == some 1 then
      let ht ← t 0
      let hx ← v 1
      let (_, xv) ← valOf hx
      let hr ← ctorFact K ``Inhabited.mk
      let cw ← ctorRowOf ``Inhabited.mk
      bump "inhMk"
      mkN ``ds_inhMk_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρE), ("e", eQ), ("t", ← q 0), ("x", ← q 1), ("u", qL ls.head!), ("T", ← tyOf ht), ("v", xv),
        ("cw", ctorRowE cw.induct cw.numParams cw.numFields), ("he", heE), ("hu", reflT (optT natT) (someE natT (toExpr (1 : Nat)))), ("hr", hr), ("ht", ht), ("hx", hx)]
    else if c == ``Inhabited.default && ls == [.succ .zero] && args.length == 2 then
      let ht ← t 0
      let hi ← v 1
      let (_, iv) ← valOf hi
      bump "inhDefault"
      mkN ``DS.inhDefault (env0 ++ [("t", ← q 0), ("inst", ← q 1), ("T", ← tyOf ht), ("iv", iv), ("ht", ht), ("hi", hi)])
    else if c == ``Prod.mk && ls == [.zero, .zero] && args.length == 4 then
      let ha ← t 0
      let hb ← t 1
      let hx ← v 2
      let hy ← v 3
      let (_, xv) ← valOf hx
      let (_, yv) ← valOf hy
      let hr ← ctorFact K ``Prod.mk
      let cw ← ctorRowOf ``Prod.mk
      bump "prodMk"
      mkN ``ds_prodMk_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρE), ("e", eQ), ("a", ← q 0), ("b", ← q 1), ("x", ← q 2), ("y", ← q 3),
        ("A", ← tyOf ha), ("B", ← tyOf hb), ("xv", xv), ("yv", yv), ("cw", ctorRowE cw.induct cw.numParams cw.numFields), ("he", heE), ("hr", hr),
        ("ha", ha), ("hb", hb), ("hx", hx), ("hy", hy)]
    else if c == ``PUnit.unit && ls == [.succ .zero] && args.length == 0 then
      let hr ← ctorFact K ``PUnit.unit
      let cw ← ctorRowOf ``PUnit.unit
      bump "unitVal"
      mkN ``ds_unitVal_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρE), ("e", eQ), ("cw", ctorRowE cw.induct cw.numParams cw.numFields), ("he", heE), ("hr", hr)]
    else generic
end

end Tools.ShippingFGCircuitS2bGen
