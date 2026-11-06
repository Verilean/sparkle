import Tools.ShippingFGCircuitS2bGen
import Tools.ShippingFGCircuitS2iTbl
set_option autoImplicit false
-- FG circuit pilot S2i: the closure-environment generator for the bridge family `DT`, docs/FG-CIRCUIT-PILOT.md §35.
-- UNTRUSTED metaprogram: the term it emits is checked by the kernel (`addDecl`); a wrong generator can only fail.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # the generator

* `evalSh` runs the closure machine `Sh` on the META level (environments, closures and spines are kernel terms of type `Cx`/`Ent`, shared by pointer; there is no substitution and no copy of an expression)
  and returns the proof term of `Sh env ρ e sp hn`. Every call is MEMOISED on `(ρ, e, sp)`: a closure that is referenced twice is evaluated once and its proof object is shared (call-by-need on the proof DAG).
* `deriveT` builds `DT env ρ e r`: the direct rules (as the S2b `derive`), `bvarClo`, and `viaSh` (run `Sh`, require ONE common environment for the stuck/constructor spine, derive `c ls args` in it).
The memo of `derive` (key `(ty, ρ, e)`) is the S2b one. -/
namespace Tools.ShippingFGCircuitS2iGen
open Lean Meta Elab Command Term
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD
open Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1sCD Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS2bShare Tools.ShippingFGCircuitS2bGen
open Tools.ShippingFGCircuitS2iSh Tools.ShippingFGCircuitS2iDT

/-! ## kernel terms of the closure environments -/

def entT : Lean.Expr := mkConst ``Ent
def nilCx : Lean.Expr := mkApp (mkConst ``List.nil [lvl1]) entT
def consL (hd tl : Lean.Expr) : Lean.Expr := mkApp3 (mkConst ``List.cons [lvl1]) entT hd tl
def listEnt : List Lean.Expr → Lean.Expr
  | [] => nilCx
  | x :: xs => consL x (listEnt xs)
def entValE (c : CEntry) : Lean.Expr := mkApp (mkConst ``Ent.val) (entryE c)
def entCloE (eQ ρ : Lean.Expr) : Lean.Expr := mkApp2 (mkConst ``Ent.clo) eQ ρ
def listExprE : List Lean.Expr → Lean.Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) exprT
  | x :: xs => mkApp3 (mkConst ``List.cons [Level.zero]) exprT x (listExprE xs)
def hnCtorE (c : Name) (ls : List Level) (np : Nat) (sp : Lean.Expr) : Lean.Expr := mkApp4 (mkConst ``Hn.ctor) (toExpr c) (qLs ls) (toExpr np) sp
def hnStuckE (c : Name) (ls : List Level) (sp : Lean.Expr) : Lean.Expr := mkApp3 (mkConst ``Hn.stuck) (toExpr c) (qLs ls) sp

def parseCons (t : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if t.isAppOfArity ``List.cons 3 then some (t.getAppArgs[1]!, t.getAppArgs[2]!) else none
partial def listTerms (t : Lean.Expr) : Option (List Lean.Expr) :=
  if t.isAppOfArity ``List.nil 1 then some []
  else match parseCons t with
    | some (h, tl) => (listTerms tl).map (h :: ·)
    | none => none
partial def cxGet (ρ : Lean.Expr) (i : Nat) : Option Lean.Expr :=
  match parseCons ρ with
  | some (h, tl) => if i == 0 then some h else cxGet tl (i - 1)
  | none => none
def parseClo (t : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if t.isAppOfArity ``Ent.clo 2 then some (t.getAppArgs[0]!, t.getAppArgs[1]!) else none

/-! ## state -/

structure ShRes where
  pf : Lean.Expr
  hn : Lean.Expr
  c : Name
  ls : List Level
  sp : List Lean.Expr
  isCtor : Bool
  np : Nat

structure St2 where
  unq : Std.HashMap Lean.Expr Expr := {}
  shMemo : Std.HashMap (Lean.Expr × Lean.Expr × Lean.Expr) ShRes := {}
  shSteps : Nat := 0
  shKinds : Array (String × Nat) := #[]
  viaN : Nat := 0
  poly : Array (Name × Nat × Nat) := #[]

abbrev G2 := StateRefT St2 G

def bumpSh (k : String) : G2 Unit := modify fun s =>
  match s.shKinds.findIdx? (·.1 == k) with
  | some i => { s with shSteps := s.shSteps + 1, shKinds := s.shKinds.modify i fun (a, n) => (a, n + 1) }
  | none => { s with shSteps := s.shSteps + 1, shKinds := s.shKinds.push (k, 1) }

/-- quote an expression and remember the inverse -/
def qU (e : Expr) : G2 Lean.Expr := do
  let q ← (qE e : G Lean.Expr)
  modify fun s => { s with unq := s.unq.insert q e }
  pure q

def unq (q : Lean.Expr) : G2 Expr := do
  match (← get).unq[q]? with
  | some e => pure e
  | none => throwError "internal: a closure expression that was not created by the generator"

/-- `instLE` with the DAG preserved (equal structure, equal results) -/
def instLEShared (ps : List Name) (ls : List Level) (e : Expr) : Expr := Id.run do
  let rec go (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
    if let some r := (← get)[e]? then return r
    let r ← match e with
      | .sort u => pure (.sort (instL ps ls u))
      | .const c us => pure (.const c (us.map (instL ps ls)))
      | .app f a => do let f' ← go f; let a' ← go a; pure (.app f' a')
      | .lam x t b bi => do let t' ← go t; let b' ← go b; pure (.lam x t' b' bi)
      | .forallE x t b bi => do let t' ← go t; let b' ← go b; pure (.forallE x t' b' bi)
      | .letE x t v b nd => do let t' ← go t; let v' ← go v; let b' ← go b; pure (.letE x t' v' b' nd)
      | .mdata m e => do let e' ← go e; pure (.mdata m e')
      | .proj s i e => do let e' ← go e; pure (.proj s i e')
      | e => pure e
    modify (·.insert e r)
    pure r
  return (go e |>.run' {})

/-! ## the closure machine -/

def tblDefn (c : Name) : G (Option DefRow) := do
  match classify (← getEnv) c with
  | some (.defn r) => record #[(c, some (.defn r))]; pure (some r)
  | _ => pure none

def shOf (r : ShRes) : Lean.Expr × Lean.Expr := (r.pf, r.hn)

unsafe def evalSh (K : Kx) (ρ : Lean.Expr) (e : Expr) (sp : List Lean.Expr) : G2 ShRes := do
  let eQ ← qU e
  let spT := listEnt sp
  let key := (ρ, eQ, spT)
  if let some r := (← get).shMemo[key]? then return r
  if (← getThe St).cap > 0 && (← get).shSteps > (← getThe St).cap then throwError "CAPHIT"
  let r ← evalShCore K ρ e eQ sp spT
  modify fun s => { s with shMemo := s.shMemo.insert key r }
  pure r
where
  evalShCore (K : Kx) (ρ : Lean.Expr) (e : Expr) (eQ : Lean.Expr) (sp : List Lean.Expr) (spT : Lean.Expr) : G2 ShRes := do
    match e with
    | .app f a =>
      bumpSh "app"
      let aQ ← qU a
      let r ← evalSh K ρ f (entCloE aQ ρ :: sp)
      let pf ← mkN ``Sh.app [("env", K.env), ("ρ", ρ), ("f", ← qU f), ("a", aQ), ("sp", spT), ("hn", r.hn), ("h", r.pf)]
      pure { r with pf }
    | .lam n A b bi =>
      match sp with
      | c :: rest =>
        bumpSh "lam"
        let r ← evalSh K (consL c ρ) b rest
        let pf ← mkN ``Sh.lam [("env", K.env), ("ρ", ρ), ("n", toExpr n), ("A", ← qU A), ("b", ← qU b), ("bi", biE bi), ("c", c), ("sp", listEnt rest), ("hn", r.hn), ("h", r.pf)]
        pure { r with pf }
      | [] => throwError "Sh: a lambda with an empty spine (a function value, not a head)"
    | .letE n A v b nd =>
      if coreHead A then throwError "Sh: a core-type let in head position"
      bumpSh "letZ"
      let vQ ← qU v
      let r ← evalSh K (consL (entCloE vQ ρ) ρ) b sp
      let pf ← mkN ``Sh.letZ [("env", K.env), ("ρ", ρ), ("n", toExpr n), ("A", ← qU A), ("v", vQ), ("b", ← qU b), ("nd", toExpr nd), ("sp", spT), ("hn", r.hn),
        ("hA", reflT boolT (mkConst ``false)), ("h", r.pf)]
      pure { r with pf }
    | .bvar i =>
      match cxGet ρ i with
      | none => throwError "Sh: bvar {i} is not bound (environment too short)"
      | some ent =>
        match parseClo ent with
        | none => throwError "Sh: bvar {i} is bound to a value entry in head position"
        | some (eq', ρ') =>
          bumpSh "bvarC"
          let e' ← unq eq'
          let r ← evalSh K ρ' e' sp
          let hb := mkApp2 (mkConst ``Eq.refl [.succ (.succ .zero)]) (mkApp (mkConst ``Option [lvl1]) entT) (mkApp2 (mkConst ``Option.some [lvl1]) entT ent)
          let pf ← mkN ``Sh.bvarC [("env", K.env), ("ρ", ρ), ("i", toExpr i), ("e'", eq'), ("ρ'", ρ'), ("sp", spT), ("hn", r.hn), ("hb", hb), ("h", r.pf)]
          pure { r with pf }
    | .const c ls => evalConst K ρ e eQ c ls sp spT
    | .proj S i x =>
      bumpSh "proj"
      let rx ← evalSh K ρ x []
      unless rx.isCtor do throwError "Sh: proj {S}#{i} of a stuck head {rx.c}"
      let some (fe, fρ) := (rx.sp[rx.np + i]?).bind parseClo | throwError "Sh: proj {S}#{i}: field {rx.np + i} of {rx.c} is not a closure"
      let ctr ← match classify (← getEnv) rx.c with
        | some (.ctor r) => record #[(rx.c, some (.ctor r))]; pure r
        | _ => throwError "Sh: {rx.c} is not a constructor"
      unless ctr.induct == S do throwError "Sh: proj {S}#{i}: the constructor {rx.c} belongs to {ctr.induct}"
      let fld := (rx.sp[rx.np + i]?).get!
      let r ← evalSh K fρ (← unq fe) sp
      let pf ← mkN ``sh_proj_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρ), ("S", toExpr S), ("i", toExpr i), ("x", ← qU x), ("sp", spT), ("hn", r.hn),
        ("c", toExpr rx.c), ("ls", qLs rx.ls), ("np", toExpr rx.np), ("args", listEnt rx.sp), ("e'", fe), ("ρ'", fρ),
        ("r", mkApp3 (mkConst ``CtorRow.mk) (toExpr ctr.induct) (toExpr ctr.numParams) (toExpr ctr.numFields)),
        ("hx", rx.pf), ("hr", reflT (optT lkT) (someE lkT (mkApp (mkConst ``Lk.ctor) (ctorRowE ctr.induct ctr.numParams ctr.numFields)))),
        ("hS", reflT nameT (toExpr S)),
        ("hf", mkApp2 (mkConst ``Eq.refl [.succ (.succ .zero)]) (mkApp (mkConst ``Option [lvl1]) entT) (mkApp2 (mkConst ``Option.some [lvl1]) entT fld)), ("h", r.pf)]
      pure { r with pf }
    | _ => throwError "Sh: head {e.ctorName} cannot be evaluated"

  evalConst (K : Kx) (ρ : Lean.Expr) (e : Expr) (eQ : Lean.Expr) (c : Name) (ls : List Level) (sp : List Lean.Expr) (spT : Lean.Expr) : G2 ShRes := do
    if c == ``List.rec then
      match sp with
      | a0 :: mot :: nilc :: consc :: maj :: extra =>
        let some (em, ρm) := parseClo maj | throwError "Sh: List.rec major premise is not a closure"
        let rm ← evalSh K ρm (← unq em) []
        unless rm.isCtor do throwError "Sh: List.rec major premise is stuck at {rm.c}"
        record #[(``List.rec, some .recl)]
        let extraT := listEnt extra
        if rm.c == ``List.nil then
          bumpSh "recNil"
          let some (en, ρn) := parseClo nilc | throwError "Sh: List.rec nil case is not a closure"
          let r ← evalSh K ρn (← unq en) extra
          let pf ← mkN ``sh_recNil_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρ), ("ls", qLs ls), ("a0", a0), ("mot", mot), ("consc", consc),
            ("em", em), ("ρm", ρm), ("extra", extraT), ("lsN", qLs rm.ls), ("sp1", listEnt rm.sp), ("en", en), ("ρn", ρn), ("hn", r.hn), ("hrec", recFact), ("hm", rm.pf), ("h", r.pf)]
          pure { r with pf }
        else if rm.c == ``List.cons then
          bumpSh "recCons"
          let some (ec, ρc) := parseClo consc | throwError "Sh: List.rec cons case is not a closure"
          let [al, hd, tl] := rm.sp | throwError "Sh: List.rec major premise cons has {rm.sp.length} fields"
          let recQ ← qU (recCallE ls)
          let recEnv := listEnt [tl, consc, nilc, mot, a0]
          let spine' := hd :: tl :: entCloE recQ recEnv :: extra
          let r ← evalSh K ρc (← unq ec) spine'
          let pf ← mkN ``sh_recCons_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρ), ("ls", qLs ls), ("a0", a0), ("mot", mot), ("nilc", nilc),
            ("em", em), ("ρm", ρm), ("extra", extraT), ("lsC", qLs rm.ls), ("al", al), ("hd", hd), ("tl", tl), ("ec", ec), ("ρc", ρc), ("hn", r.hn),
            ("hrec", recFact), ("hm", rm.pf), ("h", r.pf)]
          pure { r with pf }
        else throwError "Sh: List.rec major premise reaches {rm.c}"
      | _ => throwError "Sh: List.rec with {sp.length} arguments (needs 5)"
    else if stopD c then
      bumpSh "prim"
      let pf ← mkN ``Sh.prim [("env", K.env), ("ρ", ρ), ("c", toExpr c), ("ls", qLs ls), ("sp", spT), ("hs", reflT boolT (mkConst ``true))]
      pure { pf, hn := hnStuckE c ls spT, c, ls, sp, isCtor := false, np := 0 }
    else
      match classify (← getEnv) c with
      | some (.defn r) =>
        record #[(c, some (.defn r))]
        unless r.lps.length == ls.length do throwError "Sh: {c}: {ls.length} levels for {r.lps.length} parameters"
        let rowE := mkApp (mkConst ``Lk.defn) (mkApp2 (mkConst ``DefRow.mk) (toExpr r.lps) (← qU r.value))
        let hr := reflT (optT lkT) (someE lkT rowE)
        if r.lps.isEmpty then
          bumpSh "unf"
          let rb ← evalSh K nilCx r.value sp
          let pf ← mkN ``sh_unf0_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρ), ("c", toExpr c), ("v", ← qU r.value), ("sp", spT), ("hn", rb.hn),
            ("hr", hr), ("hs", reflT boolT (mkConst ``false)), ("h", rb.pf)]
          pure { rb with pf }
        else
          bumpSh "unfPoly"
          modify fun s => { s with poly := s.poly.push (c, r.lps.length, 0) }
          let body := instLEShared r.lps ls r.value
          let bodyQ ← qU body
          let rb ← evalSh K nilCx body sp
          let pf ← mkN ``sh_unf_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρ), ("c", toExpr c), ("ls", qLs ls), ("r", mkApp2 (mkConst ``DefRow.mk) (toExpr r.lps) (← qU r.value)),
            ("sp", spT), ("hn", rb.hn), ("e'", bodyQ), ("hr", hr), ("hl", reflT natT (toExpr ls.length)), ("hs", reflT boolT (mkConst ``false)),
            ("he'", reflT exprT bodyQ), ("h", rb.pf)]
          pure { rb with pf }
      | some (.ctor r) =>
        record #[(c, some (.ctor r))]
        unless sp.length == r.numParams + r.numFields do throwError "Sh: constructor {c} with {sp.length} arguments (needs {r.numParams + r.numFields})"
        bumpSh "ctor"
        let pf ← mkN ``sh_ctor_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρ), ("c", toExpr c), ("ls", qLs ls), ("r", ctorRowE r.induct r.numParams r.numFields),
          ("sp", spT), ("hr", reflT (optT lkT) (someE lkT (mkApp (mkConst ``Lk.ctor) (ctorRowE r.induct r.numParams r.numFields)))),
          ("hs", reflT boolT (mkConst ``false)), ("hn", reflT natT (toExpr sp.length))]
        pure { pf, hn := hnCtorE c ls r.numParams spT, c, ls, sp, isCtor := true, np := r.numParams }
      | _ => throwError "Sh: {c} is neither a definition nor a constructor of the environment (a stop head is missing?)"

/-! ## the derivation of `DT` -/

def dtOf (pf : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let t ← whnfR (← inferType pf)
  unless t.getAppFn.isConstOf ``DT do throwError "not a DT proof: {t}"
  let a := t.getAppArgs
  unless a.size == 4 do throwError "DT arity"
  pure (a[2]!, a[3]!)
def dtVal (pf : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let (_, r) ← dtOf pf
  unless r.getAppFn.isConstOf ``Res.val do throwError "expected a value judgement, got {r}"
  pure (r.getAppArgs[0]!, r.getAppArgs[1]!)
def dtTy (pf : Lean.Expr) : MetaM Lean.Expr := do
  let (_, r) ← dtOf pf
  unless r.getAppFn.isConstOf ``Res.ty do throwError "expected a type judgement, got {r}"
  pure r.getAppArgs[0]!

/-- parse a value entry `Ent.val (Entry.mk τ (Dyn.mk T a))` -/
def parseVal (t : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  if t.isAppOfArity ``Ent.val 1 then
    let en := t.getAppArgs[0]!
    if en.isAppOfArity ``Entry.mk 2 then
      let d := en.getAppArgs[1]!
      if d.isAppOfArity ``Dyn.mk 2 then some (en.getAppArgs[0]!, d.getAppArgs[0]!, d.getAppArgs[1]!) else none
    else none
  else none

mutual
unsafe def deriveT (K : Kx) (ty : Bool) (ρ : Lean.Expr) (e : Expr) : G2 Lean.Expr := do
  let key := (ty, ρ, e)
  if let some p := (← getThe St).memo[key]? then return p
  modifyThe St fun s => { s with nodes := s.nodes + 1 }
  if (← getThe St).cap > 0 && (← getThe St).nodes > (← getThe St).cap then throwError "CAPHIT"
  let p ← if (← getThe St).probe then
      try deriveCore K ty ρ e
      catch ex =>
        let msg ← ex.toMessageData.toString
        if msg.startsWith "CAPHIT" then throw ex
        modifyThe St fun s => { s with stops := s.stops.push msg }
        let tv ← mkFreshExprMVar (some (mkSort (.succ .zero)))
        let r ← if ty then pure (mkApp (mkConst ``Res.ty) tv)
          else do
            let vv ← mkFreshExprMVar (some tv)
            pure (mkApp2 (mkConst ``Res.val) tv vv)
        mkFreshExprMVar (some (mkAppN (mkConst ``DT) #[K.env, ρ, ← qU e, r]))
    else deriveCore K ty ρ e
  modifyThe St fun s => { s with memo := s.memo.insert key p }
  pure p

unsafe def deriveCore (K : Kx) (ty : Bool) (ρ : Lean.Expr) (e : Expr) : G2 Lean.Expr := do
  match e with
  | .bvar i =>
    let some ent := cxGet ρ i | throwError "bvar {i} is not bound"
    match parseClo ent with
    | some (eq', ρ') =>
      let p ← deriveT K ty ρ' (← unq eq')
      let (_, r) ← dtOf p
      let hb := mkApp2 (mkConst ``Eq.refl [.succ (.succ .zero)]) (mkApp (mkConst ``Option [lvl1]) entT) (mkApp2 (mkConst ``Option.some [lvl1]) entT ent)
      bump "bvarClo"
      mkN ``DT.bvarClo [("env", K.env), ("ρ", ρ), ("i", toExpr i), ("e'", eq'), ("ρ'", ρ'), ("r", r), ("hb", hb), ("h", p)]
    | none =>
      if ty then throwError "bvar {i} judged as a type"
      let some (τ, T, a) := parseVal ent | throwError "bvar {i}: an entry that is neither a closure nor a value"
      bump "bvar"
      mkN ``DT.bvar [("env", K.env), ("ρ", ρ), ("i", toExpr i), ("τ", τ), ("T", T), ("a", a),
        ("h", mkApp2 (mkConst ``Eq.refl [.succ (.succ .zero)]) (mkApp (mkConst ``Option [lvl1]) entT) (mkApp2 (mkConst ``Option.some [lvl1]) entT ent))]
  | .lam n A b bi =>
    if ty then throwError "lam judged as a type"
    let eQ ← qU e
    let hA ← deriveT K true ρ A
    let TA ← dtTy hA
    bump "lam"
    withLocalDeclD `a TA fun av => do
      let c : CEntry := { tau := ← qU A, ty := TA, val := av }
      let hb ← deriveT K false (consL (entValE c) ρ) b
      let (αb, vb) ← dtVal hb
      let TB ← mkLambdaFVars #[av] αb
      let f ← mkLambdaFVars #[av] vb
      let hbL ← mkLambdaFVars #[av] hb
      mkN ``DT.lam [("env", K.env), ("ρ", ρ), ("e", eQ), ("A", ← qU A), ("body", ← qU b), ("n", toExpr n), ("bi", biE bi),
        ("TA", TA), ("TB", TB), ("f", f), ("he", reflT exprT eQ), ("hA", hA), ("hb", hbL)]
  | .letE n A v b nd =>
    if coreHead A then
      if ty then throwError "let judged as a type"
      let eQ ← qU e
      let hA ← deriveT K true ρ A
      let TA ← dtTy hA
      let hv ← deriveT K false ρ v
      let (_, a) ← dtVal hv
      let c : CEntry := { tau := ← qU A, ty := TA, val := a }
      let hb ← deriveT K false (consL (entValE c) ρ) b
      let (T, r) ← dtVal hb
      bump "letE"
      mkN ``DT.letE [("env", K.env), ("ρ", ρ), ("e", eQ), ("A", ← qU A), ("v", ← qU v), ("body", ← qU b), ("n", toExpr n), ("nd", toExpr nd),
        ("TA", TA), ("T", T), ("a", a), ("r", r), ("he", reflT exprT eQ), ("hA", hA), ("hc", reflT boolT (mkConst ``true)), ("hv", hv), ("hb", hb)]
    else viaShRoute K ty ρ e
  | .mdata .. => throwError "mdata"
  | _ =>
    match appFn e with
    | .const c ls => if directHead c then deriveConst K ty ρ e c ls else viaShRoute K ty ρ e
    | _ => viaShRoute K ty ρ e

unsafe def viaShRoute (K : Kx) (ty : Bool) (ρ : Lean.Expr) (e : Expr) : G2 Lean.Expr := do
  let r ← evalSh K ρ e []
  -- one common environment for the spine
  let mut args : Array Expr := #[]
  let mut ρ₀ : Option Lean.Expr := none
  for ent in r.sp do
    match parseClo ent with
    | some (aq, ρa) =>
      match ρ₀ with
      | none => ρ₀ := some ρa
      | some p => unless p == ρa do throwError "viaSh: the arguments of {r.c} are closures over different environments (not a common-environment spine)"
      args := args.push (← unq aq)
    | none => throwError "viaSh: an argument of {r.c} is a value entry"
  let ρ0 := ρ₀.getD nilCx
  let argl := args.toList
  let e₀ := appN r.c r.ls argl
  unless directHead r.c do throwError "viaSh: the head {r.c} reached by evaluation has no rule ({if r.isCtor then "constructor" else "stuck"}; {argl.length} arguments)"
  let p ← deriveT K ty ρ0 e₀
  let (_, res) ← dtOf p
  modify fun s => { s with viaN := s.viaN + 1 }
  bump "viaSh"
  let hcan ← match argl with
    | [] => pure (mkConst ``canon_nil)
    | a :: as => do pure (mkAppN (mkConst ``canon_cons) #[ρ0, ← qU a, listExprE (← as.mapM qU)])
  mkN ``DT.viaSh [("env", K.env), ("ρ", ρ), ("e", ← qU e), ("hn", r.hn), ("args", listExprE (← argl.mapM qU)), ("ρ₀", ρ0), ("r", res),
    ("hv", reflT boolT (mkConst ``true)), ("hsh", r.pf), ("hsp", reflT (mkApp (mkConst ``List [lvl1]) entT) (listEnt r.sp)), ("hcan", hcan), ("h", p)]

unsafe def deriveConst (K : Kx) (ty : Bool) (ρ : Lean.Expr) (e : Expr) (c : Name) (ls : List Level) : G2 Lean.Expr := do
  let eQ ← qU e
  let args := appArgs e
  let a (i : Nat) : G2 Expr := do
    let some x := args[i]? | throwError "{c}: argument {i} missing"
    pure x
  let q (i : Nat) : G2 Lean.Expr := do qU (← a i)
  let heE := reflT exprT eQ
  let v (i : Nat) : G2 Lean.Expr := do deriveT K false ρ (← a i)
  let t (i : Nat) : G2 Lean.Expr := do deriveT K true ρ (← a i)
  let env0 : List (String × Lean.Expr) := [("env", K.env), ("ρ", ρ), ("e", eQ), ("he", heE)]
  let noRule : G2 Lean.Expr := throwError "{c}: no direct rule applies ({if ty then "type" else "value"}, levels {ls}, {args.length} arguments)"
  if ty then
    if c == ``Nat then bump "nat"; mkN ``DT.nat [("env", K.env), ("ρ", ρ), ("e", eQ), ("he", heE)]
    else if c == ``Bool then bump "bool"; mkN ``DT.bool [("env", K.env), ("ρ", ρ), ("e", eQ), ("he", heE)]
    else if c == ``Sparkle.Core.Domain.DomainConfig then bump "domainConfig"; mkN ``DT.domainConfig [("env", K.env), ("ρ", ρ), ("e", eQ), ("he", heE)]
    else if c == ``BitVec then
      let hw ← v 0
      let (_, n) ← dtVal hw
      bump "bitvec"
      mkN ``DT.bitvec (env0 ++ [("w", ← q 0), ("n", n), ("hw", hw)])
    else if c == ``Signal then
      let hd ← v 0
      let ht ← t 1
      let (_, D) ← dtVal hd
      bump "signal"
      mkN ``DT.signal (env0 ++ [("d", ← q 0), ("t", ← q 1), ("D", D), ("T", ← dtTy ht), ("hd", hd), ("ht", ht)])
    else if c == ``Prod && ls == [.zero, .zero] && args.length == 2 then
      let ha ← t 0
      let hb ← t 1
      bump "prodTy"
      mkN ``DT.prodTy (env0 ++ [("a", ← q 0), ("b", ← q 1), ("A", ← dtTy ha), ("B", ← dtTy hb), ("ha", ha), ("hb", hb)])
    else if c == ``PUnit && ls == [.succ .zero] && args.length == 0 then
      bump "punitTy"
      mkN ``DT.punitTy [("env", K.env), ("ρ", ρ), ("e", eQ), ("he", heE)]
    else noRule
  else
    if c == ``OfNat.ofNat then
      match args[1]? with
      | some (Lean.Expr.lit (.natVal n)) => bump "natLit"; mkN ``DT.natLit (env0 ++ [("n", toExpr n)])
      | _ => throwError "OfNat.ofNat: not a literal"
    else if c == ``Sparkle.Core.Domain.defaultDomain then bump "domDefault"; mkN ``DT.domDefault [("env", K.env), ("ρ", ρ), ("e", eQ), ("he", heE)]
    else if c == ``instInhabitedBool then bump "boolInhabited"; mkN ``DT.boolInhabited [("env", K.env), ("ρ", ρ), ("e", eQ), ("he", heE)]
    else if c == ``BitVec.ofNat then
      let hw ← v 0
      let hk ← v 1
      let (_, W) ← dtVal hw
      let (_, Kk) ← dtVal hk
      bump "bvOfNat"
      mkN ``DT.bvOfNat (env0 ++ [("w", ← q 0), ("k", ← q 1), ("W", W), ("K", Kk), ("hw", hw), ("hk", hk)])
    else if c == ``BitVec.instInhabited then
      let hw ← v 0
      let (_, W) ← dtVal hw
      bump "bvInhabited"
      mkN ``DT.bvInhabited (env0 ++ [("w", ← q 0), ("W", W), ("hw", hw)])
    else if c == ``Signal.pure then
      let hd ← v 0
      let ht ← t 1
      let hx ← v 2
      let (_, D) ← dtVal hd
      let (_, av) ← dtVal hx
      bump "sigPure"
      mkN ``DT.sigPure (env0 ++ [("d", ← q 0), ("t", ← q 1), ("x", ← q 2), ("D", D), ("T", ← dtTy ht), ("a", av), ("hd", hd), ("ht", ht), ("hx", hx)])
    else if c == ``Signal.register then
      let hd ← v 0
      let ht ← t 1
      let hi ← v 2
      let hs ← v 3
      let (_, D) ← dtVal hd
      let (_, av) ← dtVal hi
      let (_, sv) ← dtVal hs
      bump "sigRegister"
      mkN ``DT.sigRegister (env0 ++ [("d", ← q 0), ("t", ← q 1), ("i", ← q 2), ("s", ← q 3), ("D", D), ("T", ← dtTy ht), ("a", av), ("sv", sv),
        ("hd", hd), ("ht", ht), ("hi", hi), ("hs", hs)])
    else if c == ``Signal.mux then
      let hd ← v 0
      let ht ← t 1
      let hc ← v 2
      let ha ← v 3
      let hb ← v 4
      let (_, D) ← dtVal hd
      let (_, cv) ← dtVal hc
      let (_, av) ← dtVal ha
      let (_, bv) ← dtVal hb
      bump "sigMux"
      mkN ``DT.sigMux (env0 ++ [("d", ← q 0), ("t", ← q 1), ("c", ← q 2), ("a", ← q 3), ("b", ← q 4), ("D", D), ("T", ← dtTy ht), ("cv", cv), ("av", av), ("bv", bv),
        ("hd", hd), ("ht", ht), ("hc", hc), ("ha", ha), ("hb", hb)])
    else if c == ``Signal.loop then
      let hd ← v 0
      let ht ← t 1
      let hi ← v 2
      let hf ← v 3
      let (_, D) ← dtVal hd
      let (_, iv) ← dtVal hi
      let (_, g) ← dtVal hf
      bump "sigLoop"
      mkN ``DT.sigLoop (env0 ++ [("d", ← q 0), ("t", ← q 1), ("inst", ← q 2), ("f", ← q 3), ("D", D), ("T", ← dtTy ht), ("iv", iv), ("g", g),
        ("hd", hd), ("ht", ht), ("hi", hi), ("hf", hf)])
    else if c == ``HAdd.hAdd then
      let inst ← a 3
      let ia := appArgs inst
      let some dq := ia[0]? | throwError "HAdd: instance args"
      let some wq := ia[1]? | throwError "HAdd: instance args"
      let hd ← deriveT K false ρ dq
      let hw ← deriveT K false ρ wq
      let ha ← v 4
      let hb ← v 5
      let (_, D) ← dtVal hd
      let (_, W) ← dtVal hw
      let (_, av) ← dtVal ha
      let (_, bv) ← dtVal hb
      bump "sigAddBV"
      mkN ``DT.sigAddBV (env0 ++ [("d", ← qU dq), ("w", ← qU wq), ("a", ← q 4), ("b", ← q 5), ("D", D), ("W", W), ("av", av), ("bv", bv),
        ("hd", hd), ("hw", hw), ("ha", ha), ("hb", hb)])
    else if c == ``HAnd.hAnd || c == ``HOr.hOr then
      let inst ← a 3
      let some dq := (appArgs inst)[0]? | throwError "HAnd/HOr: instance args"
      let hd ← deriveT K false ρ dq
      let ha ← v 4
      let hb ← v 5
      let (_, D) ← dtVal hd
      let (_, av) ← dtVal ha
      let (_, bv) ← dtVal hb
      bump (if c == ``HAnd.hAnd then "sigAndBool" else "sigOrBool")
      mkN (if c == ``HAnd.hAnd then ``DT.sigAndBool else ``DT.sigOrBool) (env0 ++ [("d", ← qU dq), ("a", ← q 4), ("b", ← q 5), ("D", D), ("av", av), ("bv", bv),
        ("hd", hd), ("ha", ha), ("hb", hb)])
    else if c == ``Complement.complement then
      let inst ← a 1
      let some dq := (appArgs inst)[0]? | throwError "Complement: instance args"
      let hd ← deriveT K false ρ dq
      let ha ← v 2
      let (_, D) ← dtVal hd
      let (_, av) ← dtVal ha
      bump "sigNotBool"
      mkN ``DT.sigNotBool (env0 ++ [("d", ← qU dq), ("a", ← q 2), ("D", D), ("av", av), ("hd", hd), ("ha", ha)])
    else if c == ``Sparkle.Core.Signal.Signal.beq then
      let bvT ← a 0
      let some wq := (appArgs bvT)[0]? | throwError "beq: BitVec arg"
      let hd ← v 1
      let hw ← deriveT K false ρ wq
      let ha ← v 3
      let hb ← v 4
      let (_, D) ← dtVal hd
      let (_, W) ← dtVal hw
      let (_, av) ← dtVal ha
      let (_, bv) ← dtVal hb
      bump "sigBeqBV"
      mkN ``DT.sigBeqBV (env0 ++ [("d", ← q 1), ("w", ← qU wq), ("a", ← q 3), ("b", ← q 4), ("D", D), ("W", W), ("av", av), ("bv", bv),
        ("hd", hd), ("hw", hw), ("ha", ha), ("hb", hb)])
    else if (bvAbbrevRow c).isSome then throwError "bvAbbrev {c}: not supported by the generator"
    else if c == ``Signal.map && ls == [.zero] && args.length == 5 && (projFnG (args[3]!)).isSome then
      let some (isFst, pa, pb) := projFnG (args[3]!) | throwError "unreachable"
      let hd ← v 0
      let hp ← t 1
      let ht ← t 2
      let ha ← deriveT K true ρ pa
      let hb ← deriveT K true ρ pb
      let hs ← v 4
      let (_, D) ← dtVal hd
      let (_, sv) ← dtVal hs
      let tyArg := if isFst then "ta" else "tb"
      bump (if isFst then "mapFst" else "mapSnd")
      mkN (if isFst then ``DT.mapFst else ``DT.mapSnd) (env0 ++ [("d", ← q 0), ("tp", ← q 1), (tyArg, ← q 2), ("a", ← qU pa), ("b", ← qU pb), ("s", ← q 4),
        ("D", D), ("A", ← dtTy (if isFst then ht else ha)), ("B", ← dtTy hb), ("sv", sv), ("hd", hd), ("hp", hp), ("ht", ht), ("ha", ha), ("hb", hb), ("hs", hs)])
    else if c == ``Sparkle.Core.Signal.bundle2 && ls == [.zero] && args.length == 5 then
      let hd ← v 0
      let hta ← t 1
      let htb ← t 2
      let ha ← v 3
      let hb ← v 4
      let (_, D) ← dtVal hd
      let (_, av) ← dtVal ha
      let (_, bv) ← dtVal hb
      bump "bundle2"
      mkN ``DT.bundle2 (env0 ++ [("d", ← q 0), ("ta", ← q 1), ("tb", ← q 2), ("a", ← q 3), ("b", ← q 4), ("D", D), ("A", ← dtTy hta), ("B", ← dtTy htb),
        ("av", av), ("bv", bv), ("hd", hd), ("hta", hta), ("htb", htb), ("ha", ha), ("hb", hb)])
    else if c == ``Inhabited.mk && ls.length == 1 && args.length == 2 && lvlNat (ls.head!) == some 1 then
      let ht ← t 0
      let hx ← v 1
      let (_, xv) ← dtVal hx
      let hr ← ctorFact K ``Inhabited.mk
      let cw ← ctorRowOf ``Inhabited.mk
      bump "inhMk"
      mkN ``dt_inhMk_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρ), ("e", eQ), ("t", ← q 0), ("x", ← q 1), ("u", qL ls.head!), ("T", ← dtTy ht), ("v", xv),
        ("cw", ctorRowE cw.induct cw.numParams cw.numFields), ("he", heE), ("hu", reflT (optT natT) (someE natT (toExpr (1 : Nat)))), ("hr", hr), ("ht", ht), ("hx", hx)]
    else if c == ``Inhabited.default && ls == [.succ .zero] && args.length == 2 then
      let ht ← t 0
      let hi ← v 1
      let (_, iv) ← dtVal hi
      bump "inhDefault"
      mkN ``DT.inhDefault (env0 ++ [("t", ← q 0), ("inst", ← q 1), ("T", ← dtTy ht), ("iv", iv), ("ht", ht), ("hi", hi)])
    else if c == ``Prod.mk && ls == [.zero, .zero] && args.length == 4 then
      let ha ← t 0
      let hb ← t 1
      let hx ← v 2
      let hy ← v 3
      let (_, xv) ← dtVal hx
      let (_, yv) ← dtVal hy
      let hr ← ctorFact K ``Prod.mk
      let cw ← ctorRowOf ``Prod.mk
      bump "prodMk"
      mkN ``dt_prodMk_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρ), ("e", eQ), ("a", ← q 0), ("b", ← q 1), ("x", ← q 2), ("y", ← q 3),
        ("A", ← dtTy ha), ("B", ← dtTy hb), ("xv", xv), ("yv", yv), ("cw", ctorRowE cw.induct cw.numParams cw.numFields), ("he", heE), ("hr", hr),
        ("ha", ha), ("hb", hb), ("hx", hx), ("hy", hy)]
    else if c == ``PUnit.unit && ls == [.succ .zero] && args.length == 0 then
      let hr ← ctorFact K ``PUnit.unit
      let cw ← ctorRowOf ``PUnit.unit
      bump "unitVal"
      mkN ``dt_unitVal_t [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρ), ("e", eQ), ("cw", ctorRowE cw.induct cw.numParams cw.numFields), ("he", heE), ("hr", hr)]
    else if (c == ``Bool.false || c == ``Bool.true) && ls == [] && args.length == 0 then
      let hr ← ctorFact K c
      let cw ← ctorRowOf c
      bump (if c == ``Bool.false then "boolFalse" else "boolTrue")
      mkN (if c == ``Bool.false then ``dt_boolFalse_t else ``dt_boolTrue_t) [("env", K.env), ("lk", K.lk), ("hlk", K.hlk), ("ρ", ρ), ("e", eQ),
        ("cw", ctorRowE cw.induct cw.numParams cw.numFields), ("he", heE), ("hr", hr)]
    else noRule
end

end Tools.ShippingFGCircuitS2iGen
