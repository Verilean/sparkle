import Lean

/-! # Recursive helpers on literal data

A user helper defined by structural recursion (`treeReduceAux f z 4 [a, b, c,
d]`, `lutMuxTreeList index dflt [(v₀, 0), …]`) is applied to LITERAL data —
a list written out, a fuel number — whose recursion ends in hardware. The
inliner leaves recursive definitions alone; this pass unfolds such a call
through its smart-unfolding body (`f._sunfold`, whose recursive calls name
`f`) and reduces its `match` by `casesOn` on the constructor literal. A call
whose match does not reduce (a symbolic list) is left as it is, so nothing
that reads today reads differently.

The result is definitionally the call (delta, beta, iota), which is all the
endpoint's kernel checks need; the entry proofs treat the unfolding as an
opaque function of the environment. -/
namespace Sparkle.Compiler.MachRecUnfold
open Lean

/-- A `Nat` literal in the compiler's canonical form (`OfNat.ofNat Nat n`). -/
def natLitE (n : Nat) : Expr :=
  mkApp3 (.const ``OfNat.ofNat [.zero]) (.const ``Nat []) (.lit (.natVal n))
    (mkApp (.const ``instOfNatNat []) (.lit (.natVal n)))

/-- A `Nat` literal as a constructor: `0` is `Nat.zero`, `n + 1` is
`Nat.succ n`. -/
def natCtor? (natLit? : Expr → Option Nat) (e : Expr) : Option (Name × Array Expr) :=
  match natLit? e with
  | some 0 => some (``Nat.zero, #[])
  | some (n + 1) => some (``Nat.succ, #[natLitE n])
  | none => none

/-- `e` in constructor form: the constructor and its arguments. -/
def ctorApp? (env : Environment) (natLit? : Expr → Option Nat) (e : Expr) :
    Option (ConstructorVal × Array Expr) :=
  let e := e.consumeMData
  match natCtor? natLit? e with
  | some (c, fields) =>
    match env.find? c with
    | some (.ctorInfo cv) => some (cv, fields)
    | _ => none
  | none =>
    match e.getAppFn with
    | .const c _ =>
      match env.find? c with
      | some (.ctorInfo cv) =>
        let args := e.getAppArgs
        if args.size == cv.numParams + cv.numFields then some (cv, args.extract cv.numParams args.size)
        else none
      | _ => none
    | _ => none

/-- Head beta through metadata at the head. -/
partial def headBetaM (e : Expr) : Expr :=
  let e := e.consumeMData
  let f := e.getAppFn.consumeMData
  if f.isLambda && e.getAppNumArgs > 0 then headBetaM (f.beta e.getAppArgs)
  else e

/-- Head beta, then `T.casesOn` on a constructor literal, repeatedly; `none`
when a `casesOn` meets a major premise that is not a constructor. -/
partial def iota (env : Environment) (natLit? : Expr → Option Nat) (fuel : Nat) (e : Expr) :
    Option Expr := do
  if fuel == 0 then none else
  let e := headBetaM e
  match e.getAppFn with
  | .const n ls =>
    match n with
    -- the auxiliary `casesOn` of overlapping patterns: its definition
    | .str _ s =>
      if s.startsWith "_sparseCasesOn" then
        match env.find? n with
        | some (.defnInfo d) =>
          iota env natLit? (fuel - 1)
            (mkAppN (d.value.instantiateLevelParams d.levelParams ls) e.getAppArgs)
        | _ => some e
      -- a recursor on a constructor: its rule (the kernel's iota)
      else if s == "rec" then
        match env.find? n with
        | some (.recInfo rv) =>
          let args := e.getAppArgs
          let majorIdx := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices
          if args.size <= majorIdx then none else
          let (cv, fields) ← ctorApp? env natLit? args[majorIdx]!
          let some rule := rv.rules.find? (·.ctor == cv.name) | none
          let rhs := rule.rhs.instantiateLevelParams rv.levelParams ls
          let pre := args.extract 0 (rv.numParams + rv.numMotives + rv.numMinors)
          let rest := args.extract (majorIdx + 1) args.size
          iota env natLit? (fuel - 1) (mkAppN (mkAppN (mkAppN rhs pre) fields) rest)
        | _ => some e
      else if s == "casesOn" then
        match n with
        | .str T _ =>
          match env.find? T with
          | some (.inductInfo iv) =>
            let args := e.getAppArgs
            -- params, motive, indices, major, one alternative per constructor
            let majorIdx := iv.numParams + 1 + iv.numIndices
            let altsStart := majorIdx + 1
            if args.size < altsStart + iv.ctors.length then none else
            let (cv, fields) ← ctorApp? env natLit? args[majorIdx]!
            let alt := args[altsStart + cv.cidx]!
            let rest := args.extract (altsStart + iv.ctors.length) args.size
            iota env natLit? (fuel - 1) (mkAppN (mkAppN alt fields) rest)
          | _ => some e
        | _ => some e
      else some e
    | _ => some e
  | _ => some e

/-- A matcher application, reduced by unfolding the matcher (its `casesOn`
tree) on constructor discriminants. -/
def reduceMatcher? (env : Environment) (natLit? : Expr → Option Nat) (e : Expr) : Option Expr := do
  let .const n ls := e.getAppFn | none
  if !Lean.Meta.isMatcherCore env n then none else
  let some (.defnInfo d) := env.find? n | none
  let v := d.value.instantiateLevelParams d.levelParams ls
  let r ← iota env natLit? 256 (mkAppN v e.getAppArgs)
  -- reduced: no `casesOn` left at the head
  match r.getAppFn with
  | .const (.str _ s) _ =>
    if s == "casesOn" || s == "rec" || s.startsWith "_sparseCasesOn" then none else some r
  | _ => some r

/-- The value with every matcher at the head of a `let`-free spine reduced,
when the matchers' discriminants are constructors; `none` when one is not. -/
partial def reduceHead (env : Environment) (natLit? : Expr → Option Nat) (fuel : Nat) (e : Expr) :
    Option Expr := do
  if fuel == 0 then none else
  let e := headBetaM e
  match e with
  | .letE n t v b nd => do
    let b' ← reduceHead env natLit? (fuel - 1) b
    some (.letE n t v b' nd)
  | _ =>
    if Lean.Meta.isMatcherCore env (e.getAppFn.constName?.getD .anonymous) then
      let r ← reduceMatcher? env natLit? e
      reduceHead env natLit? (fuel - 1) r
    else some e

/-- Beta everywhere. -/
partial def betaAll : Expr → Expr
  | e@(.app ..) =>
    let f := betaAll e.getAppFn
    let args := e.getAppArgs.map betaAll
    let e' := mkAppN f args
    if f.consumeMData.isLambda then betaAll (headBetaM e') else e'
  | .lam n t b bi => .lam n t (betaAll b) bi
  | .letE n t v b nd => .letE n t (betaAll v) (betaAll b) nd
  | .mdata m b => .mdata m (betaAll b)
  | e => e

/-- One call of a recursive user helper (`isUser`), unfolded through its
smart-unfolding body when its match reduces. -/
def unfoldCall? (env : Environment) (natLit? : Expr → Option Nat) (isUser : Name → Bool)
    (e : Expr) : Option Expr := do
  let .const n ls := e.getAppFn | none
  if !isUser n then none else
  let some (.defnInfo d) := env.find? (Lean.Meta.mkSmartUnfoldingNameFor n) | none
  let v := d.value.instantiateLevelParams d.levelParams ls
  let r ← reduceHead env natLit? 64 (v.beta e.getAppArgs)
  some (betaAll r)

/-! ## Closed literal data

The data a recursive helper walks is often computed by library functions on
literals (`table.toList.zipIdx` of an array literal, `table.size == 0`). These
are evaluated here — to the literal the kernel computes too. -/

/-- A literal list (through closed `let`s, `List.toArray`/`Array.toList`,
`List.zipIdx`): its element type and elements. -/
partial def listLit? (natLit? : Expr → Option Nat) : Expr → Option (Expr × List Expr)
  | .mdata _ b => listLit? natLit? b
  | .letE _ _ v b _ => if v.hasLooseBVars then none else listLit? natLit? (b.instantiate1 v)
  | e =>
    match e.getAppFn, e.getAppArgs with
    | .const ``List.nil _, #[α] => some (α, [])
    | .const ``List.cons _, #[α, a, rest] => do
      let (_, xs) ← listLit? natLit? rest
      some (α, a :: xs)
    | .const ``Array.toList _, #[_, a] => listLit? natLit? a
    | .const ``List.toArray _, #[_, l] => listLit? natLit? l
    | .const ``Array.mk _, #[_, l] => listLit? natLit? l
    | .const ``List.zipIdx _, #[α, l, n] => do
      let (_, xs) ← listLit? natLit? l
      let n0 ← natLit? n
      let pair := mkApp2 (.const ``Prod [.zero, .zero]) α (.const ``Nat [])
      some (pair, xs.zipIdx.map fun (a, i) =>
        mkApp4 (.const ``Prod.mk [.zero, .zero]) α (.const ``Nat []) a (natLitE (i + n0)))
    | _, _ => none

/-- A literal list as `List.cons` … `List.nil`. -/
def mkListLit (α : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun a rest => mkApp3 (.const ``List.cons [.zero]) α a rest) (mkApp (.const ``List.nil [.zero]) α)

/-- A closed `Nat` (a literal, the size of a literal array or list). -/
def natVal? (natLit? : Expr → Option Nat) (e : Expr) : Option Nat :=
  match natLit? e with
  | some n => some n
  | none =>
    match e.getAppFn, e.getAppArgs with
    | .const ``Array.size _, #[_, a] => (listLit? natLit? a).map (·.2.length)
    | .const ``List.length _, #[_, l] => (listLit? natLit? l).map (·.2.length)
    | _, _ => none

/-- A closed `Bool`: a literal or `==` of closed `Nat`s. -/
def boolVal? (natLit? : Expr → Option Nat) (e : Expr) : Option Bool :=
  match e.consumeMData with
  | .const ``Bool.true _ => some true
  | .const ``Bool.false _ => some false
  | e =>
    match e.getAppFn, e.getAppArgs with
    | .const ``BEq.beq _, #[ty, _, a, b] =>
      if ty.isConstOf ``Nat then do
        let x ← natVal? natLit? a
        let y ← natVal? natLit? b
        some (x == y)
      else none
    | _, _ => none

/-- One node of closed literal evaluation. -/
def evalNode? (natLit? : Expr → Option Nat) (e : Expr) : Option Expr :=
  match e.getAppFn, e.getAppArgs with
  -- `if c = true then a else b` on a closed `c`
  | .const ``ite _, #[_, c, _, a, b] =>
    match c.consumeMData.getAppFn, c.consumeMData.getAppArgs with
    | .const ``Eq _, #[ty, x, y] =>
      if !ty.isConstOf ``Bool then none else do
      let vx ← boolVal? natLit? x
      let vy ← boolVal? natLit? y
      some (if vx == vy then a else b)
    | _, _ => none
  | .const ``List.zipIdx _, _ => (listLit? natLit? e).map fun (α, xs) => mkListLit α xs
  | .const ``Array.toList _, _ => (listLit? natLit? e).map fun (α, xs) => mkListLit α xs
  | .const ``List.headD _, #[_, l, d] =>
    (listLit? natLit? l).map fun (_, xs) => xs.headD d
  | _, _ => none

/-- Every reducible recursive call of `e` unfolded (and the unfolding's own
calls, while the literal data lasts), innermost first; closed literal data
evaluated, closed `let`s of literal data substituted. Memoised: the values
the front end sees are shared DAGs. -/
partial def passM (env : Environment) (natLit? : Expr → Option Nat) (isUser : Name → Bool)
    (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some r := (← get).get? e then return r
  let r ← match e with
    | .app .. => do
      let f ← passM env natLit? isUser e.getAppFn
      let args ← e.getAppArgs.mapM (passM env natLit? isUser)
      let e' := mkAppN f args
      match evalNode? natLit? e' with
      | some r => passM env natLit? isUser r
      | none =>
      match unfoldCall? env natLit? isUser e' with
      | some r => passM env natLit? isUser r
      | none => pure e'
    | .lam n t b bi => return .lam n t (← passM env natLit? isUser b) bi
    | .letE n t v b nd => do
      let v' ← passM env natLit? isUser v
      -- a closed list `let` is substituted: the data a helper walks
      if !v'.hasLooseBVars && !v'.hasFVar && (listLit? natLit? v').isSome then
        passM env natLit? isUser (b.instantiate1 v')
      else return .letE n t v' (← passM env natLit? isUser b) nd
    | .mdata m b => return .mdata m (← passM env natLit? isUser b)
    | e => pure e
  modify (·.insert e r)
  return r

/-- Whether `e` has anything the pass acts on (a recursive user helper, or a
literal-data operation): otherwise the pass is skipped. -/
def relevant (isUser : Name → Bool) (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .const n _ => isUser n || n == ``List.zipIdx || n == ``Array.toList || n == ``List.headD
    | _ => false).isSome

def pass (env : Environment) (natLit? : Expr → Option Nat) (isUser : Name → Bool) (e : Expr) :
    Expr :=
  (passM env natLit? isUser e |>.run' {})

/-- Whether the constants reachable from `e` through the user definitions it
unfolds (`defs`) include something the pass acts on — decided on the small
definition bodies, not on the (large) unfolded value. -/
partial def relevantClosure (defs : Name → Option Expr) (isUser : Name → Bool) (e : Expr) : Bool :=
  let hit (n : Name) : Bool :=
    isUser n || n == ``List.zipIdx || n == ``Array.toList || n == ``List.headD
  let rec go (todo : List Name) (seen : Std.HashSet Name) (fuel : Nat) : Bool :=
    match fuel, todo with
    | 0, _ => true
    | _, [] => false
    | f + 1, n :: rest =>
      if seen.contains n then go rest seen f
      else if hit n then true
      else
        let more := match defs n with
          | some v => v.getUsedConstants.toList
          | none => []
        go (more ++ rest) (seen.insert n) f
  go e.getUsedConstants.toList {} 100000

end Sparkle.Compiler.MachRecUnfold
