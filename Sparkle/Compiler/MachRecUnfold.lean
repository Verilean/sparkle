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

/-! ## Fuel

Every definition below is total.  `iota` and `reduceHead` keep the fuel they
always had (256 / 64; running out means "does not reduce", as before).  The four
definitions whose termination rests on typing or on the environment —
`headBetaM`, `betaAll`, `listLit?`, `passM` — carry a fuel that only the NON-structural re-entries consume
(a β-step of `headBetaM`; the `betaAll` re-entry after `headBetaM`; the zeta step
of a `letE` in `listLit?`; the re-entry of `passM` on the result of
`evalNode?` / `unfoldCall?` / a substituted `let`).  Recursion on a subterm is
structural and does NOT consume fuel, so the fuel needed is the number of
unfolding steps along one path, not the size of the expression.  Running out is
a compile error, never a silent cut: the message names the definition and the
limit (the caller adds the declaration). -/

/-- The single provisional fuel limit shared by the four limits below (one constant to switch;
the threshold measurement `scripts/shipping-coverage/rt_fuel_threshold.sh` rewrites this line). -/
def fuelLimit : Nat := 100

/-- Limit of `headBetaM`: head β-steps in one call. -/
def headBetaLimit : Nat := fuelLimit
/-- Limit of `betaAll`: re-entries after a head β along one path. -/
def betaAllLimit : Nat := fuelLimit
/-- Limit of `listLit?`: `let` zeta-steps along one path. -/
def listLitLimit : Nat := fuelLimit
/-- Limit of `passM`: re-entries on a rewritten value / substituted `let` along one path. -/
def passLimit : Nat := fuelLimit

/-- The message of a fuel exhaustion. -/
def fuelMsg (what : String) (limit : Nat) (unit : String) : String :=
  s!"MachRecUnfold.{what}: fuel exhausted (limit {limit} {unit})"

/-- A step that either reduces, is stuck (`none`: the term is left as it is), or
runs out of fuel (`error`). -/
abbrev M := ExceptT String Option

/-- Not reducible / not a literal. -/
def stuck {α : Type} : M α := ExceptT.lift none

/-- An `Except` result as a step. -/
def ofExcept {α : Type} (x : Except String α) : M α := ExceptT.mk (some x)

/-- Head beta through metadata at the head. -/
def headBetaM (fuel : Nat) (e : Expr) : Except String Expr :=
  let e := e.consumeMData
  let f := e.getAppFn.consumeMData
  if f.isLambda && e.getAppNumArgs > 0 then
    match fuel with
    | 0 => .error (fuelMsg "headBetaM" headBetaLimit "head beta-steps")
    | fuel + 1 => headBetaM fuel (f.beta e.getAppArgs)
  else .ok e

/-- Head beta, then `T.casesOn` on a constructor literal, repeatedly; stuck
when a `casesOn` meets a major premise that is not a constructor. -/
def iota (env : Environment) (natLit? : Expr → Option Nat) (fuel : Nat) (e : Expr) :
    M Expr :=
  match fuel with
  | 0 => stuck
  | fuel + 1 => do
  let e ← ofExcept (headBetaM headBetaLimit e)
  match e.getAppFn with
  | .const n ls =>
    match n with
    -- the auxiliary `casesOn` of overlapping patterns: its definition
    | .str _ s =>
      if s.startsWith "_sparseCasesOn" then
        match env.find? n with
        | some (.defnInfo d) =>
          iota env natLit? fuel
            (mkAppN (d.value.instantiateLevelParams d.levelParams ls) e.getAppArgs)
        | _ => pure e
      -- a recursor on a constructor: its rule (the kernel's iota)
      else if s == "rec" then
        match env.find? n with
        | some (.recInfo rv) =>
          let args := e.getAppArgs
          let majorIdx := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices
          if args.size <= majorIdx then stuck else
          let (cv, fields) ← ctorApp? env natLit? args[majorIdx]!
          let some rule := rv.rules.find? (·.ctor == cv.name) | stuck
          let rhs := rule.rhs.instantiateLevelParams rv.levelParams ls
          let pre := args.extract 0 (rv.numParams + rv.numMotives + rv.numMinors)
          let rest := args.extract (majorIdx + 1) args.size
          iota env natLit? fuel (mkAppN (mkAppN (mkAppN rhs pre) fields) rest)
        | _ => pure e
      else if s == "casesOn" then
        match n with
        | .str T _ =>
          match env.find? T with
          | some (.inductInfo iv) =>
            let args := e.getAppArgs
            -- params, motive, indices, major, one alternative per constructor
            let majorIdx := iv.numParams + 1 + iv.numIndices
            let altsStart := majorIdx + 1
            if args.size < altsStart + iv.ctors.length then stuck else
            let (cv, fields) ← ctorApp? env natLit? args[majorIdx]!
            let alt := args[altsStart + cv.cidx]!
            let rest := args.extract (altsStart + iv.ctors.length) args.size
            iota env natLit? fuel (mkAppN (mkAppN alt fields) rest)
          | _ => pure e
        | _ => pure e
      else pure e
    | _ => pure e
  | _ => pure e

/-- A matcher application, reduced by unfolding the matcher (its `casesOn`
tree) on constructor discriminants. -/
def reduceMatcher? (env : Environment) (natLit? : Expr → Option Nat) (e : Expr) : M Expr := do
  let .const n ls := e.getAppFn | stuck
  if !Lean.Meta.isMatcherCore env n then stuck else
  let some (.defnInfo d) := env.find? n | stuck
  let v := d.value.instantiateLevelParams d.levelParams ls
  let r ← iota env natLit? 256 (mkAppN v e.getAppArgs)
  -- reduced: no `casesOn` left at the head
  match r.getAppFn with
  | .const (.str _ s) _ =>
    if s == "casesOn" || s == "rec" || s.startsWith "_sparseCasesOn" then stuck else pure r
  | _ => pure r

/-- The value with every matcher at the head of a `let`-free spine reduced,
when the matchers' discriminants are constructors; stuck when one is not. -/
def reduceHead (env : Environment) (natLit? : Expr → Option Nat) (fuel : Nat) (e : Expr) :
    M Expr :=
  match fuel with
  | 0 => stuck
  | fuel + 1 => do
  let e ← ofExcept (headBetaM headBetaLimit e)
  match e with
  | .letE n t v b nd => do
    let b' ← reduceHead env natLit? fuel b
    pure (.letE n t v b' nd)
  | _ =>
    if Lean.Meta.isMatcherCore env (e.getAppFn.constName?.getD .anonymous) then
      let r ← reduceMatcher? env natLit? e
      reduceHead env natLit? fuel r
    else pure e

mutual
/-- Beta everywhere (the spine's arguments and the node itself).  Recursion on a
subterm keeps the fuel; the re-entry after a head beta consumes one. -/
def betaAll (fuel : Nat) : Expr → Except String Expr
  | .app f a => do
    let (h, args) ← betaSpine fuel f
    let a' ← betaAll fuel a
    let e' := mkAppN h (args.push a')
    if h.consumeMData.isLambda then
      match fuel with
      | 0 => .error (fuelMsg "betaAll" betaAllLimit "re-entries after a head beta")
      | fuel + 1 => do
        let e'' ← headBetaM headBetaLimit e'
        betaAll fuel e''
    else pure e'
  | .lam n t b bi => do pure (.lam n t (← betaAll fuel b) bi)
  | .letE n t v b nd => do pure (.letE n t (← betaAll fuel v) (← betaAll fuel b) nd)
  | .mdata m b => do pure (.mdata m (← betaAll fuel b))
  | e => pure e
termination_by e => (fuel, sizeOf e, 0)

/-- The head and the arguments (in order) of an application spine, each `betaAll`. -/
def betaSpine (fuel : Nat) : Expr → Except String (Expr × Array Expr)
  | .app f a => do
    let (h, args) ← betaSpine fuel f
    let a' ← betaAll fuel a
    pure (h, args.push a')
  | h => do pure (← betaAll fuel h, #[])
termination_by e => (fuel, sizeOf e, 1)
end

/-- One call of a recursive user helper (`isUser`), unfolded through its
smart-unfolding body when its match reduces. -/
def unfoldCall? (env : Environment) (natLit? : Expr → Option Nat) (isUser : Name → Bool)
    (e : Expr) : M Expr := do
  let .const n ls := e.getAppFn | stuck
  if !isUser n then stuck else
  let some (.defnInfo d) := env.find? (Lean.Meta.mkSmartUnfoldingNameFor n) | stuck
  let v := d.value.instantiateLevelParams d.levelParams ls
  let r ← reduceHead env natLit? 64 (v.beta e.getAppArgs)
  let r' ← ofExcept (betaAll betaAllLimit r)
  pure r'

/-! ## Closed literal data

The data a recursive helper walks is often computed by library functions on
literals (`table.toList.zipIdx` of an array literal, `table.size == 0`). These
are evaluated here — to the literal the kernel computes too. -/

/-- A literal list (through closed `let`s, `List.toArray`/`Array.toList`,
`List.zipIdx`): its element type and elements.  Stuck when `e` is not one.  The
shapes are matched as applications (`f a b` = `.app (.app f a) b`), which is what
`getAppFn` / `getAppArgs` of the exact length give. -/
def listLit? (natLit? : Expr → Option Nat) (fuel : Nat) (e : Expr) :
    M (Expr × List Expr) :=
  match e with
  | .mdata _ b => listLit? natLit? fuel b
  | .letE _ _ v b _ =>
    if v.hasLooseBVars then stuck else
    match fuel with
    | 0 => ExceptT.mk (some (.error (fuelMsg "listLit?" listLitLimit "let zeta-steps")))
    | fuel + 1 => listLit? natLit? fuel (b.instantiate1 v)
  | .app (.const ``List.nil _) α => pure (α, [])
  | .app (.app (.app (.const ``List.cons _) α) a) rest => do
    let (_, xs) ← listLit? natLit? fuel rest
    pure (α, a :: xs)
  | .app (.app (.const ``Array.toList _) _) a => listLit? natLit? fuel a
  | .app (.app (.const ``List.toArray _) _) l => listLit? natLit? fuel l
  | .app (.app (.const ``Array.mk _) _) l => listLit? natLit? fuel l
  | .app (.app (.app (.const ``List.zipIdx _) α) l) n => do
    let (_, xs) ← listLit? natLit? fuel l
    let n0 ← natLit? n
    let pair := mkApp2 (.const ``Prod [.zero, .zero]) α (.const ``Nat [])
    pure (pair, xs.zipIdx.map fun (a, i) =>
      mkApp4 (.const ``Prod.mk [.zero, .zero]) α (.const ``Nat []) a (natLitE (i + n0)))
  | _ => stuck

/-- A literal list as `List.cons` … `List.nil`. -/
def mkListLit (α : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun a rest => mkApp3 (.const ``List.cons [.zero]) α a rest) (mkApp (.const ``List.nil [.zero]) α)

/-- A closed `Nat` (a literal, the size of a literal array or list). -/
def natVal? (natLit? : Expr → Option Nat) (e : Expr) : M Nat :=
  match natLit? e with
  | some n => pure n
  | none =>
    match e.getAppFn, e.getAppArgs with
    | .const ``Array.size _, #[_, a] => do
      let (_, xs) ← listLit? natLit? listLitLimit a
      pure xs.length
    | .const ``List.length _, #[_, l] => do
      let (_, xs) ← listLit? natLit? listLitLimit l
      pure xs.length
    | _, _ => stuck

/-- A closed `Bool`: a literal or `==` of closed `Nat`s. -/
def boolVal? (natLit? : Expr → Option Nat) (e : Expr) : M Bool :=
  match e.consumeMData with
  | .const ``Bool.true _ => pure true
  | .const ``Bool.false _ => pure false
  | e =>
    match e.getAppFn, e.getAppArgs with
    | .const ``BEq.beq _, #[ty, _, a, b] =>
      if ty.isConstOf ``Nat then do
        let x ← natVal? natLit? a
        let y ← natVal? natLit? b
        pure (x == y)
      else stuck
    | _, _ => stuck

/-- One node of closed literal evaluation. -/
def evalNode? (natLit? : Expr → Option Nat) (e : Expr) : M Expr :=
  match e.getAppFn, e.getAppArgs with
  -- `if c = true then a else b` on a closed `c`
  | .const ``ite _, #[_, c, _, a, b] =>
    match c.consumeMData.getAppFn, c.consumeMData.getAppArgs with
    | .const ``Eq _, #[ty, x, y] =>
      if !ty.isConstOf ``Bool then stuck else do
      let vx ← boolVal? natLit? x
      let vy ← boolVal? natLit? y
      pure (if vx == vy then a else b)
    | _, _ => stuck
  | .const ``List.zipIdx _, _ => do
    let (α, xs) ← listLit? natLit? listLitLimit e
    pure (mkListLit α xs)
  | .const ``Array.toList _, _ => do
    let (α, xs) ← listLit? natLit? listLitLimit e
    pure (mkListLit α xs)
  | .const ``List.headD _, #[_, l, d] => do
    let (_, xs) ← listLit? natLit? listLitLimit l
    pure (xs.headD d)
  | _, _ => stuck

/-- The pass's state: the memo of rewritten subterms.  An exhaustion is an
`error`, which leaves no entry for the cut-off computation. -/
abbrev PM := ExceptT String (StateM (Std.HashMap Expr Expr))

/-- A step as a pass step: stuck is `none`, an exhaustion is the pass's error. -/
def liftStep {α : Type} (x : M α) : PM (Option α) :=
  match x.run with
  | none => pure none
  | some (.ok a) => pure (some a)
  | some (.error m) => throw m

mutual
/-- Every reducible recursive call of `e` unfolded (and the unfolding's own
calls, while the literal data lasts), innermost first; closed literal data
evaluated, closed `let`s of literal data substituted. Memoised: the values
the front end sees are shared DAGs. -/
def passM (env : Environment) (natLit? : Expr → Option Nat) (isUser : Name → Bool)
    (fuel : Nat) (e : Expr) : PM Expr := do
  if let some r := (← get).get? e then return r
  let r ← passStep env natLit? isUser fuel e
  modify (·.insert e r)
  return r
termination_by (fuel, sizeOf e, 2)

/-- The rewrite of one node. -/
def passStep (env : Environment) (natLit? : Expr → Option Nat) (isUser : Name → Bool)
    (fuel : Nat) (e : Expr) : PM Expr :=
  match e with
  | .app f a => do
    let (h, args) ← passSpine env natLit? isUser fuel f
    let a' ← passM env natLit? isUser fuel a
    let e' := mkAppN h (args.push a')
    match ← liftStep (evalNode? natLit? e') with
    | some r =>
      match fuel with
      | 0 => throw (fuelMsg "passM" passLimit "re-entries on a rewritten value")
      | fuel + 1 => passM env natLit? isUser fuel r
    | none =>
    match ← liftStep (unfoldCall? env natLit? isUser e') with
    | some r =>
      match fuel with
      | 0 => throw (fuelMsg "passM" passLimit "re-entries on a rewritten value")
      | fuel + 1 => passM env natLit? isUser fuel r
    | none => pure e'
  | .lam n t b bi => return .lam n t (← passM env natLit? isUser fuel b) bi
  | .letE n t v b nd => do
    let v' ← passM env natLit? isUser fuel v
    -- a closed list `let` is substituted: the data a helper walks
    if !v'.hasLooseBVars && !v'.hasFVar &&
        (← liftStep (listLit? natLit? listLitLimit v')).isSome then
      match fuel with
      | 0 => throw (fuelMsg "passM" passLimit "re-entries on a substituted let")
      | fuel + 1 => passM env natLit? isUser fuel (b.instantiate1 v')
    else return .letE n t v' (← passM env natLit? isUser fuel b) nd
  | .mdata m b => return .mdata m (← passM env natLit? isUser fuel b)
  | e => pure e
termination_by (fuel, sizeOf e, 1)

/-- The head and the arguments (in order) of an application spine, each rewritten. -/
def passSpine (env : Environment) (natLit? : Expr → Option Nat) (isUser : Name → Bool)
    (fuel : Nat) (e : Expr) : PM (Expr × Array Expr) :=
  match e with
  | .app f a => do
    let (h, args) ← passSpine env natLit? isUser fuel f
    let a' ← passM env natLit? isUser fuel a
    pure (h, args.push a')
  | h => do pure (← passM env natLit? isUser fuel h, #[])
termination_by (fuel, sizeOf e, 3)
end

/-- Whether `e` has anything the pass acts on (a recursive user helper, or a
literal-data operation): otherwise the pass is skipped. -/
def relevant (isUser : Name → Bool) (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .const n _ => isUser n || n == ``List.zipIdx || n == ``Array.toList || n == ``List.headD
    | _ => false).isSome

/-- The pass from an empty memo; an `error` is a fuel exhaustion (the definition
and its limit), which the compiler reports as a compile error. -/
def pass (env : Environment) (natLit? : Expr → Option Nat) (isUser : Name → Bool) (e : Expr) :
    Except String Expr :=
  (passM env natLit? isUser passLimit e).run.run' {}

/-- Whether the constants reachable from `e` through the user definitions it
unfolds (`defs`) include something the pass acts on — decided on the small
definition bodies, not on the (large) unfolded value. -/
def relevantClosure (defs : Name → Option Expr) (isUser : Name → Bool) (e : Expr) : Bool :=
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
