/-! SKETCH ONLY — not built, not registered in lakefile. Companion of
`docs/parallel/O-p5s-unfold-plan.md` (units U1, U3, U4). Names are proposals.

Candidate copy of `userInliner` (Sparkle/Compiler/Elab.lean 3387) whose behaviour
on `.forallE` inputs has equations, plus the statements to prove. Everything marked
`-- UNSURE` is a guess about elaboration details that the integrator's build decides. -/
import Sparkle.Compiler.Elab

namespace Tools.ShippingInlCand
open Lean Sparkle.Compiler.Elab
open Sparkle.Compiler.MachRecUnfold (passM relevantClosure evalNode? unfoldCall? listLit?)

/-! ## U1a: `passM` with fuel; at fuel 0 the ORIGINAL `partial` `passM`

At runtime the compiled `passM` is its body, so by induction on `n`,
`passF n e s = passM e s` on every input (including exhaustion, which runs the
original code): output-identical by construction. In the logic, `passF (n+1)` has
its equation; `passF 0` is the opaque original and is never reached on a
`.forallE` input. -/
def passF (env : Environment) (natLit? : Expr → Option Nat) (isUser : Name → Bool) :
    Nat → Expr → StateM (Std.HashMap Expr Expr) Expr
  | 0, e => passM env natLit? isUser e
  | n + 1, e => do
    if let some r := (← get).get? e then return r
    let r ← match e with
      | .app .. => do
        let f ← passF env natLit? isUser n e.getAppFn
        let args ← e.getAppArgs.mapM (passF env natLit? isUser n)  -- UNSURE: structural through mapM; else `termination_by n`
        let e' := mkAppN f args
        match evalNode? natLit? e' with
        | some r => passF env natLit? isUser n r
        | none =>
        match unfoldCall? env natLit? isUser e' with
        | some r => passF env natLit? isUser n r
        | none => pure e'
      | .lam nm t b bi => return .lam nm t (← passF env natLit? isUser n b) bi
      | .letE nm t v b nd => do
        let v' ← passF env natLit? isUser n v
        if !v'.hasLooseBVars && !v'.hasFVar && (listLit? natLit? v').isSome then
          passF env natLit? isUser n (b.instantiate1 v')
        else return .letE nm t v' (← passF env natLit? isUser n b) nd
      | .mdata m b => return .mdata m (← passF env natLit? isUser n b)
      | e => pure e
    modify (·.insert e r)
    return r

/-- Recursion-depth budget; exhaustion falls back to `passM` (identical output). -/
def passDepth : Nat := 1000000

def passT (env : Environment) (natLit? : Expr → Option Nat) (isUser : Name → Bool) (e : Expr) :
    Expr :=
  (passF env natLit? isUser passDepth e |>.run' {})

/-! ## U1b: abbreviation step with a structural replace on `.forallE` inputs (G1 guard) -/

/-- G1: library constants the reading positions of `declOuts?` / `machResultKind?`
contain as `.const c []`. In a real environment none is a user abbreviation
(`inlUserModule` is false for `Init`), so excluding them changes nothing. -/
def inlLibConsts : List Name := [``BitVec, ``Bool, ``Nat, ``instOfNatNat]

def userAbbrevC? (env : Environment) (n : Name) : Option Expr :=
  if inlLibConsts.contains n then none else userAbbrev? env n

def abbrevFn (env : Environment) : Expr → Option Expr := fun x => match x with
  | .const c [] => userAbbrevC? env c
  | _ => none

/-- `Expr.replace` (extern `replaceImpl`) on values; `Expr.replaceNoCache`
(structural) on `.forallE` inputs (types: small, no DAG blow-up). -/
def abbrevStep (env : Environment) (e : Expr) : Expr :=
  if e.isForall then e.replaceNoCache (abbrevFn env) else e.replace (abbrevFn env)

def inlAbbrevsC (env : Environment) : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e =>
    let e' := abbrevStep env e
    if e' == e then e else inlAbbrevsC env n e'.headBeta

/-! ## U1c: the candidate inliner (verbatim structure of `userInliner`) -/

def userInlinerC (env : Environment) : Expr → Expr := fun e =>
  let inl (e : Expr) : Expr :=
    match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
    | some (e', _) => e'
    | none => e
  let isRec (n : Name) : Bool :=
    inlUserModule env n && !Sparkle.Compiler.isHardwareModule env n &&
      env.contains (Lean.Meta.mkSmartUnfoldingNameFor n)
  let rec rounds : Nat → Expr → Expr
    | 0, e => e
    | k + 1, e =>
      let e' := passT env canonicalNatLitValue? isRec e
      if e' == e then e else rounds k (inl e')
  let e1 := inl e
  if relevantClosure (userDefinition? env) isRec e then
    inlFoldNat (inlAbbrevsC env 4 (rounds 64 e1))
  else inlFoldNat (inlAbbrevsC env 4 e1)

/-! ## U3: Expr facts (statements) -/

theorem inlineDefs_forall (defs projs) (n : Name) (d b : Expr) (bi : BinderInfo) :
    inlineDefs defs projs inlineDepth (.forallE n d b bi) inlineBudget =
      some (.forallE n d b bi, inlineBudget) := by
  sorry -- U3: unfold; `inlSpine (.forallE ..) [] = (.forallE .., [])`, last match arm, `inlMap [] b = some ([], b)`

theorem passT_forall (env natLit? isUser) (n : Name) (d b : Expr) (bi : BinderInfo) :
    passT env natLit? isUser (.forallE n d b bi) = .forallE n d b bi := by
  sorry -- U3: `passDepth = k+1`; `Std.HashMap.getElem?_empty` (only BEq/Hashable needed, v4.32.1 HashMap/Lemmas.lean 256)

/-- `rounds` fixes a `.forallE` input, whatever the opaque `==` answers (case split
on the Bool, induction on `k`). -/
theorem rounds_forall (env : Environment) (k : Nat) (e : Expr) (hf : e.isForall = true) :
    userInlinerC.rounds env k e = e := by  -- UNSURE: the auxiliary's exact name/arguments
  sorry

theorem headBeta_forall (e : Expr) (hf : e.isForall = true) : e.headBeta = e := by
  sorry -- U3: `getAppFn` of a forallE is itself; `isHeadBetaTargetFn false (.forallE ..) = false`

theorem replaceNoCache_isForall (f : Expr → Option Expr) (hf : ∀ n d b bi, f (.forallE n d b bi) = none)
    (e : Expr) (he : e.isForall = true) : (e.replaceNoCache f).isForall = true := by
  sorry

/-! ## U4: the reading lemmas (the core) -/

/-- L2 (result kind, discharges `P5At` on `.forallE` types). No environment premise. -/
theorem resKind_userInlinerC (env : Environment) (ty : Expr) (hf : ty.isForall = true)
    {k : MixedGateBinder} (h : machResultKind? ty = some k) :
    machResultKind? (userInlinerC env ty) = some k := by
  sorry

/-- L1 (output list, used for `p5s`). `hNS` / `hSum` are removed by guard G2
(`userStructure?` excludes `Signal`, `HAdd.hAdd`, `HSub.hSub`). -/
theorem declOuts_userInlinerC (env : Environment) (ty : Expr) (hf : ty.isForall = true)
    (hNS : (structEnv env).fields ``Sparkle.Core.Signal.Signal = none)
    (hSum : ∀ s ls, (Tools.ShippingCallWidthsStructRes.resBody ty).getAppFn = .const s ls →
      s ≠ ``HAdd.hAdd ∧ s ≠ ``HSub.hSub)
    {o} (h : Tools.ShippingMachineShapeUnfold.declOuts? (structEnv env) ty = some o) :
    Tools.ShippingMachineShapeUnfold.declOuts? (structEnv env) (userInlinerC env ty) = some o := by
  sorry

end Tools.ShippingInlCand
