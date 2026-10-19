import Sparkle.Compiler.Elab

/-! # Candidate copy of the front-end inliner with equations on `∀` types (unit U1c)

UNBUILT at the time of writing (worker O-INLC, branch par/o-inlc, base a230f9d1; written without
running Lean). ISOLATED CANDIDATE: nothing in `Sparkle/Compiler` is changed, no production name is
redirected, `userInliner` (Sparkle/Compiler/Elab.lean 3387) is untouched. Plan:
`docs/parallel/O-p5s-unfold-plan.md` option (a′), first vertical increment U1c + U3 + U4-L2 + U5a.

What differs from the production `userInliner`, and what is (and is NOT) claimed about it:

* `passF` replaces the `partial` `MachRecUnfold.passM` by a fuel recursion whose fuel-0 case IS the
  original `passM`. `passF n e s = passM e s` is a RUNTIME COMPATIBILITY ARGUMENT ONLY (a compiled
  `partial def` executes its body; induction on `n` over identical memo operations). It is NOT a
  kernel equivalence: `passM` is an opaque constant in the logic, so no such theorem exists or is
  claimed here.
* `abbrevStep` uses the STRUCTURAL `Lean.Expr.replaceNoCache` on `∀` inputs and the cached extern
  `Lean.Expr.replace` (`replaceImpl`, `@[extern "lean_replace_expr"] opaque`) otherwise. Agreement
  `replaceNoCache f e = replace f e` is OPEN: no claim is made (the extern has no logical content).
* `roundsC` / `inlC` / `isRecC` are the `let` / `let rec` locals of `userInliner` lifted to top-level
  definitions (same computation; the lifting itself is a source-level refactoring, not a theorem).
* NO exclusion guard (G1 / G2 of the plan) is in these definitions: `userAbbrev?` and
  `userStructure?` are used exactly as in production. Where the proofs need the library constants of
  the reading positions not to be user abbreviations, that is an EXPLICIT environment premise
  (`ReadConstsPlain env`, localisation, not elimination).

No `sorry`, no axiom, no `native_decide`. Nothing is added to `RefLaws` or any trust / allowed-premise
list. -/
namespace Tools.ShippingInlCand
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachRecUnfold (passM relevantClosure evalNode? unfoldCall? listLit?)

/-! ## `passM` with fuel; at fuel 0 the ORIGINAL `partial` `passM` -/

/-- The body of `MachRecUnfold.passM` (MachRecUnfold.lean 243) with its recursive calls going to
fuel `n`, and the ORIGINAL `passM` at fuel 0.

Runtime compatibility (NOT a kernel theorem): at runtime a `partial def` runs its body, so by
induction on the fuel `passF n e s` performs the same memo reads/writes and returns the same value
as `passM e s` for every `n`, including exhaustion (which runs `passM` itself). In the logic `passM`
is opaque and only `passF (n+1)` has an equation. -/
def passF (env : Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Name → Bool) :
    Nat → Lean.Expr → StateM (Std.HashMap Lean.Expr Lean.Expr) Lean.Expr
  | 0, e => passM env natLit? isUser e
  | n + 1, e => do
    if let some r := (← get).get? e then return r
    let r ← match e with
      | .app .. => do
        let f ← passF env natLit? isUser n e.getAppFn
        let args ← e.getAppArgs.mapM (passF env natLit? isUser n)  -- UNSURE: structural through `mapM` (else WF; the proofs only use the equation lemmas)
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

/-- Recursion-depth budget of `passT`; exhaustion runs the original `passM` (runtime
compatibility argument only, see `passF`). -/
def passDepth : Nat := 1000000

/-- Candidate for `MachRecUnfold.pass` (MachRecUnfold.lean 276). Production starts from `{}`;
here the empty map is written `∅` (the `EmptyCollection` instance, same value). -/
def passT (env : Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Name → Bool)
    (e : Lean.Expr) : Lean.Expr :=
  (passF env natLit? isUser passDepth e).run' (∅ : Std.HashMap Lean.Expr Lean.Expr)

/-! ## The abbreviation step: structural replace on `∀` inputs (NO guard) -/

/-- The replacement function of production `inlAbbrevs` (Elab.lean 3379–3381), named. -/
def abbrevFn (env : Environment) : Lean.Expr → Option Lean.Expr
  | .const c [] => userAbbrev? env c
  | _ => none

/-- Structural `replaceNoCache` on `∀` inputs (types: small trees), the cached extern
`Expr.replace` on everything else (values: shared DAGs). `replaceNoCache f e = replace f e` is
OPEN (no claim): this is a behaviour change on `∀` inputs whose equivalence is not shown. -/
def abbrevStep (env : Environment) (e : Lean.Expr) : Lean.Expr :=
  if e.isForall then e.replaceNoCache (abbrevFn env) else e.replace (abbrevFn env)

/-- Production `inlAbbrevs` (Elab.lean 3376) with `abbrevStep` for the replace. -/
def inlAbbrevsC (env : Environment) : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, e =>
    let e' := abbrevStep env e
    if e' == e then e else inlAbbrevsC env n e'.headBeta

/-! ## The candidate inliner (production structure, locals lifted) -/

/-- The `inl` local of `userInliner`. -/
def inlC (env : Environment) (e : Lean.Expr) : Lean.Expr :=
  match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
  | some (e', _) => e'
  | none => e

/-- The `isRec` local of `userInliner`. -/
def isRecC (env : Environment) (n : Name) : Bool :=
  inlUserModule env n && !Sparkle.Compiler.isHardwareModule env n &&
    env.contains (Lean.Meta.mkSmartUnfoldingNameFor n)

/-- The `let rec rounds` of `userInliner`, with `passT` for `MachRecUnfold.pass`. -/
def roundsC (env : Environment) : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | k + 1, e =>
    let e' := passT env canonicalNatLitValue? (isRecC env) e
    if e' == e then e else roundsC env k (inlC env e')

/-- **Candidate `userInliner`.** Same branches as production (`relevantClosure` is still the
production `partial def`: proofs case-split on its Bool and never need its value). -/
def userInlinerC (env : Environment) (e : Lean.Expr) : Lean.Expr :=
  let e1 := inlC env e
  if relevantClosure (userDefinition? env) (isRecC env) e then
    inlFoldNat (inlAbbrevsC env 4 (roundsC env 64 e1))
  else inlFoldNat (inlAbbrevsC env 4 e1)

/-- **Localisation premise (explicit, NOT a guard).** The library constants that occur at the
reading positions of `machResultKind?` (`Signal`, `Bool`, `BitVec`, and the canonical `Nat`
literal `OfNat.ofNat Nat n (instOfNatNat n)`) are not user abbreviations of `env`. In a real
environment these come from `Init` / `Sparkle`, so `inlUserModule` is false for them and
`userAbbrev?` returns `none`; that is NOT proved here (the environment is abstract), so the fact is
a premise of every lemma that needs it. -/
structure ReadConstsPlain (env : Environment) : Prop where
  signal : userAbbrev? env ``Sparkle.Core.Signal.Signal = none
  bool : userAbbrev? env ``Bool = none
  bitVec : userAbbrev? env ``BitVec = none
  ofNat : userAbbrev? env ``OfNat.ofNat = none
  nat : userAbbrev? env ``Nat = none
  instOfNatNat : userAbbrev? env ``instOfNatNat = none

end Tools.ShippingInlCand
