import Tools.Prototype.ExtModelLetOk

/-! # EXT: EXECUTED agreement of the shipped extern / partial operations with their kernel-visible MODELS

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.ExtModelAgreeTest`; not in `Tests.AllTests`). EVIDENCE only, not a proof: the premises
`LiftCorr`, `LowerCorr`, `Inst1Corr`, `BetaCorr`, `EqvCorr`, `RootFloatCorr` stay PREMISES. A finite hand-written grid of `Expr`s (loose
variables under binders, `mdata`, `proj`, `let`, nested `let`s in value position, `let` as the last application argument) is run through the
shipped operation and the model; the outputs are compared with `Expr.equal` (structural, binder names included). -/
namespace Tests.Compiler.ExtModelAgreeTest
open Lean Tools.Prototype.ExtModelLetOk

def nat (n : Nat) : Expr := .lit (.natVal n)
def b (i : Nat) : Expr := .bvar i
def f1 : Expr := .const `f []

def grid : List Expr :=
  [ b 0, b 1, b 3, f1, nat 4, .app f1 (b 0), .app (b 2) (.app (b 0) (b 5)),
    .lam `x f1 (.app (b 0) (b 1)) .default,
    .lam `x (b 0) (.lam `y (b 1) (.app (b 0) (.app (b 1) (b 2))) .default) .default,
    .forallE `x (b 0) (.app (b 1) (b 0)) .default,
    .letE `x (b 0) (.app (b 1) (b 0)) (.app (b 0) (.app (b 1) (b 2))) false,
    .mdata {} (.app (b 0) (b 2)), .proj `Prod 1 (.app (b 0) (b 3)),
    .lam `x f1 (.mdata {} (.letE `y (b 0) (b 1) (.lam `z (b 2) (b 3) .default) true)) .default ]

def probe : IO Unit := do
  for (s, d) in [(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (3, 2)] do
    IO.println s!"lower probe s={s} d={d}: real {(b 1).lowerLooseBVars s d} / {(b 2).lowerLooseBVars s d} / {(b 3).lowerLooseBVars s d}; model {lowerM (b 1) s d} / {lowerM (b 2) s d} / {lowerM (b 3) s d}"

#eval probe

def run : IO Unit := do
  let mut cnt := 0
  let mut changed := 0
  for e in grid do
    for s in [0, 1, 2] do
      for d in [0, 1, 2] do
        unless (e.liftLooseBVars s d).equal (liftM e s d) do throw (IO.userError s!"lift differs {e} {s} {d}")
        unless (e.lowerLooseBVars s d).equal (lowerM e s d) do throw (IO.userError s!"lower differs {e} {s} {d}: real {e.lowerLooseBVars s d} model {lowerM e s d}")
        cnt := cnt + 2
        unless (e.liftLooseBVars s d).equal e do changed := changed + 1
    for a in grid do
      unless (e.instantiate1 a).equal (inst1M e a 0) do throw (IO.userError s!"instantiate1 differs {e} {a}")
      unless (e.beta #[a]).equal (betaM e a) do throw (IO.userError s!"beta differs {e} {a}")
      cnt := cnt + 2
      unless (e.instantiate1 a).equal e do changed := changed + 1
      if (e == a) && !eqvM e a then throw (IO.userError "eqv: == without eqvM")
      -- the converse (eqvM without ==) is expected for mdata payloads / binder names: reported, not asserted
  -- `eqv` ignoring binder names (a == b although names differ) must be covered by the model
  let l1 := Expr.lam `a f1 (b 0) .default
  let l2 := Expr.lam `c f1 (b 0) .default
  unless (l1 == l2) && eqvM l1 l2 do throw (IO.userError "binder-name case")
  IO.println s!"EXT AGREEMENT: lift/lower/instantiate1/beta comparisons={cnt}, nontrivial={changed}"
  unless changed ≥ 100 do throw (IO.userError "vacuous grid")

#eval run

/-- `rootFloat` vs `rootFloatN`: nested `let` in value position, `let` as last argument (loose-variable lifting exercised). -/
def rootCases : List Expr :=
  [ .letE `x f1 (.letE `y f1 (b 0) (.app (b 0) (b 1)) false) (.app (b 0) (b 1)) false,
    .letE `x (b 0) (.letE `y (b 1) (nat 1) (b 0) true) (.letE `z f1 (.letE `w f1 (b 1) (b 0) false) (b 2) false) false,
    .app f1 (.letE `x f1 (b 0) (.app (b 0) (b 3)) false),
    .app (b 2) (.letE `x (b 1) (.letE `y (b 0) (b 1) (b 2) false) (b 3) false),
    .letE `x f1 (nat 2) (.app (b 5) (.letE `y f1 (b 0) (b 1) false)) false, nat 3, b 0 ]

def runRoot : IO Unit := do
  let mut ch := 0
  for e in rootCases do
    match rootFloatN 1000 e with
    | none => throw (IO.userError s!"rootFloatN exhausted on {e}")
    | some m =>
      unless (Sparkle.Compiler.MachRawSurface.rootFloat e).equal m do throw (IO.userError s!"rootFloat differs {e}")
      unless m.equal e do ch := ch + 1
  IO.println s!"EXT ROOTFLOAT AGREEMENT: cases={rootCases.length}, changed-by-rootFloat={ch}"
  unless ch ≥ 4 do throw (IO.userError "vacuous rootFloat grid")

#eval runRoot

end Tests.Compiler.ExtModelAgreeTest
