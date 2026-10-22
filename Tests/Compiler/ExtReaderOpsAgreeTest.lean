import Tools.Prototype.ExtReaderGlue
import Tests.Compiler.ExtModelAgreeTest

/-! # EXT2: EXECUTED agreement of the shipped operations with the models used by the model reader `machineShapeXM`

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.ExtReaderOpsAgreeTest`; not in `Tests.AllTests`). EVIDENCE only, NOT a proof:
nothing here discharges a premise (the model reader's theorem has none to discharge; these checks say how close the models are to the
shipped operations on a finite grid). Compared: `eqvX` vs `Expr.eqv` (`==`) on all pairs of a grid with binder names / binder infos /
`nonDep` / `mdata` payloads / levels / literals; `rootFloatS` vs `rootFloat`; `zeroLitM` vs `zeroLit`; `zetaAllM` vs `zetaAll`; `rawNodeX
modelOps` and `rawNodeX shippedOps` vs `rawNode` on raw-surface nodes. Every comparison THROWS on a difference; each section asserts a
minimum number of non-trivial cases. -/
namespace Tests.Compiler.ExtReaderOpsAgreeTest
open Lean Tools.Prototype.ExtReader Tests.Compiler.ExtModelAgreeTest
open Sparkle.Compiler.Elab

def u : Level := .param `u
def md1 : MData := (KVMap.empty).insert `k (DataValue.ofNat 1)
def md2 : MData := (KVMap.empty).insert `k (DataValue.ofNat 2)

def eqvGrid : List Expr := grid ++
  [ .mdata md1 f1, .mdata md2 f1, .mdata {} f1, .mdata md1 (.mdata md2 f1),
    .sort .zero, .sort (.succ .zero), .sort u, .sort (.max u (.succ .zero)), .sort (.imax u .zero),
    .const `g [], .const `g [.zero], .const `g [u], .const `g [u, .zero], .const `h [],
    .lit (.natVal 1), .lit (.natVal 2), .lit (.strVal "a"), .lit (.strVal "b"),
    .mvar ⟨`m⟩, .mvar ⟨`n⟩, .fvar ⟨`x⟩, .fvar ⟨`y⟩,
    .lam `x f1 (b 0) .default, .lam `y f1 (b 0) .default, .lam `x f1 (b 0) .implicit, .lam `x f1 (b 1) .default,
    .forallE `x f1 (b 0) .default, .forallE `x f1 (b 0) .instImplicit,
    .letE `x f1 (b 0) (b 0) true, .letE `x f1 (b 0) (b 0) false, .letE `y f1 (b 0) (b 0) false,
    .proj `A 0 f1, .proj `B 0 f1, .proj `A 1 f1,
    .app (.mdata md1 f1) (b 0), .app f1 (.mdata md1 (b 0)) ]

def runEqv : IO Unit := do
  let mut trues := 0
  let mut falses := 0
  let mut nonSyn := 0
  let mut diffs : List String := []
  for a in eqvGrid do
    for c in eqvGrid do
      let r := a == c
      if r != eqvX a c then diffs := s!"{a} / {c}: real {r} model {eqvX a c}" :: diffs
      if r then
        trues := trues + 1
        unless a.equal c do nonSyn := nonSyn + 1
      else falses := falses + 1
  IO.println s!"EXT2 EQV AGREEMENT: pairs={trues + falses} equal={trues} unequal={falses} alpha-only-equal={nonSyn} differences={diffs.length}"
  unless diffs.isEmpty do throw (IO.userError s!"eqv differs ({diffs.length}); first: {diffs.take 12}")
  unless trues ≥ eqvGrid.length && falses ≥ 100 && nonSyn ≥ 3 do throw (IO.userError "vacuous eqv grid")

#eval runEqv

def optEq : Option Expr → Option Expr → Bool
  | none, none => true
  | some a, some c => a.equal c
  | _, _ => false

def runRoot : IO Unit := do
  let mut ch := 0
  for e in rootCases ++ grid do
    let r := Sparkle.Compiler.MachRawSurface.rootFloat e
    unless r.equal (rootFloatM e) do throw (IO.userError s!"rootFloat differs on {e}")
    unless r.equal e do ch := ch + 1
  IO.println s!"EXT2 ROOTFLOAT AGREEMENT: cases={(rootCases ++ grid).length} changed={ch}"
  unless ch ≥ 4 do throw (IO.userError "vacuous rootFloat grid")

#eval runRoot

def bz (w : Nat) : Expr := .app (.const ``BitVec.zero []) (inlNatLit w)

def zeroCases : List Expr :=
  [ bz 8, .app f1 (bz 4), .lam `x (bz 3) (.app (bz 2) (b 0)) .default, .app (.const ``BitVec.zero []) (b 0),
    .letE `x f1 (bz 5) (bz 6) false, nat 1, .mdata {} (bz 7), .app (.const ``BitVec.zero []) (.app f1 (bz 1)) ]

def runZero : IO Unit := do
  let mut ch := 0
  for e in zeroCases do
    let r := Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e
    unless r.equal (zeroLitM e) do throw (IO.userError s!"zeroLit differs on {e}")
    unless r.equal e do ch := ch + 1
  IO.println s!"EXT2 ZEROLIT AGREEMENT: cases={zeroCases.length} changed={ch}"
  unless ch ≥ 5 do throw (IO.userError "vacuous zeroLit grid")

#eval runZero

def zetaCases : List Expr :=
  [ .letE `x f1 (nat 1) (.app (b 0) (b 0)) false, .letE `x f1 (nat 1) (.letE `y f1 (b 0) (.app (b 0) (b 1)) false) false,
    .app (.letE `x f1 (nat 1) (b 0) false) (.letE `y f1 (nat 2) (b 0) false), f1, b 0,
    .lam `x f1 (.letE `y f1 (nat 2) (b 0) false) .default ]

def runZeta : IO Unit := do
  let mut ch := 0
  for e in zetaCases do
    let r := Sparkle.Compiler.MachRawSurface.zetaAll e
    unless r.equal (zetaAllM e) do throw (IO.userError s!"zetaAll differs on {e}")
    unless r.equal e do ch := ch + 1
  IO.println s!"EXT2 ZETAALL AGREEMENT: cases={zetaCases.length} changed={ch}"
  unless ch ≥ 3 do throw (IO.userError "vacuous zetaAll grid")

#eval runZeta

/-! ## raw-surface nodes -/

def circ : Expr := mkApp2 (.const ``Sparkle.Core.Circuit []) f1 (nat 7)
def tyA : Expr := .const `A []
def punit : Expr := .const ``PUnit [.succ .zero]
def lamBody : Expr := .lam `a tyA (.app (b 1) (b 0)) .default
def elems : Expr :=
  mkApp3 (.const ``List.cons []) tyA (b 3) (mkApp3 (.const ``List.cons []) tyA (b 4) (.app (.const ``List.nil []) tyA))
def forM : Expr := mkAppN (.const ``List.forM []) #[circ, f1, tyA, elems, lamBody]
def matcherAlt : Expr := .lam `p tyA (.lam `q (b 0) (.app (b 1) (.app (b 0) (b 2))) .default) .default

def rawCases : List (String × Expr) :=
  [ ("read", mkAppN (.const ``Sparkle.Core.Circuit.read []) #[f1, nat 1, tyA, nat 2, b 0]),
    ("bind", mkAppN (.const ``Bind.bind []) #[circ, mkApp2 (.const ``Monad.toBind []) circ f1, tyA, tyA, b 0, b 1]),
    ("bind-not-circuit", mkAppN (.const ``Bind.bind []) #[tyA, mkApp2 (.const ``Monad.toBind []) circ f1, tyA, tyA, b 0, b 1]),
    ("pure", mkAppN (.const ``Pure.pure []) #[circ, mkApp2 (.const ``Applicative.toPure []) circ f1, tyA, b 0]),
    ("circuit-bind-forM", mkAppN (.const ``Sparkle.Core.Circuit.bind []) #[f1, nat 7, tyA, tyA, forM, .lam `u punit (b 2) .default]),
    ("forM", forM),
    ("matcher", mkAppN (.const `mat []) #[tyA, b 0, matcherAlt]),
    ("matcher-bad-arity", mkAppN (.const `mat []) #[tyA, b 0]),
    ("other", .app f1 (b 0)) ]

def pm : Name → Option Nat := fun n => if n == `mat then some 2 else none

def runRaw : IO Unit := do
  let mut some_ := 0
  for (nm, e) in rawCases do
    let r := Sparkle.Compiler.MachRawSurface.rawNode pm e
    unless optEq r (rawNodeX shippedOps pm e) do throw (IO.userError s!"rawNodeX shippedOps differs on {nm}")
    unless optEq r (rawNodeX modelOps pm e) do throw (IO.userError s!"rawNodeX modelOps differs on {nm}: real {r} model {rawNodeX modelOps pm e}")
    if r.isSome then some_ := some_ + 1
  IO.println s!"EXT2 RAWNODE AGREEMENT: cases={rawCases.length} rewritten={some_}"
  unless some_ ≥ 6 do throw (IO.userError "vacuous rawNode grid")

#eval runRaw

end Tests.Compiler.ExtReaderOpsAgreeTest
