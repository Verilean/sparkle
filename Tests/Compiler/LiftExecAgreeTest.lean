import Tools.Prototype.NormNodeModelLetOk

/-! # LC19: EXECUTED agreement of the shipped `machLiftScalarN` / `machNormNode` with `execLift` / `machNormNodeM`

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.LiftExecAgreeTest`; not in `Tests.AllTests`). EVIDENCE only, not a proof of
the production correspondence (`NodeCorr`, which stays OPEN): the grid is finite and hand-written. It re-runs LC17's grid against
the `partial_fixpoint` `execLift` (success AND refusal compared with `Expr.equal`), then compares the shipped node rewriter with the
isolated-path model on `Signal.map` nodes that reach the lift arm and the `boolMap` arm, asserting that those nodes are REWRITTEN
(output differs from the input), so the comparison is not vacuous. -/
namespace Tests.Compiler.LiftExecAgreeTest
open Lean Sparkle.Compiler.Elab Tools.Prototype.LiftExecLetOk Tools.Prototype.NormNodeModelLetOk
  Tools.Prototype.BoolMapModelLetOk

def senv : StructEnv := { proj := fun _ => none, fields := fun _ => none }
def bv (w : Nat) : Expr := mkApp (.const ``BitVec []) (inlNatLit w)
def dom : Expr := .const `dom []
def sig : Expr := .const `sig []
def k5 : Expr := machBVLit 8 5
def addI (w : Nat) : Expr :=
  mkApp2 (.const ``instHAdd [.zero]) (bv w) (mkApp (.const ``BitVec.instAdd []) (inlNatLit w))
def addE (w : Nat) (x y : Expr) : Expr :=
  mkApp6 (.const ``HAdd.hAdd [.zero, .zero, .zero]) (bv w) (bv w) (bv w) (addI w) x y
def appE (m n : Nat) (x y : Expr) : Expr :=
  mkApp6 (.const ``HAppend.hAppend [.zero, .zero, .zero]) (bv m) (bv n) (bv (m + n))
    (.const ``BitVec.instHAppendHAddNat []) x y
def beqI (ty : Expr) : Expr := mkApp2 (.const ``instBEqOfDecidableEq [.zero]) ty (.const `dec [])
def beqE (ty x y : Expr) : Expr := mkApp4 (.const ``BEq.beq [.zero]) ty (beqI ty) x y
def x0 : Expr := .bvar 0

def cases : List (String × Expr) :=
  [ ("var", x0), ("var-oob", .bvar 3), ("const", k5), ("const-bad", .const `junk []),
    ("add", addE 8 x0 k5), ("add-width", addE 4 x0 k5), ("add-oobvar", addE 8 (.bvar 2) k5),
    ("append-op", appE 8 8 x0 x0), ("append-mism", appE 4 8 x0 x0),
    ("BitVec.append", mkApp4 (.const ``BitVec.append []) (inlNatLit 8) (inlNatLit 8) x0 x0),
    ("extract", mkApp4 (.const ``BitVec.extractLsb' []) (inlNatLit 8) (inlNatLit 2) (inlNatLit 3) x0),
    ("extract-zext", mkApp4 (.const ``BitVec.extractLsb' []) (inlNatLit 8) (inlNatLit 0) (inlNatLit 12) x0),
    ("not", mkApp2 (.const ``BitVec.not []) (inlNatLit 8) x0),
    ("neg", mkApp3 (.const ``Neg.neg [.zero]) (bv 8) (.const `negI []) x0),
    ("compl", mkApp3 (.const ``Complement.complement [.zero]) (bv 8) (.const `cI []) x0),
    ("sext", mkApp3 (.const ``BitVec.signExtend []) (inlNatLit 8) (inlNatLit 12) x0),
    ("sext-bad", mkApp3 (.const ``BitVec.signExtend []) (inlNatLit 8) (inlNatLit 4) x0),
    ("sshr-const", mkApp3 (.const ``BitVec.sshiftRight []) (inlNatLit 8) x0 (inlNatLit 2)),
    ("sshr-var", mkApp3 (.const ``BitVec.sshiftRight []) (inlNatLit 8) x0 (mkApp2 (.const ``BitVec.toNat []) (inlNatLit 8) x0)),
    ("ashr", mkApp3 (.const ``Sparkle.Core.Signal.ashr []) (inlNatLit 8) x0 x0),
    ("sshr-big", mkApp3 (.const ``BitVec.sshiftRight []) (inlNatLit 8) x0 (inlNatLit 300)),
    ("nest", addE 8 (addE 8 x0 k5) (mkApp2 (.const ``BitVec.not []) (inlNatLit 8) x0)) ]

def eqO : Option (Nat × Expr) → Option (Nat × Expr) → Bool
  | none, none => true
  | some (w, a), some (w', b) => w == w' && a.equal b
  | _, _ => false

/-- a `Signal.map` node whose lambda body is `body` over a width-8 signal `sig` (to Bool when `toBool`). -/
def mapNode (body : Expr) (toBool : Bool) : Expr :=
  let tyB := if toBool then Expr.const ``Bool [] else bv 8
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero, .zero]) dom (bv 8) tyB
    (.lam `x (bv 8) body .default) sig

def run : IO Unit := do
  let vars := [(8, sig)]
  let mut some_ := 0
  let mut none_ := 0
  for (nm, e) in cases do
    let o := machLiftScalarN senv dom vars e
    let m := execLift senv dom vars e
    unless eqO o m do throw (IO.userError s!"DISAGREE on {nm}: {e}")
    if o.isSome then some_ := some_ + 1 else none_ := none_ + 1
  let nodes : List (String × Expr × Bool) :=
    [ ("map-neg", mapNode (mkApp3 (.const ``Neg.neg [.zero]) (bv 8) (.const `negI []) x0) false, true),
      ("map-ext", mapNode (mkApp4 (.const ``BitVec.append []) (inlNatLit 8) (inlNatLit 8) x0 x0) false, false),
      ("map-bool-beq", mapNode (beqE (bv 8) (addE 8 x0 k5) x0) true, true),
      ("map-bool-not", mapNode (mkApp (.const ``not []) (beqE (bv 8) x0 k5)) true, true) ]
  let mut rewritten := 0
  for (nm, e, mustRewrite) in nodes do
    let o := machNormNode senv e
    let m := machNormNodeM senv e
    unless o.equal m do throw (IO.userError s!"NODE DISAGREE on {nm}")
    if !o.equal e then rewritten := rewritten + 1
    else if mustRewrite then throw (IO.userError s!"node {nm} was not rewritten (vacuous)")
  IO.println s!"EXECLIFT AGREEMENT: lift cases={cases.length} some={some_} none={none_}; nodes={nodes.length} rewritten={rewritten}; disagreements=0"
  unless some_ ≥ 12 && none_ ≥ 6 && rewritten ≥ 3 do throw (IO.userError s!"vacuous grid: {some_} {none_} {rewritten}")

#eval run

end Tests.Compiler.LiftExecAgreeTest
