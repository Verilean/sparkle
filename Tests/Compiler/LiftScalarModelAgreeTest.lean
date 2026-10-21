import Tools.Prototype.LiftScalarModelLetOk

/-! # LC17: EXECUTED agreement of the shipped `partial def machLiftScalarN` with `liftN` on concrete inputs

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.LiftScalarModelAgreeTest`; not in `Tests.AllTests`). EVIDENCE only, not a
proof of `LiftScalarCorr`: the grid is finite and hand-written. Every comparison throws on a mismatch (`Expr.equal` on the
results and equal widths). The grid asserts at least 12 `some` and at least 8 `none` results, and that these named lift arms
SUCCEED on both sides (`some`): var reference, closed constant, `+` (six-argument binary op), `++` (HAppend), `BitVec.append`,
`extractLsb'`, `BitVec.not`, `Neg.neg`, `Complement.complement`. It also asserts that the shipped `machBoolMap` SUCCEEDS through
a lift arm (operands `bvar`, a constant, and `bvar + bvar`) and agrees with `boolMapModel` there (this is the evidence LC16's grid
lacked: its `+`/`++` operands were refused by both sides, so that grid did not exercise the lift arms beyond the var reference). -/
namespace Tests.Compiler.LiftScalarModelAgreeTest
open Lean Sparkle.Compiler.Elab Tools.Prototype.LiftScalarModelLetOk Tools.Prototype.BoolMapModelLetOk

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
    ("add", addE 8 x0 k5), ("add-const", addE 8 k5 k5), ("add-width", addE 4 x0 k5), ("add-oobvar", addE 8 (.bvar 2) k5),
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
    ("sshr-zero-width", mkApp3 (.const ``BitVec.sshiftRight []) (inlNatLit 0) x0 (inlNatLit 2)),
    ("sshr-big", mkApp3 (.const ``BitVec.sshiftRight []) (inlNatLit 8) x0 (inlNatLit 300)),
    ("extract-width", mkApp4 (.const ``BitVec.extractLsb' []) (inlNatLit 4) (inlNatLit 2) (inlNatLit 3) x0),
    ("not-width", mkApp2 (.const ``BitVec.not []) (inlNatLit 4) x0),
    ("nest", addE 8 (addE 8 x0 k5) (mkApp2 (.const ``BitVec.not []) (inlNatLit 8) x0)) ]

/-- arms that must SUCCEED on both sides -/
def mustSome : List String :=
  ["var", "const", "add", "append-op", "BitVec.append", "extract", "not", "neg", "compl"]

def eqO : Option (Nat × Expr) → Option (Nat × Expr) → Bool
  | none, none => true
  | some (w, a), some (w', b) => w == w' && a.equal b
  | _, _ => false

def eqB : Option Expr → Option Expr → Bool
  | none, none => true
  | some a, some b => a.equal b
  | _, _ => false

def run : IO Unit := do
  let vars := [(8, sig)]
  let mut some_ := 0
  let mut none_ := 0
  for (nm, e) in cases do
    let o := machLiftScalarN senv dom vars e
    let m := liftN senv dom vars 64 e
    unless eqO o m do throw (IO.userError s!"DISAGREE on {nm}: {e}")
    if mustSome.contains nm && o.isNone then throw (IO.userError s!"arm {nm} was refused, expected success")
    if o.isSome then some_ := some_ + 1 else none_ := none_ + 1
  -- machBoolMap through the lift arms: var reference, constant, `+`
  let bm : List (String × Nat × Expr) :=
    [ ("bm-var", 8, beqE (bv 8) x0 x0), ("bm-const", 8, beqE (bv 8) x0 k5), ("bm-add", 8, beqE (bv 8) (addE 8 x0 k5) x0),
      ("bm-add-var", 8, beqE (bv 8) (addE 8 x0 x0) k5), ("bm-refused", 8, beqE (bv 8) (.const `junk []) x0) ]
  let mut bmSome := 0
  for (nm, wa, b) in bm do
    let o := machBoolMap senv dom sig wa b
    let m := boolMapModel (machLiftScalarN senv dom [(wa, sig)]) dom b
    unless eqB o m do throw (IO.userError s!"BoolMap DISAGREE on {nm}")
    if nm != "bm-refused" && o.isNone then throw (IO.userError s!"{nm} was refused, expected success")
    if o.isSome then bmSome := bmSome + 1
  IO.println s!"LIFT MODEL AGREEMENT: cases={cases.length} some={some_} none={none_} disagreements=0; machBoolMap lift-arm successes={bmSome}"
  unless some_ ≥ 12 && none_ ≥ 8 && bmSome ≥ 4 do throw (IO.userError s!"vacuous grid: some={some_} none={none_} bm={bmSome}")

#eval run

end Tests.Compiler.LiftScalarModelAgreeTest
