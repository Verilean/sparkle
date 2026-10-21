import Tools.Prototype.BoolMapModelLetOk

/-! # LC16: EXECUTED agreement of the shipped `partial def machBoolMap` with `boolMapModel` on concrete inputs

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.BoolMapModelAgreeTest`; not in `Tests.AllTests`). EVIDENCE only, not a
proof of `BoolMapCorr`: the grid is finite and hand-written, and `machLiftScalarN` is the same compiled function on both sides.
Every comparison throws on a mismatch (`Expr.equal` on the results) and the grid must have at least 4 `some` results and
at least 8 `none` results (so it is not vacuous in either direction). A successful build means every line held. -/
namespace Tests.Compiler.BoolMapModelAgreeTest
open Lean Sparkle.Compiler.Elab Tools.Prototype.BoolMapModelLetOk

def senv : StructEnv := { proj := fun _ => none, fields := fun _ => none }
def bv (w : Nat) : Expr := mkApp (.const ``BitVec []) (inlNatLit w)
def beqI (ty : Expr) : Expr := mkApp2 (.const ``instBEqOfDecidableEq [.zero]) ty (.const `dec [])
def beqE (ty inst x y : Expr) : Expr := mkApp4 (.const ``BEq.beq [.zero]) ty inst x y
def nots : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => .app (.const ``Bool.not []) (nots n e)
def addE (w : Nat) (x y : Expr) : Expr :=
  mkApp6 (.const ``HAdd.hAdd [.zero, .zero, .zero]) (bv w) (bv w) (bv w) (.const `instAdd []) x y
def appE (m n : Nat) (x y : Expr) : Expr :=
  mkApp6 (.const ``HAppend.hAppend [.zero, .zero, .zero]) (bv m) (bv n) (bv (m + n))
    (.const ``BitVec.instHAppendHAddNat []) x y

def dom : Expr := .const `dom []
def sig : Expr := .const `sig []

def bodies : List (Nat × Expr) :=
  let b8 := beqE (bv 8) (beqI (bv 8)) (.bvar 0) (.bvar 0)
  [ (8, b8), (4, b8), (8, beqE (bv 8) (.const `otherInst []) (.bvar 0) (.bvar 0)),
    (8, beqE (.const `Foo []) (beqI (.const `Foo [])) (.bvar 0) (.bvar 0)),
    (8, beqE (bv 8) (beqI (bv 8)) (.bvar 1) (.bvar 0)),
    (8, beqE (bv 8) (beqI (bv 8)) (addE 8 (.bvar 0) (.bvar 0)) (.bvar 0)),
    (16, beqE (bv 16) (beqI (bv 16)) (appE 8 8 (.bvar 0) (.bvar 0)) (.bvar 0)),
    (8, beqE (bv 8) (beqI (bv 8)) (.const `k []) (.bvar 0)),
    (8, .const `junk []), (8, .mdata {} b8), (8, mkApp2 (.const ``Bool.not []) b8 b8),
    (8, .app (.const `other []) b8) ] ++
  (List.range 4).map (fun n => (8, nots n b8)) ++ (List.range 4).map (fun n => (8, nots n (beqE (bv 8) (beqI (bv 8)) (.bvar 0) (.bvar 3))))

def eqO : Option Expr → Option Expr → Bool
  | none, none => true
  | some a, some b => a.equal b
  | _, _ => false

def run : IO Unit := do
  let mut some_ := 0
  let mut none_ := 0
  for (wa, b) in bodies do
    let o := machBoolMap senv dom sig wa b
    let m := boolMapModel (machLiftScalarN senv dom [(wa, sig)]) dom b
    unless eqO o m do throw (IO.userError s!"DISAGREE at width {wa}: {b}")
    if o.isSome then some_ := some_ + 1 else none_ := none_ + 1
  IO.println s!"BOOLMAP MODEL AGREEMENT: cases={bodies.length} some={some_} none={none_} disagreements=0"
  unless some_ ≥ 4 && none_ ≥ 8 do throw (IO.userError s!"vacuous grid: some={some_} none={none_}")

#eval run

end Tests.Compiler.BoolMapModelAgreeTest
