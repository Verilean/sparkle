import Tools.Prototype.StartDomOk2

/-! # SDOM4: EXECUTED check of what `Expr.eqv` (`==`) does on atoms, mdata, binder names, and `LetOk 0`

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.ExprEqvAtomTest`).  EVIDENCE about the extern `lean_expr_eqv`, not a
proof.  Every `check` throws on a mismatch, so a successful build means every line below held in this toolchain. -/
namespace Tests.Compiler.ExprEqvAtomTest
open Lean Tools.ShippingLetsReaderInv

def fv : Expr := .fvar ⟨`x⟩
def fv2 : Expr := .fvar ⟨`y⟩
def cs : Expr := .const `Nat []
def cs2 : Expr := .const `Int []
def md (e : Expr) : Expr := .mdata (KVMap.empty.insert `k (.ofNat 1)) e
def mdE (e : Expr) : Expr := .mdata {} e
def ml : Expr := .fvar ⟨.num (.str .anonymous "_machLet") 0⟩

def check (name : String) (b : Bool) : IO Unit := unless b do throw (IO.userError s!"FAILED: {name}")

def main : IO Unit := do
  -- reflexive / distinct atoms
  check "fvar==fvar" (fv == fv)
  check "fvar!=fvar'" (!(fv == fv2))
  check "const==const" (cs == cs)
  check "const!=const'" (!(cs == cs2))
  check "fvar!=const" (!(fv == cs) && !(cs == fv))
  -- mdata is NOT transparent to ==, either side, empty or nonempty
  check "mdata fvar == fvar is false" (!(md fv == fv))
  check "fvar == mdata fvar is false" (!(fv == md fv))
  check "mdata{} fvar == fvar is false" (!(mdE fv == fv))
  check "mdata const == const is false" (!(md cs == cs) && !(cs == md cs))
  check "mdata fvar == mdata fvar" (md fv == md fv)
  -- other shapes against atoms
  check "app != fvar" (!(Expr.app fv fv == fv))
  check "lam != const" (!(Expr.lam `a cs cs .default == cs))
  check "ml==ml" (ml == ml)
  -- alpha-equivalence: binder names / infos are ignored, and LetOk 0 is invariant on those pairs
  let l1 := Expr.lam `a cs (.bvar 0) .default
  let l2 := Expr.lam `b cs (.bvar 0) .implicit
  check "alpha lam" (l1 == l2)
  check "alpha LetOk0" (LetOk 0 l1 == LetOk 0 l2)
  let m1 := Expr.lam `a cs ml .default
  let m2 := Expr.lam `b cs ml .instImplicit
  check "alpha lam with _machLet" (m1 == m2)
  check "LetOk 0 false on both" (!LetOk 0 m1 && !LetOk 0 m2)
  check "LetOk 1 true on both" (LetOk 1 m1 && LetOk 1 m2)
  -- a LetOk 0 expression is never == a _machLet atom unless equal
  check "ml != fv" (!(ml == fv))
  check "LetOk 0 fv, const, mdata" (LetOk 0 fv && LetOk 0 cs && LetOk 0 (md fv))

#eval main

end Tests.Compiler.ExprEqvAtomTest
