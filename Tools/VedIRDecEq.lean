/-
  Decidable equality for the IR AST, for the VED U1 tools only.

  The U1 contract decides equalities on `Module`/`Port`/`Stmt`/`Expr`
  (`DecidableEq` statements checked with `decide`).  `main`'s
  `Sparkle/IR/AST.lean` derives only `Repr`/`BEq` for these, so the instances
  live here rather than in the compiler (compiler files stay unchanged).
  `Expr.decEq`/`Expr.decEqList` are copied verbatim from the `poc` branch's
  `Sparkle/IR/AST.lean` (par/ved-plan 0a36bae0): `deriving` does not handle the
  nested `List Expr`.  Everything here is a definition; no axiom is added.
-/
import Sparkle.IR.AST

namespace Sparkle.IR.AST

open Sparkle.IR.Type

mutual
/-- Decidable equality of expressions (structural; `deriving` does not handle
the nested `List Expr`). -/
def Expr.decEq : (a b : Expr) → Decidable (a = b)
  | .const v₁ w₁, .const v₂ w₂ =>
    match _root_.decEq v₁ v₂, _root_.decEq w₁ w₂ with
    | isTrue h0, isTrue h1 => isTrue (by subst h0; subst h1; rfl)
    | isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h => isFalse (fun e => by injection e; contradiction)
  | .const v₁ w₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .const v₁ w₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .const v₁ w₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .const v₁ w₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .const v₁ w₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .const v₁ w₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .ref n₂ =>
    match _root_.decEq n₁ n₂ with
    | isTrue h0 => isTrue (by subst h0; rfl)
    | isFalse h => isFalse (fun e => by injection e; contradiction)
  | .ref n₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .ref n₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .op o₂ as₂ =>
    match _root_.decEq o₁ o₂, Expr.decEqList as₁ as₂ with
    | isTrue h0, isTrue h1 => isTrue (by subst h0; subst h1; rfl)
    | isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h => isFalse (fun e => by injection e; contradiction)
  | .op o₁ as₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .op o₁ as₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .concat as₂ =>
    match Expr.decEqList as₁ as₂ with
    | isTrue h0 => isTrue (by subst h0; rfl)
    | isFalse h => isFalse (fun e => by injection e; contradiction)
  | .concat as₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .concat as₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .slice e₂ hi₂ lo₂ =>
    match Expr.decEq e₁ e₂, _root_.decEq hi₁ hi₂, _root_.decEq lo₁ lo₂ with
    | isTrue h0, isTrue h1, isTrue h2 => isTrue (by subst h0; subst h1; subst h2; rfl)
    | isFalse h, _, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, _, isFalse h => isFalse (fun e => by injection e; contradiction)
  | .slice e₁ hi₁ lo₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .slice e₁ hi₁ lo₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .sliceDim e₁ hi₁ lo₁, .sliceDim e₂ hi₂ lo₂ =>
    match Expr.decEq e₁ e₂, _root_.decEq hi₁ hi₂, _root_.decEq lo₁ lo₂ with
    | isTrue h0, isTrue h1, isTrue h2 => isTrue (by subst h0; subst h1; subst h2; rfl)
    | isFalse h, _, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, _, isFalse h => isFalse (fun e => by injection e; contradiction)
  | .sliceDim e₁ hi₁ lo₁, .index a₂ i₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .const v₂ w₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .ref n₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .op o₂ as₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .concat as₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .slice e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .sliceDim e₂ hi₂ lo₂ => isFalse (fun h => Expr.noConfusion h)
  | .index a₁ i₁, .index a₂ i₂ =>
    match Expr.decEq a₁ a₂, Expr.decEq i₁ i₂ with
    | isTrue h0, isTrue h1 => isTrue (by subst h0; subst h1; rfl)
    | isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h => isFalse (fun e => by injection e; contradiction)
/-- Decidable equality of expression lists. -/
def Expr.decEqList : (a b : List Expr) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | x :: xs, y :: ys =>
    match Expr.decEq x y, Expr.decEqList xs ys with
    | isTrue h0, isTrue h1 => isTrue (by subst h0; subst h1; rfl)
    | isFalse h, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h => isFalse (fun e => by injection e; contradiction)
end

instance : DecidableEq Expr := Expr.decEq

deriving instance DecidableEq for Parameter
deriving instance DecidableEq for Port
deriving instance DecidableEq for Stmt
deriving instance DecidableEq for Module

end Sparkle.IR.AST
