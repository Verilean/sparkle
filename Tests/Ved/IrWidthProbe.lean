import Sparkle.IR.Semantics

/-! Width probe (sparkle-ved-ir-width): the smallest case where inlining a wire changes the IR semantics. See docs/VED-IR-WIDTH.md. -/
namespace Tests.Ved.IrWidthProbe
open Sparkle.IR.AST Sparkle.IR.Semantics

/-- wire x : 8 bits := add(a:4, b:4)   (rhs width 4 ≠ declared 8); out := not x -/
def we : WEnv := fun n => if n = "x" then 8 else 4
def E : Env := fun n => if n = "a" then 9 else if n = "b" then 5 else if n = "x" then 14 else 0
def rhs : Expr := .op .add [.ref "a", .ref "b"]
def useX : Expr := .op .not [.ref "x"]
def useInl : Expr := .op .not [rhs]

-- the assignment HOLDS in E (x = (9+5) mod 16 = 14) ...
theorem hold : evalExpr we E rhs = some (E "x") := by decide +kernel
-- ... but widthOf differs: 8 vs 4
theorem w_differs : widthOf we (.ref "x") ≠ widthOf we rhs := by decide +kernel
-- naive inlining changes the value: 241 (8-bit not 14) vs 1 (4-bit not 14)
theorem naive_inl_false : evalExpr we E useX ≠ evalExpr we E useInl := by decide +kernel
theorem vals : evalExpr we E useX = some 241 ∧ evalExpr we E useInl = some 1 := by decide +kernel
-- full type of the (false) naive statement, i.e. inl_sound WITHOUT the width conjunct `widthOf we r = we l`:
def A : String → Option Expr := fun n => if n = "x" then some rhs else none
def NaiveInlSound : Prop :=
  ∀ (we : WEnv) (E : Env) (A : String → Option Expr),
    (∀ l r, A l = some r → evalExpr we E r = some (E l)) →
    ∀ e : Expr, evalExpr we E (.op .not [match e with | .ref x => (match A x with | some r => r | none => .ref x) | e => e]) = evalExpr we E (.op .not [e])
theorem naive_unsound : ¬ NaiveInlSound := by
  intro h
  have := h we E A (by
    intro l r hl
    by_cases hx : l = "x"
    · subst hx; simp [A] at hl; subst hl; exact hold
    · simp [A, hx] at hl) (.ref "x")
  revert this; decide +kernel
-- the explicit adjustment (option 1): zero-extension via existing forms
def rhsExt : Expr := .concat [.const 0 4, rhs]            -- width 8 = declWidth
theorem ext_w : widthOf we rhsExt = widthOf we (.ref "x") := by decide +kernel
theorem ext_ok : evalExpr we E (.op .not [rhsExt]) = evalExpr we E useX := by decide +kernel
-- truncation case: wire y : 2 bits := add(a:4,b:4): evalAssigns stores UNMASKED value
def we2 : WEnv := fun n => if n = "y" then 2 else 4
theorem trunc_unmasked : evalExpr we2 E rhs = some 14 := by decide +kernel  -- stored in y although declWidth y = 2

end Tests.Ved.IrWidthProbe
