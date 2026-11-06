import Tools.ShippingFGCircuitS2iRun
set_option autoImplicit false
-- FG circuit pilot S2o scaling measurement (docs/FG-CIRCUIT-PILOT.md §36). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.
-- SHARE-CHAIN n: `(fun x0 : Bool => (fun x1 : T0 => … (fun xn : T(n-1) => xn) (Prod.mk x(n-1) x(n-1))) (Prod.mk x0 x0)) false`, T(k+1) = T k × T k.
-- The value has 2^n leaves as a tree and n+1 distinct subterms as a DAG; each variable is referenced twice. The log lines give DT nodes / Sh steps / generator ms / kernel ms / term DAG vs tree.
namespace Tests.Gen5.FGCircuitPilotCheck35
open Lean Meta Elab Command Term Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1sCD Tools.ShippingFGCircuitS2iRun

def bl : Lean.Expr := .const ``Bool []
def tyAt : Nat → Lean.Expr
  | 0 => bl
  | k + 1 => let t := tyAt k; appN ``Prod [.zero, .zero] [t, t]
def mkAt (k : Nat) (x : Lean.Expr) : Lean.Expr := let t := tyAt k; appN ``Prod.mk [.zero, .zero] [t, t, x, x]
/-- inside the binder of `x_k : T k` (de Bruijn 0); `n` binders after the first -/
def body (n : Nat) (k : Nat) : Lean.Expr :=
  if k ≥ n then .bvar 0 else .app (.lam `x (tyAt (k + 1)) (body n (k + 1)) .default) (mkAt k (.bvar 0))
termination_by n - k
def chain (n : Nat) : Lean.Expr := .app (.lam `x bl (body n 0) .default) (.const ``Bool.false [])

derive_expr_t c4 := chain 4
derive_expr_t c8 := chain 8
derive_expr_t c12 := chain 12
derive_expr_t c16 := chain 16
derive_expr_t c20 := chain 20
derive_expr_t c24 := chain 24

end Tests.Gen5.FGCircuitPilotCheck35
