import Tools.ShippingFGCircuitS2dKids
set_option autoImplicit false
-- FG circuit pilot S2g: `HftKidsGates` reduced to the closed declarations of the two callees + finitely many environment queries. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §33.

open Lean Elab Command Meta in
/-- `quote_decl% c as T V Vi Ti`: closed `Lean.Expr` quotes of the declaration's type `T` and value `V`, and of `userInliner env` of the value (`Vi`) and of the type (`Ti`) in the build's environment (the last two are SNAPSHOTS; the facts that they are what the environment's inliner returns are named hypotheses, `ui_val`/`ui_ty`) -/
elab "quote_decl% " c:ident " as " t:ident v:ident vi:ident ti:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
  liftTermElabM do
    let ci ← getConstInfo declName
    let env ← getEnv
    let add (n : Ident) (e : Lean.Expr) : MetaM Unit :=
      let v := Tools.ShippingFGCircuitRoots.exprToE e
      addAndCompile (.defnDecl { name := n.getId, levelParams := [], type := mkConst ``Lean.Expr, value := v, hints := .abbrev, safety := .safe })
    add t ci.type
    add v ci.value!
    add vi (Sparkle.Compiler.Elab.userInliner env ci.value!)
    add ti (Sparkle.Compiler.Elab.userInliner env ci.type)

quote_decl% Sparkle.IP.Net.HTTP.httpGetByte as Tools.ShippingFGCircuitS2gGates.httpType Tools.ShippingFGCircuitS2gGates.httpValue Tools.ShippingFGCircuitS2gGates.httpInlValue Tools.ShippingFGCircuitS2gGates.httpInlType
quote_decl% Sparkle.IP.Bus.PCIe.tlpCplByte as Tools.ShippingFGCircuitS2gGates.tlpType Tools.ShippingFGCircuitS2gGates.tlpValue Tools.ShippingFGCircuitS2gGates.tlpInlValue Tools.ShippingFGCircuitS2gGates.tlpInlType
