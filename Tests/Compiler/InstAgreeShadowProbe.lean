-- PROBE (evidence for the runtime-agreement boundary `InstAgree`, NOT a proof; never-failing).
-- Run sh3 (3 GiB, swap 0, -j 1): 4260 comparisons, 0 mismatches (2026-10-19).
import Tools.ShippingInstSubstModel
import Tests.Compiler.MemNameCollisionTest
import Tests.Compiler.ProdResultProbe
import Tests.Compiler.CallWidthsContractTest
open Lean Meta Elab Command
#print axioms Tools.ShippingInstSubstModel.instSubstM
#print axioms Tools.ShippingInstSubstModel.instSubst_of_agree
-- Shadow check of `InstAgree` (evidence only, not a proof): every hardware
-- every telescope step, several argument shapes.
run_cmd liftTermElabM do
  let env ← getEnv
  let mut n : Nat := 0
  let mut bad : Nat := 0
  let args : List Expr := [.fvar ⟨`x⟩, .bvar 0, .bvar 3, mkApp (.const ``Nat.succ []) (.bvar 1),
    .lam `y (.sort 0) (.bvar 1) .default, .lit (.natVal 7)]
  for (c, ci) in env.constants.toList do
    if !(Sparkle.Compiler.isHardwareModule env c || (`Sparkle.Core.Signal).isPrefixOf c) then continue
    let mut t := ci.type
    let mut steps : Nat := 0
    while steps < 12 do
      match t with
      | .forallE _ _ b _ =>
        for a in args do
          n := n + 1
          if b.instantiate1 a != Tools.ShippingInstSubstModel.inst1M b 0 a then
            bad := bad + 1
            if bad ≤ 5 then logInfo m!"MISMATCH {c} step {steps}"
        t := b.instantiate1 (.fvar ⟨`z⟩)
        steps := steps + 1
      | _ => steps := 99
  logInfo m!"InstAgree shadow: {n} comparisons, {bad} mismatches"
