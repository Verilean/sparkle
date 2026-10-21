import Tools.Prototype.NormStepModel
import Tests.Compiler.LiftExecAgreeTest

/-! # NMI: EXECUTED agreement of the shipped normaliser `machNorm` with the MODEL normaliser `execNormM`

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.NormStepModelAgreeTest`; not in `Tests.AllTests`). EVIDENCE only, not a proof
(`NodeCorr` stays OPEN): a finite hand-written grid. Each input is normalised by the shipped `machNorm senv` and by
`execNormM senv`; the outputs are compared with `Expr.equal`. `execNormM` answering `none` (no finite derivation) is reported as a
disagreement. Inputs include nodes the node rewriter rewrites (the comparison asserts a minimum number of changed outputs, so it is
not vacuous) and nodes it leaves unchanged (lift refused: width mismatch, out-of-range variable, unknown constant). -/
namespace Tests.Compiler.NormStepModelAgreeTest
open Lean Sparkle.Compiler.Elab Tools.Prototype.NormStepModel Tests.Compiler.LiftExecAgreeTest

def run : IO Unit := do
  let nodes : List (String × Expr) :=
    [ ("map-neg", mapNode (mkApp3 (.const ``Neg.neg [.zero]) (bv 8) (.const `negI []) x0) false),
      ("map-ext", mapNode (mkApp4 (.const ``BitVec.append []) (inlNatLit 8) (inlNatLit 8) x0 x0) false),
      ("map-bool-beq", mapNode (beqE (bv 8) (addE 8 x0 k5) x0) true),
      ("map-bool-not", mapNode (mkApp (.const ``not []) (beqE (bv 8) x0 k5)) true),
      ("map-add-width-refused", mapNode (addE 4 x0 k5) false),
      ("map-oob-var-refused", mapNode (addE 8 (.bvar 2) k5) false),
      ("map-unknown-const", mapNode (.const `junk []) false),
      ("map-not", mapNode (mkApp2 (.const ``BitVec.not []) (inlNatLit 8) x0) false) ]
  let mut changed := 0
  let mut total := 0
  for (nm, node) in nodes do
    let wrapped : List (String × Expr) :=
      [ (nm ++ "/bare", node), (nm ++ "/lam", .lam `y (bv 8) node .default),
        (nm ++ "/app", .app (.const `f []) node) ]
    for (nm', e) in wrapped do
      let o := machNorm senv e
      match execNormM senv e with
      | none => throw (IO.userError s!"execNormM gave no answer on {nm'}")
      | some m =>
        unless o.equal m do throw (IO.userError s!"DISAGREE on {nm'}")
        total := total + 1
        unless o.equal e do changed := changed + 1
  IO.println s!"NORMALISER AGREEMENT: inputs={total} changed-by-normaliser={changed}; disagreements=0"
  unless total ≥ 24 && changed ≥ 6 do throw (IO.userError s!"vacuous grid: {total} {changed}")

#eval run

end Tests.Compiler.NormStepModelAgreeTest
