import Tools.ShippingReaderRawNodeArm
import Tools.ShippingReaderMatcherArityReal

/-! # The two units together: `rawNode` at the compiler's own `prodMatch`

WRITTEN, NOT BUILT (branch `fix/reader-p1`; `docs/parallel/P-reader-2.md`).
Needs the switch-over of `prodMatcherArity?`. A leaf.

The reader calls `rawNode senv.prodMatch`, and `senv.prodMatch` is
`MachRawSurface.prodMatcherArity? env` (`Elab.lean`, `structEnv`). With
`real_canon` (the REAL `prodMatcherArity?` returns `dcs.length + 1` on a
canonical pair matcher) and `rawNode_pairArm_some`, the real `rawNode`, at
the compiler's own `prodMatch`, succeeds on every three-argument node whose
head is a canonical pair matcher and whose alternative has enough leading
lambdas. The one premise about the extern `Expr.eqv` (`hrefl`) stays an
explicit hypothesis, as in `prodMatcherArityT_canon`. -/
namespace Tools.ShippingReaderRawNodeCanon
open Lean
open Tools.ShippingReaderMatcherArity (Deco matcherE)
open Tools.ShippingReaderProjChainArm (peelC buildC armTys armJobs)

theorem rawNode_canon (hrefl : ∀ i : Nat, ((Expr.bvar i) == (Expr.bvar i)) = true)
    (env : Environment) (n : Name) (d : DefinitionVal) (m0 m1 m2 : Name × Expr × BinderInfo)
    (dcs : List Deco) (hf : env.find? n = some (.defnInfo d)) (hv : d.value = matcherE m0 m1 m2 dcs)
    (e : Expr) (us : List Level) (m regs alt : Expr) (binders : List (Name × Expr)) (body : Expr)
    (h1 : e.getAppFn = Expr.const n us) (h2 : e.getAppArgs = #[m, regs, alt])
    (hp : peelC (dcs.length + 1) alt [] = some (binders, body)) :
    Sparkle.Compiler.MachRawSurface.rawNode (Sparkle.Compiler.MachRawSurface.prodMatcherArity? env) e =
      buildC regs (armTys binders) (dcs.length + 1) body (armJobs (dcs.length + 1) binders) :=
  Tools.ShippingReaderRawNodeArm.rawNode_pairArm (Sparkle.Compiler.MachRawSurface.prodMatcherArity? env) e n us m regs alt (dcs.length + 1) binders body
    h1 h2 (Tools.ShippingReaderMatcherArityReal.real_canon hrefl env n d m0 m1 m2 dcs hf hv) hp

theorem rawNode_canon_some (hrefl : ∀ i : Nat, ((Expr.bvar i) == (Expr.bvar i)) = true)
    (env : Environment) (n : Name) (d : DefinitionVal) (m0 m1 m2 : Name × Expr × BinderInfo)
    (dcs : List Deco) (hf : env.find? n = some (.defnInfo d)) (hv : d.value = matcherE m0 m1 m2 dcs)
    (e : Expr) (us : List Level) (m regs alt : Expr) (binders : List (Name × Expr)) (body : Expr)
    (h1 : e.getAppFn = Expr.const n us) (h2 : e.getAppArgs = #[m, regs, alt])
    (hp : peelC (dcs.length + 1) alt [] = some (binders, body)) :
    ∃ r, Sparkle.Compiler.MachRawSurface.rawNode
      (Sparkle.Compiler.MachRawSurface.prodMatcherArity? env) e = some r :=
  Tools.ShippingReaderRawNodeArm.rawNode_pairArm_some (Sparkle.Compiler.MachRawSurface.prodMatcherArity? env) e n us m regs alt (dcs.length + 1) binders
    body h1 h2 (Tools.ShippingReaderMatcherArityReal.real_canon hrefl env n d m0 m1 m2 dcs hf hv) hp

end Tools.ShippingReaderRawNodeCanon
