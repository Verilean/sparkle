import Tools.ShippingChildTeleCP
-- BUILT (unit C2): tp1 exit 1 (unknown constant in a #print), tp2 exit 0, tp3 exit 1 (private-name #print
-- syntax), tp4 exit 0 (final). No sorry, no axiom, no native_decide, no new law.
--
-- RESULT (feasibility of proving `forallTelescopeReducing` from RefLawsAOps by unfolding): NO, for a
-- precise reason. The tp4 log shows (Lean v4.32.1):
--  * `forallTelescopeReducing` = `map2MetaM (forallTelescopeReducingImp …)` (SAFE def, unfoldable), and
--    `forallTelescopeReducingImp = forallTelescopeReducingAux type none k …`.
--  * `forallTelescopeReducingAux`, `forallTelescopeReducingAuxAux`, `…AuxAux.process`,
--    `lambdaTelescopeImp.process`, `withNewLocalInstancesImp`, `isClassExpensive?` are `partial def`s: in
--    the kernel environment they are `opaque` constants (their `_unsafe_rec` twins are `partial`
--    definitions, not usable in proofs). STUCK GOAL: after `unfold forallTelescopeReducing`/the Imp chain
--    the goal is `Keeps … I (forallTelescopeReducingAux ty none k c w)` with `forallTelescopeReducingAux`
--    an opaque constant: there is no equation lemma, so no unfolding step exists. The primitive that needs
--    a law not in RefLawsAOps is therefore `forallTelescopeReducingAux` itself (equivalently the pair
--    `…AuxAux`/`process`), i.e. precisely the content of `RefLawsATele.telescope`.
--  * `withLocalDecl` is DIFFERENT: `withLocalDeclImp` is a safe def = `mkFreshFVarId` (writes
--    `Core.State.ngen` through `cref`), `withReader` (context update, provable: `keeps_withReader` below,
--    built) and `withNewFVar` (→ `isClass?`/`withNewLocalInstances`, whose workers
--    `isClassExpensive?`/`withNewLocalInstancesImp` are opaque partial). So `localDecl` is also stuck, at
--    the opaque workers and at `mkFreshFVarId` (a Core.State write that no FramedA operation models).
--  * `letDecl` (`withLetDeclImp`) is a safe def of the same shape (not printed; same stuck points).
--  So: only the reader-update step is provable; every telescope/local-decl law needs a premise about an
--  opaque constant, or about `Core.State`'s `ngen`/Meta caches. NOT shown: that no other proof route exists.
-- Purpose: how far can `forallTelescopeReducing` be reached from `RefLawsAOps` operations by
-- unfolding Lean core? The `#print` lines record the definitional chain in the build log.

namespace Tools.ShippingChildTeleProbe
open Lean Meta
open Tools.ShippingChildInv
open Tools.ShippingChildInvA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
  {I : Void IO.RealWorld → Prop}

#print Lean.Meta.forallTelescopeReducing
#print Lean.Meta.forallTelescope
#print Lean.Meta.withLocalDecl
#print Lean.Meta.withLocalDeclD
#print Lean.Meta.withLCtx
#print Lean.Meta.withNewLocalInstances

-- The private implementation constants behind the telescope / local-decl primitives:
-- kind (defn / opaque / unsafe / partial) as the kernel sees them.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let pats := ["forallTelescopeReducingImp", "forallTelescopeReducingAuxAux", "forallTelescopeReducingAux",
    "withLocalDeclImp", "withLetDeclImp", "withLocalContextImp", "withNewLocalInstancesImpAux",
    "lambdaTelescopeImp", "lambdaTelescope", "withNewLocalInstancesImp", "isClassExpensive"]
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if (s.startsWith "_private.Lean.Meta.Basic" || s.startsWith "Lean.Meta") && pats.any (fun p => (s.splitOn p).length > 1) && !((s.splitOn "_eq").length > 1) && !((s.splitOn "match_").length > 1) then
      let kind := match ci with
        | .defnInfo d => s!"defn(safety={repr d.safety})"
        | .opaqueInfo o => s!"opaque(isUnsafe={o.isUnsafe})"
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "thm"
        | _ => "other"
      logInfo m!"{n} : {kind} implementedBy={(Compiler.getImplementedBy? env n)}"


open Lean Elab Command Meta in
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if s.startsWith "_private.Lean.Meta.Basic" && ["withLocalDeclImp", "withLocalContextImp",
        "withNewLocalInstancesImpAux", "forallTelescopeReducingImp"].any (fun p => s.endsWith ("Meta." ++ p)) then
      if let some v := ci.value? then
        let f ← liftCoreM (MetaM.run' (ppExpr v))
        logInfo m!"{n} :=\n{f}"

-- PROVABLE piece: a context update (`withReader`) transports `Keeps` to the updated context.
theorem keeps_withReader {α : Type} (f : Meta.Context → Meta.Context) (x : MetaM α)
    (h : Keeps (f mctx) mref cctx cref I x) :
    Keeps mctx mref cctx cref I (withReader f x) := h

-- Is the telescope's inner loop a `partial def` (opaque to the kernel/unfolding)?
open Lean.Meta in
#print axioms Lean.Meta.forallTelescopeReducing
