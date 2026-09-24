import Tools.ShippingCacheSoundness

/-! Expression-cache rules of the shipping compiler: axiom audit, plus runtime
checks of the two facts the soundness argument rests on.

The proofs live in `Tools/ShippingCacheSoundness.lean`. What cannot be proven
there is that `Lean.Meta.withLocalDeclD` mints a FRESH `FVarId` per entry, since
that is a property of the MetaM implementation, and that `Expr.equal`
distinguishes the results — `Expr.equal` is `opaque`. Both are checked here by
running them, and both are labelled as checks, not proofs. -/

namespace Sparkle.Tests.Compiler.ShippingCacheSoundnessTest

open Lean Meta Elab Command Tools.ShippingCacheSoundness

-- The fresh-binder fact: repeated `withLocalDeclD` entries give distinct
-- `FVarId`s, so a body built under one scope is a different cache KEY from the
-- same body built under another. This is what makes a stale hit impossible for
-- expressions containing scoped binders.
run_cmd Lean.Elab.Command.liftTermElabM do
  let t := mkConst ``Nat
  let mut ids : Array Name := #[]
  for _ in [0:3] do
    let id ← withLocalDeclD `x t fun fv => pure fv.fvarId!
    ids := ids.push id.name
  unless ids.toList.eraseDups.length == 3 do
    throwError "withLocalDeclD reused an FVarId: {ids}"
  -- and the structural key really separates them
  let e1 ← withLocalDeclD `x t fun fv => pure (mkAppN (mkConst ``Nat.succ) #[fv])
  let e2 ← withLocalDeclD `x t fun fv => pure (mkAppN (mkConst ``Nat.succ) #[fv])
  if (ExprStructEq.mk e1 == ExprStructEq.mk e2) then
    throwError "structurally identical bodies from DIFFERENT scopes compared equal: {e1} vs {e2}"
  -- the same expression is of course equal to itself (a hit must still work)
  unless (ExprStructEq.mk e1 == ExprStructEq.mk e1) do
    throwError "an expression did not compare equal to itself"

-- The instance gap recorded in the header: core has no `EquivBEq` for
-- `ExprStructEq`, which is why `InsertSpec` is a hypothesis rather than an
-- appeal to `Std.HashMap.get?_insert`. Checked so the file's justification
-- stays true if core ever adds the instance.
run_cmd Lean.Elab.Command.liftTermElabM do
  let inst ← try
      let _ ← synthInstance (← mkAppM ``EquivBEq #[mkConst ``Lean.ExprStructEq])
      pure true
    catch _ => pure false
  if inst then
    logInfo "NOTE: core now provides EquivBEq ExprStructEq — InsertSpec can become a lemma"

run_cmd do
  if (← get).messages.hasErrors then throwError "cache regression failed"
  for name in [``Valid.hit, ``Valid.hit_stripped, ``Valid.hit_congr,
      ``Valid.insert, ``Valid.reserve, ``valid_empty, ``Valid.write_fresh,
      ``cacheable_open_application, ``not_cacheable_fvar,
      ``not_cacheable_named, ``not_cacheable_toplevel,
      ``exprCache_of_state, ``valid_at_synthesis_start,
      -- the hypotheses, now proved or split
      ``insertSpec_of_lawful, ``insertSpec_holds,
      ``keyFaithful_of_keySound, ``stableBetween_refl, ``hit_across] do
    for a in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected cache axiom: {name}: {a}"
  logInfo "SHIPPING CACHE OK: hit/stripped-hit/congruent-hit, insert under an explicit lookup spec, reserve, empty, fresh-write non-interference, shipping eligibility equations, standard axioms only"
  logInfo "CACHE KEY OK: withLocalDeclD freshness and structural-key separation checked at runtime"
  logInfo "CACHE HYPOTHESES (none discharged on the shipping path): Valid.insert still TAKES InsertSpec; insertSpec_of_lawful applies only to lawful keys and the Expr key is not one. KeyFaithful is reduced to the syntactic KeySound, scope stability is split out as StableBetween (separate open item). Remaining assumptions: InsertSpec at the real table, KeySound, EquivBEq/LawfulHashable for the key, consumeMData denotation preservation, and that handlers maintain Valid."

end Sparkle.Tests.Compiler.ShippingCacheSoundnessTest
