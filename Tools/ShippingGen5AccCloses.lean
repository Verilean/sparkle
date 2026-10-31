import Tools.ShippingGen5AccRoute
import Tools.ShippingMachineClosesData
import Tools.ShippingClosesSplit
set_option autoImplicit false
-- NOT BUILT as of this commit (A7 written by g5ac-r14; Pod build result is recorded in the header by a later comment-only commit).

/-! # DG-ACC unit A7: `ClosesOfShape` from data facts (scripts/gen5/DG_ACC_FREEZE_REV7.md §1)

PROVED here (conditionally): `ClosesOfShape env₀ L Reach` follows from `ReachCover`, `DataOfShape`, `ClosesData` (the three data facts
`d.ok`, the body equation, `letsAliasOk` for the reader data of each reached name) and `ClosesCalls` (`CallsClose` for the reached names with
non-empty `insts`; leaf names need none).

LIMITS: `ClosesData` and `ClosesCalls` themselves are NOT supplied (F is a dg-dataof integration obligation, L and C′ : this survey found no route),
nor `ReachCover`, `DataOfShape`, `ReadsSupplyAt`, `GenSFacts`, off-route, any real run. Not DG-ACC / M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingClosesSplit (CallsClose)
open Tools.ShippingMachineClosesData (letsClose_of_data)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingUnifiedSource (quote)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- The data facts the machine closing needs (conjuncts 2,3 of `dataOfFrom_sound`, plus `letsAliasOk`), for every reached name. -/
def ClosesData (K : AssignKit ι dom env₀) (Reach : Name → Prop) : Prop :=
  ∀ c d, Reach c → dataOf₀ K c = some d →
    d.ok = true ∧
    d.shape.body = Tools.ShippingUnifiedSource.quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.letsAliasOk = true

/-- `CallsClose` for the non-leaf reached names, at every admissible context. -/
def ClosesCalls (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c d, Reach c → dataOf₀ K c = some d → d.shape.insts ≠ [] →
    ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
      CallsClose mctx mref cctx cref c d.shape

theorem closesOfShape_of_data (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop)
    (hcov : ReachCover K Reach) (hDS : DataOfShape K)
    (hD : ClosesData K Reach) (hC : ClosesCalls K L Reach) : ClosesOfShape env₀ L Reach := by
  intro c ci shape hc hf hsh mctx cctx hA
  obtain ⟨E, g, hE, hg⟩ := hcov c hc
  have hd := dataOf₀_of_genData₀ K hE hg
  have hEq : entry₀ env₀ c = some (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) := by
    unfold entry₀; rw [hf]; rfl
  have hdd : dataOf₀ K c = K.dataOf (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) shape := by
    unfold dataOf₀; rw [hEq]; simp [Option.bind, hsh]
  have hdsh : (K.dOf g).shape = shape := hDS _ _ _ _ (hdd ▸ hd)
  obtain ⟨hok, hbody, hal⟩ := hD c (K.dOf g) hc hd
  subst hdsh
  have hl : Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref c (K.dOf g).shape :=
    letsClose_of_data (declName := c) (K.dOf g) hok hbody hal mctx mref cctx cref
  have hcc : (K.dOf g).shape.insts ≠ [] → CallsClose mctx mref cctx cref c (K.dOf g).shape :=
    fun hne => @hC c (K.dOf g) hc hd hne mctx cctx hA
  have hM : MachineCloses mctx mref cctx cref c (K.dOf g).shape :=
    Tools.ShippingClosesSplit.machineCloses_iff.mpr ⟨hl, hcc⟩
  exact @machineClosesAtA_of_closes mctx mref cctx cref L c _ @hM

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.closesOfShape_of_data
