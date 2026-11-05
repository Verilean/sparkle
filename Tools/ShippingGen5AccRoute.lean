import Tools.ShippingGen5AccServed
set_option autoImplicit false
-- Built (coder, issue-linked incremental build ac8v-da5a6106, approved at da5a6106): `kjob lake build Tools.ShippingGen5AccRoute`, exit 0 (724 jobs for the Check). No sorry / axiom / native_decide.

/-! # DG-ACC unit A6a: `MachineRouteAt` from `ReachCover` + gates + closes (scripts/gen5/DG_ACC_FREEZE_REV4.md §1)

PROVED here (given the premises named in each statement): `machineRouteAt_of_cover` derives, from `ReachCover K Reach` and the kit field
`genData₀_dataOf`, the existence of the machine shape of the entry constant of every reached name, and with the premises `GatesNoneAt`
(the two gate refusals at `env₀`) and `ClosesOfShape` (`MachineClosesAtA` for that shape) gives `MachineRouteAt`. `accServed0_of_cover_gates`
is `accServed0_of_cover` applied to it.

CONDITIONAL on named premises that are NOT supplied here (this investigation found no supplier or route for them): `ReachCover K Reach`,
`GatesNoneAt env₀ Reach`, `ClosesOfShape env₀ L Reach`, `ReadsSupplyAt env₀ L Reach` (for the FG's `L`), `DataOfShape K` (at integration: conjunct 1
of `dataOfAt_sound`; not importable on this lineage), and `hcl`.
Limits: `GatesNoneAt` / `ClosesOfShape` / `ReachCover` / `ReadsSupplyAt` stay premises. Off-route names (reached names outside route 3) are not served
here; connecting them is the obligation of the M4 gate / fallback generalisation, and `Reach` is neither restricted to route 3 nor is the FG narrowed.
No census statement is counted as a supply of `find?` for all reached names. `DataOfShape` and the EnvQ agreement (`QuietStrengthA`/`AdmDownA`,
source text only so far) remain obligations at integration (this lineage is before S1). Not DG-ACC / M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingGen5Env (ReadsAt MachineDefinesR)
open Sparkle.IR.Machine

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
variable (K : AssignKit ι dom env₀)

/-- The two gate refusals of `MachineDefines`, at `env₀`, for the entry constant of every reached name. -/
def GatesNoneAt (env₀ : Environment) (Reach : Name → Prop) : Prop :=
  ∀ c ci, Reach c → env₀.find? c = some ci →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (instancePredicate env₀) = none

/-- `MachineClosesAtA` for the machine shape of the entry constant of every reached name. -/
def ClosesOfShape (env₀ : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c ci shape, Reach c → env₀.find? c = some ci →
    machineShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) = some shape →
    ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c shape

theorem machineRouteAt_of_cover (L : Laws mref cref) (Reach : Name → Prop)
    (hcov : ReachCover K Reach) (hG : GatesNoneAt env₀ Reach) (hC : ClosesOfShape env₀ L Reach) :
    MachineRouteAt env₀ L Reach := by
  intro c hc mctx cctx hA
  obtain ⟨E, g, hE, hg⟩ := hcov c hc
  have hdd := K.genData₀_dataOf hg
  unfold entry₀ at hE
  cases hf : env₀.find? c with
  | none => rw [hf] at hE; exact absurd hE (by simp)
  | some ci =>
    rw [hf] at hE
    have hE' : E = entryConst true false [] ci (instancePredicate env₀) (userInliner env₀) (structEnv env₀) :=
      (Option.some.inj hE).symm
    subst hE'
    cases hsh : machineShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
        (structEnv env₀)) (structEnv env₀) with
    | none => rw [hsh] at hdd; exact absurd hdd (by simp)
    | some shape =>
      obtain ⟨hg1, hg2⟩ := hG c ci hc hf
      exact ⟨shape, Tools.ShippingGen5Env.machineDefinesR_of_env hf hg1 hg2 hsh, hC c ci shape hc hf hsh mctx cctx hA⟩

theorem accServed0_of_cover_gates (L : Laws mref cref) (Reach : Name → Prop)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hcov : ReachCover K Reach) (hDS : DataOfShape K) (hG : GatesNoneAt env₀ Reach)
    (hC : ClosesOfShape env₀ L Reach) (hRS : ReadsSupplyAt env₀ L Reach) : AccServed0Stmt K L Reach :=
  accServed0_of_cover K L Reach hcl (machineRouteAt_of_cover K L Reach hcov hG hC) hcov hDS hRS

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.machineRouteAt_of_cover
#print axioms Tools.ShippingGen5Acc.accServed0_of_cover_gates
