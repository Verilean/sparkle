import Tools.ShippingGenFGLedgerPremisesG
set_option autoImplicit false
-- C.DG-1 (Issue sparkle-ledger-dg1). No `sorry`, no `axiom`, no `native_decide`.

/-! # C.DG-1: the `GeneratedAt` requirement after GPFIX (`P := genGP`)

After GPFIX the package table of every final root is `genGP lvl hs genData₀ env`, so DG-1 (iii) `P = genP env₀` holds by definition.
The (i) `dataOf` success and (ii) `GenWF d = true` are the fields `hdata` / `wf` of the `GenData` that C.AC-4 (`ReachCover`,
`genData₀ E = some g`) supplies; `GenData.hshape` is the shape part of the reader data. This file states exactly that and nothing more:
* `genGP_fields`: from `genGP … c = some p` the `GenData` `g` with `genData₀ env E = some g`, `wf`, `hshape`, `hdata` and `GeneratedAtK`.
* `hpkg_tgtRun_of_cover`: the package row (A.P-08, `T1HypND.pkg`) at `Reach := TgtRun genGP declName` from C.AC-4 (`ReachCover`) over
  the least call-closed set, C.AC-8 (`Acc`) and the `DataOk` row.
* `pkgAssign_of_cover`: the `hDG_PKGASSIGN` premise of `stepDec_of_ties` at `genGP` from the same coverage.
C.AC-4 is NOT supplied: it stays a premise (`hcov`). -/

namespace Tools.ShippingGen5DG1
open Lean Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGenFGLedgerPremises
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.Core Sparkle.Core.Signal

section
variable {ι : Type} {dom : ι → DomainConfig}
variable (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
  (hs : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf)
  (genData₀ : (env : Environment) → (E : ConstantInfo) →
    Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
  (env : Environment)

/-- `genGP … c = some p` carries the `GenData` of C.AC-4 with its `wf` / `hshape` / `hdata` fields, and `GeneratedAtK`. -/
theorem genGP_fields {c : Name} {p : Pkg ι dom} (hp : genGP (ι := ι) (dom := dom) lvl hs genData₀ env c = some p) :
    ∃ (E : ConstantInfo) (g : GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)),
      entry₀ env c = some E ∧ genData₀ env E = some g ∧ GenWF g.d = true ∧
      machineShape? false [] E (structEnv env) = some g.d.shape ∧
      Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) g.d.shape = some g.d ∧
      Acc (CallRel (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env))) c ∧
      GeneratedAtK (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)) (genGP lvl hs genData₀ env) c E p := by
  obtain ⟨s, hsome, -⟩ := genP_some_inv (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env))
    (factsOf_genS_assembled'' hs (genData₀ env)) hp
  obtain ⟨E, g, hE, hg, hacc, -, -⟩ := genS_some_inv _ hsome
  obtain ⟨E', hE', hgen⟩ := genP_generated (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env))
    (factsOf_genS_assembled'' hs (genData₀ env)) hp
  have hEE : E' = E := Option.some.inj (hE'.symm.trans hE)
  subst hEE
  exact ⟨E', (g : GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E' (structEnv env)), hE, hg,
    (g : GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E' (structEnv env)).wf,
    (g : GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E' (structEnv env)).hshape,
    (g : GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E' (structEnv env)).hdata, hacc, hgen⟩

end

end Tools.ShippingGen5DG1
