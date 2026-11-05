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

local notation "KK" => genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)
local notation "GPP" => genGP (ι := ι) (dom := dom) lvl hs genData₀ env

/-- A call of a package in the table is a `CallEdge` of the kit. -/
theorem callEdge_of_genGP {c : Name} {q : Pkg ι dom} (hq : GPP c = some q) (k : Nat) (hk : k < q.d.shape.insts.length)
    (hord : (q.d.shape.instOrigins.getD k .ord).child? = none) : CallEdge KK c (q.d.shape.insts[k]'hk).1 := by
  obtain ⟨d, hd, hqd⟩ := genP_d_edges (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env))
    (factsOf_genS_assembled'' hs (genData₀ env)) hq
  subst hqd
  exact ⟨q.d, hd, k, hk, hord, rfl⟩

/-- `TgtRun` of the generated table lies in the least call-closed set over the target. -/
theorem tgtRun_reachEdge {declName c : Name} (h : TgtRun GPP declName c) :
    ReachEdge KK (fun x => x = declName) c := by
  induction h with
  | top => exact ReachEdge.top rfl
  | call hc hq k hk ord ih => exact ReachEdge.edge ih (callEdge_of_genGP lvl hs genData₀ env hq k hk ord)

/-- The package row A.P-08 (`T1HypND.pkg`) at `P := genGP`, `Reach := TgtRun genGP declName`, from C.AC-4 (`hcov`), C.AC-8 (`hacc`)
and the `DataOk` row. -/
theorem hpkg_tgtRun_of_cover {declName : Name} {DataOk : Pkg ι dom → Prop}
    (hacc : ∀ c, ReachEdge KK (fun x => x = declName) c → Acc (CallRel KK) c)
    (hcov : ReachCover KK (ReachEdge KK (fun x => x = declName)))
    (hOk : ∀ c, TgtRun GPP declName c → ∀ q : Pkg ι dom, GPP c = some q → DataOk q) :
    ∀ c, TgtRun GPP declName c → ∃ q, GPP c = some q ∧ q.decl = c ∧ DataOk q := by
  intro c hc
  obtain ⟨q, hq, hd, -⟩ := genP_pkg (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env))
    (factsOf_genS_assembled'' hs (genData₀ env)) (Reach := ReachEdge KK (fun x => x = declName))
    (DataOk := fun _ => True) (fun X c hX he => ReachEdge.edge hX he) hacc hcov (fun _ _ _ _ => trivial) c
    (tgtRun_reachEdge lvl hs genData₀ env hc)
  exact ⟨q, hq, hd, hOk c hc q hq⟩

/-- `hDG_PKGASSIGN` of `stepDec_of_ties` at `P := genGP`, from the same coverage over any target `Top` containing `p.decl`. -/
theorem pkgAssign_of_cover {Top : Name → Prop}
    (hacc : ∀ c, ReachEdge KK Top c → Acc (CallRel KK) c) (hcov : ReachCover KK (ReachEdge KK Top))
    (p : Pkg ι dom) (hTop : Top p.decl) (hPp : GPP p.decl = some p) :
    ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∃ q, GPP (p.d.shape.insts[k]).1 = some q := by
  intro k hk hord
  obtain ⟨q, hq, -, -⟩ := genP_pkg (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env))
    (factsOf_genS_assembled'' hs (genData₀ env)) (Reach := ReachEdge KK Top)
    (DataOk := fun _ => True) (fun X c hX he => ReachEdge.edge hX he) hacc hcov (fun _ _ _ _ => trivial)
    (p.d.shape.insts[k]).1
    (ReachEdge.edge (ReachEdge.top hTop) (callEdge_of_genGP lvl hs genData₀ env hPp k hk hord))
  exact ⟨q, hq⟩

end

#print axioms Tools.ShippingGen5DG1.genGP_fields
#print axioms Tools.ShippingGen5DG1.hpkg_tgtRun_of_cover
#print axioms Tools.ShippingGen5DG1.pkgAssign_of_cover

end Tools.ShippingGen5DG1
