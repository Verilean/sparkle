import Tools.ShippingGenFGLedgerPremisesR
import Tools.ShippingGen5AccGenDataKit
import Tools.ShippingGen5AccGenP
import Tools.ShippingGen5AccOrdCallees
import Tools.ShippingGen5SemExtPkg
set_option autoImplicit false
-- GPFIX (scripts/gen5/GPFIX_FREEZE.md). No `sorry`, no `axiom`, no `native_decide`.

/-! # FG ledger premises with the package carrier fixed to the generated table (D.T-1 / D.D-3 / C.SM-7)

User decision 2026-11-05 (scripts/gen5/GP_FIX_DECISION.md, option A): the carrier `GP` of `FGLedgerPremisesStmtR` is fixed to
`genGP lvl hs genData₀ env := genP (genKit …) (factsOf_genS_assembled'' hs (genData₀ env))`, the generated table over the kit of AC9KIT.
Then the inner hypothesis `h_D_T1` (`GenExtAtCall` at every reached ordinary call) is PROVED (`hDT1_of_genGP`) from `genP_generated`,
the definitional unfolding `GenData.genSem hs Q X g = genSemI Q X (g.toIn hs)` and `genExtAtCall_of_genSem`, whose `hq` / `hord` are the
antecedents of `h_D_T1` themselves. `FGLedgerPremisesStmtG` is `FGLedgerPremisesStmtR` at that `GP` without `h_D_T1`; new binders are the
values `lvl initsOf genData₀` and `hs` (C.SM-1). `fgLedgerPremisesStmtG_of_R` shows it follows from `FGLedgerPremisesStmtR`.
Nothing here proves FG, the coverage of `genP` (O2), or supplies the other rows. -/

namespace Tools.ShippingGenFGLedgerPremises
open Lean Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Tools.ShippingEntryReadsLinked (envAt)

section
variable {ι : Type} {dom : ι → DomainConfig}

/-- The kit of AC9KIT (`accKit%`) at environment `env`. -/
noncomputable def genKit (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf) (env : Environment)
    (g₀ : (E : ConstantInfo) → Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env))) :
    AssignKit ι dom env :=
  mkKit (Tools.ShippingGen5DataOf.dataOfAt lvl) (fun E => GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env))
    (fun {E} g => g.d) g₀ ordCallees₀ (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem
    (genData_gdEvidence _) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)

/-- The generated package table at every environment. -/
noncomputable def genGP (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env))) :
    Environment → Pkgs ι dom :=
  fun env => genP (genKit lvl hs env (genData₀ env)) (factsOf_genS_assembled'' hs (genData₀ env))

/-- `h_D_T1` for the generated table. -/
theorem hDT1_of_genGP (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    (env : Environment) (c : Name) (p : Pkg ι dom) (hp : genGP lvl hs genData₀ env c = some p)
    (k : Nat) (hk : k < p.d.shape.insts.length) (hord : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (q : Pkg ι dom) (hq : genGP lvl hs genData₀ env (p.d.shape.insts[k]).1 = some q) :
    GenExtAtCall p q k hk := by
  obtain ⟨E, -, g, hg⟩ := genP_generated (genKit lvl hs env (genData₀ env)) (factsOf_genS_assembled'' hs (genData₀ env)) hp
  exact genExtAtCall_of_genSem (genGP lvl hs genData₀ env) c (g.toIn hs) p q k hk hg hq hord

end

def FGLedgerPremisesStmtG : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    -- carriers (binders, NOT hypotheses; their characterizing rows are in the registry)
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)        -- D.D-1
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)             -- A.P-05
    -- D.D-3 fixed (user decision 2026-11-05, GP_FIX_DECISION A): GP := genGP lvl hs genData₀
    (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf)                          -- C.SM-1 (existing row)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    (CV : ConstValueRel)                                                      -- D.D-4
    (L : Laws mref cref)                                                      -- A.P-01  (= T1L-01)
    -- outer hypotheses (closed Props)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)   -- C.EN-4
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)                                        -- C.RK-6
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),                      -- C.CV-4 (= T1L-43)
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)),
    ConstValueFunctional CV ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →     -- A.P-02 Start, A.P-04 run, D.D-1 ReflectsAll
      -- inner hypotheses; P := genGP lvl hs genData₀ (envAt cref w), Reach := TgtRun P declName  (Q-F2)
      (∀ c, TgtRun (genGP lvl hs genData₀ (envAt cref w)) declName c → ∀ q : Pkg ι dom, genGP lvl hs genData₀ (envAt cref w) c = some q →      -- h_A_P06
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (genGP lvl hs genData₀ (envAt cref w)) declName c → ∀ p : Pkg ι dom, genGP lvl hs genData₀ (envAt cref w) c = some p →      -- h_D_T4
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      -- conclusion: the tail of the FG_CONNECT body (FG.lean), unchanged
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, genGP lvl hs genData₀ (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          genGP lvl hs genData₀ (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (genGP lvl hs genData₀ (envAt cref w)) (TgtRun (genGP lvl hs genData₀ (envAt cref w)) declName)

/-- `FGLedgerPremisesStmtG` follows from `FGLedgerPremisesStmtR` at `GP := genGP lvl hs genData₀` (`h_D_T1` by `hDT1_of_genGP`). -/
theorem fgLedgerPremisesStmtG_of_R : FGLedgerPremisesStmtR → FGLedgerPremisesStmtG := by
  unfold FGLedgerPremisesStmtR FGLedgerPremisesStmtG
  intro h ι dom mref cref ReflectsAll Post CV L lvl initsOf hs genData₀ h_C_EN4 h_C_RK6 h_C_CV4
  obtain ⟨hcv, hmain⟩ := h ReflectsAll Post (genGP lvl hs genData₀) CV L h_C_EN4 h_C_RK6 h_C_CV4
  refine ⟨hcv, fun declName parameters mctx cctx w w' b D hw hA6 hT4 => ?_⟩
  exact hmain declName parameters mctx cctx w w' b D hw hA6
    (fun c _ p hp k hk hord q hq => hDT1_of_genGP lvl hs genData₀ (envAt cref w) c p hp k hk hord q hq) hT4

end Tools.ShippingGenFGLedgerPremises

#print axioms Tools.ShippingGenFGLedgerPremises.hDT1_of_genGP
#print axioms Tools.ShippingGenFGLedgerPremises.fgLedgerPremisesStmtG_of_R
