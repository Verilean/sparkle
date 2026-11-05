import Tools.ShippingGenFGLedgerPremisesG
set_option autoImplicit false
-- C.SM-1 (Issue sparkle-ledger-sm1). No `sorry`, no `axiom`, no `native_decide`.

/-! # C.SM-1: `hs : DataOfSound (dataOfAt lvl) initsOf` fixed to the concrete `initsOf`

`FGLedgerPremisesStmtG` carries the binders `{initsOf}` (implicit, universally quantified) and `hs : DataOfSound (dataOfAt lvl) initsOf`.
`dataOfAt_sound` proves `DataOfSound (dataOfAt lvl)` for the concrete `Tools.ShippingGen5DataOfPure.initsOf` (the reset values read off
the layout slots, which `dataOfCore` / `initOk_of_ok` use), so `hs` is not an assumption there: `dataOfSound_initsOf`.
`FGLedgerPremisesStmtH` is `FGLedgerPremisesStmtG` with both binders removed and `hs := dataOfSound_initsOf lvl` in `genGP`;
`fgLedgerPremisesStmtH_of_G` derives it from G. Existing theorems are not edited. -/

namespace Tools.ShippingGen5SM1
open Lean Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.Core Sparkle.Core.Signal
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGenFGLedgerPremises

/-- `DataOfSound (dataOfAt lvl)` at the concrete `initsOf` of `DataOfPure`: `dataOfAt_sound`. -/
theorem dataOfSound_initsOf (lvl : Lean.Expr → Nat) :
    DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) Tools.ShippingGen5DataOfPure.initsOf :=
  fun _ _ _ _ h => Tools.ShippingGen5DataOf.dataOfAt_sound lvl h

def FGLedgerPremisesStmtH : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    -- carriers (binders, NOT hypotheses; their characterizing rows are in the registry)
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)        -- D.D-1
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)             -- A.P-05
    -- D.D-3 fixed (user decision 2026-11-05, GP_FIX_DECISION A): GP := genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀
    (lvl : Lean.Expr → Nat)
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
      -- inner hypotheses; P := genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w), Reach := TgtRun P declName  (Q-F2)
      (∀ c, TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName c → ∀ q : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) c = some q →      -- h_A_P06
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName c → ∀ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) c = some p →      -- h_D_T4
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      -- conclusion: the tail of the FG_CONNECT body (FG.lean), unchanged
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) (TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName)

/-- `FGLedgerPremisesStmtH` follows from `FGLedgerPremisesStmtG` (G at `initsOf := DataOfPure.initsOf`, `hs := dataOfSound_initsOf lvl`). -/
theorem fgLedgerPremisesStmtH_of_G : FGLedgerPremisesStmtG → FGLedgerPremisesStmtH := by
  unfold FGLedgerPremisesStmtG FGLedgerPremisesStmtH
  intro h ι dom mref cref ReflectsAll Post lvl genData₀ CV L h_C_EN4 h_C_RK6 h_C_CV4
  exact h ReflectsAll Post lvl (dataOfSound_initsOf lvl) genData₀ CV L h_C_EN4 h_C_RK6 h_C_CV4

end Tools.ShippingGen5SM1

#print axioms Tools.ShippingGen5SM1.dataOfSound_initsOf
#print axioms Tools.ShippingGen5SM1.fgLedgerPremisesStmtH_of_G
