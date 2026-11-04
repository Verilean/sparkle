import Tools.ShippingGenFGLedgerPremises
set_option autoImplicit false
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # FG ledger premises without C.RK-1 (scripts/gen5/RK1_FREEZE.md)

`FGLedgerPremisesStmt` (`Tools/ShippingGenFGLedgerPremises.lean`) takes both `h_C_EN4 : CellPrem MkRefd mref cref` (C.EN-4) and
`h_C_RK1 : ReadKeeps cref` (C.RK-1). The ninth conjunct of `CellPrem` is `ReadWorld cref`, and `ReadWorld.readKeeps`
(`Tools/ShippingStRefCorrespondence.lean`, proved) gives `ReadKeeps cref` from it. `FGLedgerPremisesStmtR` is the same text with the
`h_C_RK1` binder line deleted (nothing else changed), and `fgLedgerPremisesStmtR_iff` shows the two statements are equivalent.
The original file is not changed. This is a statement-level removal: like `FGLedgerPremisesStmt` itself, nothing here proves FG,
supplies C.EN-4, or decides whether C.EN-4 is TRUSTED (DG_ENV_FREEZE §4 A/B/C). -/

namespace Tools.ShippingGenFGLedgerPremises
open Lean Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)

/-- C.RK-1 from C.EN-4: the ninth conjunct of `CellPrem` is `ReadWorld cref`. -/
theorem readKeeps_of_cellPrem {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (h : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref) :
    Tools.ShippingStRefCorrespondence.ReadKeeps cref :=
  Tools.ShippingStRefCorrespondence.ReadWorld.readKeeps h.2.2.2.2.2.2.2.2.1

def FGLedgerPremisesStmtR : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    -- carriers (binders, NOT hypotheses; their characterizing rows are in the registry)
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)        -- D.D-1
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)             -- A.P-05
    (GP : Environment → Pkgs ι dom)                                           -- D.D-3
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
      -- inner hypotheses; P := GP (envAt cref w), Reach := TgtRun P declName  (Q-F2)
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ q : Pkg ι dom, GP (envAt cref w) c = some q →      -- h_A_P06
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →      -- h_D_T1
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
          (p.d.shape.instOrigins.getD k .ord).child? = none →
          ∀ q : Pkg ι dom, GP (envAt cref w) (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →      -- h_D_T4
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      -- conclusion: the tail of the FG_CONNECT body (FG.lean), unchanged
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)


/-- The two statements are equivalent: `h_C_RK1` is supplied by `readKeeps_of_cellPrem h_C_EN4`. -/
theorem fgLedgerPremisesStmtR_iff : FGLedgerPremisesStmtR ↔ FGLedgerPremisesStmt := by
  unfold FGLedgerPremisesStmtR FGLedgerPremisesStmt
  constructor
  · intro h ι dom mref cref ReflectsAll Post GP CV L h_C_EN4 _h_C_RK1 h_C_RK6 h_C_CV4
    exact h ReflectsAll Post GP CV L h_C_EN4 h_C_RK6 h_C_CV4
  · intro h ι dom mref cref ReflectsAll Post GP CV L h_C_EN4 h_C_RK6 h_C_CV4
    exact h ReflectsAll Post GP CV L h_C_EN4 (readKeeps_of_cellPrem h_C_EN4) h_C_RK6 h_C_CV4

end Tools.ShippingGenFGLedgerPremises

#print axioms Tools.ShippingGenFGLedgerPremises.readKeeps_of_cellPrem
#print axioms Tools.ShippingGenFGLedgerPremises.fgLedgerPremisesStmtR_iff
