import Lean
import Tools.ShippingGen2Defs
import Tools.ShippingGen5FG
import Tools.ShippingGen5EnvFrame3
import Tools.ShippingGen5T2Tie
import Tools.ShippingReaderFuelShape
import Tools.ShippingStRefCorrespondence
import Tools.Prototype.DGenStored2
set_option autoImplicit false
-- NOT BUILT (agent has not yet built this tree; the clean build is the coder's).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # FG ledger premises: the typed part of the stage-2 plan (scripts/gen2/PREMISE_LEDGER.md §8.3, approved design)

`FGLedgerPremisesStmt` is a CONDITIONAL DESIGN CONFIRMATION, not a supply of premises (ledger delta 0 / 0). It is a `Prop` definition
(no proof is given and none is claimed). It lists the 7 hypotheses that could be typed (outer 4: `h_C_EN4 h_C_RK1 h_C_RK6 h_C_CV4`;
inner 3 under the `EntryWitness`: `h_A_P06 h_D_T1 h_D_T4`) in front of the body of `FG_CONNECT` (kjob/g5dc-r23@0fcce4e7).

* The carriers `ReflectsAll` `Post` `GP` `CV` are universally quantified BOOKKEEPING binders only (Q-F5): nothing here says they can be
  supplied, are non-vacuous, or that the final theorem holds. The statement is a conditional schema (`fgCond_trivial`).
* The 69 registry blocks (not typed) are NOT in this statement. `AllPos θ` / `LegalBinding D θ` are not premises of it (Q-F3).
* The 16 T1-ledger rows are a provisional crosswalk kept apart and are not added here (Q-F1); `h_C_CV4` (C.CV-4 ShapeFuelBridge) is kept on the FG side.
* The inner closures (Q-F2) read `P := GP (envAt cref w)`, `Reach := TgtRun P declName` with the guard `child? = none`.
Name resolution is decided by elaboration; a rename would be a comment/name fix, not an added premise. -/

namespace Tools.ShippingGenFGLedgerPremises
open Lean Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)

def FGLedgerPremisesStmt : Prop :=
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
    (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)                                 -- C.RK-1
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

end Tools.ShippingGenFGLedgerPremises
