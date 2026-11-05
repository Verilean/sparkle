import Lean
import Tools.ShippingGen5PTRootShard
set_option autoImplicit false
-- D.D-4 Q-B, root-name-fixed statements (Issue sparkle-ledger-dd4-shard, changes_requested fix 1). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Ordinary definitions and theorems checked by the kernel.

/-! # The statement of ONE entry (root name fixed)

`FGLedgerPremisesStmtRootAt PT` (in `Tools.ShippingGen5PTRootShard`, unchanged) quantifies `∀ declName` inside, and `Root Ss` fixes only the shard list `Ss`: nothing in the statement ties `Ss` to a root name.
New definitions here:

* `FGLedgerPremisesStmtEntryAt PT declName`: the same text with the entry name a PARAMETER (`EntryWitness … declName …`, `TgtRun … declName`, `genGP … declName`, `DeclConnect … declName`).
* `FGLedgerPremisesStmtRootEntry root Ss := EntryAt (rootPT Ss) root`: the statement of the root `root` that needs the shards `Ss`; the name `root` occurs in the statement.
* `FGLedgerPremisesStmtRootBy tab := ∀ declName, EntryAt (rootPT (tab declName)) declName`: the shard list is CHOSEN from the entry name inside the quantifier.

Bridges are the specialisation from `FGLedgerPremisesStmtCV` / `H` (the same as before: a statement about every table, specialised). `RootAt PT → EntryAt PT d` is the specialisation of the inner `∀ declName`.
Nothing here says that `root` exists in an environment, that `Ss` are the shards `root` needs, or that any semantics is preserved: `CV` / `H` are unproved statements, so these specialisations
are NOT a proof that a real root satisfies its statement. -/

namespace Tools.ShippingGen5PTRootShard
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5PTCorpus Tools.ShippingGen5PTShard

section stmt
open Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.Core Sparkle.Core.Signal
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1
open Tools.ShippingGen5ConstValueESoundK (OblLbrZero)
open Tools.ShippingGen5EnvDeclClosed (KernelClosedInvariant)
open Tools.ShippingGen5CVFinal Tools.ShippingGen5RowTypedV Tools.ShippingGen5ConstValueEVL

/-- `FGLedgerPremisesStmtRootAt PT` with the entry name FIXED: the quantifier `∀ declName` is replaced by the parameter `declName`
(the same text otherwise; `declName` occurs in `EntryWitness` and in `TgtRun … declName`, the genGP and the `DeclConnect` conclusion). -/
def FGLedgerPremisesStmtEntryAt (PT : PrimTableK) (declName : Name) : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    -- carriers (binders, NOT hypotheses; their characterizing rows are in the registry)
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)        -- D.D-1
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)             -- A.P-05
    -- D.D-3 fixed (GP := genGP lvl (dataOfSound_initsOf lvl) genData₀); D.D-4 fixed (CV := CVFinal PT, PT := the root's table)
    (lvl : Lean.Expr → Nat)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    (L : Laws mref cref)                                                      -- A.P-01  (= T1L-01)
    -- outer hypotheses (closed Props)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)   -- C.EN-4
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)                                        -- C.RK-6
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),                      -- C.CV-4 (= T1L-43)
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp))
    (h_D_LBR : OblLbrZero),                                                                      -- named premise: lbr bridge (unresolved)
    ConstValueFunctional (CVFinal PT) ∧
    ∀ (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →     -- A.P-02 Start, A.P-04 run, D.D-1 ReflectsAll
      -- named premises on the entry environment (unresolved obligations of the carrier; ordinary hypotheses)
      KernelClosedInvariant (envAt cref w) →                                    -- EnvDeclClosed via OblLbrZero (audit: 0 counterexamples)
      LitRows PT (envAt cref w) →                                               -- Nat / String rows of PT
      OblRowTypedV PT (envAt cref w) →                                          -- RowTypedAtV rows (incl. the dependent ones)
      (∀ (c : Name) (ls : List Level), RowTeleEvAt PT (envAt cref w) c ls) →    -- RowTeleEvAt rows
      -- inner hypotheses; P := genGP lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w), Reach := TgtRun P declName  (Q-F2)
      (∀ c, TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName c → ∀ q : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) c = some q →      -- h_A_P06
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName c → ∀ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) c = some p →      -- h_D_T4
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      -- conclusion: the tail of the FG_CONNECT body (FG.lean), unchanged except CV := CVFinal PT
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect (CVFinal PT) (envAt cref w) (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) (TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName)

/-- The statement of the root `root` that needs the shards `Ss`: the root name is fixed in the statement. -/
noncomputable def FGLedgerPremisesStmtRootEntry (root : Name) (Ss : List PTShard) : Prop := FGLedgerPremisesStmtEntryAt (rootPT Ss) root

/-- The shard list chosen from the entry name inside the quantifier. -/
noncomputable def FGLedgerPremisesStmtRootBy (tab : Name → List PTShard) : Prop := ∀ declName : Name, FGLedgerPremisesStmtEntryAt (rootPT (tab declName)) declName

/-- The `∀ declName` form specialises to one entry. -/
theorem fgLedgerPremisesStmtEntryAt_of_RootAt {PT : PrimTableK} (h : FGLedgerPremisesStmtRootAt PT) (d : Name) : FGLedgerPremisesStmtEntryAt PT d := by
  unfold FGLedgerPremisesStmtRootAt at h
  unfold FGLedgerPremisesStmtEntryAt
  intro ι dom mref cref ReflectsAll Post lvl genData₀ L h_C_EN4 h_C_RK6 h_C_CV4 h_D_LBR
  have h' := @h ι dom mref cref ReflectsAll Post lvl genData₀ L h_C_EN4 h_C_RK6 h_C_CV4 h_D_LBR
  exact ⟨h'.1, h'.2 d⟩

theorem fgLedgerPremisesStmtEntryAt_of_CV : FGLedgerPremisesStmtCV → ∀ PT d, FGLedgerPremisesStmtEntryAt PT d :=
  fun h PT d => fgLedgerPremisesStmtEntryAt_of_RootAt (fgLedgerPremisesStmtRootAt_of_CV h PT) d

/-- Specialisation of `CV` (an unproved statement) to the root `root` with the shards `Ss`: not a proof that `root` is a real root or that `Ss` is what it needs. -/
theorem fgLedgerPremisesStmtRootEntry_of_CV : FGLedgerPremisesStmtCV → ∀ root Ss, FGLedgerPremisesStmtRootEntry root Ss :=
  fun h root Ss => fgLedgerPremisesStmtEntryAt_of_CV h _ root

theorem fgLedgerPremisesStmtRootEntry_of_H : FGLedgerPremisesStmtH → ∀ root Ss, FGLedgerPremisesStmtRootEntry root Ss :=
  fun h => fgLedgerPremisesStmtRootEntry_of_CV (fgLedgerPremisesStmtCV_of_H h)

theorem fgLedgerPremisesStmtRootBy_of_CV : FGLedgerPremisesStmtCV → ∀ tab, FGLedgerPremisesStmtRootBy tab :=
  fun h tab d => fgLedgerPremisesStmtEntryAt_of_CV h _ d

/-- The chosen-inside form gives the fixed-name form at the chosen list. -/
theorem fgLedgerPremisesStmtRootEntry_of_By {tab : Name → List PTShard} (h : FGLedgerPremisesStmtRootBy tab) (root : Name) : FGLedgerPremisesStmtRootEntry root (tab root) := h root

/-- With no shard, the entry statement is the entry specialisation of `FGLedgerPremisesStmtPTC` (not an equivalence: `PTC` quantifies over all entries). -/
theorem fgLedgerPremisesStmtRootEntry_nil_of_PTC : FGLedgerPremisesStmtPTC → ∀ root, FGLedgerPremisesStmtRootEntry root [] :=
  fun h root => fgLedgerPremisesStmtEntryAt_of_RootAt (PT := rootPT []) h root

end stmt

end Tools.ShippingGen5PTRootShard

#print axioms Tools.ShippingGen5PTRootShard.fgLedgerPremisesStmtRootEntry_of_CV
#print axioms Tools.ShippingGen5PTRootShard.fgLedgerPremisesStmtRootBy_of_CV
#print axioms Tools.ShippingGen5PTRootShard.fgLedgerPremisesStmtRootEntry_nil_of_PTC
