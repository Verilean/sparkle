import Tools.ShippingGenFGLedgerPremises
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built at 9cb96b88c9999b3420d576b6cc49713caad80bf5 (agent incremental `kjob lake build`, exit 0; the clean issue-linked build is the coder's).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # Check for `Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmt` (scripts/gen2/PREMISE_LEDGER.md §8.7)

A CONDITIONAL DESIGN CONFIRMATION (ledger delta 0 / 0). What is checked: (1) the full type against an independent `Expected` written in
this file; (2) the counts (typed hypotheses 7: outer 4 + inner 3; carrier binders 4; `L` 1); (3) the tail of the statement equals the unfolded
`FG_CONNECT` body; (4) the ledger counts (typed 7, registry 69, FG leaf 76, blocks 110, index 146 - 36 removed); (5) no hypothesis type is
`False`/`True` (a shape check only); (6) mutants, rejected by the comparator (signature/defeq rejection, NOT a semantic counterexample);
(7) axioms; (8) the closures of the three inner hypotheses (Q-F2).

NOT checked or claimed: a proof of the statement; that any of the 69 registry blocks is false or underivable; that the 7 hypotheses are
jointly satisfiable; that the carriers `ReflectsAll Post GP CV` can be supplied or are non-vacuous (they are bookkeeping binders, Q-F5); the
completion of T1, M3 or FG. With trivial carriers (`fgCond_trivial`) the schema stays conditional. -/

namespace Tests.Gen5.FGLedgerPremisesCheck
open Lean Meta Elab Command Term
open Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tests.Gen3.ExpectedType
open Tools.ShippingGenFGLedgerPremises

/-! ## 1. Independent Expected statement (written separately from the Tools file) and mutants -/

def ExpectedFGLedgerPremisesStmt : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom)
    (CV : ConstValueRel)
    (L : Laws mref cref)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)),
    ConstValueFunctional CV ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ q : Pkg ι dom, GP (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
          (p.d.shape.instOrigins.getD k .ord).child? = none →
          ∀ q : Pkg ι dom, GP (envAt cref w) (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

/-- mutant (rejected by signature / defeq; not a semantic counterexample) -/
def MutM1NoChildGuard : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom)
    (CV : ConstValueRel)
    (L : Laws mref cref)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)),
    ConstValueFunctional CV ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ q : Pkg ι dom, GP (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
          ∀ q : Pkg ι dom, GP (envAt cref w) (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

/-- mutant (rejected by signature / defeq; not a semantic counterexample) -/
def MutM2NoAdmCtx : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom)
    (CV : ConstValueRel)
    (L : Laws mref cref)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)),
    ConstValueFunctional CV ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ q : Pkg ι dom, GP (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), True →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
          (p.d.shape.instOrigins.getD k .ord).child? = none →
          ∀ q : Pkg ι dom, GP (envAt cref w) (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

/-- mutant (rejected by signature / defeq; not a semantic counterexample) -/
def MutM3WidthPlusOne : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom)
    (CV : ConstValueRel)
    (L : Laws mref cref)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)),
    ConstValueFunctional CV ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ q : Pkg ι dom, GP (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
          (p.d.shape.instOrigins.getD k .ord).child? = none →
          ∀ q : Pkg ι dom, GP (envAt cref w) (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some (pt.ty.bitWidth + 1)) →
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

/-- mutant (rejected by signature / defeq; not a semantic counterexample) -/
def MutM4NoO1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom)
    (CV : ConstValueRel)
    (L : Laws mref cref)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)),
    ConstValueFunctional CV ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ q : Pkg ι dom, GP (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
          (p.d.shape.instOrigins.getD k .ord).child? = none →
          ∀ q : Pkg ι dom, GP (envAt cref w) (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

/-- mutant (rejected by signature / defeq; not a semantic counterexample) -/
def MutM5TwoInner : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom)
    (CV : ConstValueRel)
    (L : Laws mref cref)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)),
    ConstValueFunctional CV ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ q : Pkg ι dom, GP (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
          (p.d.shape.instOrigins.getD k .ord).child? = none →
          ∀ q : Pkg ι dom, GP (envAt cref w) (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk) →
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

/-- mutant (rejected by signature / defeq; not a semantic counterexample) -/
def MutM6OtherFresh : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom)
    (CV : ConstValueRel)
    (L : Laws mref cref)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem (fun _ _ => False) mref cref)
    (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)),
    ConstValueFunctional CV ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ q : Pkg ι dom, GP (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
          (p.d.shape.instOrigins.getD k .ord).child? = none →
          ∀ q : Pkg ι dom, GP (envAt cref w) (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

/-- mutant (rejected by signature / defeq; not a semantic counterexample) -/
def MutM7ReachTrue : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom)
    (CV : ConstValueRel)
    (L : Laws mref cref)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)),
    ConstValueFunctional CV ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
      (∀ c, True → ∀ q : Pkg ι dom, GP (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
          (p.d.shape.instOrigins.getD k .ord).child? = none →
          ∀ q : Pkg ι dom, GP (envAt cref w) (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

/-! ## 2. Ledger counts (IDs of ledger §8.2; the 36 removed IDs of §8.1) -/

def idCTX : List String := ["A.P-01"]
def idANT : List String := ["A.P-02", "A.P-04"]
def idTY : List String := ["A.P-06", "C.EN-4", "C.RK-1", "C.RK-6", "C.CV-4", "D.T-1", "D.T-4"]
def idUN : List String := ["A.P-05", "A.P-18", "B.G-1", "B.G-3", "B.G-4", "B.G-5", "B.G-6", "B.G-7", "B.G-9", "B.F-4", "B.F-8", "B.P-1", "B.P-2", "B.P-3", "B.P-4", "B.P-5", "B.P-7", "B.P-8", "C.RR-2", "C.CR-2", "C.EN-1", "C.EN-2", "C.EN-3", "C.EN-5", "C.EN-6", "C.EN-7", "C.EN-8", "C.RK-2", "C.RK-4", "C.RK-7", "C.RK-8", "C.DO-2", "C.DO-3", "C.SM-1", "C.SM-2", "C.SM-3", "C.SM-4", "C.SM-6", "C.AC-2", "C.AC-3", "C.AC-4", "C.AC-5", "C.AC-7", "C.AC-9", "C.CV-1", "C.CV-2", "C.CV-3", "C.CV-5", "C.CV-6", "C.RT-1", "C.RT-2", "C.RT-3", "C.RT-4", "C.DG-1", "D.D-1", "D.D-3", "D.D-4", "D.D-5", "D.D-7", "D.E-1", "D.E-2", "D.E-3", "D.E-4", "D.E-5", "D.E-6", "D.E-7", "D.E-8", "D.E-9", "D.E-12"]
def idT1 : List String := ["A.P-07", "A.P-08", "A.P-09", "A.P-10", "A.P-11", "A.P-12", "A.P-14", "A.P-15", "A.P-16", "A.P-19", "A.P-22", "A.P-23", "A.P-24", "A.P-25", "A.P-26", "C.CR-1"]
def idPA : List String := ["A.P-13", "A.P-17", "C.CR-4", "C.RK-5", "C.SM-5", "C.SM-7", "D.T-2", "D.T-8", "D.T-9", "D.D-8"]
def idAU : List String := ["A.P-27", "A.P-28"]
def idXC : List String := ["A.P-21", "B.G-10", "D.E-13"]
def idRemoved : List String := ["B.F-3", "D.E-10", "A.P-03", "C.RR-1", "B.F-2", "D.E-11", "D.D-6", "B.F-5", "B.G-2", "C.CR-5", "D.T-12", "B.G-8", "B.F-6", "B.F-7", "C.RR-3", "D.D-9", "C.AC-6", "B.P-6", "D.D-2", "D.P1", "D.T-7", "D.P2", "D.P3", "B.F-1", "C.CR-3", "C.AC-8", "D.T-3", "D.T-10", "D.T-11", "C.DG-2", "D.T-6", "D.T-5", "C.DO-1", "C.AC-1", "C.RK-3", "A.P-20"]
def idCarrier : List String := ["A.P-05", "D.D-1", "D.D-3", "D.D-4"]
def idsAll : List String := idCTX ++ idANT ++ idTY ++ idUN ++ idT1 ++ idPA ++ idAU ++ idXC

def nodup (xs : List String) : Bool := (xs.eraseDups).length == xs.length

run_cmd do
  let cnt := [("CTX", idCTX.length, 1), ("ANT", idANT.length, 2), ("TY", idTY.length, 7), ("UN", idUN.length, 69),
              ("T1", idT1.length, 16), ("PA", idPA.length, 10), ("AU", idAU.length, 2), ("XC", idXC.length, 3)]
  for (n, a, e) in cnt do
    unless a == e do throwError "FGLP CHECK FAILED: class {n} has {a} IDs, expected {e}"
  unless idsAll.length == 110 && nodup idsAll do throwError "FGLP CHECK FAILED: the 8 classes are not disjoint with sum 110"
  unless idRemoved.length == 36 && nodup idRemoved do throwError "FGLP CHECK FAILED: removed IDs"
  -- 146 = 110 + 36, all distinct (the ledger section-7 index has 146 rows: A4 checks that outside Lean)
  unless nodup (idsAll ++ idRemoved) && (idsAll ++ idRemoved).length == 146 do
    throwError "FGLP CHECK FAILED: 110 + 36 is not 146 distinct IDs"
  -- registry 69, FG-side leaves 76 = typed 7 + registry 69
  unless idUN.length == 69 && idTY.length + idUN.length == 76 do throwError "FGLP CHECK FAILED: leaf count"
  -- lines of the statement: CTX + ANT + TY + 4 carriers = 14; the carriers are registry blocks
  unless idCarrier.all (fun c => idUN.contains c) do throwError "FGLP CHECK FAILED: carrier not in registry"
  unless (idCTX.length + idANT.length + idTY.length + idCarrier.length) == 14 do throwError "FGLP CHECK FAILED: 14"
  logInfo m!"FGLP COUNTS OK: typed 7, registry 69, FG leaves 76, blocks 110, index 146 = 110 + 36 (ledger delta 0 / 0)"

/-! ## 3. Binder counts, the FG_CONNECT tail, no empty binder -/

/-- the binders (name, type) of the telescope, and the final body -/
def teleInfo (e : Expr) : MetaM (Array (Name × Expr) × Nat) := do
  forallTelescope e fun xs _ => do
    let mut r := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      r := r.push (d.userName, d.type)
    return (r, xs.size)

def isConstApp (c : Name) (e : Expr) : Bool := e.getUsedConstants.contains c

def checkShape : MetaM Unit := do
  let stmt ← stmtOf ``FGLedgerPremisesStmt
  forallTelescope stmt fun xs body => do
    -- outer binders: 2 implicit types + 2 implicit refs + 4 carriers + L + 4 outer hypotheses = 13
    unless xs.size == 13 do throwError "FGLP CHECK FAILED A1: outer binders {xs.size}, expected 13"
    let names ← xs.mapM fun x => do pure (← x.fvarId!.getDecl).userName
    let hs := names.filter fun n => (n.toString.startsWith "h_")
    unless hs == #[`h_C_EN4, `h_C_RK1, `h_C_RK6, `h_C_CV4] do throwError "FGLP CHECK FAILED A1: outer h_ binders {hs}"
    unless names[4:9].toArray == #[`ReflectsAll, `Post, `GP, `CV, `L] do throwError "FGLP CHECK FAILED A1: carriers/L {names[4:9]}"
    -- body = ConstValueFunctional CV ∧ ∀ declName .. D, EntryWitness .. → H1 → H2 → H3 → tail
    let some (cvf, rest) := body.and? | throwError "FGLP CHECK FAILED A2: body is not a conjunction"
    unless isConstApp ``ConstValueFunctional cvf do throwError "FGLP CHECK FAILED A2: first conjunct"
    forallTelescope rest fun ys tail => do
      unless ys.size == 8 + 1 + 3 do throwError "FGLP CHECK FAILED A1: run binders {ys.size}, expected 8 + EntryWitness + 3 inner"
      let tys ← ys.mapM fun y => do pure (← y.fvarId!.getDecl).type
      unless isConstApp ``EntryWitness tys[8]! do throwError "FGLP CHECK FAILED A1: EntryWitness position"
      unless isConstApp ``Tools.ShippingMachineEntry.MachineDefines tys[9]! do throwError "FGLP CHECK FAILED A1: inner 1 (h_A_P06)"
      unless isConstApp ``GenExtAtCall tys[10]! do throwError "FGLP CHECK FAILED A1: inner 2 (h_D_T1)"
      unless isConstApp ``Tools.ShippingMachineEntry.kindTy tys[11]! do throwError "FGLP CHECK FAILED A1: inner 3 (h_D_T4)"
      -- A2: against the unfolded FG_CONNECT on the same fvars
      let ι := xs[0]!; let dom := xs[1]!; let mref := xs[2]!; let cref := xs[3]!
      let fg := mkAppN (Lean.mkConst ``FG_CONNECT) #[ι, dom, mref, cref, xs[4]!, xs[5]!, xs[6]!, xs[7]!, xs[8]!]
      let some fgU ← unfoldDefinition? fg | throwError "FGLP CHECK FAILED A2: cannot unfold FG_CONNECT"
      let fgB := fgU.headBeta
      let some (cvf', rest') := fgB.and? | throwError "FGLP CHECK FAILED A2: FG_CONNECT body"
      unless cvf == cvf' do throwError "FGLP CHECK FAILED A2: ConstValueFunctional conjunct differs"
      forallTelescope rest' fun zs tail' => do
        unless zs.size == 9 do throwError "FGLP CHECK FAILED A2: FG_CONNECT run binders {zs.size}"
        for i in [0:9] do
          let a ← inferType ys[i]!
          let b ← inferType zs[i]!
          let b := b.replaceFVars zs ys[:9].toArray
          unless a == b do throwError "FGLP CHECK FAILED A2: run binder {i} (incl. EntryWitness) differs from FG_CONNECT"
        let tail'' := tail'.replaceFVars zs ys[:9].toArray
        unless tail == tail'' do throwError "FGLP CHECK FAILED A2: conclusion tail differs from FG_CONNECT"
      -- no empty binder: each of the 7 hypothesis types is neither False nor True (shape check only)
      let hypTys := (xs[9:13].toArray.map fun x => x) |>.map id
      let mut allH : Array Expr := #[]
      for x in hypTys do allH := allH.push (← x.fvarId!.getDecl).type
      for i in [9:12] do allH := allH.push tys[i]!
      unless allH.size == 7 do throwError "FGLP CHECK FAILED A1: typed hypotheses {allH.size}, expected 7"
      for T in allH do
        if T == Lean.mkConst ``False || T == Lean.mkConst ``True then throwError "FGLP CHECK FAILED: trivial hypothesis type"
        if (← withoutModifyingState (isDefEq T (Lean.mkConst ``False))) then throwError "FGLP CHECK FAILED: hypothesis defeq False"
        if (← withoutModifyingState (isDefEq T (Lean.mkConst ``True))) then throwError "FGLP CHECK FAILED: hypothesis defeq True"
      -- Q-F2: the three closures quantify over TgtRun and the registered guards
      unless isConstApp ``TgtRun tys[9]! && isConstApp ``TgtRun tys[10]! && isConstApp ``TgtRun tys[11]! do
        throwError "FGLP CHECK FAILED Q-F2: reach predicate"
      unless isConstApp ``Tools.ShippingChildInvA.AdmCtx tys[9]! do throwError "FGLP CHECK FAILED Q-F2: AdmCtx of h_A_P06"
      unless tys[10]!.getUsedConstants.any (fun c => c.toString.endsWith "child?") do
        throwError "FGLP CHECK FAILED Q-F2: child? = none guard of h_D_T1"
      unless isConstApp ``Tools.ShippingChildCacheA.RealChildA tys[11]! do throwError "FGLP CHECK FAILED Q-F2: output-pin quantification of h_D_T4"
      logInfo m!"FGLP SHAPE OK: outer 13 binders (4 carriers, L, 4 outer h_), 7 typed hypotheses (4 + 3), tail = FG_CONNECT body, none False/True"

run_cmd Lean.Elab.Command.liftTermElabM checkShape

/-! ## 4. Full type against Expected, mutants, axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``FGLedgerPremisesStmt ``ExpectedFGLedgerPremisesStmt
  checkMutant ``FGLedgerPremisesStmt ``MutM1NoChildGuard
  checkMutant ``FGLedgerPremisesStmt ``MutM2NoAdmCtx
  checkMutant ``FGLedgerPremisesStmt ``MutM3WidthPlusOne
  checkMutant ``FGLedgerPremisesStmt ``MutM4NoO1
  checkMutant ``FGLedgerPremisesStmt ``MutM5TwoInner
  checkMutant ``FGLedgerPremisesStmt ``MutM6OtherFresh
  checkMutant ``FGLedgerPremisesStmt ``MutM7ReachTrue
  checkAxioms ``FGLedgerPremisesStmt
  checkAxioms ``ExpectedFGLedgerPremisesStmt

#print axioms FGLedgerPremisesStmt
#print axioms ExpectedFGLedgerPremisesStmt

end Tests.Gen5.FGLedgerPremisesCheck
