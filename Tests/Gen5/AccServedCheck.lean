import Tools.ShippingGen5AccServed
import Tests.Gen5.AccCheck
set_option autoImplicit false
-- Built in the Pod (g5ac-r6) at 5c38c6fc: `kjob lake build Tests.Gen5.AccServedCheck`, exit 0, 723 jobs. TYPE 15 (4 definitions + 11 theorems, all syntactic, no isDefEq fallback; the 2 helper theorems `getEnv_runs_exists`/`accServed_core` are covered by AXIOMS / CLOSURE, not TYPE), MUTANT 12 (signature/defeq rejection, not semantic), AXIOMS 17 (standard three; 15 TYPE items + 2 helpers), walker controls + unknown controls + CLOSURE OK 13304 constants, ENVQ AGREEMENT by source text (2 changed copies rejected). Clean issue-linked build is the coder's. No sorry / axiom / native_decide in this source (the 3 `sorry` warnings come from the intended walker-control negatives).

/-! # DG-ACC unit A5b checks (Tools/ShippingGen5AccServed.lean; scripts/gen5/DG_ACC_FREEZE_REV3.md §2.2-§2.5)

TYPE: the 4 definitions (`MachineRouteAt`, `RunDataLink`, `DataOfShape`, `ChildrenAccI`) and the 11 theorems of REV3 §2.2-§2.5 are each compared
binder by binder (`checkExpected`) with an independently written `Expected…` statement (written from the prose of REV3, not copied from the
implementation file). The two extra theorems of the file (`getEnv_runs_exists`, `accServed_core`) are helpers of the assembly: they are NOT in
the TYPE count; they are covered by AXIOMS and CLOSURE.
MUTANT: one-place, well-typed changes (or a dropped conjunct / premise) rejected by `checkMutant` -- a rejection by signature / defeq, NOT a
semantic counterexample. AXIOMS: standard three only. CLOSURE: the explicit-value walker of `AccCheck`, with its negative/clean controls and the
unknown-name controls re-run; the roots are put in `seen` and judged.
ENVQ AGREEMENT: `QuietStrengthA` / `AdmDownA` (in `ShippingGen5AccReads`, used by `readsSupply_of_quiet`) are textual copies of EnvQ's
`QuietStrength` / `AdmDown`. EnvQ cannot be imported here (its dependency `Tools/ShippingGen5T2Tie.lean` fails to elaborate on this base),
so the Check compares the definition TEXT of the copies with `Tools/ShippingGen5EnvQ.lean` (whitespace-normalised, `env₀` renamed) and
rejects a changed copy (negative control). This shows the copies agree with the original text on this base; it is not a typed comparison,
and the copies are still to be unified at EnvQ integration. -/
namespace Tests.Gen5.AccServedCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tests.Gen3.ExpectedType
open Tools.ShippingGen2 (Laws)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (CoreSaved coreHead)
open Tools.ShippingChildInv (Res profLogIO)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingChildCacheA (JQC RealChildA)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingMachineEntry (MachineCloses MemChildren machNIn)
open Tools.ShippingGen5Env (ReadsAt MachineDefinesR)
open Tools.ShippingMachineAuto (MachineData)

section Expected

def ExpectedMachineRouteAt {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (env₀ : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∃ shape : MachineShape, MachineDefinesR env₀ mctx mref cctx cref c shape ∧ MachineClosesAtA L.O mctx cctx c shape

def ExpectedRunDataLink {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ shape : MachineShape, MachineDefinesR env₀ mctx mref cctx cref c shape →
      ∃ d, dataOf₀ K c = some d ∧ d.shape = shape

def ExpectedDataOfShape {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (K : AssignKit ι dom env₀) : Prop :=
  ∀ (E : ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), K.dataOf E se s = some d → d.shape = s

def ExpectedChildrenAccI {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop) (shape : MachineShape) (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    ((shape.instOrigins.getD k .ord).child? = some y ∨
      (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → Acc (CallRel K) (shape.insts[k]).1)))

def ExpectedClear : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ (D : Nat) {R : Exception → Void IO.RealWorld → Prop},
    Tools.ShippingChildInv.Triple mctx mref cctx cref (JQ L.O.quiet D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => AccInvAt K L Reach D) R

def ExpectedHead : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {X : Name} {D : Nat} {w w1 : Void IO.RealWorld} {s : CoreSaved},
    (hw : JQC L.O D w) → (hc : D = 0 ∨ CacheAcc K Reach (cv w)) →
    (hh : RunsTo (coreHead X) mctx mref cctx cref w s w1) → AccInvAt K L Reach (D + 1) w1

def ExpectedMachineBranch : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) →
    ∀ {tenv : Environment} {b : Bool} {X : Name} {n : Nat} {ci : ConstantInfo} {isInst : Lean.Expr → Bool}
      {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld},
    (old : certifiedShape? false [] ci = none) → (miss : mixedCertifiedShape? false [] ci isInst = none) →
    (hw : AccInvAt K L Reach n w) →
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false true
      ci isInst) mctx mref cctx cref w (m, d) w') →
    ∃ (envR' : Environment) (w₁ : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR' w₁ ∧
      ∀ shape, machineShape? false [] ci (structEnv envR') = some shape →
        ∃ (r : Option Res) (w₂ : Void IO.RealWorld),
          RunsTo (synthesizeMachineCertified (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X shape)
            mctx mref cctx cref w₁ r w₂ ∧ AccInvAt K L Reach n w₁ ∧ (∀ res, r = some res → res = (m, d))

def ExpectedChildAcc : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res},
    (hw : AccInvAt K L Reach D w) → (hIH : AccIHAt K L Reach D) → (hKI : AccChildKeeps K L Reach D) →
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') →
    RealChildA L.O n r ∧ (Reach n → Acc (CallRel K) n) ∧ AccInvAt K L Reach D w'

def ExpectedCloseM : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {D : Nat}, (hIH : AccIHAt K L Reach D) → (hKI : AccChildKeeps K L Reach D) →
    ∀ {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
      {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld},
    (hw : AccInvAt K L Reach D w) →
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') →
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      children.length = shape.insts.length ∧
      (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → Acc (CallRel K) (shape.insts[k]).1))) ∧
      AccInvAt K L Reach D w'

def ExpectedCloseGM : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {D : Nat}, (hIH : AccIHAt K L Reach D) → (hKI : AccChildKeeps K L Reach D) →
    ∀ {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
      {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld},
    (hw : AccInvAt K L Reach D w) →
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') →
    ∃ children, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧ MemChildren shape children ∧
      ChildrenAccI K L Reach shape children ∧ AccInvAt K L Reach D w'

def ExpectedRunsAcc : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {n : Nat} {tenv : Lean.Environment},
    (hIH : AccIHAt K L Reach n) → (hKI : AccChildKeeps K L Reach n) →
    ∀ {b : Bool} {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module}
      {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld},
    (hw : AccInvAt K L Reach n w) →
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') →
    (shape.insts = [] ∨ (shape.insts ≠ [] ∧ ∃ children, ChildrenAccI K L Reach shape children))

def ExpectedChildrenReached : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    {L : Laws mref cref} {Reach : Name → Prop},
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) → ∀ {X : Name}, (hX : Reach X) →
    ∀ {d : MachineData}, (hd : dataOf₀ K X = some d) → ∀ {shape : MachineShape}, (hsh : d.shape = shape) →
    ∀ {children : List Res}, (hch : ChildrenAccI K L Reach shape children) →
    ∀ c, CallEdge K X c → Acc (CallRel K) c

def ExpectedServedRoute : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) →
    (hRoute : MachineRouteAt env₀ L Reach) → (hLink : RunDataLink K L Reach) →
    (hRS : ReadsSupplyAt env₀ L Reach) → AccServed0Stmt K L Reach

def ExpectedClosesBridge : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) {c : Name} {shape : MachineShape},
    (h : MachineCloses mctx mref cctx cref c shape) → MachineClosesAtA L.O mctx cctx c shape

def ExpectedServedCover : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) →
    (hRoute : MachineRouteAt env₀ L Reach) → (hcov : ReachCover K Reach) → (hDS : DataOfShape K) →
    (hRS : ReadsSupplyAt env₀ L Reach) → AccServed0Stmt K L Reach

-- mutants (each well-typed, one place changed; signature/defeq rejection only)
/-- `hcl` dropped from `accServed0_of_route` -/
def MutRouteNoHcl : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hRoute : MachineRouteAt env₀ L Reach) → (hLink : RunDataLink K L Reach) →
    (hRS : ReadsSupplyAt env₀ L Reach) → AccServed0Stmt K L Reach

/-- `hcl` dropped from `accServed0_of_cover` -/
def MutCoverNoHcl : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hRoute : MachineRouteAt env₀ L Reach) → (hcov : ReachCover K Reach) → (hDS : DataOfShape K) →
    (hRS : ReadsSupplyAt env₀ L Reach) → AccServed0Stmt K L Reach

/-- `ReadsSupplyAt` dropped from `accServed0_of_route` -/
def MutRouteNoReads : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) →
    (hRoute : MachineRouteAt env₀ L Reach) → (hLink : RunDataLink K L Reach) → AccServed0Stmt K L Reach

/-- `DataOfShape` dropped from `accServed0_of_cover` -/
def MutCoverNoDataOfShape : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) →
    (hRoute : MachineRouteAt env₀ L Reach) → (hcov : ReachCover K Reach) →
    (hRS : ReadsSupplyAt env₀ L Reach) → AccServed0Stmt K L Reach

/-- `ChildrenAccI` with the `Reach` premise dropped from the `Acc` conjunct -/
def MutChildrenNoReach {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop) (shape : MachineShape) (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    ((shape.instOrigins.getD k .ord).child? = some y ∨
      (RealChildA L.O (shape.insts[k]).1 y ∧ Acc (CallRel K) (shape.insts[k]).1))

/-- `childrenAcc_reached` without `hcl` -/
def MutReachedNoHcl : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    {L : Laws mref cref} {Reach : Name → Prop},
    ∀ {X : Name}, (hX : Reach X) →
    ∀ {d : MachineData}, (hd : dataOf₀ K X = some d) → ∀ {shape : MachineShape}, (hsh : d.shape = shape) →
    ∀ {children : List Res}, (hch : ChildrenAccI K L Reach shape children) →
    ∀ c, CallEdge K X c → Acc (CallRel K) c

/-- `coreHead_accInvAt` without the cache disjunct -/
def MutHeadNoCache : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {X : Name} {D : Nat} {w w1 : Void IO.RealWorld} {s : CoreSaved},
    (hw : JQC L.O D w) →
    (hh : RunsTo (coreHead X) mctx mref cctx cref w s w1) → AccInvAt K L Reach (D + 1) w1

/-- `synthesizeChild_acc` without `AccChildKeeps` -/
def MutChildAccNoKeeps : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res},
    (hw : AccInvAt K L Reach D w) → (hIH : AccIHAt K L Reach D) →
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') →
    RealChildA L.O n r ∧ (Reach n → Acc (CallRel K) n) ∧ AccInvAt K L Reach D w'

/-- `fromConst_machine_accInvAt` without the conjunct `AccInvAt n w₁` -/
def MutMachineBranchNoInv : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) →
    ∀ {tenv : Environment} {b : Bool} {X : Name} {n : Nat} {ci : ConstantInfo} {isInst : Lean.Expr → Bool}
      {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld},
    (old : certifiedShape? false [] ci = none) → (miss : mixedCertifiedShape? false [] ci isInst = none) →
    (hw : AccInvAt K L Reach n w) →
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false true
      ci isInst) mctx mref cctx cref w (m, d) w') →
    ∃ (envR' : Environment) (w₁ : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR' w₁ ∧
      ∀ shape, machineShape? false [] ci (structEnv envR') = some shape →
        ∃ (r : Option Res) (w₂ : Void IO.RealWorld),
          RunsTo (synthesizeMachineCertified (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X shape)
            mctx mref cctx cref w₁ r w₂ ∧ (∀ res, r = some res → res = (m, d))

/-- `MachineRouteAt` without the admissibility premise -/
def MutRouteAtNoAdm {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (env₀ : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context),
    ∃ shape : MachineShape, MachineDefinesR env₀ mctx mref cctx cref c shape ∧ MachineClosesAtA L.O mctx cctx c shape

/-- `RunDataLink` without the shape equation -/
def MutLinkNoShape {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ shape : MachineShape, MachineDefinesR env₀ mctx mref cctx cref c shape →
      ∃ d, dataOf₀ K c = some d

/-- `DataOfShape` reversed (the shape is given, the data is concluded) -/
def MutDataOfShapeWrong {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (K : AssignKit ι dom env₀) : Prop :=
  ∀ (E : ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), d.shape = s → K.dataOf E se s = some d

end Expected

section Examples
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
/-- the cover form's conclusion statement is the same as the route form's (they differ only in the link premise) -/
example (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop := AccServed0Stmt K L Reach
end Examples

/-! ## EnvQ agreement (copies vs originals, by source text) -/

/-- The text of `def <name> …` up to the next blank line, whitespace-normalised, with the definition name removed and `env₀` renamed `e`. -/
def defText (src : String) (name : String) : Option String := do
  let rest ← (src.splitOn ("def " ++ name ++ " "))[1]?
  let blk := (rest.splitOn "\n\n").head!
  let ws := ((blk.replace "\n" " ").splitOn " ").filter (· ≠ "")
  pure (" ".intercalate (ws.map fun w => w.replace "env₀" "e"))

/-- `EnvQ` cannot be built on this base (`Tools/ShippingGen5T2Tie.lean` does not elaborate here, independent of this unit), so the copies
`QuietStrengthA` / `AdmDownA` are compared with `Tools/ShippingGen5EnvQ.lean` by source text, not by `isDefEq`. -/
def agreement : IO Unit := do
  let envq ← IO.FS.readFile "Tools/ShippingGen5EnvQ.lean"
  let reads ← IO.FS.readFile "Tools/ShippingGen5AccReads.lean"
  let get (src n : String) : IO String :=
    match defText src n with
    | some t => pure t
    | none => throw (IO.userError s!"GEN5 ENVQ AGREEMENT FAILED: no `def {n}` found")
  let q ← get envq "QuietStrength"
  let qa ← get reads "QuietStrengthA"
  let a ← get envq "AdmDown"
  let aa ← get reads "AdmDownA"
  unless q == qa do throw (IO.userError s!"GEN5 ENVQ AGREEMENT FAILED: QuietStrengthA differs:\n{qa}\nvs\n{q}")
  unless a == aa do throw (IO.userError s!"GEN5 ENVQ AGREEMENT FAILED: AdmDownA differs:\n{aa}\nvs\n{a}")
  -- negative controls: a changed copy must NOT agree
  if q == qa.replace "∧" "∨" then throw (IO.userError "GEN5 ENVQ AGREEMENT CONTROL FAILED: changed QuietStrengthA accepted")
  if a == aa.replace "AdmCtx L.O" "AdmCtx L'.O" then throw (IO.userError "GEN5 ENVQ AGREEMENT CONTROL FAILED: changed AdmDownA accepted")
  IO.println "GEN5 ENVQ AGREEMENT OK: the definitions of QuietStrengthA and AdmDownA agree with EnvQ's source text; 2 changed copies rejected"

#eval agreement

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``MachineRouteAt ``ExpectedMachineRouteAt
  checkExpected ``RunDataLink ``ExpectedRunDataLink
  checkExpected ``DataOfShape ``ExpectedDataOfShape
  checkExpected ``ChildrenAccI ``ExpectedChildrenAccI
  checkExpected ``tripleAcc_clear ``ExpectedClear
  checkExpected ``coreHead_accInvAt ``ExpectedHead
  checkExpected ``fromConst_machine_accInvAt ``ExpectedMachineBranch
  checkExpected ``synthesizeChild_acc ``ExpectedChildAcc
  checkExpected ``closeInstsM_acc ``ExpectedCloseM
  checkExpected ``closeInstsGM_acc ``ExpectedCloseGM
  checkExpected ``synthesizeMachineCertified_runsAcc ``ExpectedRunsAcc
  checkExpected ``childrenAcc_reached ``ExpectedChildrenReached
  checkExpected ``accServed0_of_route ``ExpectedServedRoute
  checkExpected ``machineClosesAtA_of_closes ``ExpectedClosesBridge
  checkExpected ``accServed0_of_cover ``ExpectedServedCover
  checkMutant ``accServed0_of_route ``MutRouteNoHcl
  checkMutant ``accServed0_of_cover ``MutCoverNoHcl
  checkMutant ``accServed0_of_route ``MutRouteNoReads
  checkMutant ``accServed0_of_cover ``MutCoverNoDataOfShape
  checkMutant ``ChildrenAccI ``MutChildrenNoReach
  checkMutant ``childrenAcc_reached ``MutReachedNoHcl
  checkMutant ``coreHead_accInvAt ``MutHeadNoCache
  checkMutant ``synthesizeChild_acc ``MutChildAccNoKeeps
  checkMutant ``fromConst_machine_accInvAt ``MutMachineBranchNoInv
  checkMutant ``MachineRouteAt ``MutRouteAtNoAdm
  checkMutant ``RunDataLink ``MutLinkNoShape
  checkMutant ``DataOfShape ``MutDataOfShapeWrong

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``MachineRouteAt, ``RunDataLink, ``DataOfShape, ``ChildrenAccI, ``tripleAcc_clear, ``coreHead_accInvAt,
      ``fromConst_machine_accInvAt, ``synthesizeChild_acc, ``closeInstsM_acc, ``closeInstsGM_acc,
      ``synthesizeMachineCertified_runsAcc, ``childrenAcc_reached, ``accServed0_of_route, ``machineClosesAtA_of_closes,
      ``accServed0_of_cover, ``getEnv_runs_exists, ``accServed_core] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

/-- Unknown-name controls through the same `closureReport` path (see AccIndCheck): root / helper value / helper type naming an
absent constant MUST be reported; a clean chain MUST NOT. -/
def unknownControls : MetaM Unit := do
  let ghost := `Ghost.Absent.name
  let addU (n : Name) (type value : Expr) : MetaM Unit :=
    withOptions (fun o => debug.skipKernelTC.set o true) do
      addDecl (.thmDecl { name := n, levelParams := [], type := type, value := value })
  let unk (roots : List Name) : MetaM (Array Name) := do
    let (_, u, _) ← Tests.Gen5.AccCheck.closureReport (← getEnv) roots
    pure u
  let u1 ← unk [ghost]
  unless u1 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: unknown root not reported ({u1})"
  let u2 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperVal (mkConst ``True) (mkConst ghost)
    addU `Tests.Gen5.UnkCtl.RootVal (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperVal)
    unk [`Tests.Gen5.UnkCtl.RootVal]
  unless u2 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper value naming an unknown constant not reported ({u2})"
  let u3 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperTy (mkConst ghost) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.RootTy (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperTy)
    unk [`Tests.Gen5.UnkCtl.RootTy]
  unless u3 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper type naming an unknown constant not reported ({u3})"
  let u4 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.CleanHelper (mkConst ``True) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.CleanRoot (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.CleanHelper)
    unk [`Tests.Gen5.UnkCtl.CleanRoot]
  unless u4.isEmpty do throwError "GEN5 UNKNOWN CONTROL FAILED: clean control reported unknown ({u4})"
  logInfo m!"GEN5 UNKNOWN CONTROLS OK: 3 negatives reported unknown (root / helper value / helper type), clean control not reported"

run_cmd Lean.Elab.Command.liftTermElabM unknownControls

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``MachineRouteAt, ``RunDataLink, ``DataOfShape, ``ChildrenAccI, ``tripleAcc_clear, ``coreHead_accInvAt,
    ``fromConst_machine_accInvAt, ``synthesizeChild_acc, ``closeInstsM_acc, ``closeInstsGM_acc,
    ``synthesizeMachineCertified_runsAcc, ``childrenAcc_reached, ``accServed0_of_route, ``machineClosesAtA_of_closes,
    ``accServed0_of_cover, ``getEnv_runs_exists, ``accServed_core]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A5b): {seen.toList.length} constants, no forbidden constant, no supplier-unit constant, no unknown constant"

end Tests.Gen5.AccServedCheck
