import Tools.ShippingGen5AccInd
import Tools.ShippingGen5EnvR
import Tools.ShippingGen5RunReads
set_option autoImplicit false
-- Clean issue-linked build ac6v-a88c3e9c (incremental kjob lake build): exit 0, 724 jobs, source=base=end, dirty=false, approved at a88c3e9c (earlier clean build ac5v-802381fe, approved at 802381fe) (earlier Pod build g5ac-r5 at 0f120373, 716 jobs). No sorry / axiom / native_decide.

/-! # DG-ACC rev2 R1 (read worlds) and R2 (`hacc` from top runs) (scripts/gen5/DG_ACC_FREEZE_REV2.md §B.2, §C.2)

The statements are those of the freeze text. CONDITIONAL: `readsSupply_of_quiet` needs `QuietStrengthA` and `GetEnvFrame` as premises,
`accInvAt_down` needs `AdmDownA`; `hacc_of_top_runs` needs `AccServed0Stmt`, `AccKeepChildStmt`, `LimitStmt` and a successful outermost run of
each top. Nothing here supplies them. `QuietStrengthA`/`AdmDownA` are textual copies of EnvQ's (EnvQ cannot be imported on this base). -/
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (CoreSaved coreHead)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingChildCacheA (JQC RealChildA)
open Tools.ShippingChildBndCore (cv dv sv)
open Tools.ShippingGen5Env (ReadsAt MachineDefinesR)
open Tools.ShippingEnvSnapshot (GetEnvFrame envFrame_getConstInfo)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
variable (K : AssignKit ι dom env₀)

/-! ## R1 -/

/-- Copy of `Tools.ShippingGen5EnvQ.QuietStrength` (EnvQ cannot be imported on this base, freeze rev1 §B.0). -/
def QuietStrengthA (L L' : Laws mref cref) (e : Environment) : Prop :=
  ∀ w, L'.O.quiet w ↔ (L.O.quiet w ∧ ReadsAt e cref w)

/-- Copy of `Tools.ShippingGen5EnvQ.AdmDown`. -/
def AdmDownA (L L' : Laws mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L'.O.quiet mctx cctx → AdmCtx L.O.quiet mctx cctx

/-- The read worlds of the actual run chain (`RunReadsAt.chain`): the three worlds at which `MachineDefinesR` asks `ReadsAt`. -/
def ChainReadsAt (e : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (X : Name) (w : Void IO.RealWorld) : Prop :=
  ∀ (s : CoreSaved) (w1 w2 w3 w5 : Void IO.RealWorld) (ci : ConstantInfo) (envR envR' : Environment),
    RunsTo (coreHead X) mctx mref cctx cref w s w1 →
    RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
    ReadsAt e cref w1 ∧ ReadsAt e cref w2 ∧ ReadsAt e cref w3

/-- The exact supply proposition for the read worlds (R1 (a)): at the start `w` of a run of a reached name. -/
def ReadsSupplyAt (e : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ X, Reach X → ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld),
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → ChainReadsAt e mctx mref cctx cref X w

/-- Use: `MachineDefinesR` gives its three conjuncts at the chain's read worlds. -/
theorem machineDefines_at_chain {e : Environment} {mctx : Meta.Context} {cctx : Core.Context} {X : Name}
    {shape : MachineShape} {w : Void IO.RealWorld} (hD : MachineDefinesR e mctx mref cctx cref X shape)
    (hR : ChainReadsAt e mctx mref cctx cref X w) {s : CoreSaved} {w1 w2 w3 w5 : Void IO.RealWorld}
    {ci : ConstantInfo} {envR envR' : Environment}
    (h0 : RunsTo (coreHead X) mctx mref cctx cref w s w1)
    (h1 : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2)
    (h2 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (h3 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5) :
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (instancePredicate envR) = none ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape := by
  obtain ⟨r1, r2, r3⟩ := hR s w1 w2 w3 w5 ci envR envR' h0 h1 h2 h3
  exact hD w1 ci w2 w2 envR w3 w3 envR' w5 r1 r2 r3 h1 h2 h3

/-- (b) `AccInvAt` at a quiet-strengthened `L'` carries `ReadsAt`. -/
theorem accInvAt_readsAt {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e)
    {Reach : Name → Prop} {D : Nat} {w : Void IO.RealWorld} (h : AccInvAt K L' Reach D w) : ReadsAt e cref w :=
  ((hq w).mp h.1.1.1).2

theorem jqA_down {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e) {D : Nat}
    {w : Void IO.RealWorld} (h : JQ L'.O.quiet D w) : JQ L.O.quiet D w := by
  unfold JQ at h ⊢
  exact ⟨((hq w).mp h.1).1, h.2⟩

theorem realChildA_downA {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e)
    (hd : AdmDownA L L') {c : Name} {r : Res} (h : RealChildA L'.O c r) : RealChildA L.O c r := by
  induction h with
  | run mctx cctx w w' adm _ synth quiet hr ih =>
    exact .run mctx cctx w w' (hd _ _ adm) (fun c' r' hc => ih c' r' hc) synth ((hq w).mp quiet).1 hr

theorem jqc_downA {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e)
    (hd : AdmDownA L L') {D : Nat} {w : Void IO.RealWorld} (h : JQC L'.O D w) : JQC L.O D w :=
  ⟨jqA_down hq h.1, fun c r hc => realChildA_downA hq hd (h.2 c r hc)⟩

/-- Transport `L' → L` of the Acc invariant (needs `AdmDownA`, an OPEN premise of DG-ENV). -/
theorem accInvAt_down {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e)
    (hd : AdmDownA L L') {Reach : Name → Prop} {D : Nat} {w : Void IO.RealWorld}
    (h : AccInvAt K L' Reach D w) : AccInvAt K L Reach D w :=
  ⟨jqc_downA hq hd h.1, h.2⟩

/-- The supply of the read worlds at the quiet-strengthened `L'`: from `QuietStrengthA` and the one primitive premise
`GetEnvFrame` (DG-ENV). The head world `w1` is quiet by RR1 (`coreHead_jqcA`), hence `ReadsAt`; `w2`, `w3` by the frame. -/
theorem readsSupply_of_quiet {L L' : Laws mref cref} {e : Environment} (hq : QuietStrengthA L L' e)
    (hg : ∀ (mctx : Meta.Context) (cctx : Core.Context), GetEnvFrame mctx mref cctx cref)
    (Reach : Name → Prop) : ReadsSupplyAt e L' Reach := by
  intro X _ mctx cctx w hA hjqc s w1 w2 w3 w5 ci envR envR' h0 h1 h2 h3
  have hj1 : JQC L'.O (dv w + 1) w1 :=
    Tools.ShippingGen5RunReads.coreHead_jqcA L'.O hA hjqc.1 (Or.inr hjqc.2) h0
  have r1 : ReadsAt e cref w1 := ((hq w1).mp hj1.1.1).2
  have r2 : ReadsAt e cref w2 :=
    Tools.ShippingGen5Env.ReadsAt.of_frame (envFrame_getConstInfo X (hg mctx cctx)) h1 r1
  exact ⟨r1, r2, Tools.ShippingGen5Env.ReadsAt.of_frame (hg mctx cctx) h2 r2⟩

/-! ## R2 -/

/-- Acc flows down the static edges (`Acc.inv`; `CallRel K c X = CallEdge K X c`). -/
theorem acc_of_edge {X c : Name} (h : Acc (CallRel K) X) (he : CallEdge K X c) : Acc (CallRel K) c :=
  h.inv he

theorem acc_reach_of_top {Top : Name → Prop} (hT : ∀ t, Top t → Acc (CallRel K) t) :
    ∀ c, ReachEdge K Top c → Acc (CallRel K) c := by
  intro c hc
  induction hc with
  | top ht => exact hT _ ht
  | edge _ he ih => exact acc_of_edge K ih he

/-- A successful outermost run of `t` gives `Acc t` (its served static callees are `Acc`, and `Acc.intro`). -/
theorem acc_top_of_run (L : Laws mref cref) (Reach : Name → Prop) (hS : AccServed0Stmt K L Reach)
    (hI : AccIHAt K L Reach 1) (hKI : AccChildKeeps K L Reach 1) {t : Name} (ht : Reach t)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {r : Res}
    (hSt : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCore t [] false) mctx mref cctx cref w r w') :
    Acc (CallRel K) t := by
  have hdv : dv w = 0 := hSt.2.1.2.2
  have hIH : AccIHAt K L Reach (dv w + 1) := by rw [hdv]; exact hI
  have hKI' : AccChildKeeps K L Reach (dv w + 1) := by rw [hdv]; exact hKI
  have hsrv := hS t mctx cctx w w' r ht hSt.1 (by rw [hdv]; exact hSt.2) (Or.inl hdv) hIH hKI' hr
  exact Acc.intro t fun y hy => hsrv y hy

/-- `hacc` for every reached name from successful outermost runs of the tops (no run of the other reached names). -/
theorem hacc_of_top_runs (L : Laws mref cref) (Top : Name → Prop)
    (hLim : LimitStmt L) (hS : AccServed0Stmt K L (ReachEdge K Top)) (hKC : AccKeepChildStmt K L (ReachEdge K Top))
    (hrun : ∀ t, Top t → ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
      Start L mctx cctx w ∧ RunsTo (synthesizeCombinationalCore t [] false) mctx mref cctx cref w r w') :
    ∀ c, ReachEdge K Top c → Acc (CallRel K) c := by
  obtain ⟨hI, hKI⟩ := acc_of_run K L (ReachEdge K Top) hLim hS hKC 1 (Nat.le_refl 1)
  refine acc_reach_of_top K fun t ht => ?_
  obtain ⟨mctx, cctx, w, w', r, hSt, hr⟩ := hrun t ht
  exact acc_top_of_run K L (ReachEdge K Top) hS hI hKI (ReachEdge.top ht) hSt hr

end Tools.ShippingGen5Acc
