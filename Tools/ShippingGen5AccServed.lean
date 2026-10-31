import Tools.ShippingGen5AccKeep
import Tools.ShippingGen5AccReads
import Tools.ShippingGen2ServedRun
set_option autoImplicit false
-- Built in the Pod (g5ac-r6) at 5c38c6fc: `kjob lake build Tools.ShippingGen5AccServed`, exit 0, 720 jobs (the build was of the identical content; this header is the only later change). Clean issue-linked build is the coder's. No sorry / axiom / native_decide.

/-! # DG-ACC unit A5b: `AccServed0Stmt` from named premises (scripts/gen5/DG_ACC_FREEZE_REV3.md §2.2-§2.5, items 6-12)

Acc copies of M3's `ServedRun` chain (`Tools/ShippingGen2ServedRun.lean`; `Tools/ShippingGen5RunReads.lean:69-140` for the head and
the machine branch), with `InvAt L P Reach` replaced by `AccInvAt K L Reach`, `CacheShips`/`ShipsRes` by `CacheAcc K Reach`/`Acc (CallRel K)`.

PROVED here (given the premises named in each statement): the head `coreHead_accInvAt`, the machine branch
`fromConst_machine_accInvAt`, the children `synthesizeChild_acc`/`closeInstsM_acc`/`closeInstsGM_acc`/`synthesizeMachineCertified_runsAcc`,
`childrenAcc_reached`, and the two assemblies `accServed0_of_route` / `accServed0_of_cover`.

CONDITIONAL on named premises that are NOT supplied here (this investigation found no supplier or route for them):
`MachineRouteAt env₀ L Reach` (machine shape of every reached name, with `MachineClosesAtA`), `ReadsSupplyAt env₀ L Reach` (rev2 §B; built
in `ShippingGen5AccReads`), and the shape link `RunDataLink K L Reach`, or in the cover form `ReachCover K Reach` + `DataOfShape K`;
`hcl`, the closure `Reach X → CallEdge K X c → Reach c`. Off-route names are excluded by `MachineRouteAt`, not served.
Not supplied: `GenSFacts`, `QuietStrengthA`/`GetEnvFrame`/`AdmDownA`, `OffRouteServes`. Not DG-ACC / M5 / FG completion.

"No `hrow`" in this file is a statement about the ordinary static edges only (`child? = none` entries of the one-output / general
closing): it is NOT a claim about the supply of `ServedP` in general. `QuietStrengthA` / `AdmDownA` (in `ShippingGen5AccReads`) and any
other text copied from EnvQ must be checked against the original when EnvQ is integrated. `Tests/Gen5/AccServedCheck.lean` compares the
definition TEXT of `QuietStrengthA` / `AdmDownA` with `Tools/ShippingGen5EnvQ.lean` (EnvQ cannot be imported on this base, so this is a source-text
comparison, not a typed one) and rejects changed copies. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Tools.ShippingEntryReadsLinked (CoreSaved coreHead)
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFrontCP
open Tools.ShippingChildFresh
open Tools.ShippingChildCacheA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildDepthC
open Tools.ShippingChildCoreC
open Tools.ShippingChildComposeC
open Tools.ShippingChildVertA
open Tools.ShippingChildRunA
open Tools.ShippingChildRunAKids
open Tools.ShippingGen5Env (ReadsAt MachineDefinesR ci_of_readsAt envR_of_readsAt)
open Sparkle.IR.Machine
open Tools.ShippingMachineAuto (MachineData)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
variable (K : AssignKit ι dom env₀)

/-! ## Premise definitions (rev1 §B.2 texts) -/

def MachineRouteAt (env₀ : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∃ shape : MachineShape, MachineDefinesR env₀ mctx mref cctx cref c shape ∧ MachineClosesAtA L.O mctx cctx c shape

def RunDataLink (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ shape : MachineShape, MachineDefinesR env₀ mctx mref cctx cref c shape →
      ∃ d, dataOf₀ K c = some d ∧ d.shape = shape

def DataOfShape : Prop :=
  ∀ (E : ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), K.dataOf E se s = some d → d.shape = s

/-! ## 1. The depth-0 clear and the head -/

theorem tripleAcc_clear (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ L.O.quiet D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => AccInvAt K L Reach D) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := L.O.cacheSet hA _ _ _ _ h hw.1
    refine ⟨⟨⟨L.O.cacheSetQ hA _ _ _ _ h hw.1, hk.2.1.trans hw.2.1, hk.2.2.trans hw.2.2⟩, ?_⟩, ?_⟩
    · rw [hk.1]; exact cacheInvA_empty L.O
    · rw [hk.1]; exact cacheAcc_empty K Reach

/-- The head of the core entry (over `coreHead X`, the form `ChainReadsAt` exposes) establishes `AccInvAt (D+1)`: a copy of
`coreHead_jqcA` (`ShippingGen5RunReads.lean:69`) with the clear of `tripleAcc_clear` and the stable invariant `stableA_accInvAt`. -/
theorem coreHead_accInvAt (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {X : Name} {D : Nat} {w w1 : Void IO.RealWorld} {s : CoreSaved}
    (hw : JQC L.O D w) (hc : D = 0 ∨ CacheAcc K Reach (cv w))
    (hh : RunsTo (coreHead X) mctx mref cctx cref w s w1) :
    AccInvAt K L Reach (D + 1) w1 := by
  have h := hh
  unfold Tools.ShippingEntryReadsLinked.coreHead at h
  by_cases h0 : D = 0
  · subst h0
    replace hw := hw.1
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_JQ _ 0) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag L.O hA (stableA_JQ _ 0)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet L.O hA (stableA_JQ _ 0)) hw s3
    have hdD : d = 0 := hd.2.trans hd.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    simp only [↓reduceIte, beq_self_eq_true] at h
    peelP h; peelP h; peelP h; peelP h; peelP h; peelP h; peelP h
    peelF L.O hA (stableA_JQ _ 0) h hw; peelF L.O hA (stableA_JQ _ 0) h hw
    peelF L.O hA (stableA_JQ _ 0) h hw; peelF L.O hA (stableA_JQ _ 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleAcc_clear K L Reach hA 0 (R := fun _ _ => False)) hw step
    clear step
    peelF L.O hA (stableA_accInvAt K L Reach 0) h hw; peelF L.O hA (stableA_accInvAt K L Reach 0) h hw
    peelF L.O hA (stableA_accInvAt K L Reach 0) h hw; peelF L.O hA (stableA_accInvAt K L Reach 0) h hw
    peelF L.O hA (stableA_accInvAt K L Reach 0) h hw; peelF L.O hA (stableA_accInvAt K L Reach 0) h hw
    peelF L.O hA (stableA_accInvAt K L Reach 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleAcc_depthSet K L Reach hA 0 (0 + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨-, rfl⟩ := RunsTo.pure_world h
    exact hw
  · replace hw : AccInvAt K L Reach D w := ⟨hw, hc.resolve_left h0⟩
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_accInvAt K L Reach D)
      (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag L.O hA (stableA_accInvAt K L Reach D)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet L.O hA (stableA_accInvAt K L Reach D)) hw s3
    have hdD : d = D := hd.2.trans hd.1.1.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    have h0' : ¬ ((d == 0) = true) := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at h
    peelF L.O hA (stableA_accInvAt K L Reach d) h hw; peelF L.O hA (stableA_accInvAt K L Reach d) h hw
    peelF L.O hA (stableA_accInvAt K L Reach d) h hw; peelF L.O hA (stableA_accInvAt K L Reach d) h hw
    peelF L.O hA (stableA_accInvAt K L Reach d) h hw; peelF L.O hA (stableA_accInvAt K L Reach d) h hw
    peelF L.O hA (stableA_accInvAt K L Reach d) h hw
    peelF L.O hA (stableA_accInvAt K L Reach d) h hw; peelF L.O hA (stableA_accInvAt K L Reach d) h hw
    peelF L.O hA (stableA_accInvAt K L Reach d) h hw; peelF L.O hA (stableA_accInvAt K L Reach d) h hw
    peelF L.O hA (stableA_accInvAt K L Reach d) h hw; peelF L.O hA (stableA_accInvAt K L Reach d) h hw
    peelF L.O hA (stableA_accInvAt K L Reach d) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleAcc_depthSet K L Reach hA d (d + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨-, rfl⟩ := RunsTo.pure_world h
    exact hw

/-! ## 2. The machine branch -/

theorem fromConst_machine_accInvAt (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {tenv : Environment} {b : Bool} {X : Name} {n : Nat}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none) (miss : mixedCertifiedShape? false [] ci isInst = none)
    (hw : AccInvAt K L Reach n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false true
      ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR' : Environment) (w₁ : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR' w₁ ∧
      ∀ shape, machineShape? false [] ci (structEnv envR') = some shape →
        ∃ (r : Option Res) (w₂ : Void IO.RealWorld),
          RunsTo (synthesizeMachineCertified (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X shape)
            mctx mref cctx cref w₁ r w₂ ∧ AccInvAt K L Reach n w₁ ∧ (∀ res, r = some res → res = (m, d)) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_accInvAt K L Reach n)
    FramedA.env)) hw henv
  obtain ⟨mach, w2, hp, hr⟩ := RunsTo.bind hr
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  refine ⟨envR, _, henv, ?_⟩
  intro shape hs
  rw [hs] at hr
  dsimp only at hr
  obtain ⟨r, w3, hmach, hr⟩ := RunsTo.bind hr
  refine ⟨r, w3, hmach, hw1, ?_⟩
  intro res hres
  subst hres
  dsimp only at hr
  have hr := hr.mreturns
  peel_bind hr
  peel_bind hr
  exact (MReturns.pure hr).symm

/-! ## 3. The children -/

def ChildrenAccI (L : Laws mref cref) (Reach : Name → Prop) (shape : MachineShape) (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    ((shape.instOrigins.getD k .ord).child? = some y ∨
      (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → Acc (CallRel K) (shape.insts[k]).1)))

theorem synthesizeChild_acc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res}
    (hw : AccInvAt K L Reach D w) (hIH : AccIHAt K L Reach D) (hKI : AccChildKeeps K L Reach D)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') :
    RealChildA L.O n r ∧ (Reach n → Acc (CallRel K) n) ∧ AccInvAt K L Reach D w' := by
  refine ⟨?_, synthesizeChild_accRes K L Reach hA hw hIH h, ?_⟩
  · have h' := h
    unfold synthesizeChild at h'
    obtain ⟨m, w1, hget, h'⟩ := RunsTo.bind h'
    have hw1 : AccInvAt K L Reach D w1 ∧ m = cv w1 :=
      runs_of_triple (tripleAcc_cacheGet K L Reach hA D) hw hget
    cases hc : m.get? n with
    | some y =>
      simp only [hc] at h'
      obtain ⟨hy, -⟩ := RunsTo.pure_world h'
      rw [hy]
      exact hw1.1.1.2 n y (by rw [← hw1.2]; exact hc)
    | none =>
      simp only [hc] at h'
      obtain ⟨r1, w2, hrun, h'⟩ := RunsTo.bind h'
      obtain ⟨u, w3, -, h'⟩ := RunsTo.bind h'
      obtain ⟨hy, -⟩ := RunsTo.pure_world h'
      rw [hy]
      exact RealChildA.of_jqc L.O hA hw1.1.1 hrun
  · have hK : Tools.ShippingChildFrontCP.ChildSynthA L.O (AccInvAt K L Reach D) := hKI
    have hk := (hK mctx cctx hA n w hw).1
    rw [endW_of_runs h] at hk
    exact hk

theorem closeInstsM_acc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} (hIH : AccIHAt K L Reach D) (hKI : AccChildKeeps K L Reach D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : AccInvAt K L Reach D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      children.length = shape.insts.length ∧
      (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → Acc (CallRel K) (shape.insts[k]).1))) ∧
      AccInvAt K L Reach D w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  have hw1 : AccInvAt K L Reach D w1 :=
    framed_runs L.O hA (stableA_accInvAt K L Reach D) hw hget FramedA.synthGet
  obtain ⟨rfl, -⟩ := jqc_synthGet L.O hA hw.1 hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoareA _ (AccInvAt K L Reach D)
    (fun (x : Name × List Nat × MixedGateBinder) y =>
      RealChildA L.O x.1 y ∧ (Reach x.1 → Acc (CallRel K) x.1))
    (fun x w y w' hp hy => by
      obtain ⟨h1, h2, h3⟩ := synthesizeChild_acc K L Reach hA (n := x.1) hp hIH hKI hy
      exact ⟨⟨h1, h2⟩, h3⟩)
    shape.insts children hw1 hch
  exact ⟨children, heq.symm, hlen, hk, hw2⟩

theorem closeInstsGM_acc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} (hIH : AccIHAt K L Reach D) (hKI : AccChildKeeps K L Reach D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : AccInvAt K L Reach D w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧ MemChildren shape children ∧
      ChildrenAccI K L Reach shape children ∧ AccInvAt K L Reach D w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  have hw1 : AccInvAt K L Reach D w1 :=
    framed_runs L.O hA (stableA_accInvAt K L Reach D) hw hget FramedA.synthGet
  obtain ⟨rfl, -⟩ := jqc_synthGet L.O hA hw.1 hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := Tools.ShippingChildInv.mapM_hoare _ (AccInvAt K L Reach D)
    (fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) y =>
      (∀ md, x.2.child? = some md → y = md) ∧
      (x.2.child? = some y ∨ (RealChildA L.O x.1 y ∧ (Reach x.1 → Acc (CallRel K) x.1))))
    (fun x w y w' hp hy => by
      obtain ⟨c, o⟩ := x
      dsimp only at hy ⊢
      cases hmc : Sparkle.Compiler.MachInstOrigin.InstOrigin.child? o with
      | some md =>
        rw [hmc] at hy
        obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hy
        exact ⟨⟨fun md' h => by cases h; rfl, Or.inl rfl⟩, hp⟩
      | none =>
        rw [hmc] at hy
        obtain ⟨hrc, hsr, hp'⟩ := synthesizeChild_acc K L Reach hA (n := c) hp hIH hKI hy
        exact ⟨⟨fun md' h => (by cases h), Or.inr ⟨hrc, hsr⟩⟩, hp'⟩)
    shape.instTagged children hw1 hch
  have hlenI : children.length = shape.insts.length := by
    rw [hlen]; exact instTagged_length' shape
  refine ⟨children, heq.symm, ?_, ⟨hlenI, fun k hkl => ?_⟩, hw2⟩
  · intro k hkl md hmd
    obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
    obtain ⟨y, hky, hm, _⟩ := hk k hkT
    rw [he] at hm
    rw [hm md hmd] at hky
    exact hky
  · obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
    obtain ⟨y, hky, _, hor⟩ := hk k hkT
    rw [he] at hor
    exact ⟨y, hky, hor⟩

/-- The Acc form is weaker than M3's `synthesizeMachineCertified_runsS`: it drops the `MReturns` / `closeLets` / `CloseCalls`
conjuncts, which A5 does not use. -/
theorem synthesizeMachineCertified_runsAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {n : Nat} {tenv : Lean.Environment}
    (hIH : AccIHAt K L Reach n) (hKI : AccChildKeeps K L Reach n)
    {b : Bool} {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : AccInvAt K L Reach n w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    (shape.insts = [] ∨ (shape.insts ≠ [] ∧ ∃ children, ChildrenAccI K L Reach shape children)) := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (mixed_keepsAP L.O hA (stableA_accInvAt K L Reach n)
    (fun e hint top named => translateExprToWire tenv e hint top named) b declName
    shape.binders shape.body
    (fun e hint top named =>
      (translate_keepsAcc_of_tele K L Reach n hKI tenv) mctx cctx hA e hint top named))) hw run
  dsimp only at hr
  split at hr
  · rename_i t' hcl
    split at hr
    · rename_i hi
      exact Or.inl hi
    · rename_i hi
      have hne : shape.insts ≠ [] := by rw [hi]; exact List.cons_ne_nil _ _
      split at hr
      · rename_i hf
        obtain ⟨children, hc, hlen, hreal, _⟩ := closeInstsM_acc K L Reach hA hIH hKI hw1 hr
        exact Or.inr ⟨hne, children, hlen, fun k hk => by
          obtain ⟨y, hy, hre⟩ := hreal k hk
          exact ⟨y, hy, Or.inr hre⟩⟩
      · rename_i hf
        obtain ⟨children, hc, hmc, hreal, _⟩ := closeInstsGM_acc K L Reach hA hIH hKI hw1 hr
        exact Or.inr ⟨hne, children, hreal⟩
  · have eq := RunsTo.pure_eq hr
    cases eq

/-! ## 4. Reached children are `Acc` -/

theorem childrenAcc_reached {L : Laws mref cref} {Reach : Name → Prop}
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) {X : Name} (hX : Reach X)
    {d : MachineData} (hd : dataOf₀ K X = some d) {shape : MachineShape} (hsh : d.shape = shape)
    {children : List Res} (hch : ChildrenAccI K L Reach shape children) :
    ∀ c, CallEdge K X c → Acc (CallRel K) c := by
  intro c hedge
  obtain ⟨d', hd', k, hk, hnone, hc⟩ := hedge
  have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst hdd
  have hedge : CallEdge K X c := ⟨d', hd', k, hk, hnone, hc⟩
  subst hsh
  obtain ⟨-, hall⟩ := hch
  obtain ⟨y, -, hor⟩ := hall k hk
  rcases hor with h | ⟨-, hacc⟩
  · rw [hnone] at h; cases h
  · subst hc
    exact hacc (hcl X _ hX hedge)

/-! ## 5. The assemblies -/

/-- `getEnv` returns at every world (so a chain's second `getEnv` run can be exhibited before the body is unfolded). -/
theorem getEnv_runs_exists (w : Void IO.RealWorld) :
    ∃ (e : Environment) (w' : Void IO.RealWorld), RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w e w' := by
  have key : (Lean.getEnv : MetaM Environment) mctx mref cctx cref w =
      (match (ST.Ref.get cref : ST IO.RealWorld Core.State) w with
        | .mk v w2 => EST.Out.ok v.env w2) := rfl
  unfold RunsTo
  rw [key]
  cases (ST.Ref.get cref : ST IO.RealWorld Core.State) w with
  | mk v w2 => exact ⟨v.env, w2, rfl⟩

/-- The shared run analysis of A5b: from a successful core run of a reached name, under `MachineRouteAt` and `ReadsSupplyAt`,
the route's shape with the children of the run, and the `env₀`-side form of the run's shape equation. -/
theorem accServed_core (L : Laws mref cref) (Reach : Name → Prop)
    (hRoute : MachineRouteAt env₀ L Reach) (hRS : ReadsSupplyAt env₀ L Reach)
    {X : Name} (hX : Reach X) (hA : AdmCtx L.O.quiet mctx cctx) {w w' : Void IO.RealWorld} {r : Res}
    (hjqc : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheAcc K Reach (cv w))
    (hIH : AccIHAt K L Reach (dv w + 1)) (hKI : AccChildKeeps K L Reach (dv w + 1))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w r w') :
    ∃ (ci : ConstantInfo) (shape : MachineShape) (children : List Res),
      MachineDefinesR env₀ mctx mref cctx cref X shape ∧ env₀.find? X = some ci ∧
      machineShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀) (structEnv env₀))
        (structEnv env₀) = some shape ∧
      ChildrenAccI K L Reach shape children := by
  obtain ⟨M, Dg⟩ := r
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, hfin⟩ :=
    Tools.ShippingEntryReadsLinked.core_chain hr
  have hw1 := coreHead_accInvAt K L Reach hA hjqc hc hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_accInvAt K L Reach (dv w + 1))
    (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_accInvAt K L Reach (dv w + 1))
    FramedA.env)) hw2 henv
  have hCR := hRS X hX mctx cctx w hA hjqc
  obtain ⟨e', w5', h3'⟩ := getEnv_runs_exists (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) w3
  obtain ⟨r1, r2, r3⟩ := hCR s w1 w2 w3 w5' ci envR e' hh hget henv h3'
  obtain ⟨shape, hD, hcl⟩ := hRoute X hX mctx cctx hA
  obtain ⟨old, miss, -⟩ := hD w1 ci w2 w2 envR w3 w2 envR w3 r1 r2 r2 hget henv henv
  obtain ⟨envR', w₁, henv', hmach⟩ := fromConst_machine_accInvAt K L Reach hA old miss hw3 hbody
  obtain ⟨r1', r2', r3'⟩ := hCR s w1 w2 w3 w₁ ci envR envR' hh hget henv henv'
  obtain ⟨-, -, hshape⟩ := Tools.ShippingGen5Acc.machineDefines_at_chain hD hCR hh hget henv henv'
  obtain ⟨r', w₂, hrun, hw₁, hres⟩ := hmach shape hshape
  have hne := hcl s.profile (dv w + 1) w₁ r' w₂ hw₁.1 (by omega) hrun
  cases r' with
  | none => exact absurd rfl hne
  | some res =>
    have hres' := hres res rfl
    subst hres'
    have hch := synthesizeMachineCertified_runsAcc K L Reach hA hIH hKI hw₁ hrun
    have hch' : ∃ children, ChildrenAccI K L Reach shape children := by
      rcases hch with h | ⟨-, hc'⟩
      · exact ⟨[], by simp [h], fun k hk => absurd hk (by simp [h])⟩
      · exact hc'
    obtain ⟨children, hchildren⟩ := hch'
    have hci : env₀.find? X = some ci := ci_of_readsAt hget r1'
    obtain ⟨-, hi, hu, hs⟩ := envR_of_readsAt henv r2'
    obtain ⟨-, -, -, hs'⟩ := envR_of_readsAt henv' r3'
    refine ⟨ci, shape, children, hD, hci, ?_, hchildren⟩
    rw [hi, hu, hs, hs'] at hshape
    exact hshape

theorem accServed0_of_route (L : Laws mref cref) (Reach : Name → Prop)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hRoute : MachineRouteAt env₀ L Reach) (hLink : RunDataLink K L Reach)
    (hRS : ReadsSupplyAt env₀ L Reach) : AccServed0Stmt K L Reach := by
  intro X mctx cctx w w' r hX hA hjqc hc hIH hKI hr
  obtain ⟨ci, shape, children, hD, -, -, hch⟩ := accServed_core K L Reach hRoute hRS hX hA hjqc hc hIH hKI hr
  obtain ⟨d, hd, hsh⟩ := hLink X hX mctx cctx hA shape hD
  exact childrenAcc_reached K hcl hX hd hsh hch

theorem machineClosesAtA_of_closes (L : Laws mref cref) {c : Name} {shape : MachineShape}
    (h : MachineCloses mctx mref cctx cref c shape) : MachineClosesAtA L.O mctx cctx c shape := by
  intro tenv b n w r w' _ _ hrun
  exact h (profLogIO b) w r w' hrun

theorem accServed0_of_cover (L : Laws mref cref) (Reach : Name → Prop)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hRoute : MachineRouteAt env₀ L Reach) (hcov : ReachCover K Reach) (hDS : DataOfShape K)
    (hRS : ReadsSupplyAt env₀ L Reach) : AccServed0Stmt K L Reach := by
  intro X mctx cctx w w' r hX hA hjqc hc hIH hKI hr
  obtain ⟨ci, shape, children, hD, hci, hsh0, hch⟩ := accServed_core K L Reach hRoute hRS hX hA hjqc hc hIH hKI hr
  obtain ⟨E, g, hE, hg⟩ := hcov X hX
  have hd : dataOf₀ K X = some (K.dOf g) := dataOf₀_of_genData₀ K hE hg
  have hdd := K.genData₀_dataOf hg
  have hE' : E = entryConst true false [] ci (instancePredicate env₀) (userInliner env₀) (structEnv env₀) := by
    unfold entry₀ at hE
    rw [hci] at hE
    exact (Option.some.inj hE).symm
  subst hE'
  rw [hsh0] at hdd
  have hdd' : K.dataOf _ (structEnv env₀) shape = some (K.dOf g) := hdd
  exact childrenAcc_reached K hcl hX hd (hDS _ _ _ _ hdd') hch

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.tripleAcc_clear
#print axioms Tools.ShippingGen5Acc.coreHead_accInvAt
#print axioms Tools.ShippingGen5Acc.fromConst_machine_accInvAt
#print axioms Tools.ShippingGen5Acc.synthesizeChild_acc
#print axioms Tools.ShippingGen5Acc.closeInstsM_acc
#print axioms Tools.ShippingGen5Acc.closeInstsGM_acc
#print axioms Tools.ShippingGen5Acc.synthesizeMachineCertified_runsAcc
#print axioms Tools.ShippingGen5Acc.childrenAcc_reached
#print axioms Tools.ShippingGen5Acc.accServed0_of_route
#print axioms Tools.ShippingGen5Acc.machineClosesAtA_of_closes
#print axioms Tools.ShippingGen5Acc.accServed0_of_cover
