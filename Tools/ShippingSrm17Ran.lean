import Tools.ShippingSrm17Body
import Tools.ShippingSrm4Core2
import Tools.ShippingSrm3Iface
import Tools.ShippingSeqChildIfaceA
import Tools.ShippingQuadLeafGeneric
set_option autoImplicit false
-- UNBUILT (unit SRM17): see REPORT-SRM17.md for run names / exits.
-- SCOPE: the three structural facts `ModP` (= `IUb ∧ Agb ∧ Rdb`, Tools/ShippingSrm17Body.lean) of the modules a MACHINE RUN produced.
-- * `ran_modP`: a `MachineRanA` run with calls (`insts ≠ []`, `instFields ≠ []`): of the run's module `M` and of its post-processed form `b` (`b.body = M.body` from `core_kids_facts_ranAM`).  Distinct instance names are
--   `core_raw_facts_ranAM`'s (it takes `hsl : slots ≠ []`, kept as a premise here); distinct register names and no memory statement come from the closing's `nextKeys` nodup (`CloseCalls.some`), the closed machine being
--   assignments and registers (`closedBody_kinds_of_run`) and the added statements instances.
-- * `leaf_modPA`: a run of a machine WITHOUT calls from a `JQ` world (the leaf form of `seqChild_ifaceA`): the register statements are slot registers of distinct names (`MachineWired`), the body is assignments and registers;
--   the post-processing is `dropZeroWidthModule` or `mergeChecked` of it (`modP_mergeChecked`).
-- `RealChildA` is a history of past synthesis results, not semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.
namespace Tools.ShippingSrm17Ran
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.IR.OptCheck (seqStmtOk)
open Tools.ShippingSeqChildIface
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingCallWidthsChildRealA Tools.ShippingChildBndCore
open Tools.ShippingClosedKinds
open Tools.ShippingSrm17Body

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem nodup_idx : ∀ {l : List String} {i j : Nat} {r : String}, l.Nodup → l[i]? = some r → l[j]? = some r → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | a :: l, i, j, r, hnd, hi, hj => by
    have hn := List.nodup_cons.mp hnd
    rcases i with _ | i <;> rcases j with _ | j
    · rfl
    · exfalso
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hi hj
      exact hn.1 (hi ▸ List.mem_of_getElem? hj)
    · exfalso
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hi hj
      exact hn.1 (hj ▸ List.mem_of_getElem? hi)
    · simp only [List.getElem?_cons_succ] at hi hj
      exact congrArg Nat.succ (nodup_idx hn.2 hi hj)

/-! ## A run with calls -/

/-- **`ModP` of the module of a machine run with calls, and of its post-processed form.**  Premise `hsl : slots ≠ []` is `core_raw_facts_ranAM`'s (the distinct instance names); the register-name and memory facts are from the closing. -/
theorem ran_modP (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    ModP M ∧ ModP b := by
  have hbb : b.body = M.body :=
    (Tools.ShippingSrm3Iface.core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran).2.1
  have hndB : (Tools.ShippingHierState.instNames b.body).Nodup :=
    (Tools.ShippingSrm4Core2.core_raw_facts_ranAM O d ok hbody hC hslots hdomB hins hsl hfne outTy hpost ran).2.1
  rw [hbb] at hndB
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran0
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨-, -, -, L, hLinst, hperm, -, -, -, -, hnk, -, -⟩ := hcc.some
  obtain ⟨hseq0, -, -⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  have hnoMem0 : NoMemB ((closeMachine d.shape.layout t').body ++ L) := by
    intro nm aw dw cl wa wd we ra rd cr ew er hx
    rcases List.mem_append.mp hx with h0 | h0
    · have := List.all_eq_true.mp hseq0 _ h0
      simp [seqStmtOk] at this
    · have := List.all_eq_true.mp hLinst _ h0
      simp [isInst] at this
  have hrNd : (regNames M.body).Nodup := by
    have h1 : (regNames ((closeMachine d.shape.layout t').body ++ L)).Nodup := by
      rw [← nextKeys_eq_regNames _ hnoMem0]
      exact hnk
    exact (regNames_perm hperm).nodup_iff.mp h1
  have hM : ModP M := modP_of_nodups hndB hrNd (noMemB_of_perm hperm hnoMem0)
  refine ⟨hM, ?_⟩
  obtain ⟨h1, h2, h3⟩ := hM
  exact ⟨by rw [hbb]; exact h1, by rw [hbb]; exact h2, by rw [hbb]; exact h3⟩

/-! ## A run without calls -/

/-- **`ModP` of the served module of a machine run WITHOUT calls** (the leaf form of `seqChild_ifaceA`: same run, same premises). -/
theorem leaf_modPA {c : Name} (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {D : Nat} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    ModP b := by
  obtain ⟨M, D', w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ := machine_run_of_coreA O hA hcore entry hw hc
  have hne := closesM (profLogIO bb) _ _ _ hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hMeq, hDeq⟩ := synthesizeMachineCertified_leaf_runs hno hrun9
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeCombinationalCore_machine_sound hcore entry closesM d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, hregsNd, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hclean, -⟩ := wired
  obtain ⟨⟨hzb, -, -, -⟩, -, -, hregs, -, -, -, -, hseq⟩ := hclean hno outTy
  -- the module `M`: assignments and registers, the registers are slots' of distinct names
  have hmod : ModP M := by
    have hsq : ∀ st ∈ M.body, seqStmtOk st = true := fun st hs => List.all_eq_true.mp hseq st hs
    refine ⟨?_, ?_, ?_⟩
    · intro mn i cn mn' cn' h1 _
      have := hsq _ h1
      simp [seqStmtOk] at this
    · intro r cl rs inp init cl' rs' inp' init' h1 h2
      obtain ⟨k, f, hk, hf, he⟩ := hregs r cl rs inp init h1
      obtain ⟨k', f', hk', hf', he'⟩ := hregs r cl' rs' inp' init' h2
      have hkk : k = k' := nodup_idx hregsNd hk hk'
      subst hkk
      rw [hf] at hf'
      cases hf'
      rw [he, he']
    · intro nm aw dw cl wa wd we ra rd cr ew er hm
      have := hsq _ hm
      simp [seqStmtOk] at this
  have hZ : ModP (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) := by
    obtain ⟨h1, h2, h3⟩ := hmod
    exact ⟨by rw [hzb]; exact h1, by rw [hzb]; exact h2, by rw [hzb]; exact h3⟩
  rcases hpost with rfl | rfl
  · exact hZ
  · exact modP_mergeChecked hZ

end Tools.ShippingSrm17Ran
