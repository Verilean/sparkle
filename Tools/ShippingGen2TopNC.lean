import Tools.ShippingGen2Defs
import Tools.ShippingGen2SlotlessLeaf
set_option autoImplicit false
-- Built: g2nc3-ba4334f8 (clean snapshot, exit 0, standard axioms).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # The no-clock top contract `TopShipsNC`, the proposed R-G contract, L1-L4 and U-TOP-S2

Specifications: scripts/gen2/S5_SLOTLESS_FREEZE.md rev1 §5 C2 (+ rev1.1 notes) and
scripts/gen2/TOP_CONTRACT_REVISION.md §2, §3 (+ rev1.1 notes: NC suppliers and L1-L4 FIRST, in new files).
Shared definitions are NOT edited: `Tools/ShippingGen2Defs.lean` is unchanged; R-G is stated here as a LOCAL copy
`TopShipsRG` of the proposed text, for L1-L4 only (the Defs switch, U-TOP-DEF, comes later, serially).

* C2 `TopShipsNC`: `TopShips` (Defs:273-295) with line :283 deleted. That one line holds BOTH premises
  (`∀ t, ins t "rst" = 0` and `∀ t st, seedIn b ins t st "clk" = 0`), so both are gone. Every other line verbatim.
* `TopShipsRG`: `TopShips` with line :283 replaced by the two guarded premises (TOP_CONTRACT_REVISION §2 R-G):
  `("rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0) → ("clk" ∈ b.inputs.map (·.name) → ∀ t, ins t "clk" = 0)`.
* L1 `topShips_of_RG` (new ⇒ old, no hypothesis); L2 `topShipsRG_of_old` (old ⇒ new, given BOTH "rst" and "clk"
  inputs); L3 `topShipsRG_of_NC` (NC ⇒ new, no hypothesis); L4 `topShipsNC_of_RG` (new ⇒ NC, given NEITHER is an
  input). Same witnesses throughout. R-G coincides with `TopShipsNC` only when neither "rst" nor "clk" is an input
  (rev1.1 note 3); old ⇒ new without the clk membership is NOT claimed.
* `topShips_of_NC` (C2's weakening, = L1 ∘ L3): recorded as a projection only. Its target's inner part is vacuous
  without a clock input (Tools/ShippingGen2TopVacuity.lean), so it is NOT a slotless top guarantee; the stage-C
  theorems must not reach it (audit in Tests/Gen2/TopNCCheck.lean).
* U-TOP-S2 `slotlessLeaf_topShipsNC_of_LB` / `slotlessLeaf_topShipsNC`: the slotless leaf's top WITHOUT the rst/clk
  premises. Copy of `slotlessLeaf_topShips_of_LB` (SlotlessLeaf:180-281): the reset premise of the trace at the
  zeroed seed `sllSeedZ` comes from the module's ACTUAL inputs (`"rst"` ∉ `b.inputs`, the inputs are allocated:
  `slotless_inputs_alloc_ofRun`, SlotlessLeaf:397), not from `ins t "rst" = 0`; `runModule_rst_irrel` moves the run
  to `seedIn` (the `"rst"`-input branch of the original is impossible here). The run-level form supplies every
  premise from the run, as `slotlessLeaf_ships` (SlotlessLeaf:438) does. `slotlessLeaf_topShipsRG` = L3 of it. -/

/-! ## 1. The contracts and L1-L4 (ambient: the opens of Tools/ShippingGen2Defs.lean) -/
namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineShipsDepth (ResetNk)

/-- **C2 `TopShipsNC`**: `TopShips` (Defs:273-295) with line :283 (`ins t "rst" = 0` AND
`seedIn b ins t st "clk" = 0`) deleted; every other line verbatim. -/
def TopShipsNC {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- **The proposed R-G contract, LOCAL copy** (TOP_CONTRACT_REVISION.md §2): `TopShips` with line :283 replaced by
the two premises guarded on the module's actual inputs; every other line verbatim. -/
def TopShipsRG {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      ("rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0) →
      ("clk" ∈ b.inputs.map (·.name) → ∀ t, ins t "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- `seedIn` at an input reads the stream (local copy of `sll_seedIn_in`, SlotlessLeaf:70). -/
theorem tnc_seedIn_in {m : Sparkle.IR.AST.Module} {ins : Nat → String → Nat} {t : Nat} {st : String → Nat}
    {x : String} (hx : x ∈ m.inputs.map (·.name)) : seedIn m ins t st x = ins t x := by
  have hc : (m.inputs.map (·.name)).contains x = true := List.contains_iff_mem.mpr hx
  show (if (m.inputs.map (·.name)).contains x then ins t x else st x) = ins t x
  rw [if_pos hc]

/-- **L1 (new ⇒ old)**, no hypothesis: the old antecedents give the guarded ones (rst trivially; clk through
`seedIn` at an input). Same witnesses. -/
theorem topShips_of_RG {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) :
    TopShipsRG p n declName b raw D → TopShips p n declName b raw D := by
  intro h
  unfold TopShipsRG at h
  unfold TopShips
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hreset hfit hst
  refine H i bools bits T ins st0 mems kids hsrc hpass (fun _ => hrst) ?_ hinit hreset hfit hst
  intro hc t
  have h0 := hclk t (fun _ => 0)
  rw [tnc_seedIn_in hc] at h0
  exact h0

/-- **L2 (old ⇒ new)**, given BOTH `"rst"` and `"clk"` inputs: the guarded premises with the memberships give
Defs:283 (`seedIn` reads `ins t "clk"`). Same witnesses. -/
theorem topShipsRG_of_old {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design)
    (hr : "rst" ∈ b.inputs.map (·.name)) (hc : "clk" ∈ b.inputs.map (·.name)) :
    TopShips p n declName b raw D → TopShipsRG p n declName b raw D := by
  intro h
  unfold TopShips at h
  unfold TopShipsRG
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrstG hclkG hinit hreset hfit hst
  refine H i bools bits T ins st0 mems kids hsrc hpass (hrstG hr) ?_ hinit hreset hfit hst
  intro t st
  rw [tnc_seedIn_in hc]
  exact hclkG hc t

/-- **L3 (NC ⇒ new)**, no hypothesis: drop the two guarded antecedents. Same witnesses. -/
theorem topShipsRG_of_NC {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) :
    TopShipsNC p n declName b raw D → TopShipsRG p n declName b raw D := by
  intro h
  unfold TopShipsNC at h
  unfold TopShipsRG
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass _ _ hinit hreset hfit hst
  exact H i bools bits T ins st0 mems kids hsrc hpass hinit hreset hfit hst

/-- **L4 (new ⇒ NC)**, given that NEITHER `"rst"` nor `"clk"` is an input: each guard is supplied by its own
hypothesis's refutation (not an execution premise). Same witnesses. -/
theorem topShipsNC_of_RG {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design)
    (hr : "rst" ∉ b.inputs.map (·.name)) (hc : "clk" ∉ b.inputs.map (·.name)) :
    TopShipsRG p n declName b raw D → TopShipsNC p n declName b raw D := by
  intro h
  unfold TopShipsRG at h
  unfold TopShipsNC
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hinit hreset hfit hst
  exact H i bools bits T ins st0 mems kids hsrc hpass (fun h' => absurd h' hr) (fun h' => absurd h' hc)
    hinit hreset hfit hst

/-- C2's weakening `topShips_of_NC` (= L1 ∘ L3). A PROJECTION ONLY: without a clock input its target's inner part
is vacuous (Tools/ShippingGen2TopVacuity.lean), so this is NOT the slotless top guarantee. -/
theorem topShips_of_NC {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) :
    TopShipsNC p n declName b raw D → TopShips p n declName b raw D :=
  fun h => topShips_of_RG p n declName b raw D (topShipsRG_of_NC p n declName b raw D h)

end Tools.ShippingGen2

/-! ## 2. U-TOP-S2: the slotless leaf's `TopShipsNC` (ambient: the opens of Tools/ShippingGen2SlotlessLeaf.lean) -/
namespace Tools.ShippingGen2
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildBndCore (cv dv)

/-- **U-TOP-S2 (pure)**: `slotlessLeaf_topShips_of_LB` (SlotlessLeaf:180-281) with conclusion `TopShipsNC` and one
premise more, `hinA` (allocated raw inputs; the run supplies it, `slotless_inputs_alloc_ofRun`). The trace's reset
premise at `sllSeedZ` is discharged by `"rst"` ∉ `b.inputs` (from `hinA`), not by `ins t "rst" = 0`. -/
theorem slotlessLeaf_topShipsNC_of_LB {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) {raw b : Module}
    {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hclosed0 : readsClosedB ((Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).inputs.map (·.name))
        (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body = true ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body.all isAssign = true)
    (hinA : ∀ q ∈ raw.inputs, Sparkle.IR.NameHints.Allocated q.name)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (n : Nat) :
    TopShipsNC p n p.decl b raw D := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, _, wired, tr⟩ := id hL
  have hregs0 : regs = [] := List.eq_nil_of_length_eq_zero (by simp [rlen, hSS, hsl0])
  subst hregs0
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, _⟩ := hclean hnoI houtTy
  have houtOk := ok_outNameOk p.d hok
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost hclosed0
  obtain ⟨hcl0, hall0⟩ := hclosed0
  obtain ⟨hbi, hbo, _, hallB, hevB⟩ := sll_post hall0 hpost
  -- no input is the reset: the inputs are allocated names (as SlotlessLeaf:335-339)
  have hrstB : "rst" ∉ b.inputs.map (·.name) := by
    rw [hbi, hi]
    intro h
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp h
    exact Tools.ShippingFirstGateChild.nAlloc_rst (by rw [← hqn]; exact hinA q hq)
  refine ⟨ids, nd, len, cache, [], rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hinp _ _ _ hinsB _
  -- the core module's run, at the canonical seed with the state held at 0 on `"rst"`
  obtain ⟨envs, hrun, hlen, hobs, _⟩ := tr i bools bits T (sllSeedZ b ins) st0 mems
    (fun t st ht => by
      have h := hinp t (fun x => if x = "rst" then 0 else st x) ht
      rw [htake] at h
      exact h)
    (fun t st r hr => by simp at hr)
    (fun t st => sll_seedZ_rst (fun h => absurd h hrstB))
    (fun k r f hr _ => by simp at hr)
  have hrun0 : runModule (declWidth r0) r0.body (sllSeedZ b ins) T st0 mems = some envs := by
    rw [hb, show declWidth r0 = weOf r0 from rfl, hw]; exact hrun
  -- the canonical seed: `"rst"` is not an input and is not read
  have hR : ∃ envsR, runModule (declWidth r0) r0.body (seedIn b ins) T st0 mems = some envsR ∧
      envsR.length = envs.length ∧
      ∀ j (h₁ : j < envs.length) (h₂ : j < envsR.length) y, y ≠ "rst" →
        (envsR[j]'h₂) y = (envs[j]'h₁) y :=
    runModule_rst_irrel (X := b.inputs.map (·.name)) (seed₁ := sllSeedZ b ins)
      (seed₂ := seedIn b ins) hall0 (by rw [hbi]; exact hcl0) hrstB
      (fun t st y hy => sll_seedZ_ne (m := b) (ins := ins) (t := t) (st := st) hy) T st0 mems envs hrun0
  obtain ⟨envsR, hrunR, hlenR, hcorrR⟩ := hR
  -- the merge: the same environments
  obtain ⟨envsB, hrunB, hlenB, hcorrB⟩ := Tools.ShippingMachineShipsComb.runModule_assigns hall0 hallB
    (P := fun _ => True) (fun _ => True) (fun _ _ => trivial)
    (fun mems init e _ h => ⟨e, hevB mems init e h, fun _ _ => rfl⟩) T st0 mems envsR hrunR
  -- the optimizer: the same outputs
  have stepO : ∃ envsO, runModule (declWidth (checkedOptimize b)) (checkedOptimize b).body
        (seedIn b ins) T st0 mems = some envsO ∧ envsO.length = envsB.length ∧
      ∀ q ∈ b.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envsB.length),
        (envsO[j]'hj) q.name = (envsB[j]'hj') q.name := by
    cases hsB : simpleBody b with
    | true =>
      obtain ⟨envsO, hrunO, hlO, hcO⟩ := Tools.ShippingMachineShipsComb.runModule_assigns
        (we₁ := declWidth b) (we₂ := declWidth (checkedOptimize b)) hallB
        (Tools.ShippingMachineShipsComb.checkedOptimize_assigns hsB)
        (P := fun x => x ∈ b.outputs.map (·.name))
        (fun init => ∀ x ∈ b.inputs.map (·.name), init x < 2 ^ declWidth b x)
        (by
          intro k st x hx
          rw [sll_seedIn_in hx]
          exact hinsB k x hx)
        (fun mems init e hq h => by
          obtain ⟨envO, hevO, heq, _, _⟩ := Tools.ShippingOptSoundness.checkedOptimize_sound hsB hq h
          refine ⟨envO, hevO, fun x hx => ?_⟩
          obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hx
          exact heq q hq') T st0 mems envsB hrunB
      refine ⟨envsO, hrunO, hlO, fun q hq j hj hj' => ?_⟩
      have hqn : q.name ∈ b.outputs.map (·.name) := List.mem_map.mpr ⟨q, hq, rfl⟩
      exact hcO j hj hj' q.name hqn
    | false =>
      rcases checkedOptimize_seqOk hsB (Tools.ShippingMachineShipsComb.assigns_seqOk hallB) with hchk | heq
      · exact Tools.ShippingRefineNoRst.refineCheck_transfer_noReg hchk (sll_seqRegs_nil hallB) ins hinsB
          (stO := st0) hrunB
      · rw [heq]
        exact ⟨envsB, hrunB, rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨envsO, hrunO, hlenO, hcorrO⟩ := stepO
  refine ⟨envsO, ?_, by omega, ?_⟩
  · rw [runModuleTG_instFree _ _ _ _
      (Tools.ShippingMachineDepthRun.instFree_of_seqOk
        (Tools.ShippingChecksDerived.checkedOptimize_seqOk_all
          (Tools.ShippingMachineShipsComb.assigns_seqOk hallB)))]
    exact hrunO
  · intro j hj k o f hk hf
    have hq : ({ name := o.name, ty := o.ty } : Port) ∈ b.outputs := by
      rw [hbo, ho, houts]; exact List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩
    have hne : o.name ≠ "rst" :=
      (Tools.ShippingCallsAssemblyG.outName_ne_clk (houtOk o (List.mem_of_getElem? hk))).2
    have h1 : (envsO[j]'hj) o.name = (envsB[j]'(by omega)) o.name :=
      hcorrO _ hq j hj (by omega)
    have h2 : (envsB[j]'(by omega)) o.name = (envsR[j]'(by omega)) o.name :=
      hcorrB j (by omega) (by omega) o.name trivial
    have h3 : (envsR[j]'(by omega)) o.name = (envs[j]'(by omega)) o.name :=
      hcorrR j (by omega) (by omega) o.name hne
    rw [h1, h2, h3]
    exact hobs j (by omega) k o f hk hf

/-- **U-TOP-S2 (run level)**: the slotless leaf's `TopShipsNC` from its run, every premise supplied as
`slotlessLeaf_ships` (SlotlessLeaf:438-448) supplies it (`hinA` by `slotless_inputs_alloc_ofRun`). -/
theorem slotlessLeaf_topShipsNC {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module}
    {D : Design}
    (hdata : LeafDataOk p) (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D) (n : Nat) :
    TopShipsNC p n p.decl b raw D := by
  obtain ⟨hok, hco, hSS, houtTy⟩ := hdata.rows
  have htake := leaf_take p.d p.kD hok hco hnoI
  have hL := (Pkg.trace L.O L.T hA p ran).toLB
  have hclosed0 := slotless_closed_ofRun L p (b := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
    hdata hnoI hsl0 hA (Or.inl rfl) ran
  have hinA := slotless_inputs_alloc_ofRun L p hdata hnoI hsl0 htake ran
  exact slotlessLeaf_topShipsNC_of_LB p hL hnoI hsl0 hok hSS houtTy htake hclosed0 hinA hpost n

/-- U-TOP-S2 read through L3: the slotless leaf's R-G top (local `TopShipsRG`). -/
theorem slotlessLeaf_topShipsRG {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module}
    {D : Design}
    (hdata : LeafDataOk p) (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D) (n : Nat) :
    TopShipsRG p n p.decl b raw D :=
  topShipsRG_of_NC p n p.decl b raw D (slotlessLeaf_topShipsNC L p hdata hnoI hsl0 hA hpost ran n)

end Tools.ShippingGen2
