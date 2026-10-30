import Tools.ShippingGen2SlotlessClosed
import Tools.ShippingGen2CombKid
import Tools.ShippingGen2MemData
import Tools.ShippingRefineNoRst
import Tools.ShippingCallsAssemblyG
import Tools.ShippingClosedTransitionTyped
import Tools.ShippingPortWidthsPure
import Tools.ShippingFirstGateChild
import Tools.ShippingCallWidthsChildRealA
import Tools.ShippingMachineSeqChild
import Tools.ShippingMachineShipsComb
import Tools.ShippingPostSoundness
import Tools.ShippingOptSoundness
import Tools.ShippingCombKidText
import Tools.ShippingLeafOneOut
import Tools.ShippingLeafSat
import Tools.ConeFold
set_option autoImplicit false

/-! # M2-step S2: the slotless leaf ships (scripts/gen2/STEP_IFACE_FREEZE.md rev3 §4 S2)

`SlotlessLeafStmt` is `LeafStmt'` (Tools/ShippingGen2Leaf.lean) with `slots ≠ []` replaced by `slots = []`.

* `runModule_rst_irrel` (pure): an assignment-only body read-closed over `X ∌ "rst"` runs the same at every name
  other than `"rst"` under two seeds that agree there (S1 `runModule_seed_local` on `X ++ writesOf`, and
  `evalAssigns_frame` elsewhere).
* `slotlessLeaf_topShips_of_LB` (pure): the trace at `sllSeedZ b ins` (the canonical seed with the state held at
  0 on `"rst"`), moved to `seedIn b ins` (equal seeds when `"rst"` is an input, else `runModule_rst_irrel`), the merge
  (`mergeDuplicates_sound`), the optimizer (`checkedOptimize_sound` on the simple shape, else
  `refineCheck_transfer_noReg`: no register), `runModuleTG_instFree`.
* `slotlessLeaf_childShips_of_LB` (pure): the `CombChildRunN` branch of `ChildRunN`, from the trace at the identity
  extension (`traceL_of_LB`), `sourceInputs_of_vals`, the merge, `runModule_rst_irrel` on the shipped body,
  `RunOn_instFree`.
  **Deviation from the brief**: one premise more, `hinA : ∀ q ∈ raw.inputs, Allocated q.name`. `MachineWired`'s
  input clause leaves `extra = [] ∨ (extra = [clk, rst] ∧ slots = [])` open (MachineEntry.lean:742; the same gap
  is recorded in Tools/ShippingChecksRaw.lean:33 and Tools/ShippingSlotlessClk.lean:20), so `"clk"`/`"rst"` ∉
  inputs is not derivable from the trace. It is supplied from the run by `slotless_inputs_alloc_ofRun`
  (`synthesizeMachineCertified_leaf_runs` + `closedTransition_of_run` + `closeMachine_inputs`, as
  `leaf_run_portsA` does), so `slotlessLeaf_ships` has no premise beyond `SlotlessLeafStmt`'s.
* `slotlessLeaf_ships : SlotlessLeafStmt L`.

BUILT: g2st-s2-4632dfb6 at 4632dfb6; audit g2st-ax-0464c3cd; re-verified with `Pkg.comb` by g2cp2-698be477 (scoped-accepted at 22417406). -/
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

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## 1. Seeds and reset irrelevance (pure) -/

/-- The canonical seed with the state held at 0 on `"rst"`. -/
def sllSeedZ (m : Sparkle.IR.AST.Module) (ins : Nat → String → Nat) : Nat → (String → Nat) → Env :=
  fun t st => seedIn m ins t (fun x => if x = "rst" then 0 else st x)

theorem sll_seedIn_in {m : Sparkle.IR.AST.Module} {ins : Nat → String → Nat} {t : Nat} {st : String → Nat}
    {x : String} (hx : x ∈ m.inputs.map (·.name)) : seedIn m ins t st x = ins t x := by
  have hc : (m.inputs.map (·.name)).contains x = true := List.contains_iff_mem.mpr hx
  show (if (m.inputs.map (·.name)).contains x then ins t x else st x) = ins t x
  rw [if_pos hc]

theorem sll_seedZ_in {m : Sparkle.IR.AST.Module} {ins : Nat → String → Nat} {t : Nat} {st : String → Nat}
    {x : String} (hx : x ∈ m.inputs.map (·.name)) : sllSeedZ m ins t st x = ins t x := by
  show seedIn m ins t (fun y => if y = "rst" then 0 else st y) x = ins t x
  exact sll_seedIn_in hx

theorem sll_seedZ_ne {m : Sparkle.IR.AST.Module} {ins : Nat → String → Nat} {t : Nat} {st : String → Nat}
    {y : String} (hy : y ≠ "rst") : sllSeedZ m ins t st y = seedIn m ins t st y := by
  show (if (m.inputs.map (·.name)).contains y then ins t y else (if y = "rst" then 0 else st y)) =
    (if (m.inputs.map (·.name)).contains y then ins t y else st y)
  rw [if_neg hy]

theorem sll_seedZ_rst {m : Sparkle.IR.AST.Module} {ins : Nat → String → Nat} {t : Nat} {st : String → Nat}
    (h : "rst" ∈ m.inputs.map (·.name) → ins t "rst" = 0) : sllSeedZ m ins t st "rst" = 0 := by
  show (if (m.inputs.map (·.name)).contains "rst" then ins t "rst"
    else (if "rst" = "rst" then 0 else st "rst")) = 0
  by_cases hc : (m.inputs.map (·.name)).contains "rst" = true
  · rw [if_pos hc]
    exact h (List.contains_iff_mem.mp hc)
  · rw [if_neg hc]
    exact if_pos rfl

/-- With `"rst"` an input, holding the state at 0 on `"rst"` changes nothing. -/
theorem sll_seedZ_eq {m : Sparkle.IR.AST.Module} {ins : Nat → String → Nat}
    (h : "rst" ∈ m.inputs.map (·.name)) : sllSeedZ m ins = seedIn m ins := by
  funext t st y
  by_cases hy : y = "rst"
  · subst hy
    rw [sll_seedZ_in h, sll_seedIn_in h]
  · exact sll_seedZ_ne hy

/-- **Reset irrelevance** (pure): an assignment-only body read-closed over `X ∌ "rst"` runs the same, at every
name other than `"rst"`, under two seeds that agree at every name other than `"rst"`. -/
theorem runModule_rst_irrel {we : WEnv} {body : List Stmt} {X : List String}
    (hA : body.all isAssign = true) (hR : readsClosedB X body = true) (hX : "rst" ∉ X)
    {seed₁ seed₂ : Nat → (String → Nat) → Env}
    (hagree : ∀ t st y, y ≠ "rst" → seed₁ t st y = seed₂ t st y) :
    ∀ T st mems envs₁, runModule we body seed₁ T st mems = some envs₁ →
      ∃ envs₂, runModule we body seed₂ T st mems = some envs₂ ∧ envs₂.length = envs₁.length ∧
        ∀ j (h₁ : j < envs₁.length) (h₂ : j < envs₂.length) y, y ≠ "rst" →
          (envs₂[j]'h₂) y = (envs₁[j]'h₁) y := by
  intro T st mems envs₁ hrun₁
  obtain ⟨envs₂, hrun₂, hlen, hloc⟩ := Tools.ShippingGen2Comb.runModule_seed_local hA hR
    (seed₁ := seed₁) (seed₂ := seed₂)
    (fun t st x hx => hagree t st x (fun h => hX (by rw [← h]; exact hx))) T st mems envs₁ hrun₁
  refine ⟨envs₂, hrun₂, hlen, ?_⟩
  intro j hj₁ hj₂ y hy
  by_cases hyW : y ∈ X ++ Sparkle.IR.Reorder.writesOf body
  · exact hloc j hj₁ hj₂ y hyW
  · have hyw : y ∉ Sparkle.IR.Reorder.writesOf body := fun h => hyW (List.mem_append_right _ h)
    obtain ⟨_, hg₁⟩ := runModule_assigns_get hA T st mems envs₁ hrun₁
    obtain ⟨_, hg₂⟩ := runModule_assigns_get hA T st mems envs₂ hrun₂
    rw [Tools.ConeFold.evalAssigns_frame we mems body _ _ (hg₂ j hj₂)
        (Tools.ShippingGen2Comb.memFree_of_assigns hA) y hyw,
      Tools.ConeFold.evalAssigns_frame we mems body _ _ (hg₁ j hj₁)
        (Tools.ShippingGen2Comb.memFree_of_assigns hA) y hyw]
    exact (hagree _ _ y hy).symm

/-! ## Small module facts (pure) -/

theorem sll_seqRegsL_nil : ∀ {body : List Stmt}, body.all isAssign = true →
    Tools.ShippingSeqOptSoundness.seqRegsL body = []
  | [], _ => rfl
  | st :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases st with
    | assign l e =>
      simp only [Tools.ShippingSeqOptSoundness.seqRegsL, List.filterMap_cons]
      exact sll_seqRegsL_nil h.2
    | _ => simp [isAssign] at h

theorem sll_seqRegs_nil {b : Sparkle.IR.AST.Module} (h : b.body.all isAssign = true) :
    Sparkle.IR.OptCheck.seqRegs b = [] :=
  sll_seqRegsL_nil h

/-- The post-processing of an assignment-only module: the same ports and widths, assignments only, and every
evaluation of the cleaned body is one of the shipped body (`mergeDuplicates_sound`). -/
theorem sll_post {r0 b : Sparkle.IR.AST.Module} (hall0 : r0.body.all isAssign = true)
    (hpost : b = r0 ∨ b = mergeChecked r0) :
    b.inputs = r0.inputs ∧ b.outputs = r0.outputs ∧ declWidth b = declWidth r0 ∧
      b.body.all isAssign = true ∧
      ∀ mems init e, evalAssigns (declWidth r0) mems r0.body init = some e →
        evalAssigns (declWidth b) mems b.body init = some e := by
  rcases hpost with rfl | rfl
  · exact ⟨rfl, rfl, rfl, hall0, fun _ _ _ h => h⟩
  · have hmc : mergeChecked r0 = Sparkle.IR.RegDedup.mergeDuplicates r0 :=
      Tools.ShippingCombKidText.mergeChecked_assign hall0
    refine ⟨(mergeChecked_ports r0).1, (mergeChecked_ports r0).2.1,
      Tools.ShippingLeafSat.declWidth_mergeChecked r0, ?_, ?_⟩
    · rw [hmc]
      exact Tools.ShippingLeafOneOut.mergeDuplicates_assign hall0
    · intro mems init e h
      rw [hmc]
      exact (Tools.ShippingPostSoundness.mergeDuplicates_sound r0 mems init e hall0 h).1

/-- Without calls, no binder after the first `kD` (`kD ≥` the declared arity) is a domain binder. -/
theorem sll_domB (d : MachineData) (kD : Nat) (hok : d.ok = true) (hkD : d.bsIn.length ≤ kD) :
    ∀ b ∈ d.shape.binders.drop kD, b.2 ≠ .domain := by
  intro b hb
  rw [d.binders_split, List.append_assoc, List.drop_append, List.drop_eq_nil_of_le hkD,
    List.nil_append] at hb
  exact data_hSL d hok b (List.mem_of_mem_drop hb)

/-! ## 2. `TopShips` of a slotless leaf (pure; the trace as given) -/

theorem slotlessLeaf_topShips_of_LB (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hclosed0 : readsClosedB ((Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).inputs.map (·.name))
        (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body = true ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body.all isAssign = true)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (n : Nat) :
    TopShips p n p.decl b raw D := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, _, wired, tr⟩ := id hL
  have hregs0 : regs = [] := List.eq_nil_of_length_eq_zero (by simp [rlen, hSS, hsl0])
  subst hregs0
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, _⟩ := hclean hnoI houtTy
  have houtOk := ok_outNameOk p.d hok
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost hclosed0
  obtain ⟨hcl0, hall0⟩ := hclosed0
  obtain ⟨hbi, hbo, _, hallB, hevB⟩ := sll_post hall0 hpost
  refine ⟨ids, nd, len, cache, [], rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hinp _ hrstG _ _ _ hinsB _
  -- the core module's run, at the canonical seed with the state held at 0 on `"rst"`
  obtain ⟨envs, hrun, hlen, hobs, _⟩ := tr i bools bits T (sllSeedZ b ins) st0 mems
    (fun t st ht => by
      have h := hinp t (fun x => if x = "rst" then 0 else st x) ht
      rw [htake] at h
      exact h)
    (fun t st r hr => by simp at hr)
    (fun t st => sll_seedZ_rst (fun hm => hrstG hm t))
    (fun k r f hr _ => by simp at hr)
  have hrun0 : runModule (declWidth r0) r0.body (sllSeedZ b ins) T st0 mems = some envs := by
    rw [hb, show declWidth r0 = weOf r0 from rfl, hw]; exact hrun
  -- the canonical seed
  have hR : ∃ envsR, runModule (declWidth r0) r0.body (seedIn b ins) T st0 mems = some envsR ∧
      envsR.length = envs.length ∧
      ∀ j (h₁ : j < envs.length) (h₂ : j < envsR.length) y, y ≠ "rst" →
        (envsR[j]'h₂) y = (envs[j]'h₁) y := by
    by_cases hrX : "rst" ∈ b.inputs.map (·.name)
    · rw [sll_seedZ_eq hrX] at hrun0
      exact ⟨envs, hrun0, rfl, fun _ _ _ _ _ => rfl⟩
    · exact runModule_rst_irrel (X := b.inputs.map (·.name)) (seed₁ := sllSeedZ b ins)
        (seed₂ := seedIn b ins) hall0 (by rw [hbi]; exact hcl0) hrX
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

/-! ## 3. `ChildShips` of a slotless leaf: the combinational branch (pure) -/

theorem slotlessLeaf_childShips_of_LB (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) (hext : ExtInS p)
    (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hclosed0 : readsClosedB ((Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).inputs.map (·.name))
        (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body = true ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body.all isAssign = true)
    (hclosedB : readsClosedB (b.inputs.map (·.name)) b.body = true ∧ b.body.all isAssign = true)
    (hinA : ∀ q ∈ raw.inputs, Sparkle.IR.NameHints.Allocated q.name)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (n : Nat) :
    ChildShips p n b D := by
  have hkD : p.d.bsIn.length ≤ p.kD := by
    have h := congrArg List.length htake
    rw [List.length_take] at h
    omega
  have hLid := traceL_of_LB hL (fun i bools bits j hj => hext.1 i bools bits j (by omega))
    (fun i bools bits j n' hj => hext.2 i bools bits j n' (by omega))
  have hS : ∀ i, p.S i = fun vals => p.src i (boolsOf (D := dom i) p.d.bsIn vals)
      (bitsOf (D := dom i) p.d.bsIn vals) := by
    intro i; funext vals; simp only [Pkg.S, htake]
  obtain ⟨ids, nd, len, cache, regs, _, rlen, _, _, wired, tr⟩ := id hLid
  have hregs0 : regs = [] := List.eq_nil_of_length_eq_zero (by simp [rlen, hSS, hsl0])
  subst hregs0
  obtain ⟨_, _, _, _, _, _, _, houts, hins, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, _, _, _, hnd, _, hdisj, _, _⟩ := hclean hnoI houtTy
  have houtOk := ok_outNameOk p.d hok
  have hSlen := data_hSlen p.d hok hSS
  have hLlen := data_hLlen p.d hok
  -- the argument ports are the declaration's (copied from `seqChildRun_of_L`)
  have hbsIn : p.d.shape.binders.take (p.d.shape.binders.length - p.d.shape.layout.slots.length -
      p.d.shape.layout.lets) = p.d.bsIn := by
    have hb' := p.d.binders_split
    rw [← hSlen, ← hLlen]
    conv => lhs; rw [hb']
    simp only [List.length_append]
    rw [show p.d.bsIn.length + p.d.slotBs.length + p.d.letBs.length - p.d.slotBs.length -
      p.d.letBs.length = p.d.bsIn.length by omega, List.append_assoc, List.take_left]
  have hlenIn : p.d.bsIn.length ≤ ids.length := by
    rw [len]; simp only [MachineData.bsIn, List.length_take]; omega
  have hargs : Tools.ShippingMachineCompose.argPorts raw = machPorts p.decl ids cache p.d.bsIn := by
    unfold Tools.ShippingMachineCompose.argPorts; rw [hins hnoI, hbsIn]
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost hclosed0
  obtain ⟨_, hall0⟩ := hclosed0
  obtain ⟨hbi0, hbo0, _, hallB, hevB⟩ := sll_post hall0 hpost
  have hbi : b.inputs = raw.inputs := hbi0.trans hi
  have hbo : b.outputs = raw.outputs := hbo0.trans ho
  have hargsB : Tools.ShippingMachineCompose.argPorts b = Tools.ShippingMachineCompose.argPorts raw := by
    unfold Tools.ShippingMachineCompose.argPorts; rw [hbi]
  -- no input is the clock or the reset: the inputs are allocated names
  have hclkB : "clk" ∉ b.inputs.map (·.name) := by
    rw [hbi]
    intro h
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp h
    exact Tools.ShippingFirstGateChild.nAlloc_clk (by rw [← hqn]; exact hinA q hq)
  have hrstB : "rst" ∉ b.inputs.map (·.name) := by
    rw [hbi]
    intro h
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp h
    exact Tools.ShippingFirstGateChild.nAlloc_rst (by rw [← hqn]; exact hinA q hq)
  intro dsn _ _ i
  rw [hS i, htake]
  refine Or.inr ?_
  refine ⟨hbo.trans houts, by rw [hbi]; exact hnd, hclkB, hrstB, by rw [hbi, hbo]; exact hdisj, ?_, ?_⟩
  · rw [hargsB, hargs, Tools.ShippingMachineCompose.machPorts_length _ hlenIn]
  · intro T ins s vals hrange hports _
    rw [RunOn_instFree (childMap dsn.modules) b (instFree_of_assigns hallB)]
    -- the core module's run at the decoded values, the state held at 0 on `"rst"`
    obtain ⟨envs, hrun, hlen, hobs, _⟩ := tr i (boolsOf p.d.bsIn vals) (bitsOf p.d.bsIn vals) T
      (sllSeedZ b ins) (stOf n s) (memsOf n s)
      (fun t st ht => by
        refine Tools.ShippingMachineChild.sourceInputs_of_vals nd hlenIn hargs (sllSeedZ b ins t st)
          (vals (T - 1 - t)) ?_ (hrange _ (by omega))
        rw [← hports t ht, hargsB]
        apply List.map_congr_left
        intro q hq
        have hqi : q ∈ raw.inputs := (List.mem_filter.mp hq).1
        have hqn : q.name ∈ b.inputs.map (·.name) := by
          rw [hbi]; exact List.mem_map.mpr ⟨q, hqi, rfl⟩
        exact sll_seedZ_in hqn)
      (fun t st r hr => by simp at hr)
      (fun t st => sll_seedZ_rst (fun h => absurd h hrstB))
      (fun k r f hr _ => by simp at hr)
    have hrun0 : runModule (declWidth r0) r0.body (sllSeedZ b ins) T (stOf n s) (memsOf n s) =
        some envs := by
      rw [hb, show declWidth r0 = weOf r0 from rfl, hw]; exact hrun
    -- the merge: the same environments
    obtain ⟨envsB, hrunB, hlenB, hcorrB⟩ := Tools.ShippingMachineShipsComb.runModule_assigns hall0 hallB
      (P := fun _ => True) (fun _ => True) (fun _ _ => trivial)
      (fun mems init e _ h => ⟨e, hevB mems init e h, fun _ _ => rfl⟩) T (stOf n s) (memsOf n s) envs hrun0
    -- the canonical seed: `"rst"` is not read
    obtain ⟨envs2, hrun2, hlen2, hcorr2⟩ := runModule_rst_irrel (X := b.inputs.map (·.name))
      (seed₁ := sllSeedZ b ins) (seed₂ := seedIn b ins) hallB hclosedB.1 hrstB
      (fun t st y hy => sll_seedZ_ne (m := b) (ins := ins) (t := t) (st := st) hy)
      T (stOf n s) (memsOf n s) envsB hrunB
    refine ⟨envs2, hrun2, by omega, ?_⟩
    intro j hj k o f hk hf
    have hne : o.name ≠ "rst" :=
      (Tools.ShippingCallsAssemblyG.outName_ne_clk (houtOk o (List.mem_of_getElem? hk))).2
    have h1 : (envs2[j]'hj) o.name = (envsB[j]'(by omega)) o.name :=
      hcorr2 j (by omega) hj o.name hne
    have h2 : (envsB[j]'(by omega)) o.name = (envs[j]'(by omega)) o.name :=
      hcorrB j (by omega) (by omega) o.name trivial
    rw [h1, h2]
    exact hobs j (by omega) k o f hk hf

/-! ## The input names of a slotless leaf, from its run (A boundary) -/

set_option maxHeartbeats 2000000 in
/-- The returned core module of a leaf without slots has allocated input names only (no `"clk"`/`"rst"`): it is
`closeMachine lay t'` (`synthesizeMachineCertified_leaf_runs`), whose inputs without slots are a prefix of the
let-closed transition's (`closeMachine_inputs`), which are allocated wires (`closedTransition_of_run`). -/
theorem slotless_inputs_alloc_ofRun (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {D : Design}
    (hdata : LeafDataOk p) (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D) :
    ∀ q ∈ raw.inputs, Sparkle.IR.NameHints.Allocated q.name := by
  obtain ⟨hok, hco, hSS, _⟩ := hdata.rows
  have hkD : p.d.bsIn.length ≤ p.kD := by
    have h := congrArg List.length htake
    rw [List.length_take] at h
    omega
  obtain ⟨tenv, bb, w9, w10, hrun9, _⟩ := ran
  obtain ⟨t, t', d₀, run, hcl, hMeq, _⟩ :=
    Tools.ShippingCallWidthsChildRealA.synthesizeMachineCertified_leaf_runs hnoI hrun9
  obtain ⟨Bc, coreW, hbodyc, _, _, namesc, inWc, _⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run p.d hok (Pkg.body_eq p) hco hSS
      (sll_domB p.d p.kD hok hkD) run hcl
  obtain ⟨hcm0, _⟩ :=
    Tools.ShippingPortWidthsPure.closeMachine_inputs (t := t') (lay := p.d.shape.layout) hbodyc
  have hE : p.d.shape.layout.slots.isEmpty = true := by simp [hsl0]
  intro q hq
  rw [hMeq, hcm0 hE] at hq
  exact namesc q (inWc q (List.mem_of_mem_take hq))

/-! ## 4. The statement and the slotless leaf lemma -/

/-- **The slotless-leaf statement**: `LeafStmt'` with `slots ≠ []` replaced by `slots = []`. -/
def SlotlessLeafStmt {mref cref} (L : Laws mref cref) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    LeafDataOk p → ExtInS p → p.d.shape.insts = [] → p.d.shape.layout.slots = [] →
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    ∀ n, TopShips p n p.decl b raw D ∧ ChildShips p n b D

/-- **M2-step S2: the slotless leaf ships** (`SlotlessLeafStmt`). -/
theorem slotlessLeaf_ships (L : Laws mref cref) : SlotlessLeafStmt (ι := ι) (dom := dom) L := by
  intro p mctx cctx w w1 raw b D hdata hext hnoI hsl0 hA _ _ hpost _ ran n
  obtain ⟨hok, hco, hSS, houtTy⟩ := hdata.rows
  have htake := leaf_take p.d p.kD hok hco hnoI
  have hL := (Pkg.trace L.O L.T hA p ran).toLB
  have hclosed0 := slotless_closed_ofRun L p (b := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
    hdata hnoI hsl0 hA (Or.inl rfl) ran
  have hclosedB := slotless_closed_ofRun L p hdata hnoI hsl0 hA hpost ran
  have hinA := slotless_inputs_alloc_ofRun L p hdata hnoI hsl0 htake ran
  exact ⟨slotlessLeaf_topShips_of_LB p hL hnoI hsl0 hok hSS houtTy htake hclosed0 hpost n,
    slotlessLeaf_childShips_of_LB p hL hext hnoI hsl0 hok hSS houtTy htake hclosed0 hclosedB hinA hpost n⟩

end Tools.ShippingGen2
