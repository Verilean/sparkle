import Tests.Gen2.QuantEndpoint
import Tools.ShippingGen2MemShips
import Tools.ShippingGen2LoopRestrict
set_option autoImplicit false

/-! # loop-pkg step 3: the REAL IP top `quantModule` as a `memParent_ships` instance (LOOPPKG_FREEZE.md §3, §5.2, §6)

Suppliers (all named, all kernel-checked here):
* the loop package's `LoopFacts` from the generated `quantModule.machine_*` refl checks, and `quant_hcausal` assembled
  as the generator's `loopCalls` does (`CtxAgree.of_state`, `machine_causal_0/1`, `extendBits_val`);
* `quant_memDec` (the per-call `MemFacts` over `letObsLoop` / `ext (Signal.loop f)`), by the generator's `memTactic`
  steps (`rfl` / `decide`);
* `ExtInS`, `MemParentDataOk`, `MemOrigin` (from `quant_memDec`), the case premises.
The compiler-run premises stay hypotheses: CONDITIONAL instance (package/data satisfiability), not evidence that an
actual successful run exists. `machine_source` ties the generated `src` to the generated loop; that the generated loop
is `quantModule`'s own is G3-DECL by construction (not derived here). -/
set_option maxHeartbeats 8000000

namespace Tests.Gen2.QuantInstance
open Tools.ShippingGen2 Tools.ShippingGen2Loop
open Sparkle.Core.Domain

/-- **`quant_hcausal`**: the loop head's causality premise, assembled as `loopCalls`. -/
theorem quant_hcausal : ∀ (i : DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n))
    (l l' : Sparkle.Core.Signal.Signal i (BitVec 2 × BitVec 5 × Bool × BitVec 16)) (t : Nat),
    (∀ c, c ≤ t → l.val c = l'.val c) →
    (∀ p w, (Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExt i bools bits l p w).val t =
      (Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExt i bools bits l' p w).val t) ∧
    (∀ p, (Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExtB i bools bits l p).val t =
      (Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExtB i bools bits l' p).val t) := by
  intro i bools bits l l' t h
  have hag := Tools.ShippingMachineCausal.CtxAgree.of_state bools bits l l' t h
  have f0 := Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_causal_0 i _ _ t hag
  have f1 := Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_causal_1 i _ _ t hag
  delta Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExt Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExtB
  exact ⟨Tools.ShippingMachineAuto.extendBits_val (Tools.ShippingMachineAuto.extendBits_val (fun _ _ => rfl) f0) f1,
    fun _ => rfl⟩

/-- The loop head's premises for `quantModule`, at the generated index `(DomainConfig, id)`. -/
theorem quant_facts : LoopFacts Sparkle.IP.Video.H264.QuantSynth.quantModule.machineData (fun i : DomainConfig => i)
    Sparkle.IP.Video.H264.QuantSynth.quantModule.machineSigma Sparkle.IP.Video.H264.QuantSynth.quantModule.machineInits
    Sparkle.IP.Video.H264.QuantSynth.quantModule.machineBody Sparkle.IP.Video.H264.QuantSynth.quantModule.machineRes
    Sparkle.IP.Video.H264.QuantSynth.quantModule.machineResult Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExt
    Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExtB Sparkle.IP.Video.H264.QuantSynth.quantModule.machineSource :=
  ⟨Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_ok, Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_body,
   Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_inits, Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_reset,
   Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_writes, Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_result,
   Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_source, quant_hcausal⟩

#eval (Sparkle.IP.Video.H264.QuantSynth.quantModule.machineData.nIn,
  Sparkle.IP.Video.H264.QuantSynth.quantModule.machineData.shape.insts.length)

abbrev U := fun _ : Unit => defaultDomain

/-- `quantModule`'s loop package at `Unit` (every field the generated declaration, at `defaultDomain`). -/
noncomputable def qL : SrcPkgL Unit U :=
  { decl := ``Sparkle.IP.Video.H264.QuantSynth.quantModule,
    d := Sparkle.IP.Video.H264.QuantSynth.quantModule.machineData,
    kD := Sparkle.IP.Video.H264.QuantSynth.quantModule.machineData.nIn -
      Sparkle.IP.Video.H264.QuantSynth.quantModule.machineData.shape.insts.length,
    α := fun _ => BitVec 2 × BitVec 5 × Bool × BitVec 16, inh := fun _ => inferInstance, ρ := _,
    σ := fun _ => Sparkle.IP.Video.H264.QuantSynth.quantModule.machineSigma defaultDomain,
    inits := Sparkle.IP.Video.H264.QuantSynth.quantModule.machineInits,
    f := fun _ => Sparkle.IP.Video.H264.QuantSynth.quantModule.machineBody defaultDomain,
    res := fun _ => Sparkle.IP.Video.H264.QuantSynth.quantModule.machineRes defaultDomain,
    obsR := fun _ => Sparkle.IP.Video.H264.QuantSynth.quantModule.machineResult defaultDomain,
    ext := fun _ => Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExt defaultDomain,
    extB := fun _ => Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExtB defaultDomain,
    src := fun _ => Sparkle.IP.Video.H264.QuantSynth.quantModule.machineSource defaultDomain,
    facts := loopFacts_restrict _ defaultDomain quant_facts }

noncomputable abbrev qPkg : Pkg Unit U := .loop qL

theorem q_dataOk : MemParentDataOk qPkg := by
  unfold MemParentDataOk MemParentDataOkB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_ok, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
    first | decide | decide +kernel

theorem q_insts_ne : qPkg.d.shape.insts ≠ [] := by
  show Sparkle.IP.Video.H264.QuantSynth.quantModule.machineData.shape.insts ≠ []
  first | decide | decide +kernel
theorem q_fne : qPkg.d.shape.instFields ≠ [] := by
  show Sparkle.IP.Video.H264.QuantSynth.quantModule.machineData.shape.instFields ≠ []
  first | decide | decide +kernel
theorem q_slotsNe : qPkg.d.shape.layout.slots ≠ [] := by
  show Sparkle.IP.Video.H264.QuantSynth.quantModule.machineData.shape.layout.slots ≠ []
  first | decide | decide +kernel

theorem q_extInS : ExtInS qPkg := by
  refine ⟨fun _ bools bits j hj => ?_, fun _ bools bits j n' hj => ?_⟩
  · show Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExtB defaultDomain bools bits _ j = bools j
    delta Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExtB
    rfl
  · show Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExt defaultDomain bools bits _ j n' = bits j n'
    have hkD : qL.kD = 55 := by first | decide | decide +kernel
    change j < qL.kD at hj
    rw [hkD] at hj
    delta Sparkle.IP.Video.H264.QuantSynth.quantModule.machineExt
    simp only [Tools.ShippingMachineAuto.extendBits]
    (repeat' split) <;> first | rfl | (exfalso; omega)

theorem q_memDec : ∀ (k : Nat) (hk : k < qPkg.d.shape.insts.length), MemDec qPkg k (qPkg.d.shape.insts[k]).1 := by
  intro k hk _ bools bits
  have hl : qPkg.d.shape.insts.length = 2 := by
    show Sparkle.IP.Video.H264.QuantSynth.quantModule.machineData.shape.insts.length = 2
    first | decide | decide +kernel
  have hk2 : k < 2 := hl ▸ hk
  rcases k with _ | _ | k
  · refine ⟨true, 4, 16, ?A, ?D, ?E, ?R, ?l0, ?l1, ?l2, ?l3, rfl, rfl, ?h0, by decide, ?h1, by decide, ?h2,
      by decide, ?h3, by decide, rfl, ?hx⟩
    case hx => intro j; rfl
    all_goals rfl
  · refine ⟨false, 4, 16, ?A, ?D, ?E, ?R, ?l0, ?l1, ?l2, ?l3, rfl, rfl, ?h0, by decide, ?h1, by decide, ?h2,
      by decide, ?h3, by decide, rfl, ?hx⟩
    case hx => intro j; rfl
    all_goals rfl
  · omega

theorem q_memOrigin : MemOrigin qPkg := memOrigin_of_memDec qPkg q_memDec

/-- **The conditional instance on the real IP top `quantModule`.** -/
theorem q_ships {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design)
    (hA : Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx)
    (hjqc : Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w)
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore qPkg.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref qPkg.decl qPkg.d.shape)
    (ran : MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) qPkg.decl qPkg.d.shape raw D) (n : Nat) :
    TopShips qPkg (n + 1) qPkg.decl b raw D ∧ ChildShips qPkg (n + 1) b D :=
  memParent_ships L qPkg mctx cctx w w1 raw b D q_dataOk q_extInS q_memOrigin q_insts_ne q_fne q_slotsNe
    hA hjqc hcore hpost entry ran q_memDec n

#print axioms quant_hcausal
#print axioms q_memDec
#print axioms q_extInS
#print axioms q_dataOk
#print axioms q_ships
#print axioms Tools.ShippingGen2.memParent_ships
#print axioms Tools.ShippingGen2.Pkg.trace
#print axioms Tools.ShippingGen2Loop.genTraceL

end Tests.Gen2.QuantInstance
