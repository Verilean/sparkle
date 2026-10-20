import Tools.ShippingMachineShipsS
import Tools.ShippingSatAssemblyS

/-! # The leaf route's run hypotheses, discharged, with the slots' reset values

BUILT by the integrator: ls1 exit 0 (574 jobs, first try; axioms standard, asserted by LeafDeadInitSatTest) (round par/leafnz-sat, base 9df7578c).

`machine_ships_wiredS` (Tools/ShippingMachineShipsS.lean) concludes `MachineShipsS`, whose
hypotheses on the input stream `ins` and the source start state `st0` are left open. Here
they are DISCHARGED: for every typed input stream, the inputs are the stream's environment
(`leafIns`, built with `streamEnv` as in Tools/ShippingSatInputs.lean), the source start
state is `slotInit regs slots` (Tools/ShippingSatAssemblyS.lean: each slot register at its
reset value, `0` elsewhere), and every hypothesis — the source inputs, registers passing
through the seeding, reset low, the slot inits, the inputs and registers within their
widths, the start-state bound for the emitted text — is proved from the wiring
(`MachineWired`, under `d.shape.insts = []`) and the data condition `hinitW` (every slot's
reset value fits its slot's width).

## Why a new target state (`tgtSt2`) and not `MachineShipsS` literally

`MachineShipsS` clears the target state only when the OPTIMIZER's output is accepted; when
it is rejected it asks `Bounded (weOf wof) st0`. If the checked MERGE removed a slot
register (`mergeChecked`, e.g. two equal registers) and the optimizer is rejected, the
emitted module no longer declares that register, and `Bounded (weOf wof) st0` contradicts
its nonzero reset value: `MachineShipsS` is not satisfiable there. `tgtSt2 raw b o st0`
clears every name that is not a register of `o` whenever the merge OR the optimizer was
accepted by `refineCheck` (both steps transfer runs between two states agreeing on the
target's registers, `refineCheck_transfer`), and keeps `st0` when both were the identity.
The bound then holds in every case (`tgtSt2_bounded`, and the identity case from the
wiring). So `leaf_sat` is a proof of its own (the run chain of `machine_shipsS`, with the
state choice above), not an application of `machine_shipsS`.

What stays an antecedent: the emitted-text checks of `machine_ships_wiredS`
(`simpleBody`, `seqCheck`, the width agreement on `seqNames`), and one more width check of
the same kind: the emitted width map covers the input ports' declared widths (`hwofIn`).
No antecedent mentions `seedIn`, `Bounded` or the init equations.

Writing-time guesses (integrator: check these first):
* (g1) the 11-tuple destructuring of `MachineTraceL` and the 12 / 9-tuple ones of
  `MachineWired` (as in `machine_ships_wired`);
* (g2) `declWidth m` and `Tools.ShippingEntrySoundness.weOf m` definitionally equal
  (`have hdw : declWidth r0 = … := hw`), as `machine_ships` uses;
* (g3) `rw [h]` on `p.ty` inside the `match` of `MachineWired`'s input-width conjunct,
  closed by `rfl` / `simp [HWType.bitWidth]`;
* (g4) `List.getElem?_eq_some_iff` / `List.getElem?_eq_getElem` names on v4.32.1;
* (g5) `MachineData.bsIn` unfolds by `show`;
* (g6) the `leafIns` applications accepted up to `delta` by `exact` (`streamEnv_off`,
  `streamEnv_lt` after `rw [← hins]`; add `unfold leafIns` if not);
* (g7) the `let`s of `MachineWired` (`names`, `n`) instantiated in the destructured
  conjuncts `hnd`, `hinF` (so `rw [hPR] at h0` and `rw [← hinF hnoI] at hp` find their terms).
-/
namespace Tools.ShippingLeafSat
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Tools.ShippingMachineShipsW Tools.ShippingMachineShipsS
open Tools.ShippingSatInputs
open Tools.ShippingSatAssemblyS (slotInit slotInit_at slotInit_cases)
open Sparkle.IR.RegDedup (declWidth)

/-! ## The target start state -/

/-- The target start state: `st0` cleared on every name that is not a register of `o`,
when the merge (`raw → b`) or the optimizer (`b → o`) was accepted by `refineCheck`;
`st0` when both were the identity. -/
def tgtSt2 (raw b o : Sparkle.IR.AST.Module) (st0 : String → Nat) (n : String) : Nat :=
  if (refineCheck raw b = true ∨ refineCheck b o = true) ∧ n ∉ (seqRegs o).map (·.1) then 0
  else st0 n

/-- **The source/target correspondence**: on the registers of `o`, the target state is
the source state. -/
theorem tgtSt2_agree (raw b o : Sparkle.IR.AST.Module) (st0 : String → Nat) :
    ∀ r ∈ seqRegs o, tgtSt2 raw b o st0 r.1 = st0 r.1 := by
  intro r hr
  unfold tgtSt2
  rw [if_neg]
  intro h
  exact h.2 (List.mem_map_of_mem (f := (·.1)) hr)

theorem tgtSt2_off {raw b o : Sparkle.IR.AST.Module} (st0 : String → Nat)
    (hc : refineCheck raw b = true ∨ refineCheck b o = true) {n : String}
    (hn : n ∉ (seqRegs o).map (·.1)) : tgtSt2 raw b o st0 n = 0 := by
  unfold tgtSt2
  rw [if_pos ⟨hc, hn⟩]

theorem tgtSt2_of_false {raw b o : Sparkle.IR.AST.Module} (st0 : String → Nat)
    (h1 : refineCheck raw b = false) (h2 : refineCheck b o = false) :
    tgtSt2 raw b o st0 = st0 := by
  funext n
  unfold tgtSt2
  rw [if_neg]
  intro h
  rcases h.1 with h' | h'
  · rw [h1] at h'; exact Bool.false_ne_true h'
  · rw [h2] at h'; exact Bool.false_ne_true h'

/-- The target state within the emitted widths, from the source state's fit on the
registers of `o` and the emitted width agreement. -/
theorem tgtSt2_bounded {raw b o : Sparkle.IR.AST.Module} {wof : String → Option Nat}
    {st0 : String → Nat} (hc : refineCheck raw b = true ∨ refineCheck b o = true)
    (hfitO : ∀ r ∈ seqRegs o, st0 r.1 < 2 ^ declWidth o r.1)
    (hwag : ∀ n ∈ seqNames o.body, declWidth o n = Tools.SVParser.EmitSem.weOf wof n) :
    Bounded (Tools.SVParser.EmitSem.weOf wof) (tgtSt2 raw b o st0) := by
  intro n
  by_cases hn : n ∈ (seqRegs o).map (·.1)
  · obtain ⟨ro, hro, hro1⟩ := List.mem_map.mp hn
    subst hro1
    rw [tgtSt2_agree raw b o st0 ro hro, ← hwag ro.1 (seqRegs_mem_seqNames hro)]
    exact hfitO ro hro
  · rw [tgtSt2_off st0 hc hn]
    exact Nat.two_pow_pos _

/-- The checked merge keeps the declared widths (they are read off the wires). -/
theorem declWidth_mergeChecked (m : Sparkle.IR.AST.Module) :
    declWidth (mergeChecked m) = declWidth m := by
  funext x
  unfold declWidth
  rw [(mergeChecked_ports m).2.2]

/-- The input stream at cycle `t` of a run of `T` cycles, as an environment. -/
def leafIns (declName : Name) (bs : List (Name × MixedGateBinder)) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (T : Nat) : Nat → String → Nat :=
  fun t => streamEnv declName bs ids cache (fun j => (bools j).val (T - 1 - t))
    (fun j n => (bits j n).val (T - 1 - t))

set_option maxHeartbeats 4000000 in
/-- **A leaf state machine at the full entry, to the emitted Verilog, with every run
hypothesis discharged.** For every typed input stream and every number of cycles, the
seeding of the stream's environment carries the source inputs, and the optimized module
and its emitted Verilog, run from `tgtSt2 … (slotInit regs slots)`, show the source on
every output port at every cycle. Premises: the wired endpoint `soundL` and its structural
facts (as `machine_ships_wiredS`), the data `hlen`, `hinitW`, and the run. -/
theorem leaf_sat {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hlen : d.nIn + d.shape.layout.slots.length + d.shape.layout.lets = d.shape.binders.length)
    (hinitW : ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        (∃ lets : List String, MachineWired declName d.shape ids cache raw D regs lets) ∧
        ∀ (wof : String → Option Nat),
          simpleBody b = false →
          Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
            (checkedOptimize b).body = true →
          ((seqNames (checkedOptimize b).body).all fun n =>
            declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
          (∀ x ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).inputs.map (·.name),
            declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) x ≤
              Tools.SVParser.EmitSem.weOf wof x) →
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (T : Nat) (mems : MEnv),
            (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
              (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
              (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                (leafIns declName d.bsIn ids cache bools bits T) t st)) ∧
            ∃ envsO,
              runModule (declWidth (checkedOptimize b)) (checkedOptimize b).body
                (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                  (leafIns declName d.bsIn ids cache bools bits T)) T
                (tgtSt2 (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b (checkedOptimize b)
                  (slotInit regs d.shape.layout.slots)) mems = some envsO ∧
              (∃ pairs regs' mprog,
                Tools.SVParser.EmitSem.emitAssigns wof (checkedOptimize b).body = some pairs ∧
                Tools.SVParser.EmitSem.emitRegs wof (checkedOptimize b).body = some regs' ∧
                Tools.SVParser.EmitSem.emitMemWrites wof (checkedOptimize b).body = some mprog ∧
                Tools.SVParser.EmitSem.runModuleSV wof pairs regs' mprog
                  (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
                    (leafIns declName d.bsIn ids cache bools bits T)) T
                  (tgtSt2 (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b (checkedOptimize b)
                    (slotInit regs d.shape.layout.slots)) mems = some envsO) ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) q.name = f j := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  have hL := soundL hcore entry closes
  obtain ⟨ids, _, _, cache, regs, rnd, rlen, lets, _, wired, H⟩ := id hL
  obtain ⟨hnd, hal, _, _, _, _, _, houts, hinF, _, hclean, _⟩ := id wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, hevery, _, _, _, hinW, hok⟩ := hclean hnoI houtTy
  refine ⟨raw, D, hpost, ids, cache, regs, ⟨lets, wired⟩, ?_⟩
  intro wof hsB hsv hwag hwofIn i bools bits T mems
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost hwofIn ⊢
  -- the source start state
  generalize hst0 : slotInit regs d.shape.layout.slots = st0
  have hinit : ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
      d.shape.layout.slots[k]? = some f → st0 r = f.init := by
    intro k r f hk hf
    rw [← hst0]
    exact slotInit_at regs d.shape.layout.slots k r f rnd hk hf
  have hdw : declWidth r0 = Tools.ShippingEntrySoundness.weOf raw := hw
  -- a slot register's reset value fits its width
  have hslotW : ∀ (k : Nat) (n : String) (f : SlotField), regs[k]? = some n →
      d.shape.layout.slots[k]? = some f → f.init < 2 ^ declWidth r0 n := by
    intro k n f hk hf
    rw [hdw, (hregs k n f hk hf).1]
    exact hinitW f (List.mem_of_getElem? hf)
  -- every register statement of `r0` is a slot's: its start value fits
  have hregStmt : ∀ (n c : String) (rs : String × Sparkle.IR.Type.ResetKind)
      (inp : Sparkle.IR.AST.Expr) (iv : Int), Stmt.register n c rs inp iv ∈ r0.body →
      st0 n < 2 ^ declWidth r0 n := by
    intro n c rs inp iv hm
    rw [hb] at hm
    obtain ⟨k, f, hk, hf, -⟩ := hevery n c rs inp iv hm
    rw [hinit k n f hk hf]
    exact hslotW k n f hk hf
  have hfitR0 : ∀ r ∈ seqRegs r0, st0 r.1 < 2 ^ declWidth r0 r.1 := by
    intro r hr
    unfold seqRegs at hr
    obtain ⟨s, hs, hf⟩ := List.mem_filterMap.mp hr
    cases s with
    | register o' c rk inp iv =>
      have he : (o', c, rk, inp, iv) = r := by
        first
          | exact Option.some.inj hf
          | (simp only [Option.some.injEq] at hf; exact hf)
          | (injection hf)
      subst he
      exact hregStmt o' c rk inp iv hs
    | _ => first | cases hf | simp at hf | exact absurd hf (by simp)
  -- the merge: accepted by `refineCheck`, or the identity
  obtain ⟨f0, hf0⟩ : ∃ f, d.shape.layout.slots[0]? = some f := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons f _ => exact ⟨f, rfl⟩
  obtain ⟨r0n, hr0n⟩ : ∃ r, regs[0]? = some r := by
    cases hrs : regs with
    | nil =>
      have : d.shape.layout.slots.length = 0 := by
        rw [← hSS, ← rlen, hrs]; rfl
      rw [List.length_eq_zero_iff] at this; exact absurd this hsl
    | cons r _ => exact ⟨r, rfl⟩
  obtain ⟨_, _, rk0, inp0, hm0⟩ := hregs 0 r0n f0 hr0n hf0
  have hnA : r0.body.all Sparkle.IR.RegDedup.isAssign = false := by
    apply List.all_eq_false.mpr
    exact ⟨_, hb ▸ hm0, by simp [Sparkle.IR.RegDedup.isAssign]⟩
  have hr0ok : r0.body.all seqStmtOk = true := by rw [hb]; exact hok
  have hmerge : refineCheck r0 b = true ∨ b = r0 := by
    rcases hpost with rfl | rfl
    · exact Or.inr rfl
    · exact mergeChecked_nonAssign hnA
  have hbI : b.inputs = r0.inputs := by
    rcases hpost with rfl | rfl
    · rfl
    · exact (mergeChecked_ports r0).1
  have hbW : declWidth b = declWidth r0 := by
    rcases hpost with rfl | rfl
    · rfl
    · exact declWidth_mergeChecked r0
  have hbok : b.body.all seqStmtOk = true := by
    rcases hmerge with h | rfl
    · exact refineCheck_stmtOk_o h
    · exact hr0ok
  have hfitB : ∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1 := by
    rcases hmerge with hm | rfl
    · intro ro hro
      obtain ⟨rm, hrm, hname, hwd⟩ := refineCheck_regWidth hm ro hro
      rw [← hwd, ← hname]
      exact hfitR0 rm hrm
    · exact hfitR0
  -- the optimizer: accepted, or the identity
  have hopt : refineCheck b (checkedOptimize b) = true ∨ checkedOptimize b = b :=
    checkedOptimize_seqOk hsB hbok
  generalize hoo : checkedOptimize b = o at hopt hsv hwag ⊢
  have hoOk : o.body.all seqStmtOk = true := by
    rcases hopt with h | rfl
    · exact refineCheck_stmtOk_o h
    · exact hbok
  have hwag' : ∀ n ∈ seqNames o.body, declWidth o n = Tools.SVParser.EmitSem.weOf wof n := by
    intro n hn
    have := List.all_eq_true.mp hwag n hn
    simpa using this
  -- the declared input ports: inputs of `raw`, distinct, allocated
  have hbsIn : d.bsIn = d.shape.binders.take
      (d.shape.binders.length - d.shape.layout.slots.length - d.shape.layout.lets) := by
    show d.shape.binders.take d.nIn = _
    rw [show d.shape.binders.length - d.shape.layout.slots.length - d.shape.layout.lets = d.nIn
      by omega]
  obtain ⟨R, hPR⟩ := machPorts_take_prefix declName ids cache d.shape.binders d.nIn
  have hPmem : ∀ p ∈ machPorts declName ids cache d.bsIn,
      p ∈ machPorts declName ids cache d.shape.binders := by
    intro p hp
    rw [hPR]
    exact List.mem_append_left _ hp
  have hPin : ∀ p ∈ machPorts declName ids cache d.bsIn, p ∈ r0.inputs := by
    intro p hp
    rw [hbsIn, ← hinF hnoI] at hp
    rw [hi]
    exact (List.mem_filter.mp hp).1
  have hPnd : ((machPorts declName ids cache d.bsIn).map (·.name)).Nodup := by
    have h0 := hnd
    rw [hPR, List.map_append] at h0
    exact (List.nodup_append.mp h0).1
  have hPA : ∀ p ∈ machPorts declName ids cache d.bsIn,
      Sparkle.IR.NameHints.Allocated p.name :=
    fun p hp => hal _ (List.mem_map.mpr ⟨p, hPmem p hp, rfl⟩)
  have hoffC : ∀ p ∈ machPorts declName ids cache d.bsIn, p.name ≠ "clk" :=
    fun p hp => not_clk_of_alloc (hPA p hp)
  have hoffR : ∀ p ∈ machPorts declName ids cache d.bsIn, p.name ≠ "rst" :=
    fun p hp => not_rst_of_alloc (hPA p hp)
  generalize hins : leafIns declName d.bsIn ids cache bools bits T = ins
  -- (1) the inputs within the declared widths
  have hW0 : ∀ p ∈ machPorts declName ids cache d.bsIn, p.ty.bitWidth ≠ 0 →
      declWidth r0 p.name = p.ty.bitWidth := by
    intro p hp _
    have hpr : p ∈ raw.inputs := by rw [← hi]; exact hPin p hp
    rw [hdw, hinW p hpr (hoffC p hp) (hoffR p hp)]
    rcases machPorts_ty p hp with h | ⟨n, h⟩ <;> rw [h] <;>
      first | rfl | simp [Sparkle.IR.Type.HWType.bitWidth]
  have hinsAll : ∀ t x, ins t x < 2 ^ declWidth r0 x := by
    intro t x
    rw [← hins]
    exact streamEnv_lt (declWidth r0) hW0 x
  have hinsRaw : ∀ t x, x ∈ r0.inputs.map (·.name) → ins t x < 2 ^ declWidth r0 x :=
    fun t x _ => hinsAll t x
  have hinsB : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x := by
    intro t x _
    rw [hbW]
    exact hinsAll t x
  have hinsW : ∀ t x, x ∈ r0.inputs.map (·.name) →
      ins t x < 2 ^ Tools.SVParser.EmitSem.weOf wof x := fun t x hx =>
    Nat.lt_of_lt_of_le (hinsAll t x) (Nat.pow_le_pow_right (by decide) (hwofIn x hx))
  have hrstZ : ∀ t, ins t "rst" = 0 := by
    intro t
    rw [← hins]
    exact streamEnv_off hoffR
  have hrstIn' : "rst" ∈ r0.inputs.map (·.name) := by rw [hi]; exact hrstIn hsl
  -- (2) the source inputs and the registers through the seeding
  have hsrc : ∀ t st, t < T → SourceInputs declName d.bsIn ids cache
      (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
      (seedIn r0 ins t st) := by
    intro t st _
    refine sourceInputs_of_env hPnd (fun p hp => ?_)
    rw [seedIn_in (List.mem_map.mpr ⟨p, hPin p hp, rfl⟩), ← hins]
    try rfl
  have hpass : ∀ t st r, r ∈ regs → seedIn r0 ins t st r = st r := by
    intro t st r hr
    apply seedIn_out
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨hkl, -⟩ := List.getElem?_eq_some_iff.mp hk
    have hks : k < d.shape.layout.slots.length := by rw [← hSS, ← rlen]; exact hkl
    rw [hi]
    exact (hregs k r _ hk (List.getElem?_eq_getElem hks)).2.1
  have hrst : ∀ t st, seedIn r0 ins t st "rst" = 0 := by
    intro t st
    rw [seedIn_in hrstIn']
    exact hrstZ t
  refine ⟨hsrc, ?_⟩
  -- (3) the core run, at `r0`
  obtain ⟨envs, hrun, hlen', hobs, _⟩ := H i bools bits T (seedIn r0 ins) st0 mems hsrc hpass hrst
    hinit
  have hrun' : runModule (declWidth r0) r0.body (seedIn r0 ins) T st0 mems = some envs := by
    rw [hdw, hb]; exact hrun
  -- (4) the target run from `tgtSt2 r0 b o st0`, on the outputs equal to the core run
  have hbO : b.outputs = r0.outputs := by
    rcases hmerge with hm | rfl
    · exact (refineCheck_ports hm).2
    · rfl
  have hseed : seedIn b ins = seedIn r0 ins := seedIn_of_inputs hbI ins
  have hrstInB : "rst" ∈ b.inputs.map (·.name) := by rw [hbI]; exact hrstIn'
  have stepO : ∃ envsO,
      runModule (declWidth o) o.body (seedIn r0 ins) T (tgtSt2 r0 b o st0) mems = some envsO ∧
      envsO.length = envs.length ∧
      ∀ p ∈ r0.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) p.name = (envs[j]'hj') p.name := by
    cases hco : refineCheck b o with
    | true =>
      -- `b` from `st0`, then `o` from the target state
      have stepB : ∃ envsB,
          runModule (declWidth b) b.body (seedIn r0 ins) T st0 mems = some envsB ∧
          envsB.length = envs.length ∧
          ∀ p ∈ r0.outputs, ∀ j (hj : j < envsB.length) (hj' : j < envs.length),
            (envsB[j]'hj) p.name = (envs[j]'hj') p.name := by
        rcases hmerge with hm | rfl
        · exact refineCheck_transfer hm ins hinsRaw hrstIn' hrstZ (stO := st0)
            (fun _ _ => rfl) hfitR0 hrun'
        · exact ⟨envs, hrun', rfl, fun _ _ _ _ _ => rfl⟩
      obtain ⟨envsB, hrunB, hlenB, hcorrB⟩ := stepB
      rw [← hseed] at hrunB
      obtain ⟨envsO, hrunO, hlenO, hcorrO⟩ :=
        refineCheck_transfer hco ins hinsB hrstInB hrstZ (stO := tgtSt2 r0 b o st0)
          (tgtSt2_agree r0 b o st0) hfitB hrunB
      rw [hseed] at hrunO
      refine ⟨envsO, hrunO, by omega, ?_⟩
      intro p hp j hj hj'
      rw [hcorrO p (by rw [hbO]; exact hp) j hj (by omega), hcorrB p hp j (by omega) hj']
    | false =>
      have hob : o = b := by
        rcases hopt with h' | h'
        · rw [hco] at h'; cases h'
        · exact h'
      rw [hob] at hco ⊢
      cases hcm : refineCheck r0 b with
      | true =>
        -- the merge from `st0` to the target state
        exact refineCheck_transfer hcm ins hinsRaw hrstIn' hrstZ (stO := tgtSt2 r0 b b st0)
          (tgtSt2_agree r0 b b st0) hfitR0 hrun'
      | false =>
        have hbr : b = r0 := by
          rcases hmerge with h' | h'
          · rw [hcm] at h'; cases h'
          · exact h'
        rw [tgtSt2_of_false st0 hcm hco, hbr]
        exact ⟨envs, hrun', rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨envsO, hrunO, hlenO, hcorrO⟩ := stepO
  -- (5) the target state within the emitted widths
  have hstO : Bounded (Tools.SVParser.EmitSem.weOf wof) (tgtSt2 r0 b o st0) := by
    by_cases hc : refineCheck r0 b = true ∨ refineCheck b o = true
    · have hfitO : ∀ r ∈ seqRegs o, st0 r.1 < 2 ^ declWidth o r.1 := by
        rcases hopt with h' | rfl
        · intro ro hro
          obtain ⟨rm, hrm, hname, hwd⟩ := refineCheck_regWidth h' ro hro
          rw [← hwd, ← hname]
          exact hfitB rm hrm
        · exact hfitB
      exact tgtSt2_bounded hc hfitO hwag'
    · have h1 : refineCheck r0 b = false := by
        cases h : refineCheck r0 b
        · rfl
        · exact absurd (Or.inl h) hc
      have h2 : refineCheck b o = false := by
        cases h : refineCheck b o
        · rfl
        · exact absurd (Or.inr h) hc
      have hob : o = b := by
        rcases hopt with h' | h'
        · rw [h2] at h'; cases h'
        · exact h'
      have hbr : b = r0 := by
        rcases hmerge with h' | h'
        · rw [h1] at h'; cases h'
        · exact h'
      rw [tgtSt2_of_false st0 h1 h2]
      intro n
      rcases slotInit_cases regs d.shape.layout.slots n with h | ⟨k, f, hk, hf, he⟩
      · rw [← hst0, h]; exact Nat.two_pow_pos _
      · rw [← hst0, he]
        obtain ⟨_, _, rk, inp, hm⟩ := hregs k n f hk hf
        have hmo : Stmt.register n "clk" ("rst", rk) inp (Int.ofNat f.init) ∈ o.body := by
          rw [hob, hbr, hb]; exact hm
        rw [← hwag' n (mem_seqNames_of_reg hmo), hob, hbr]
        exact hslotW k n f hk hf
  -- (6) the emitted Verilog
  have hSV := seq_run_to_sv hoOk hsv hwag' (seedIn r0 ins) (seedIn_bounded hinsW) hstO hrunO
  refine ⟨envsO, hrunO, hSV, by omega, ?_⟩
  intro j hj k q f hq hf
  have hp : (⟨q.name, q.ty⟩ : Sparkle.IR.AST.Port) ∈ r0.outputs := by
    rw [ho, houts]; exact List.mem_map.mpr ⟨q, List.mem_of_getElem? hq, rfl⟩
  have h1 : (envsO[j]'hj) q.name = (envs[j]'(by omega)) q.name :=
    hcorrO ⟨q.name, q.ty⟩ hp j hj (by omega)
  rw [h1]
  exact hobs j (by omega) k q f hq hf

end Tools.ShippingLeafSat
