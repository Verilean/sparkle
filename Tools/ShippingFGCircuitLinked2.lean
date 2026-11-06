import Tools.ShippingFGCircuitLinked
import Tools.ShippingMachineLoopL
import Tools.ShippingMachineShipsW
set_option autoImplicit false
-- FG circuit pilot S1g, unit 2 (copy of RunLocal2 on the linked boundary): the endpoint chain `machine_trace_lets_of_streamB` → … → `machine_ships_wired` with the run-local boundary. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `counterLoop.machine_ships_wired` with `MachineDefinesLinked`

The generated endpoint `X.machine_ships_wired hr hd hc` (for `counterLoop`: `machine_ships_wired d (machine_traceL_of_loop …) …`) takes `hd : MachineDefines`, the `∀`-world boundary. The five theorems below are COPIES of the existing
proofs (`machine_trace_lets_of_streamB`, `machine_trace_lets_of_stream`, `machine_traceL_of_stream`, `machine_traceL_of_loop`, `machine_ships_wired`); the only change is the boundary premise: `MachineDefinesLinked` of the core run
(`Tools/ShippingFGCircuitLinked.lean`) in place of `MachineDefines`, consumed by `synthesizeCombinationalCore_machine_soundC`. -/
namespace Tools.ShippingFGCircuitLinked2
open Lean
open Tools.ShippingFGCircuitLinked

section A
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST
set_option maxHeartbeats 2000000 in
theorem machine_trace_lets_of_streamBC {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig)
    (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (stream : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∃ σ : Nat → HList (tys d.ss), σ 0 = inits ∧
        (∀ t, σ (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) t (σ t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) t (σ t)).v
            (d.vpos j) w) d.nexts) ∧
        (∀ j, (src i bools bits).map (fun f => f j) =
          d.outs.map fun o => enc o.1 (eval
            (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) j (σ j)).b
              (d.bpos k))
            (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) j (σ j)).v
              (d.vpos k) w) o.2)) ∧
        ∀ (j q : Nat) (g : Nat → Nat) (l : Σ s : SType, Term s),
          (lsrc i bools bits)[q]? = some g → d.ls[q]? = some l →
          g j = enc l.1 (eval
            (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) j (σ j)).b
              (d.bpos k))
            (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits) j (σ j)).v
              (d.vpos k) w) l.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefinesLinked mctx mref cctx cref declName d.shape w m design w')
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceLB declName d m design dom src ext extB lsrc := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, hslots, fb, fv, fslots, flets, nextsWF, houts, hne⟩ := ok
  have hkIn : d.bsIn.length = d.nIn := by
    simp only [MachineData.bsIn, List.length_take]; omega
  have hn : d.slotBs.length = d.ss.length := by
    simp only [MachineData.slotBs, List.length_take, List.length_drop]; omega
  have layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) =>
      f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  have hpres : MachinePreserves declName d.shape d.bsIn d.slotBs d.letBs m design :=
    synthesizeCombinationalCore_machine_soundC hr entry closes d.binders_split hlets
      (by
        intro name n hmem
        have := List.all_eq_true.mp positive _ hmem
        simpa using this)
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  cases hf : d.fields with
  | nil => simp [hf] at hne
  | cons f0 rest =>
  have hcore : d.core = packList f0 rest := by
    simp only [MachineData.core, hf, packAll]
  simp only [MachineData.packed] at hwf hbody
  generalize d.core = c at hcore hwf hbody hfit houtfit
  subst hcore
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => simp [h] at this
    | some b =>
      obtain ⟨nm, k⟩ := b
      simp only [h, Option.map_some, Option.some.injEq] at this
      subst this
      exact ⟨nm, rfl⟩
  have hv' : ∀ j, j < d.kv →
      ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => simp [h] at this
    | some b =>
      obtain ⟨nm, k⟩ := b
      simp only [h, Option.map_some, Option.some.injEq] at this
      subst this
      exact ⟨nm, rfl⟩
  have hnexts : (f0 :: rest).drop d.outs.length = d.nexts.fields := by
    rw [← hf]
    unfold MachineData.fields
    have hl : d.outs.length = (d.outs.map fun t => toField t.1 t.2).length := by simp
    rw [hl, List.drop_left]
  have facts : TermFacts d.bsIn.length d.kb d.kv d.vw d.bpos d.vpos d.K d.ss d.ls := by
    rw [hkIn]
    exact ⟨fb, fv, fun i s hs => by
      have hi : i < d.ss.length := (List.getElem?_eq_some_iff.mp hs).1
      rw [fslots i hi, hs], flets⟩
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, h⟩ :=
    machine_endpoint hpres (K := d.K) (nOuts := d.outs.length) layW hwf hb' hv' hbody hfit
      houtfit (by rw [hkIn, hn]; exact hscoped) hn hnexts (hf ▸ slotsFit_of hslots) facts
      nextsWF
  refine ⟨ids, nd, len, cache, regs, rnd, rlen.trans hn, lets, llen, wired, ?_⟩
  intro ix bools bits T seed st0 mems inputs pass rst init
  have hinit' : ∀ i, encState d.ss inits i =
      (d.shape.layout.slots[i]?.map (·.init)).getD 0 := by
    intro i
    by_cases hi : i < d.ss.length
    · have := List.all_eq_true.mp hinit i (List.mem_range.mpr hi)
      simpa using this
    · rw [encState_ge _ _ _ (by omega)]
      have hnone : d.shape.layout.slots[i]? = none := by
        rw [List.getElem?_eq_none]
        rw [layW.length_eq, hn]; omega
      rw [hnone]; rfl
  obtain ⟨σ, hσ0, hσs, hobsσ, hletσ⟩ := stream ix bools bits
  obtain ⟨envs, hrun, hlen', hobs, hletE⟩ := h σ (extB ix bools bits) (ext ix bools bits)
    (by intro i; rw [hσ0]; exact hinit' i)
    (by rw [hkIn]; exact hσs) T seed st0 mems inputs pass rst init
  refine ⟨envs, hrun, hlen', ?_, ?_⟩
  rotate_left
  · intro j hj q name g hn' hg hq
    rw [hletE j hj q name d.ls[q] hn' (List.getElem?_eq_getElem hq), hkIn,
      hletσ j q g d.ls[q] hg (List.getElem?_eq_getElem hq)]
  intro j hj k o f ho hfk
  have h1 := congrArg (fun l => l[k]?) (hobsσ j)
  simp only [List.getElem?_map, hfk, Option.map_some] at h1
  cases ht : d.outs[k]? with
  | none => simp [ht] at h1
  | some t =>
    simp only [ht, Option.map_some, Option.some.injEq] at h1
    obtain ⟨hwt, hw, hlo⟩ := outsFit_get houts ho ht
    have hk : k < d.outs.length := (List.getElem?_eq_some_iff.mp ht).1
    have hfield : (f0 :: rest)[k]? = some (toField t.1 t.2) := by
      rw [← hf]
      unfold MachineData.fields
      rw [List.getElem?_append_left (by simpa using hk), List.getElem?_map, ht]
      rfl
    have := hobs j hj o (List.mem_of_getElem? ho) t.2 hwt k hfield (hf ▸ hlo) hw
    rw [hkIn] at this
    rw [this]
    exact h1.symm

theorem machine_trace_lets_of_streamC {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig)
    (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (stream : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∃ σ : Nat → HList (tys d.ss), σ 0 = inits ∧
        (∀ t, σ (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits) t (σ t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits) t (σ t)).v
            (d.vpos j) w) d.nexts) ∧
        (∀ j, (src i bools bits).map (fun f => f j) =
          d.outs.map fun o => enc o.1 (eval
            (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits) j (σ j)).b
              (d.bpos k))
            (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits) j (σ j)).v
              (d.vpos k) w) o.2)) ∧
        ∀ (j q : Nat) (g : Nat → Nat) (l : Σ s : SType, Term s),
          (lsrc i bools bits)[q]? = some g → d.ls[q]? = some l →
          g j = enc l.1 (eval
            (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits) j (σ j)).b
              (d.bpos k))
            (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits) j (σ j)).v
              (d.vpos k) w) l.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefinesLinked mctx mref cctx cref declName d.shape w m design w')
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src ext lsrc :=
  machine_trace_lets_of_streamBC d dom inits src lsrc ok hbody hinit ext (fun _ bools _ => bools)
    stream hr entry closes
end A

section B
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge Tools.ShippingEntrySoundness
open Tools.ShippingMachineLoop Tools.ShippingMachineNest Tools.ShippingMachineSource
open Tools.ShippingMachineFuse
theorem machine_traceL_of_streamC {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig)
    (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (stream : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∃ σ : Nat → HList (tys d.ss), σ 0 = inits ∧
        (∀ t, σ (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ t)).v
            (d.vpos j) w) d.nexts) ∧
        ∀ j, (src i bools bits).map (fun f => f j) =
          d.outs.map fun o => enc o.1 (eval
            (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits j (σ j)).b
              (d.bpos k))
            (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits j (σ j)).v
              (d.vpos k) w) o.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefinesLinked mctx mref cctx cref declName d.shape w m design w')
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src (fun _ _ bits => bits) (fun _ _ _ => []) :=
  Tools.ShippingFGCircuitLinked2.machine_trace_lets_of_streamC d dom inits src (fun _ _ _ => []) ok hbody hinit
    (fun _ _ bits => bits)
    (fun i bools bits => by
      obtain ⟨σ, a, b, c⟩ := stream i bools bits
      exact ⟨σ, a, b, c, fun _ _ _ _ h => by simp at h⟩) hr entry closes

set_option maxHeartbeats 2000000 in
theorem machine_traceL_of_loopC {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) {α : ι → Type} [∀ i, Inhabited (α i)] {ρ : ι → Type}
    (σ : (i : ι) → α i → HList (tys d.ss))
    (inits : HList (tys d.ss))
    (f : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Signal (dom i) (α i))
    (res : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Signal (dom i) (α i) → ρ i)
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (h0 : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i)),
      σ i ((f i bools bits l).val 0) = inits)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i))
      (t : Nat),
      σ i ((f i bools bits l).val (t + 1)) =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (l.val t))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (l.val t))).v
            (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (L : Signal (dom i) (α i))
      (t : Nat),
      (obsR i (res i bools bits L)).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (L.val t))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (L.val t))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (res i bools bits (Signal.loop (f i bools bits))))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefinesLinked mctx mref cctx cref declName d.shape w m design w')
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src (fun _ _ bits => bits) (fun _ _ _ => []) := by
  refine machine_traceL_of_streamC d dom inits src ok hbody hinit ?_ hr entry closes
  intro i bools bits
  obtain ⟨hs0, hss⟩ := loop_stream (f i bools bits) (σ i) inits
    (fun t x => evalTerms
      (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).b (d.bpos j))
      (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).v (d.vpos j) w)
      d.nexts)
    (h0 i bools bits) (writes i bools bits)
  refine ⟨fun t => σ i ((Signal.loop (f i bools bits)).val t), hs0, hss, ?_⟩
  intro j
  rw [hsrc i bools bits]
  exact hres i bools bits _ j
end B

section C
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingMachineShipsW (machineTrace_congr)
theorem machine_ships_wiredC {declName : Name} (d : MachineData)
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
      MachineDefinesLinked mctx mref cctx cref declName d.shape w m design w' →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : ∀ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      MachineDefinesLinked mctx mref cctx cref declName d.shape w raw D w1)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (wof : String → Option Nat),
        simpleBody b = false →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
          (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
        MachineShips declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b
          (checkedOptimize b) wof dom src := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  have hL := soundL hcore (entry raw D w1) closes
  obtain ⟨_, _, _, _, regs, _, rlen, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, _, _, _, _, _, hok⟩ := hclean hnoI houtTy
  refine ⟨raw, hpost, ?_⟩
  intro wof hsB hsv hwag
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost ⊢
  have htrace : MachineTrace declName d r0 dom src :=
    machineTrace_congr hb hw (MachineTraceL.toWith hL)
  -- the core module has a register (a slot)
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
  have hbok : b.body.all seqStmtOk = true := by
    rcases hmerge with h | rfl
    · exact refineCheck_stmtOk_o h
    · exact hr0ok
  exact machine_ships htrace hmerge (checkedOptimize_seqOk hsB hbok)
    (by rw [hi]; exact hrstIn hsl)
    (fun q hq => ⟨⟨q.name, q.ty⟩, by rw [ho, houts]; exact List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩)
    hr0ok hsv hwag
end C

end Tools.ShippingFGCircuitLinked2

#print axioms Tools.ShippingFGCircuitLinked2.machine_traceL_of_loopC
#print axioms Tools.ShippingFGCircuitLinked2.machine_ships_wiredC
