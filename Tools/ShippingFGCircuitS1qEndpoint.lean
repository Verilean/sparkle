import Tools.ShippingFGCircuitS1qLinked
import Tools.ShippingFGCircuitS1iRoots
set_option autoImplicit false
-- FG circuit pilot S1q, unit 2: the endpoint chain (stream / loop / wired endpoint, leaf shipping, artifact, final4D) on the profile-free entry.  No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1q-2: the endpoint chain on `synthesizeCombinationalOff`

Copies of the existing proofs (`Tools/ShippingFGCircuitLinked2.lean`, `Final4.lean`, `Roots4.lean`, `S1iRoots.lean`) under the renaming `synthesizeCombinationalCore declName [] false → synthesizeCombinationalCoreOff declName`,
`synthesizeCombinational → synthesizeCombinationalOff`, `MachineDefinesLinked → MachineDefinesLinkedOff`, `PostRun → PostRunOff`, `X…C → X…COff` (generated mechanically; the proof bodies are not edited).
Nothing in the existing files is changed. The head of the chain is `coreHeadOff` (`Tools/ShippingFGCircuitS1qLinked.lean`): no `IO.getEnv`, no log. -/
namespace Tools.ShippingFGCircuitS1qEndpoint
open Lean
open Tools.ShippingFGCircuitS1qLinked
open Tools.ShippingEntrySoundness (RunsTo)

/-- the post-processing relation of `synthesizeCombinationalOff` tied to the run (`PostRun` for the profile-free entry) -/
def PostRunOff (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (X : Name) (D' : Sparkle.IR.AST.Design) (b raw : Sparkle.IR.AST.Module) : Prop :=
  ∃ (D₀ : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff X) mctx mref cctx cref w (raw, D₀) w1 ∧
      Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D'

/-- `synthesizeCombinationalOff` splits as the profile-free core run and `PostEntry` -/
theorem postEntryOff {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff declName) mctx mref cctx cref w (b, D') w') :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (raw, D) w1 ∧
      Tools.ShippingGen5DCEntryD.PostEntry b raw D D' := by
  unfold Sparkle.Compiler.Elab.synthesizeCombinationalOff at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  rcases Tools.ShippingEntrySoundness.RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inl ⟨this.1, this.2⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inr ⟨this.1, this.2⟩

/-- `synthesizeCombinationalOff`, keeping the CHECKED merge (`synthesizeCombinational_checked` for the profile-free entry) -/
theorem synthesizeCombinationalOff_checked {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (M, D) w1 ∧
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        M' = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) := by
  unfold Sparkle.Compiler.Elab.synthesizeCombinationalOff at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  rcases Tools.ShippingEntrySoundness.RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inl this.1
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inr this.1

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
theorem machine_trace_lets_of_streamBCOff {declName : Name} (d : MachineData) {ι : Type}
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
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName d.shape w m design w')
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
    synthesizeCombinationalCore_machine_soundCOff hr entry closes d.binders_split hlets
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

theorem machine_trace_lets_of_streamCOff {declName : Name} (d : MachineData) {ι : Type}
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
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName d.shape w m design w')
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src ext lsrc :=
  machine_trace_lets_of_streamBCOff d dom inits src lsrc ok hbody hinit ext (fun _ bools _ => bools)
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
theorem machine_traceL_of_streamCOff {declName : Name} (d : MachineData) {ι : Type}
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
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName d.shape w m design w')
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src (fun _ _ bits => bits) (fun _ _ _ => []) :=
  Tools.ShippingFGCircuitS1qEndpoint.machine_trace_lets_of_streamCOff d dom inits src (fun _ _ _ => []) ok hbody hinit
    (fun _ _ bits => bits)
    (fun i bools bits => by
      obtain ⟨σ, a, b, c⟩ := stream i bools bits
      exact ⟨σ, a, b, c, fun _ _ _ _ h => by simp at h⟩) hr entry closes

set_option maxHeartbeats 2000000 in
theorem machine_traceL_of_loopCOff {declName : Name} (d : MachineData) {ι : Type}
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
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName d.shape w m design w')
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src (fun _ _ bits => bits) (fun _ _ _ => []) := by
  refine machine_traceL_of_streamCOff d dom inits src ok hbody hinit ?_ hr entry closes
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
theorem machine_ships_wiredCOff {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w
        (m, design) w' →
      MachineDefinesLinkedOff mctx mref cctx cref declName d.shape w m design w' →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalOff declName) mctx mref cctx cref w (b, design) w')
    (entry : ∀ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      MachineDefinesLinkedOff mctx mref cctx cref declName d.shape w raw D w1)
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
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinationalOff_checked hr
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
section Regs
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST
open Tools.ShippingFGCircuitLinked
open Tools.ShippingMachineLoopL
/-- `machine_traceL_of_regs` on the linked boundary (through `machine_traceL_of_streamCOff`) -/
theorem machine_traceL_of_regsCOff {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) (inits : HList (tys d.ss))
    (σ : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (h0 : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)), σ i bools bits 0 = inits)
    (hstep : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      σ i bools bits (t + 1) = evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i bools bits t)).b
          (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i bools bits t)).v
          (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      (src i bools bits).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i bools bits t)).b
            (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i bools bits t)).v
            (d.vpos k) w) o.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName d.shape w m design w')
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src (fun _ _ bits => bits) (fun _ _ _ => []) :=
  Tools.ShippingFGCircuitS1qEndpoint.machine_traceL_of_streamCOff d dom inits src ok hbody hinit
    (fun i bools bits => ⟨σ i bools bits, h0 i bools bits, hstep i bools bits, hres i bools bits⟩)
    hr entry closes

end Regs
section Finals
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitFinal4
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitRoots4
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Sem (kDOf)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingHierStateG (instFree)
open Sparkle.IR.OptCheck
open Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingFGCircuitLinked2

/-- `leaf_topShips_of_run` from the run-local boundary (same proof, `machineRunJQC_of_closesCOff`) -/
theorem leaf_topShips_of_runCOff {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D₀ : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hkp : p.kD = kDOf d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCoreOff p.decl) mctx mref cctx cref w (raw, D₀) w1)
    (hd : MachineDefinesLinkedOff mctx mref cctx cref p.decl p.d.shape w raw D₀ w1)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape)
    (hpost : Tools.ShippingGen5DCEntry.PostT1 b raw) (n : Nat) : TopShips p n p.decl b raw D₀ := by
  obtain ⟨hok, hco, hSS, houtTy, hnoI, hsl⟩ := hleaf
  subst hdp
  have hran := machineRunJQC_of_closesCOff L.O hstart.1 hr hd
    (machineClosesAtA_of_closes L.O hcl) hstart.2.1 (Or.inl rfl)
  have hL := (Pkg.trace L.O L.T hstart.1 p hran).toLB
  have htake := leaf_take p.d p.kD hok (by rw [hkp]; exact hco) hnoI
  exact leaf_topShips_of_LB p hL hnoI hsl hok hSS houtTy htake hpost n

/-- `leaf_instFree_of_run` from the run-local boundary -/
theorem leaf_instFree_of_runCOff {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D₀ : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCoreOff p.decl) mctx mref cctx cref w (raw, D₀) w1)
    (hd : MachineDefinesLinkedOff mctx mref cctx cref p.decl p.d.shape w raw D₀ w1)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape)
    (hpost : Tools.ShippingGen5DCEntry.PostT1 b raw) :
    instFree raw.body ∧ instFree b.body ∧ instFree (checkedOptimize b).body := by
  obtain ⟨hok, hco, hSS, houtTy, hnoI, hsl⟩ := hleaf
  subst hdp
  have hran := machineRunJQC_of_closesCOff L.O hstart.1 hr hd
    (machineClosesAtA_of_closes L.O hcl) hstart.2.1 (Or.inl rfl)
  have hL := (Pkg.trace L.O L.T hstart.1 p hran).toLB
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, _, wired, tr⟩ := id hL
  obtain ⟨_, hbok, _⟩ := leaf_b_facts wired rlen hnoI hsl hSS houtTy hpost
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, hevery, _, _, _, _, hokR⟩ := hclean hnoI houtTy
  refine ⟨Tools.ShippingMachineDepthRun.instFree_of_seqOk hokR, Tools.ShippingMachineDepthRun.instFree_of_seqOk hbok,
    Tools.ShippingMachineDepthRun.instFree_of_seqOk (Tools.ShippingChecksDerived.checkedOptimize_seqOk_all hbok)⟩

/-- `hTop` for the printed design of a register leaf from the run-local boundary of the core run(s) from `w` -/
theorem hTop_of_leaf4Off {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : Tools.ShippingMachineAuto.MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hkp : p.kD = kDOf d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hd : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref p.decl p.d.shape w raw D₀ w1)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape) :
    ∀ raw, PostRunOff mctx mref cctx cref w p.decl D' b raw → ∃ n, HasConcretePackage p n p.decl b raw D' := by
  intro raw ⟨D₀, w1, hr, hpe⟩
  have hpost := Tools.ShippingGen5DCEntryD.postEntry_postT1 hpe
  obtain ⟨h1, h2, h3⟩ := leaf_instFree_of_runCOff L p hdp hleaf hstart hr (hd raw D₀ w1) hcl hpost
  exact ⟨0, rfl, topShips_design_irrel p 0 p.decl D₀ D' h1 h2 h3
    (leaf_topShips_of_runCOff L p hdp hkp hleaf hstart hr (hd raw D₀ w1) hcl hpost 0)⟩

/-- `counterLoop_artifact_at` with the run-local boundary: the wired endpoint is `machine_ships_wiredCOff` -/
theorem counterLoop_artifact_atCOff {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} {P : Pkgs ι (fun _ => defaultDomain)} {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop}
    {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``counterLoop) mctx mref cctx cref w (b, design) w')
    (hd : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1)
    (hP : P ``counterLoop = some p) (hdecl : p.decl = ``counterLoop)
    (hl : EndpointLink counterLoop.machineData 0 (fun _ bools bits => monoObs shCounter counterLoop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``counterLoop b raw design) :
    ∃ mm : MonoTy shCounter, RootArtifactMono (envAt cref w) P Post ``counterLoop shCounter mm b design p ∧
      WiredConclusion ``counterLoop counterLoop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shCounter mm bools bits) b :=
  ⟨counterLoop, ⟨hP, counterLoop_denotes hE, observationsEqualMono_of_link counterLoop_shape hl,
      fun raw hraw => (hTop raw hraw).imp fun _ hn => ⟨hdecl, hn⟩⟩,
    Tools.ShippingFGCircuitS1qEndpoint.machine_ships_wiredCOff counterLoop.machineData
      (Tools.ShippingFGCircuitS1qEndpoint.machine_traceL_of_loopCOff counterLoop.machineData (fun i => defaultDomain) counterLoop.machineSigma
        counterLoop.machineInits counterLoop.machineBody counterLoop.machineRes counterLoop.machineResult
        counterLoop.machineSource counterLoop.machine_ok counterLoop.machine_body counterLoop.machine_inits
        counterLoop.machine_reset counterLoop.machine_writes counterLoop.machine_result counterLoop.machine_source)
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      hr hd (counterLoop.machine_closes mctx mref cctx cref)⟩

/-- **`counterLoop_final4DOff`.** Premises: `Laws L`, `hstart : Start L mctx cctx w` (A.P-02), `hr` (the compile succeeded), `hdRun` (the run-local machine boundary),
`hRead : RootReader` and `hE : RootInEnv` (unchanged from S1e). No `hw`, no `ReflectsAll`, no `hA6`. -/
theorem counterLoop_final4DOff {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref ``counterLoop counterLoop.machineData.shape w raw D₀ w1)
    (hRead : RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData)
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := ι) (dom := fun _ => defaultDomain) lvl (envAt cref w) hRead
    counterLoop_wf (by have := counterLoop_leafFacts.2.2.2.2.1; exact this)
  obtain ⟨p', hP', hsrc'⟩ := counterLoop_hsrc (ι := ι) lvl (envAt cref w) hRead
  have hpp : p' = p := Option.some.inj (hP'.symm.trans hP)
  subst hpp
  have hl : EndpointLink counterLoop.machineData 0 (fun _ bools bits => monoObs shCounter counterLoop bools bits) p' :=
    ⟨hpd, by rw [hkp]; exact counterLoop_kD, hsrc'⟩
  have hcl : MachineCloses mctx mref cctx cref ``counterLoop counterLoop.machineData.shape := counterLoop.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf4Off (b := b) (D' := D') L p' hpd hkp counterLoop_leafFacts hstart
    (by rw [hdecl, hpd]; exact hdRun) (by rw [hdecl, hpd]; exact hcl)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRunOff mctx mref cctx cref w ``counterLoop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := counterLoop_artifact_atCOff (Post := PostRunOff mctx mref cctx cref w ``counterLoop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hdRun hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p', hart⟩


theorem shift4Loop_artifact_atCOff {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} {P : Pkgs ι (fun _ => defaultDomain)} {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop}
    {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``shift4Loop shift4LoopType shift4LoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``shift4Loop) mctx mref cctx cref w (b, design) w')
    (hd : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape w raw D₀ w1)
    (hP : P ``shift4Loop = some p) (hdecl : p.decl = ``shift4Loop)
    (hl : EndpointLink shift4Loop.machineData 1 (fun _ bools bits => monoObs shShift4 shift4Loop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``shift4Loop b raw design) :
    ∃ mm : MonoTy shShift4, RootArtifactMono (envAt cref w) P Post ``shift4Loop shShift4 mm b design p ∧
      WiredConclusion ``shift4Loop shift4Loop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shShift4 mm bools bits) b :=
  ⟨shift4Loop, ⟨hP, shift4Loop_denotes hE, observationsEqualMono_of_link shift4Loop_shape hl,
      fun raw hraw => (hTop raw hraw).imp fun _ hn => ⟨hdecl, hn⟩⟩,
    Tools.ShippingFGCircuitS1qEndpoint.machine_ships_wiredCOff shift4Loop.machineData
      (machine_traceL_of_regsCOff shift4Loop.machineData (fun i => defaultDomain) shift4Loop.machineInits shift4Loop.machineSigma
        shift4Loop.machineSource shift4Loop.machine_ok shift4Loop.machine_body shift4Loop.machine_inits
        shift4Loop.machine_reset shift4Loop.machine_writes shift4Loop.machine_result)
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      hr hd (shift4Loop.machine_closes mctx mref cctx cref)⟩

theorem counterEnableLoop_artifact_atCOff {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {ι : Type} {P : Pkgs ι (fun _ => defaultDomain)} {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop}
    {p : Pkg ι (fun _ => defaultDomain)}
    (hE : RootInEnv (envAt cref w) ``counterEnableLoop counterEnableLoopType counterEnableLoopValue d)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``counterEnableLoop) mctx mref cctx cref w (b, design) w')
    (hd : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape w raw D₀ w1)
    (hP : P ``counterEnableLoop = some p) (hdecl : p.decl = ``counterEnableLoop)
    (hl : EndpointLink counterEnableLoop.machineData 1 (fun _ bools bits => monoObs shEnable counterEnableLoop bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``counterEnableLoop b raw design) :
    ∃ mm : MonoTy shEnable, RootArtifactMono (envAt cref w) P Post ``counterEnableLoop shEnable mm b design p ∧
      WiredConclusion ``counterEnableLoop counterEnableLoop.machineData (fun _ : Unit => defaultDomain)
        (fun _ bools bits => monoObs shEnable mm bools bits) b :=
  ⟨counterEnableLoop, ⟨hP, counterEnableLoop_denotes hE, observationsEqualMono_of_link counterEnableLoop_shape hl,
      fun raw hraw => (hTop raw hraw).imp fun _ hn => ⟨hdecl, hn⟩⟩,
    Tools.ShippingFGCircuitS1qEndpoint.machine_ships_wiredCOff counterEnableLoop.machineData
      (Tools.ShippingFGCircuitS1qEndpoint.machine_traceL_of_loopCOff counterEnableLoop.machineData (fun i => defaultDomain) counterEnableLoop.machineSigma
        counterEnableLoop.machineInits counterEnableLoop.machineBody counterEnableLoop.machineRes counterEnableLoop.machineResult
        counterEnableLoop.machineSource counterEnableLoop.machine_ok counterEnableLoop.machine_body counterEnableLoop.machine_inits
        counterEnableLoop.machine_reset counterEnableLoop.machine_writes counterEnableLoop.machine_result counterEnableLoop.machine_source)
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      hr hd (counterEnableLoop.machine_closes mctx mref cctx cref)⟩

theorem arbiterSignal_artifact_atCOff {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {d : DefinitionVal} {P : Pkgs DomainConfig (fun i => i)}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {p : Pkg DomainConfig (fun i => i)}
    (hE : RootInEnv (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue d)
    (hB : BoundaryRowsInEnv (envAt cref w))
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w
      (b, design) w')
    (hd : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape w raw D₀ w1)
    (hP : P ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal = some p) (hdecl : p.decl = ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal)
    (hl : EndpointLink Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData (shArbiter.args.length + 1)
      (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i)
        (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits) p)
    (hTop : ∀ raw, Post b raw → ∃ n, TopShips p n ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal b raw design) :
    ∃ mm : shArbiter.Ty, RootArtifact (envAt cref w) P Post ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b design p ∧
      WiredConclusion ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData
        (fun i : DomainConfig => i) (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) mm i bools bits) b :=
  ⟨_, ⟨hP, arbiterSignal_denotes hE, observationsEqual_of_link arbiterSignal_shape hl,
      fun raw hraw => (hTop raw hraw).imp fun _ hn => ⟨hdecl, hn⟩⟩,
    Tools.ShippingFGCircuitS1qEndpoint.machine_ships_wiredCOff Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData
      (Tools.ShippingFGCircuitS1qEndpoint.machine_traceL_of_loopCOff Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData (fun i => i) Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineSigma
        Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineInits Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineBody Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineRes Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineResult
        Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineSource Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_ok Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_body Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_inits
        Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_reset Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_writes Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_result Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_source)
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      (of_decide_eq_true (Eq.refl true)) (of_decide_eq_true (Eq.refl true))
      hr hd (Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_closes mctx mref cctx cref)⟩


theorem shift4Loop_final4DOff {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``shift4Loop) mctx mref cctx cref w (b, D') w')
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape w raw D₀ w1)
    (hRead : RootReader lvl (envAt cref w) ``shift4Loop shift4Loop.machineData)
    (hE : RootInEnv (envAt cref w) ``shift4Loop shift4LoopType shift4LoopValue d) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``shift4Loop D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``shift4Loop D') ``shift4Loop shShift4 mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := ι) (dom := fun _ => defaultDomain) lvl (envAt cref w) hRead
    shift4Loop_wf (by have := shift4Loop_leafFacts.2.2.2.2.1; exact this)
  obtain ⟨p', hP', hsrc'⟩ := shift4Loop_hsrc (ι := ι) lvl (envAt cref w) hRead
  have hpp : p' = p := Option.some.inj (hP'.symm.trans hP)
  subst hpp
  have hl : EndpointLink shift4Loop.machineData 1 (fun _ bools bits => monoObs shShift4 shift4Loop bools bits) p' :=
    ⟨hpd, by rw [hkp]; exact shift4Loop_kD, hsrc'⟩
  have hcl : MachineCloses mctx mref cctx cref ``shift4Loop shift4Loop.machineData.shape := shift4Loop.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf4Off (b := b) (D' := D') L p' hpd hkp shift4Loop_leafFacts hstart
    (by rw [hdecl, hpd]; exact hdRun) (by rw [hdecl, hpd]; exact hcl)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRunOff mctx mref cctx cref w ``shift4Loop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := shift4Loop_artifact_atCOff (Post := PostRunOff mctx mref cctx cref w ``shift4Loop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hdRun hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p', hart⟩

theorem counterEnableLoop_final4DOff {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``counterEnableLoop) mctx mref cctx cref w (b, D') w')
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape w raw D₀ w1)
    (hRead : RootReader lvl (envAt cref w) ``counterEnableLoop counterEnableLoop.machineData)
    (hE : RootInEnv (envAt cref w) ``counterEnableLoop counterEnableLoopType counterEnableLoopValue d) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``counterEnableLoop D' b raw) ∧
    ∃ (mm : MonoTy shEnable) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``counterEnableLoop D') ``counterEnableLoop shEnable mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := ι) (dom := fun _ => defaultDomain) lvl (envAt cref w) hRead
    counterEnableLoop_wf (by have := counterEnableLoop_leafFacts.2.2.2.2.1; exact this)
  obtain ⟨p', hP', hsrc'⟩ := counterEnableLoop_hsrc (ι := ι) lvl (envAt cref w) hRead
  have hpp : p' = p := Option.some.inj (hP'.symm.trans hP)
  subst hpp
  have hl : EndpointLink counterEnableLoop.machineData 1 (fun _ bools bits => monoObs shEnable counterEnableLoop bools bits) p' :=
    ⟨hpd, by rw [hkp]; exact counterEnableLoop_kD, hsrc'⟩
  have hcl : MachineCloses mctx mref cctx cref ``counterEnableLoop counterEnableLoop.machineData.shape := counterEnableLoop.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf4Off (b := b) (D' := D') L p' hpd hkp counterEnableLoop_leafFacts hstart
    (by rw [hdecl, hpd]; exact hdRun) (by rw [hdecl, hpd]; exact hcl)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRunOff mctx mref cctx cref w ``counterEnableLoop D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := counterEnableLoop_artifact_atCOff (Post := PostRunOff mctx mref cctx cref w ``counterEnableLoop D') (P := genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hr hdRun hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p', hart⟩

theorem arbiterSignal_final4DOff {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalOff ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w (b, D') w')
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape w raw D₀ w1)
    (hRead : RootReader lvl (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData)
    (hE : RootInEnv (envAt cref w) ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue d)
    (hB : BoundaryRowsInEnv (envAt cref w)) :
    (∃ raw, PostRunOff mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (envAt cref w)
        (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRunOff mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b D' p := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_canon (ι := DomainConfig) (dom := fun i => i) lvl (envAt cref w) hRead
    arbiterSignal_wf (by have := arbiterSignal_leafFacts.2.2.2.2.1; exact this)
  obtain ⟨p', hP', hsrc'⟩ := arbiterSignal_hsrc lvl (envAt cref w) hRead
  have hpp : p' = p := Option.some.inj (hP'.symm.trans hP)
  subst hpp
  have hl : EndpointLink Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData (shArbiter.args.length + 1)
      (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits) p' :=
    ⟨hpd, by rw [hkp]; exact arbiterSignal_kD, hsrc'⟩
  have hcl : MachineCloses mctx mref cctx cref ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape :=
    Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_closes mctx mref cctx cref
  have hTop := hTop_of_leaf4Off (b := b) (D' := D') L p' hpd hkp arbiterSignal_leafFacts hstart
    (by rw [hdecl, hpd]; exact hdRun) (by rw [hdecl, hpd]; exact hcl)
  rw [hdecl] at hTop
  have hpost : ∃ raw, PostRunOff mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D' b raw := by
    obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
    exact ⟨raw, D₀, w1, hc, hpe⟩
  obtain ⟨mm, hart, -⟩ := arbiterSignal_artifact_atCOff (Post := PostRunOff mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D')
    (P := genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
    hE hB hr hdRun hP hdecl hl (fun raw hraw => (hTop raw hraw).imp fun _ hn => hn.2)
  exact ⟨hpost, mm, p', hart⟩


end Finals

end Tools.ShippingFGCircuitS1qEndpoint
#print axioms Tools.ShippingFGCircuitS1qEndpoint.machine_trace_lets_of_streamBCOff
#print axioms Tools.ShippingFGCircuitS1qEndpoint.machine_traceL_of_loopCOff
#print axioms Tools.ShippingFGCircuitS1qEndpoint.machine_ships_wiredCOff
#print axioms Tools.ShippingFGCircuitS1qEndpoint.hTop_of_leaf4Off
#print axioms Tools.ShippingFGCircuitS1qEndpoint.counterLoop_artifact_atCOff
#print axioms Tools.ShippingFGCircuitS1qEndpoint.counterLoop_final4DOff
#print axioms Tools.ShippingFGCircuitS1qEndpoint.shift4Loop_final4DOff
#print axioms Tools.ShippingFGCircuitS1qEndpoint.counterEnableLoop_final4DOff
#print axioms Tools.ShippingFGCircuitS1qEndpoint.arbiterSignal_final4DOff
