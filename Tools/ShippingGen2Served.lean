import Tools.ShippingGen2ServedRun
import Tools.ShippingGen2DataBridge
import Tools.ShippingGen2Pkg
set_option autoImplicit false
-- Built: g3sv-b5be62e6 (clean snapshot, exit 0, standard axioms) (written by reading at 96cbd548; scripts/gen2/SERVED_FREEZE.md rev1 §1.3-§1.6). Every proof is a
-- S1 combined: re-elaborated at 02e828fc in s1c-02e828fc (clean, exit 0, standard axioms).
-- substitution copy of a BUILT source, named at each declaration. No `sorry`, no `axiom`, no `native_decide`.

/-! # G-SERVED F2: the served trace at `ServedP (ShipsRes L P)`; producer CONDITIONAL on `hrow`

* `SoundXAt` (frozen rev1 §1.5): the `MachinePreservesX X` callback of the trace chain, for every split of the binders.
* `soundX_ships_ran`: copy of `synthesizeCombinationalCore_machine_soundRA_ranA` (Tools/ShippingServedRealA.lean:116),
  with the run at `InvAt` (`MachineRunInv`, `synthesizeMachineCertified_runsS`) and `X := ServedP (ShipsRes L P) …`.
  Premises beyond the run: `IHAt n`, `ChildKeepsInv n`, `hreach` (from `T1Hyp.closed`), `hord1` (G-ONEOUT-REACH, from
  `hrow` in the producer). The general closing's memory-origin case uses `MemChildren` (part of `CloseCalls`).
* X-generic trace copies (namespace `Tools.ShippingGen2ServedTrace`). In each, the four run premises `O hB hA htr`
  and `ran` are replaced by `hX : SoundXAt X …`; the text is otherwise verbatim:
  - `machine_trace_lets_of_streamBRX` (ServedRealATrace.lean:36);
  - `machine_traceL_of_data_causalX` (ParentSeqComposedA.lean:23);
  - `machine_traceL_of_loop_causalX` (Gen2Loop.lean:37);
  - `genTraceX`, `genTraceLX`, `machine_traceL_of_comb_callsX`, `Pkg.traceX` (cases `gen`/`loop`/`comb` of the
    combined `Pkg`; the `.comb` case was added at the S1 integration, rev1 §1.6).
* `servedShips0_proved (hrow) : ServedShips0Stmt L P Reach DataOk`: CONDITIONAL on the unsupplied row premise `hrow`.
  `t1_of_stepPF_served`: CONDITIONAL on `hrow`, `StepStmt`, `PostFactsStmt`.

NEITHER COMPLETES G-SERVED, T1/M3 OR FG while `hrow` is unsupplied (rev1 §2.3). A census or one concrete package is
not supply of `hrow`. `RealChildA` is history, not freshness or runtime fit. -/

namespace Tools.ShippingGen2

section SoundX
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingMachineTraceX
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge Tools.ShippingMachineAuto
open Tools.ShippingMachineRef Tools.ShippingMachineSource Tools.ShippingUnifiedSource

/-- **The trace chain's callback** (frozen rev1 §1.5): `MachinePreservesX X` for every binder split satisfying the
data conditions of `synthesizeCombinationalCore_machine_soundRA_ranA` (ServedRealA.lean:123-131, verbatim). -/
def SoundXAt (X : List FVarId → IO.Ref (ExprStructMap String) → Prop) (declName : Name)
    (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Design) : Prop :=
  ∀ (bsIn slotBs letBs : List (Name × MixedGateBinder)),
    shape.binders = bsIn ++ slotBs ++ letBs → shape.layout.lets = letBs.length →
    PositiveBinders shape.binders → (∀ b ∈ slotBs, b.2 ≠ .domain) → (∀ b ∈ letBs, b.2 ≠ .domain) →
    Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2) shape.layout.slots slotBs →
    (∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true) →
    (shape.layout.outs.map (·.name)).Nodup →
    MachinePreservesX X declName shape bsIn slotBs letBs m dsn

/-- **(i) The served instances ship** (copy of `synthesizeCombinationalCore_machine_soundRA_ranA`,
ServedRealA.lean:116-190). The children come from `synthesizeMachineCertified_runsS` (`ChildrenShipsI`). An
ordinary served child (`child? = none`) ships through `hreach`. The general closing's memory-origin entries are
origin-built by `MemChildren`. The one-output closing's entries have `child? = none` by `hord1`. -/
theorem soundX_ships_ran {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {n : Nat} {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    (ran : MachineRunInv L P Reach mctx cctx n declName shape m d)
    (hIH : IHAt L P Reach n) (hKI : ChildKeepsInv L P Reach n)
    (hreach : ∀ k (hk : k < shape.insts.length),
      (shape.instOrigins.getD k .ord).child? = none → Reach (shape.insts[k]).1)
    (hord1 : shape.instFields = [] → ∀ k, k < shape.insts.length →
      (shape.instOrigins.getD k .ord).child? = none) :
    SoundXAt (ServedP (ShipsRes L P) declName shape m d) declName shape m d := by
  intro bsIn slotBs letBs hbs hlets positive slotKinds letKinds layW outsOk outsNodup
  obtain ⟨tenv, prof, w9, w10, hrun, hw9⟩ := ran
  obtain ⟨t, t', d₀, hmix, hcl, hmt⟩ :=
    synthesizeMachineCertified_runsS L P Reach hA hIH hKI hw9 hrun
  have hmt0 : (shape.insts = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
      (shape.insts ≠ [] ∧ ∃ children,
        CloseCalls shape t (closeMachine shape.layout t') d₀ children m d) := by
    rcases hmt with h0 | ⟨hi, children, hcc, _⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hi, children, hcc⟩
  refine synthesizeMachineCertified_soundX _ hmix hcl hmt0 ?_ hbs hlets positive slotKinds
    letKinds layW outsOk outsNodup
  intro ids cache regs lets wired hmp notInst
  have h0 : ∀ st ∈ (closeMachine shape.layout t').body, isInst st = false := fun st hs => by
    cases hi : isInst st
    · rfl
    · exact absurd (notInst st hs hi) id
  refine ⟨?g, ?o⟩
  case o =>
    intro hfe1 k hk args mc st hargs hst hcs hmod
    rcases hmt with ⟨h0', _, _⟩ | ⟨_, children, hcc, hreal⟩
    · rw [h0'] at hk; exact absurd hk (Nat.not_lt_zero _)
    rcases hcc with ⟨_, hC⟩ | ⟨hfe0, _, _⟩
    case inr => exact absurd hfe1 hfe0
    rw [hmp] at hcs
    obtain ⟨y, hy, hmcy⟩ := Tools.ShippingChildServe.closeInsts_serves hC h0 hst hcs hmod
    have hyc := (Tools.ShippingChildServe.closeInsts_acyclic hC).2.2.2 y (List.mem_of_getElem? hy)
    obtain ⟨_, hkr⟩ := hreal
    obtain ⟨y', hy', hor⟩ := hkr k hk
    rw [hy] at hy'; cases hy'
    subst hmcy
    rcases hor with hmem | ⟨_, hS⟩
    · exact Or.inl ⟨y, hmem, rfl⟩
    · exact Or.inr ⟨y.2, hS (hreach k hk (hord1 hfe1 k hk)), hyc⟩
  case g =>
  intro hfe k hk mc iname argWs outs outWs hst hout hke hmod
  rcases hmt with ⟨h0, _, _⟩ | ⟨_, children, hcc, hreal⟩
  · rw [h0] at hk; exact absurd hk (Nat.not_lt_zero _)
  rcases hcc with ⟨hfe0, _⟩ | ⟨_, hG, hmemc⟩
  · exact absurd hfe0 hfe
  have hall := wired.2.1
  rw [hmp] at hall hout
  have hcr : "clk" ∉ t.inputs.map (·.name) ∧ "rst" ∉ t.inputs.map (·.name) :=
    ⟨fun h => (allocated_ne (hall _ h)).1 rfl, fun h => (allocated_ne (hall _ h)).2 rfl⟩
  obtain ⟨y, hy, hmcy⟩ := Tools.ShippingChildServe.closeInstsG_serves hG
    (fun st hs => by
      cases hi : isInst st
      · rfl
      · exact absurd (notInst st hs hi) id)
    hcr hk hst hout hke hmod
  have hyc := ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y (List.mem_of_getElem? hy)).2
  obtain ⟨_, hkr⟩ := hreal
  obtain ⟨y', hy', hor⟩ := hkr k hk
  rw [hy] at hy'; cases hy'
  subst hmcy
  rcases hor with hmem | ⟨_, hS⟩
  · exact Or.inl ⟨y, hmem, rfl⟩
  · cases hco : (shape.instOrigins.getD k .ord).child? with
    | none => exact Or.inr ⟨y.2, hS (hreach k hk hco), hyc⟩
    | some md =>
      -- a memory-origin entry of the general closing: the child is the origin-built one (`MemChildren`)
      have hy2 := hmemc k hk md hco
      rw [hy] at hy2
      exact Or.inl ⟨md, by first | exact hco | rfl, by rw [Option.some.inj hy2]⟩

end SoundX

end Tools.ShippingGen2

/-! ## The X-generic trace chain (copies; only the run premises are replaced by `hX`) -/

namespace Tools.ShippingGen2ServedTrace

section StreamX
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingMachineTraceX Tools.ShippingServedRealA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP

set_option maxHeartbeats 2000000 in
/-- **(j)** `machine_trace_lets_of_streamBRA_ranA` (ServedRealATrace.lean:36-184), X-generic: `O hB hA htr ran` are
replaced by `hX : SoundXAt X declName d.shape m design`, used ONLY in `hpres` (as `ran` was). -/
theorem machine_trace_lets_of_streamBRX {declName : Name} (d : MachineData) {ι : Type}
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
    {X : List FVarId → IO.Ref (ExprStructMap String) → Prop}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hX : Tools.ShippingGen2.SoundXAt X declName d.shape m design) :
    MachineTraceLBX X declName d m design dom src ext extB lsrc := by
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
  have hpres : MachinePreservesX X
      declName d.shape d.bsIn d.slotBs d.letBs m design :=
    hX d.bsIn d.slotBs d.letBs d.binders_split hlets
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
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, h⟩ :=
    machine_endpointX hpres (K := d.K) (nOuts := d.outs.length) layW hwf hb' hv' hbody hfit
      houtfit (by rw [hkIn, hn]; exact hscoped) hn hnexts (hf ▸ slotsFit_of hslots) facts
      nextsWF
  refine ⟨ids, nd, len, cache, regs, rnd, rlen.trans hn, lets, llen, wired, hx, ?_⟩
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

end StreamX

section DataX
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCausal
open Tools.ShippingMachineTraceX (MachineTraceLBX)
open Tools.ShippingQuadComposed (GenFacts)

set_option maxHeartbeats 2000000 in
/-- **(k)** `machine_traceL_of_data_causalRA_ranA` (ParentSeqComposedA.lean:23-114), X-generic (`hX` for
`O hB hA htr ran`). -/
theorem machine_traceL_of_data_causalX {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) [Inhabited (HList (tys d.ss))] {ρ : ι → Type}
    (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst)
    (hcausal : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S S' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (∀ c, c ≤ t → S.val c = S'.val c) →
      (∀ p w, (ext i bools bits S p w).val t = (ext i bools bits S' p w).val t) ∧
      (∀ p, (extB i bools bits S p).val t = (extB i bools bits S' p).val t))
    {X : List FVarId → IO.Ref (ExprStructMap String) → Prop}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hX : Tools.ShippingGen2.SoundXAt X declName d.shape m design) :
    MachineTraceLBX X declName d m design dom src
      (fun i bools bits => ext i bools bits (stateLoop inits (body i bools bits)))
      (fun i bools bits => extB i bools bits (stateLoop inits (body i bools bits)))
      (letObsB d dom inits body ext extB) := by
  refine machine_trace_lets_of_streamBRX d dom inits src (letObsB d dom inits body ext extB) ok hbody
    hinit _ _ ?_ hX
  intro i bools bits
  have hW : ∀ (l l' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (∀ c, c ≤ t → l.val c = l'.val c) →
      valsAt (tys d.ss) (writesOn (body i bools bits) l) t =
        valsAt (tys d.ss) (writesOn (body i bools bits) l') t := by
    intro l l' t h
    show valsAt (tys d.ss) (body i bools bits (mkRegList l (tys d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys d.ss) l)).snd t =
      valsAt (tys d.ss) (body i bools bits (mkRegList l' (tys d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys d.ss) l')).snd t
    obtain ⟨hv, hb⟩ := hcausal i bools bits l l' t h
    rw [writes i bools bits l t, writes i bools bits l' t, h t (Nat.le_refl t),
      typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l) (extB i bools bits l')
        (ext i bools bits l) (ext i bools bits l') t (l'.val t) hb hv]
  obtain ⟨h0, hs⟩ := circuit_state_causal inits (body i bools bits) hW
  refine ⟨fun t => (stateLoop inits (body i bools bits)).val t, h0, ?_, ?_, ?_⟩
  · intro t
    show (stateLoop inits (body i bools bits)).val (t + 1) = _
    rw [hs t]
    exact writes i bools bits _ t
  · intro j
    rw [hsrc i bools bits]
    exact hres i bools bits (stateLoop inits (body i bools bits)) j
  · intro j q g l hg hl
    simp only [letObsB, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
    rw [← hg]

/-- **(m, gen)** `genTrace` (QuadComposed.lean:156-181), X-generic (`hX` for `O T hA ran`). -/
theorem genTraceX {declName : Name} (d : MachineData) {ι : Type} (dom : ι → DomainConfig) {ρ : ι → Type}
    [Inhabited (HList (tys d.ss))]
    {inits : HList (tys d.ss)}
    {body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i)}
    {obsR : (i : ι) → ρ i → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (GF : GenFacts d dom inits body obsR ext extB src)
    {X : List FVarId → IO.Ref (ExprStructMap String) → Prop}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hX : Tools.ShippingGen2.SoundXAt X declName d.shape m design) :
    MachineTraceLBX X declName d m design dom src
      (fun i bools bits => ext i bools bits (stateLoop inits (body i bools bits)))
      (fun i bools bits => extB i bools bits (stateLoop inits (body i bools bits)))
      (letObsB d dom inits body ext extB) :=
  machine_traceL_of_data_causalX d dom inits body obsR ext extB src GF.ok GF.body_eq GF.init
    GF.writes GF.result GF.source GF.causal hX

end DataX

section LoopX
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingMachineTraceX Tools.ShippingServedRealA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP
open Tools.ShippingMachineCausal
open Tools.ShippingGen2Loop (SrcPkgL)

set_option maxHeartbeats 2000000 in
/-- **(l)** `machine_traceL_of_loop_causalRA_ranA` (Gen2Loop.lean:37-122), X-generic (`hX` for `O hB hA htr ran`). -/
theorem machine_traceL_of_loop_causalX {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) {α : ι → Type} [∀ i, Inhabited (α i)] {ρ : ι → Type}
    (σ : (i : ι) → α i → HList (tys d.ss))
    (inits : HList (tys d.ss))
    (f : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Signal (dom i) (α i))
    (res : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Signal (dom i) (α i) → ρ i)
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Nat → Signal (dom i) Bool)
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
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).v (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (L : Signal (dom i) (α i))
      (t : Nat),
      (obsR i (res i bools bits L)).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).v (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (res i bools bits (Signal.loop (f i bools bits))))
    (hcausal : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (l l' : Signal (dom i) (α i)) (t : Nat), (∀ c, c ≤ t → l.val c = l'.val c) →
      (∀ p w, (ext i bools bits l p w).val t = (ext i bools bits l' p w).val t) ∧
      (∀ p, (extB i bools bits l p).val t = (extB i bools bits l' p).val t))
    {X : List FVarId → IO.Ref (ExprStructMap String) → Prop}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hX : Tools.ShippingGen2.SoundXAt X declName d.shape m design) :
    MachineTraceLBX X declName d m design dom src
      (fun i bools bits => ext i bools bits (Signal.loop (f i bools bits)))
      (fun i bools bits => extB i bools bits (Signal.loop (f i bools bits)))
      (letObsLoop d dom σ f ext extB) := by
  refine machine_trace_lets_of_streamBRX d dom inits src
    (letObsLoop d dom σ f ext extB) ok hbody hinit _ _ ?_ hX
  intro i bools bits
  refine ⟨fun t => σ i ((Signal.loop (f i bools bits)).val t), ?_, ?_, ?_, ?_⟩
  · show σ i (Signal.loopGo (f i bools bits) 0) = inits
    rw [Signal.loopGo_eq]
    exact h0 i bools bits _
  · intro t
    show σ i (Signal.loopGo (f i bools bits) (t + 1)) = _
    rw [Signal.loopGo_eq, writes]
    have hag : ∀ c, c ≤ t →
        (⟨fun s => if s < t + 1 then Signal.loopGo (f i bools bits) s else default⟩ :
          Signal (dom i) (α i)).val c = (Signal.loop (f i bools bits)).val c := by
      intro c hc
      show (if c < t + 1 then _ else _) = Signal.loopGo (f i bools bits) c
      rw [if_pos (by omega)]
    obtain ⟨hv, hb⟩ := hcausal i bools bits _ _ t hag
    rw [hag t (Nat.le_refl t),
      typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls _ _ _ _ t _ hb hv]
  · intro j
    rw [hsrc i bools bits]
    exact hres i bools bits _ j
  · intro j q g l hg hl
    simp only [letObsLoop, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
    rw [← hg]

/-- **(m, loop)** `genTraceL` (Gen2Loop.lean:212-219), X-generic (`hX` for `O T hA ran`). -/
theorem genTraceLX {ι : Type} {dom : ι → DomainConfig} (p : SrcPkgL ι dom)
    {X : List FVarId → IO.Ref (ExprStructMap String) → Prop}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hX : Tools.ShippingGen2.SoundXAt X p.decl p.d.shape m design) :
    MachineTraceLBX X p.decl p.d m design dom p.src p.extS p.extBS p.lsrc := by
  letI := p.inh
  exact @machine_traceL_of_loop_causalX p.decl p.d ι dom p.α p.inh p.ρ p.σ p.inits p.f p.res p.obsR
    p.ext p.extB p.src p.facts.ok p.facts.hbody p.facts.hinit p.facts.h0 p.facts.writes p.facts.hres p.facts.hsrc
    p.facts.hcausal X m design hX

end LoopX

section CombX
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingMachineTraceX Tools.ShippingServedRealA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP
open Tools.ShippingMachineCausal

/-- **(m, comb)** `machine_traceL_of_comb_callsRA_ranA` (CombPkg.lean:63-83), X-generic (rev1 §1.6 (i)): `O hB hA htr
ran` replaced by `hX`, and `machine_trace_lets_of_streamBRA_ranA` by `machine_trace_lets_of_streamBRX … hX`. The stream
witness is verbatim. -/
theorem machine_traceL_of_comb_callsX {declName : Name} (d : MachineData) {ι : Type} (dom : ι → DomainConfig)
    (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (hF : Tools.ShippingGen2.CombFacts d dom inits src)
    {X : List FVarId → IO.Ref (ExprStructMap String) → Prop}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hX : Tools.ShippingGen2.SoundXAt X declName d.shape m design) :
    MachineTraceLBX X declName d m design dom src
      (fun _ _ bits => bits) (fun _ bools _ => bools)
      (Tools.ShippingMachineCausal.letObsComb d dom inits (fun _ _ bits => bits) (fun _ bools _ => bools)) := by
  refine machine_trace_lets_of_streamBRX d dom inits src
    (Tools.ShippingMachineCausal.letObsComb d dom inits (fun _ _ bits => bits) (fun _ bools _ => bools)) hF.ok hF.hbody
    hF.hinit (fun _ _ bits => bits) (fun _ bools _ => bools) ?_ hX
  intro i bools bits
  refine ⟨fun _ => inits, rfl, fun t => hF.hnext i bools bits t, hF.hres i bools bits, ?_⟩
  intro j q g l hg hl
  simp only [Tools.ShippingMachineCausal.letObsComb, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
  rw [← hg]

end CombX

end Tools.ShippingGen2ServedTrace

/-! ## The package wrapper, the producer and the T1 corollary -/

namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Core.Domain
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildRunAKids (MachineClosesAtA)

/-- **`Pkg.traceX`** (rev1 §1.5): `Pkg.trace` (Gen2Pkg.lean:103) X-generic, by cases on the combined `Pkg`
(`gen`/`loop`/`comb`; the `.comb` case added at the S1 integration, rev1 §1.6). -/
theorem Pkg.traceX {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom)
    {X : List FVarId → IO.Ref (ExprStructMap String) → Prop} {m : Sparkle.IR.AST.Module} {design : Design}
    (hX : SoundXAt X p.decl p.d.shape m design) :
    Tools.ShippingMachineTraceX.MachineTraceLBX X p.decl p.d m design dom p.src p.extS p.extBS p.lsrc := by
  cases p with
  | gen p =>
    letI := p.inh
    exact Tools.ShippingGen2ServedTrace.genTraceX (declName := p.decl) p.d dom p.gen hX
  | loop p => exact Tools.ShippingGen2ServedTrace.genTraceLX p hX
  | comb p =>
    exact Tools.ShippingGen2ServedTrace.machine_traceL_of_comb_callsX (declName := p.decl) p.d dom p.inits
      p.src p.facts hX

/-- **G-SERVED + G-START producer — CONDITIONAL on `hrow`** (rev1 §1.4, §2.3). `hrow` is the unsupplied
G-ONEOUT-REACH row premise (D1, R-ROW). It is not part of `DataOk`/`T1Hyp` (that strengthening is not approved).
This is an INTERMEDIATE: it does NOT complete G-SERVED, T1 or FG. -/
theorem servedShips0_proved {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true) :
    ServedShips0Stmt L P Reach DataOk := by
  intro hT p mctx cctx w w' raw D hR hP hA hjqc hc hIH hKI hr
  obtain ⟨q, hPq, -, hDq⟩ := hT.pkg p.decl hR
  have hpq : p = q := Option.some.inj (hP.symm.trans hPq)
  have hDp : DataOk p := by rw [hpq]; exact hDq
  have hdef : MachineDefines mctx mref cctx cref p.decl p.d.shape :=
    hT.defines p.decl hR p hP mctx cctx hA
  have hcl : MachineClosesAtA L.O mctx cctx p.decl p.d.shape :=
    hT.closes p.decl hR p hP mctx cctx hA
  have ran : MachineRunInv L P Reach mctx cctx (dv w + 1) p.decl p.d.shape raw D :=
    machineRunInv_of_closes0 L P Reach hA hr hdef hcl hjqc hc
  have hX : SoundXAt (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d.shape raw D :=
    soundX_ships_ran L P Reach hA ran hIH hKI
      (fun k hk hn => hT.closed p.decl hR p hP k hk hn)
      (fun hf k hk => Tools.ShippingGen2DataBridge.hord_of_row (hrow p hDp) hf k hk)
  exact Pkg.traceX p hX

/-- **T1 from the one-level rule — CONDITIONAL** on `hrow`, `StepStmt`, `PostFactsStmt`
(`t1_of_stepPF_kc` with `hSS := servedShips0_proved … hrow` and `hLim := limitStmt_proved`). It has one premise
(`hrow`) beyond the T1 skeleton's. Not M2/M3/FG completion. -/
theorem t1_of_stepPF_served {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hStep : StepStmt L P DataOk) (hPF : PostFactsStmt L P Reach DataOk) :
    T1Stmt L P Reach DataOk :=
  t1_of_stepPF_kc L P Reach DataOk hStep (servedShips0_proved L P Reach DataOk hrow) hPF
    (limitStmt_proved L)

end Tools.ShippingGen2

#print axioms Tools.ShippingGen2.soundX_ships_ran
#print axioms Tools.ShippingGen2ServedTrace.machine_trace_lets_of_streamBRX
#print axioms Tools.ShippingGen2ServedTrace.machine_traceL_of_data_causalX
#print axioms Tools.ShippingGen2ServedTrace.genTraceX
#print axioms Tools.ShippingGen2ServedTrace.machine_traceL_of_loop_causalX
#print axioms Tools.ShippingGen2ServedTrace.genTraceLX
#print axioms Tools.ShippingGen2ServedTrace.machine_traceL_of_comb_callsX
#print axioms Tools.ShippingGen2.Pkg.traceX
#print axioms Tools.ShippingGen2.servedShips0_proved
#print axioms Tools.ShippingGen2.t1_of_stepPF_served
