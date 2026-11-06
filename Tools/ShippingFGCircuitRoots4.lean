import Tools.ShippingFGCircuitFinal4
import Tools.ShippingMachineLoopCausal
set_option autoImplicit false
-- FG circuit pilot S1g, unit 3: the counterLoop shape (hsrc from states, leaf DesignTransport, Start + hr, linked machine boundary) applied to the other three roots. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `hsrc` and the linked final theorems for shift4Loop, counterEnableLoop, arbiterSignal

`src_eq_of_states` is the generic form of `counterLoop_src_eq`: if a sequence `Sg` of states starts at the reader's initial tuple and satisfies the one-step recurrence of the data's `nexts`, and a list `src` of sources has the data's `outs` evaluated on `Sg` at every cycle, then the generated source semantics IS `src`.
Each root supplies its own `Sg` from the endpoint lemmas `machine_inits` / `machine_writes` / `machine_result` (the same kernel `Eq.refl` facts the endpoint command proves). -/
namespace Tools.ShippingFGCircuitRoots4
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5Sem Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Sparkle.Tests.SignalLoopTest
open Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingUnifiedSource (eval)
open Tools.ShippingFGCircuitSrc (list_ext_of_map_eval)

theorem src_eq_of_states {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (gi : GenIn)
    (hleaf : gi.d.shape.insts = []) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (Sg : Nat → HList (tys gi.d.ss))
    (hS0 : Sg 0 = gi.inits)
    (hSs : ∀ t, Sg (t + 1) = evalTerms
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls bools bits t (Sg t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls bools bits t (Sg t)).v (gi.d.vpos j) w) gi.d.nexts)
    (src : List (Nat → Nat))
    (hres : ∀ t, src.map (fun f => f t) = gi.d.outs.map fun o => enc o.1 (eval
      (fun k => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls bools bits t (Sg t)).b (gi.d.bpos k))
      (fun k w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls bools bits t (Sg t)).v (gi.d.vpos k) w) o.2)) :
    (genSemGen (dom := dom) Q X gi).src i bools bits = src := by
  have hlen : gi.d.shape.insts.length = 0 := by rw [hleaf]; rfl
  have heb : ∀ S, extBOf (dom := dom) Q gi i bools bits S = bools := fun S => by
    show (ExtStage (dom := dom) Q gi i bools bits S gi.d.shape.insts.length).1 = bools
    rw [hlen]; rfl
  have hev : ∀ S, extOf (dom := dom) Q gi i bools bits S = bits := fun S => by
    show (ExtStage (dom := dom) Q gi i bools bits S gi.d.shape.insts.length).2 = bits
    rw [hlen]; rfl
  let eb := extBOf (dom := dom) Q gi
  let ev := extOf (dom := dom) Q gi
  letI : Inhabited (HList (tys gi.d.ss)) := ⟨gi.inits⟩
  let Sl : Signal (dom i) (HList (tys gi.d.ss)) :=
    @stateLoop (dom i) _ _ ⟨gi.inits⟩ gi.inits (refBodyE gi eb ev i bools bits)
  have hW : ∀ (l l' : Signal (dom i) (HList (tys gi.d.ss))) (t : Nat), l.val t = l'.val t →
      valsAt (tys gi.d.ss)
        (refBodyE gi eb ev i bools bits (mkRegList l (tys gi.d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys gi.d.ss) l)).snd t =
      valsAt (tys gi.d.ss)
        (refBodyE gi eb ev i bools bits (mkRegList l' (tys gi.d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys gi.d.ss) l')).snd t := by
    intro l l' t h
    rw [genSemGenE_writes X gi eb ev i bools bits l t, genSemGenE_writes X gi eb ev i bools bits l' t]
    simp only [eb, ev, heb, hev, h]
  obtain ⟨hS0', hSs'⟩ := loop_state (dom := dom i) (tys gi.d.ss) gi.inits
    (fun live => (refBodyE gi eb ev i bools bits (mkRegList live (tys gi.d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys gi.d.ss) live)).snd) hW
  have key : ∀ t, Sl.val t = Sg t := by
    intro t
    induction t with
    | zero => exact hS0'.trans hS0.symm
    | succ t ih =>
      have e1 : Sl.val (t + 1) = valsAt (tys gi.d.ss)
          (refBodyE gi eb ev i bools bits (mkRegList Sl (tys gi.d.ss) (fun s => s) (fun f => f))
            (mkHolds (tys gi.d.ss) Sl)).snd t := hSs' t
      rw [e1, genSemGenE_writes X gi eb ev i bools bits Sl t, hSs t, ih]
      simp only [eb, ev, heb, hev]
  apply list_ext_of_map_eval
  intro t
  show (refBodyE gi eb ev i bools bits (mkRegList Sl (tys gi.d.ss) (fun s => s) (fun f => f))
      (mkHolds (tys gi.d.ss) Sl)).fst.map (fun f => f t) = _
  rw [genSemGenE_result X gi eb ev i bools bits Sl t, hres t, key t]
  simp only [eb, ev, heb, hev]

/-- the states of a `Signal.loop` whose body satisfies the endpoint's reset and writes facts for EVERY live signal: `σ ∘ (loop f).val` starts at `inits` and follows the one-step recurrence `F`
(the causal truncation `truncLoop` is the live signal at cycle `c`) -/
theorem loop_states {D : DomainConfig} {α : Type} [Inhabited α] {S : Type} (σ : α → S) (inits : S) (F : Nat → S → S)
    (f : Signal D α → Signal D α) (h0 : ∀ l, σ ((f l).val 0) = inits)
    (hw : ∀ l t, σ ((f l).val (t + 1)) = F t (σ (l.val t))) :
    σ ((Signal.loop f).val 0) = inits ∧ ∀ t, σ ((Signal.loop f).val (t + 1)) = F t (σ ((Signal.loop f).val t)) := by
  refine ⟨?_, fun t => ?_⟩
  · show σ (Signal.loopGo f 0) = inits
    rw [Signal.loopGo_eq]
    exact h0 _
  · rw [Tools.ShippingMachineLoopCausal.loop_val_succ f t, hw (Tools.ShippingMachineLoopCausal.truncLoop f t) t,
      Tools.ShippingMachineLoopCausal.truncLoop_val f t (Nat.le_refl t)]

/-- the `hst` of a root from its generated endpoint facts when the root is a `Signal.loop` -/
theorem hst_of_loop {ι : Type} {dom : ι → DomainConfig} (d : Tools.ShippingMachineAuto.MachineData) {α : ι → Type} [∀ i, Inhabited (α i)]
    (σ : (i : ι) → α i → HList (tys d.ss)) (inits : HList (tys d.ss))
    (f : (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) → Signal (dom i) (α i) → Signal (dom i) (α i))
    {ρ : ι → Type} (res : (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) → Signal (dom i) (α i) → ρ i)
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (h0 : ∀ i bools bits l, σ i ((f i bools bits l).val 0) = inits)
    (hw : ∀ i bools bits l t, σ i ((f i bools bits l).val (t + 1)) = evalTerms
      (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (l.val t))).b (d.bpos j))
      (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (l.val t))).v (d.vpos j) w) d.nexts)
    (hres : ∀ i bools bits L t, (obsR i (res i bools bits L)).map (fun g => g t) = d.outs.map fun o => enc o.1 (eval
      (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (L.val t))).b (d.bpos k))
      (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (σ i (L.val t))).v (d.vpos k) w) o.2))
    (hsrc : ∀ i bools bits, src i bools bits = obsR i (res i bools bits (Signal.loop (f i bools bits)))) :
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)),
      ∃ Sg : Nat → HList (tys d.ss), Sg 0 = inits ∧
        (∀ t, Sg (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (Sg t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (Sg t)).v (d.vpos j) w) d.nexts) ∧
        ∀ t, (src i bools bits).map (fun g => g t) = d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (Sg t)).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (Sg t)).v (d.vpos k) w) o.2) := by
  intro i bools bits
  obtain ⟨a, b⟩ := loop_states (σ i) inits
    (fun t S => evalTerms
      (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t S).b (d.bpos j))
      (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t S).v (d.vpos j) w) d.nexts)
    (f i bools bits) (h0 i bools bits) (hw i bools bits)
  exact ⟨fun t => σ i ((Signal.loop (f i bools bits)).val t), a, b, fun t => by rw [hsrc, hres]⟩

section Generic
open Tools.ShippingGen5Acc Tools.ShippingGen5DataOf Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1 Sparkle.Compiler.Elab
open Tools.ShippingMachineAuto (MachineData)

/-- **`hsrc` of a leaf root from its states**: the package `genGP` returns observes `obs`, given the states data `hst` of the endpoint (`machine_reset` / `machine_writes` / `machine_result`). -/
theorem hsrc_of_states {ι : Type} {dom : ι → DomainConfig} (lvl : Lean.Expr → Nat) (env : Environment) {X : Name} {d : MachineData}
    (hRead : Tools.ShippingFGCircuitCover.RootReader lvl env X d) (hwf : GenWF d = true) (hleaf : d.shape.insts = [])
    (hne : (d.ss.isEmpty && d.shape.insts.isEmpty) = false)
    (obs : (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (hst : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)),
      ∃ Sg : Nat → HList (tys d.ss), Sg 0 = Tools.ShippingGen5DataOfPure.initsOf d ∧
        (∀ t, Sg (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (Sg t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (Sg t)).v (d.vpos j) w) d.nexts) ∧
        ∀ t, (obs i bools bits).map (fun g => g t) = d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (Sg t)).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (Sg t)).v (d.vpos k) w) o.2)) :
    ∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) (Tools.ShippingFGCircuitCover.canonGD lvl) env X = some p ∧
      ∀ (i : ι) bools bits, p.src i bools bits = obs i bools bits := by
  obtain ⟨p, gi, hp, hpd, hgd, hgi, Q, hsrc⟩ := Tools.ShippingFGCircuitSrc.genGP_root_canon_src (ι := ι) (dom := dom) lvl env hRead hwf hleaf
  refine ⟨p, hp, fun i bools bits => ?_⟩
  have hns : (gi.d.ss.isEmpty && gi.d.shape.insts.isEmpty) = false := by rw [hgd]; exact hne
  have e : (genSemI Q X gi).src i bools bits = (genSemGen (dom := dom) Q X gi).src i bools bits := by
    unfold genSemI; rw [hns]; rfl
  rw [hsrc, e]
  subst hgd
  obtain ⟨Sg, hS0, hSs, hr⟩ := hst i bools bits
  exact src_eq_of_states Q X gi hleaf i bools bits Sg (hS0.trans hgi.symm) hSs _ hr

end Generic

section Hsrc
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1
open Tools.ShippingFGCircuit (monoObs)
open Tools.ShippingFGCircuitRoots (shShift4 shEnable shArbiter)
open Tools.ShippingFGCircuitApply

theorem shift4Loop_hsrc {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment)
    (hRead : Tools.ShippingFGCircuitCover.RootReader lvl env ``shift4Loop shift4Loop.machineData) :
    ∃ p : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (dataOfSound_initsOf lvl) (Tools.ShippingFGCircuitCover.canonGD lvl) env ``shift4Loop = some p ∧
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs shShift4 shift4Loop bools bits :=
  hsrc_of_states (ι := ι) (dom := fun _ => defaultDomain) lvl env hRead shift4Loop_wf shift4Loop_leafFacts.2.2.2.2.1 (by decide)
    (fun _ bools bits => monoObs shShift4 shift4Loop bools bits)
    (fun _ bools bits => ⟨shift4Loop.machineSigma () bools bits, shift4Loop.machine_reset () bools bits,
      shift4Loop.machine_writes () bools bits, shift4Loop.machine_result () bools bits⟩)

theorem counterEnableLoop_hsrc {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment)
    (hRead : Tools.ShippingFGCircuitCover.RootReader lvl env ``counterEnableLoop counterEnableLoop.machineData) :
    ∃ p : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (dataOfSound_initsOf lvl) (Tools.ShippingFGCircuitCover.canonGD lvl) env ``counterEnableLoop = some p ∧
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs shEnable counterEnableLoop bools bits :=
  hsrc_of_states (ι := ι) (dom := fun _ => defaultDomain) lvl env hRead counterEnableLoop_wf counterEnableLoop_leafFacts.2.2.2.2.1 (by decide)
    (fun _ bools bits => monoObs shEnable counterEnableLoop bools bits)
    (fun _ bools bits => hst_of_loop (ι := Unit) (dom := fun _ => defaultDomain) counterEnableLoop.machineData
      (α := fun _ => BitVec 8) counterEnableLoop.machineSigma counterEnableLoop.machineInits counterEnableLoop.machineBody
      counterEnableLoop.machineRes counterEnableLoop.machineResult (fun _ bools bits => monoObs shEnable counterEnableLoop bools bits)
      counterEnableLoop.machine_reset counterEnableLoop.machine_writes counterEnableLoop.machine_result
      counterEnableLoop.machine_source () bools bits)

theorem arbiterSignal_hsrc (lvl : Lean.Expr → Nat) (env : Environment)
    (hRead : Tools.ShippingFGCircuitCover.RootReader lvl env ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData) :
    ∃ p : Pkg DomainConfig (fun i => i),
      genGP (ι := DomainConfig) (dom := fun i => i) lvl (dataOfSound_initsOf lvl) (Tools.ShippingFGCircuitCover.canonGD lvl) env
        ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal = some p ∧
      ∀ (i : DomainConfig) bools bits, p.src i bools bits = shArbiter.obs (dom := fun i : DomainConfig => i)
        (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits :=
  hsrc_of_states (ι := DomainConfig) (dom := fun i => i) lvl env hRead arbiterSignal_wf arbiterSignal_leafFacts.2.2.2.2.1 (by decide)
    (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits)
    (fun i bools bits => hst_of_loop (ι := DomainConfig) (dom := fun i => i) Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData
      (α := fun _ => BitVec 2) Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineSigma Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineInits
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineBody
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineRes Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineResult
      (fun i bools bits => shArbiter.obs (dom := fun i : DomainConfig => i) (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) i bools bits)
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_reset Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_writes
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_result
      Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_source i bools bits)

end Hsrc

end Tools.ShippingFGCircuitRoots4

#print axioms Tools.ShippingFGCircuitRoots4.src_eq_of_states
#print axioms Tools.ShippingFGCircuitRoots4.loop_states
#print axioms Tools.ShippingFGCircuitRoots4.hst_of_loop
#print axioms Tools.ShippingFGCircuitRoots4.hsrc_of_states
#print axioms Tools.ShippingFGCircuitRoots4.shift4Loop_hsrc
#print axioms Tools.ShippingFGCircuitRoots4.counterEnableLoop_hsrc
#print axioms Tools.ShippingFGCircuitRoots4.arbiterSignal_hsrc
