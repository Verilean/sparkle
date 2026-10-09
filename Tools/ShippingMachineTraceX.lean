import Tools.ShippingMachineAuto
import Tools.ShippingChildSynth
import Tools.ShippingChildServe

/-! # The machine endpoint with the run's children

The machine endpoint (`MachineTraceLB`) states the wiring (`MachineWired`) for
the binder ids and wire cache of the run, existentially. The call-to-instance
correspondence a hierarchical theorem needs is a fact about THOSE ids: the
instance whose output wires are call `k`'s ports. This file carries a fact `X`
of the ids and cache through the endpoint's layers (`machine_traceX`,
`machine_ref_traceX`, `machine_endpointX`: the proofs of `machine_trace`,
`machine_ref_trace`, `machine_endpoint` with `X` passed along), and instantiates
it, from the parent's run and the `ChildSynthIs` boundary, by `ServedReal`:
on the general closing, the module of the instance serving call `k` is the
built memory module or a result of the real entry on the call's declaration
(`synthesizeCombinationalCore_machine_soundR`, `machine_trace_lets_of_streamBR`).
-/
namespace Tools.ShippingMachineTraceX
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST

/-- **The trace of a compiled state machine.** Let `bools τ`, `bits τ` be a
valuation of the binders over time — inputs, slots and `let`s alike — whose
slot values start in the registers' state and follow the transition, and
whose `let` values are the values of their fields. Then a `T`-cycle run of
the emitted module, seeded each cycle with the inputs of that cycle over the
register state and with reset low, succeeds, and cycle `j` drives `out` with
the result field of the transition at time `j`. -/
theorem machine_traceX {X : List FVarId → IO.Ref (ExprStructMap String) → Prop} {declName shape m dsn} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (h : MachinePreservesX X declName shape bsIn slotBs letBs m dsn)
    (slotsLen : shape.layout.slots.length = slotBs.length) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = shape.binders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (bpos vpos : Nat → Nat)
        (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)),
      (packLets fs core).2.WF kb kv vw →
      (∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool)) →
      (∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j))) →
      shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
        (fun j => inputExpr shape.binders.length (vpos j)) (packLets fs core).2 →
      (∀ f ∈ shape.layout.slots, f.lo + f.width ≤ c) →
      (∀ o ∈ shape.layout.outs, o.lo + o.width ≤ c) →
      ∃ regs : List String, regs.Nodup ∧ regs.length = slotBs.length ∧
      ∃ lets : List String, lets.length = letBs.length ∧
      MachineWired declName shape ids cache m dsn regs lets ∧ X ids cache ∧
      ∀ (T : Nat) (bools : Nat → Nat → Bool) (bits : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T →
          SourceInputs declName bsIn ids cache (bools (T - 1 - t)) (bits (T - 1 - t)) (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) →
        (∀ i r b, regs[i]? = some r → slotBs[i]? = some b →
          st0 r = posEnc (bools 0) (bits 0) (bsIn.length + i) b.2) →
        (∀ τ i f b, shape.layout.slots[i]? = some f → slotBs[i]? = some b →
          posEnc (bools (τ + 1)) (bits (τ + 1)) (bsIn.length + i) b.2 =
            mask f.width (packedAt core bpos vpos (bools τ) (bits τ) >>> f.lo)) →
        (∀ τ, LetsHold bpos vpos (bools τ) (bits τ) (bsIn.length + slotBs.length) letBs fs) →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          (∀ j (hj : j < envs.length), ∀ o ∈ shape.layout.outs, (envs[j]'hj) o.name =
            mask o.width (packedAt core bpos vpos (bools j) (bits j) >>> o.lo)) ∧
          ∀ j (hj : j < envs.length) (k : Nat) (name : String) (b : Name × MixedGateBinder),
            lets[k]? = some name → letBs[k]? = some b →
            (envs[j]'hj) name = posEnc (bools j) (bits j) (bsIn.length + slotBs.length + k) b.2 := by
  obtain ⟨ids, nd, len, cache, h⟩ := h
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw bpos vpos fs c core he hb hv hbody hfit houtfit
  obtain ⟨regs, regsNd, regsLen, lets, letsLen, wired, hx, step⟩ :=
    h dom kb kv vw bpos vpos fs core he hb hv hbody hfit houtfit
  refine ⟨regs, regsNd, regsLen, lets, letsLen, wired, hx, ?_⟩
  intro T bools bits seed st0 mems inputs pass rst init follow hold
  -- `k` cycles remain; the state holds the slots' values at time `T - k`.
  suffices main : ∀ (k : Nat), k ≤ T → ∀ (st : String → Nat),
      (∀ i r b, regs[i]? = some r → slotBs[i]? = some b →
        st r = posEnc (bools (T - k)) (bits (T - k)) (bsIn.length + i) b.2) →
      ∃ envs, runModule (weOf m) m.body seed k st mems = some envs ∧ envs.length = k ∧
        (∀ j (hj : j < envs.length), ∀ o ∈ shape.layout.outs, (envs[j]'hj) o.name =
          mask o.width
            (packedAt core bpos vpos (bools (T - k + j)) (bits (T - k + j)) >>> o.lo)) ∧
        ∀ j (hj : j < envs.length) (q : Nat) (name : String) (b : Name × MixedGateBinder),
          lets[q]? = some name → letBs[q]? = some b →
          (envs[j]'hj) name =
            posEnc (bools (T - k + j)) (bits (T - k + j)) (bsIn.length + slotBs.length + q) b.2 by
    obtain ⟨envs, hrun, hlen, hobs, hlet⟩ := main T (Nat.le_refl T) st0 (by simpa using init)
    refine ⟨envs, hrun, hlen, fun j hj o ho => ?_, fun j hj q name b hn hb => ?_⟩
    · simpa using hobs j hj o ho
    · simpa using hlet j hj q name b hn hb
  intro k
  induction k with
  | zero => intro _ st _; exact ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro hk st inv
    have hτ : T - 1 - k = T - (k + 1) := by omega
    obtain ⟨envF, hstep, hout, hletF⟩ := step (bools (T - (k + 1))) (bits (T - (k + 1)))
      (seed k st) mems (hτ ▸ inputs k st (by omega))
      (fun i r b hr hb' => by
        rw [pass k st r (List.mem_of_getElem? hr)]; exact inv i r b hr hb')
      (rst k st) (hold _)
    have inv' : ∀ i r b, regs[i]? = some r → slotBs[i]? = some b →
        applyNexts st (fieldNexts (packedAt core bpos vpos (bools (T - (k + 1)))
          (bits (T - (k + 1)))) regs shape.layout.slots) r =
          posEnc (bools (T - k)) (bits (T - k)) (bsIn.length + i) b.2 := by
      intro i r b hr hb'
      have hi : i < shape.layout.slots.length := by
        have := (List.getElem?_eq_some_iff.mp hb').1; omega
      rw [applyNexts_fieldNexts regsNd i r _ hr (List.getElem?_eq_getElem hi)]
      have hT : T - k = T - (k + 1) + 1 := by omega
      rw [hT]
      exact (follow (T - (k + 1)) i _ b (List.getElem?_eq_getElem hi) hb').symm
    obtain ⟨rest, hrun, hlen, hobs, hletR⟩ := ih (by omega) _ inv'
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_, ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj o ho
      cases j with
      | zero => simpa using hout o ho
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget, hobs i hi o ho]
        have hidx : T - k + i = T - (k + 1) + (i + 1) := by
          have : i < k := by omega
          omega
        rw [hidx]
    · intro j hj q name b hn hb
      cases j with
      | zero => simpa using hletF q name b hn hb
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget, hletR i hi q name b hn hb]
        have hidx : T - k + i = T - (k + 1) + (i + 1) := by
          have : i < k := by omega
          omega
        rw [hidx]

set_option maxHeartbeats 1000000 in
/-- **The emitted module implements the reference machine.** For a machine
shape whose packed body is the quotation of `let₀ ++ … ++ core`, with every
`let` field reading earlier positions only and the reset values inside
their widths: a `T`-cycle run of the emitted module — seeded each cycle with
that cycle's inputs over the register state, reset low, the registers
starting at their reset values — succeeds, and at cycle `j` every output
port shows its field of the reference machine at time `j`. No hypothesis
about the valuation is left: the reference machine is computed from the
terms. -/
theorem machine_ref_traceX {X : List FVarId → IO.Ref (ExprStructMap String) → Prop} {declName shape m dsn}
    {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (h : MachinePreservesX X declName shape bsIn slotBs letBs m dsn)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) =>
      f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      shape.layout.slots slotBs) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = shape.binders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (bpos vpos : Nat → Nat)
        (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)),
      (packLets fs core).2.WF kb kv vw →
      (∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool)) →
      (∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j))) →
      shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
        (fun j => inputExpr shape.binders.length (vpos j)) (packLets fs core).2 →
      (∀ f ∈ shape.layout.slots, f.lo + f.width ≤ c) →
      (∀ o ∈ shape.layout.outs, o.lo + o.width ≤ c) →
      LetsScoped bpos vpos (bsIn.length + slotBs.length) letBs fs →
      ∃ regs : List String, regs.Nodup ∧ regs.length = slotBs.length ∧
      ∃ lets : List String, lets.length = letBs.length ∧
      MachineWired declName shape ids cache m dsn regs lets ∧ X ids cache ∧
      ∀ (T : Nat) (inB : Nat → Nat → Bool) (inV : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T →
          SourceInputs declName bsIn ids cache (inB (T - 1 - t)) (inV (T - 1 - t)) (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) →
        (∀ (i : Nat) (r : String) (f : SlotField), regs[i]? = some r →
          shape.layout.slots[i]? = some f → st0 r = f.init) →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          (∀ j (hj : j < envs.length), ∀ o ∈ shape.layout.outs, (envs[j]'hj) o.name =
            RefMachine.out (RefMachine.mk bsIn.length slotBs.length bpos vpos fs c core
              shape.layout.slots) inB inV j o.lo o.width) ∧
          -- a `let` wire shows its field term under the reference valuation
          ∀ j (hj : j < envs.length) (q : Nat) (name : String) (f : Σ w : Nat, Term (.bits w)),
            lets[q]? = some name → fs[q]? = some f →
            (envs[j]'hj) name =
              (eval (fun i => (RefMachine.mk bsIn.length slotBs.length bpos vpos fs c core
                  shape.layout.slots).valBAt inB inV j (bpos i))
                (fun i w => (RefMachine.mk bsIn.length slotBs.length bpos vpos fs c core
                  shape.layout.slots).valVAt inB inV j (vpos i) w) f.2).toNat := by
  have slotsLen : shape.layout.slots.length = slotBs.length := layW.length_eq
  obtain ⟨ids, nd, len, cache, h⟩ := machine_traceX h slotsLen
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw bpos vpos fs c core he hb hv hbody hfit houtfit hscoped
  obtain ⟨regs, regsNd, regsLen, lets, letsLen, wired, hx, trace⟩ :=
    h dom kb kv vw bpos vpos fs core he hb hv hbody hfit houtfit
  refine ⟨regs, regsNd, regsLen, lets, letsLen, wired, hx, ?_⟩
  intro T inB inV seed st0 mems inputs pass rst init
  -- the reference machine and its valuation over time
  let M : RefMachine := RefMachine.mk bsIn.length slotBs.length bpos vpos fs c core
    shape.layout.slots
  let B : Nat → Nat → Bool := fun τ =>
    valB bsIn.length (inB τ) (M.store (inB τ) (inV τ) (M.state inB inV τ))
  let V : Nat → (j : Nat) → (n : Nat) → BitVec n := fun τ =>
    valV bsIn.length (inV τ) (M.store (inB τ) (inV τ) (M.state inB inV τ))
  -- the state is inside the slots' widths
  have bounded : ∀ τ i f, shape.layout.slots[i]? = some f →
      M.state inB inV τ i < 2 ^ f.width := by
    intro τ i f hf
    cases τ with
    | zero =>
      have hi : i < slotBs.length := by
        have := (List.getElem?_eq_some_iff.mp hf).1; omega
      have := (layW.get i f slotBs[i] hf (List.getElem?_eq_getElem hi)).2.2
      simpa [RefMachine.state, M, hf] using this
    | succ τ =>
      show M.next _ _ _ i < _
      simp only [RefMachine.next, M, hf]
      exact mask_lt _ _
  -- a slot position of the store holds the state
  have slotStore : ∀ τ i, i < slotBs.length →
      M.store (inB τ) (inV τ) (M.state inB inV τ) (bsIn.length + i) = M.state inB inV τ i := by
    intro τ i hi
    show letStore _ _ _ _ _ _ _ _ _ = _
    rw [letStore_frame _ _ _ _ (by show bsIn.length + i < bsIn.length + slotBs.length; omega)]
    show M.state inB inV τ (bsIn.length + i - bsIn.length) = _
    rw [Nat.add_sub_cancel_left]
  have slotEnc : ∀ τ i f b, shape.layout.slots[i]? = some f → slotBs[i]? = some b →
      posEnc (B τ) (V τ) (bsIn.length + i) b.2 = M.state inB inV τ i := by
    intro τ i f b hf hb'
    have hi : i < slotBs.length := (List.getElem?_eq_some_iff.mp hb').1
    obtain ⟨hw, hk, _⟩ := layW.get i f b hf hb'
    rw [posEnc_store (by omega) hk (by
      rw [slotStore τ i hi, ← hw]; exact bounded τ i f hf), slotStore τ i hi]
  have holds : ∀ τ, LetsHold bpos vpos (B τ) (V τ) (bsIn.length + slotBs.length) letBs fs :=
    fun τ => letStore_holds fs letBs (bsIn.length + slotBs.length) _ (by omega) hscoped
  obtain ⟨envs, hrun, hlen, hobs, hlet⟩ := trace T B V seed st0 mems
    (by
      intro t st ht
      refine sourceInputs_congr nd ?_ ?_ (inputs t st ht)
      · intro j hj; simp [B, valB, hj]
      · intro j hj n; simp [V, valV, hj])
    pass rst
    (by
      intro i r b hr hb'
      have hi : i < shape.layout.slots.length := by
        have := (List.getElem?_eq_some_iff.mp hb').1; omega
      rw [slotEnc 0 i _ b (List.getElem?_eq_getElem hi) hb',
        init i r _ hr (List.getElem?_eq_getElem hi)]
      simp [RefMachine.state, M, List.getElem?_eq_getElem hi])
    (by
      intro τ i f b hf hb'
      rw [slotEnc (τ + 1) i f b hf hb']
      show M.next _ _ _ i = _
      simp only [RefMachine.next, M, hf]
      rfl)
    holds
  refine ⟨envs, hrun, hlen, fun j hj o ho => hobs j hj o ho, ?_⟩
  intro j hj q name f hn hf
  have hq : q < letBs.length := by
    rw [(holds j).length_eq]; exact (List.getElem?_eq_some_iff.mp hf).1
  rw [hlet j hj q name letBs[q] hn (List.getElem?_eq_getElem hq)]
  exact ((holds j).get q letBs[q] f (List.getElem?_eq_getElem hq) hf).1

open Tools.ShippingMachineClose (Zip₂) in
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
  Tools.ShippingEntrySoundness Sparkle.IR.AST in
set_option maxHeartbeats 2000000 in
/-- **Source to RTL for a state machine, with the declaration's part reduced
to data.** From the one-cycle theorem of the emitted module and decidable
facts about the terms: for every `circuit do` (`inits`, `body`) whose pending
writes are the typed values of the next-value terms, a run of the emitted
module from the reset values shows on every output port the typed value of
that port's term on the `circuit do`'s own state — at every cycle. -/
theorem machine_endpointX {X : List FVarId → IO.Ref (ExprStructMap String) → Prop} {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module}
    {dsn : Sparkle.IR.AST.Design} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (h : MachinePreservesX X declName shape bsIn slotBs letBs m dsn)
    {ss : List SType} {ls : List (Σ s : SType, Term s)} {nexts : Terms ss}
    {f0 : Σ w : Nat, Term (.bits w)} {rest : List (Σ w : Nat, Term (.bits w))}
    {K : Nat → Option SType} {kb kv : Nat} {vw bpos vpos : Nat → Nat} {dom : Lean.Expr}
    {nOuts : Nat}
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) =>
      f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      shape.layout.slots slotBs)
    (hwf : (packLets (ls.map fun l => toField l.1 l.2) (packList f0 rest).2).2.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j)))
    (hbody : shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
      (fun j => inputExpr shape.binders.length (vpos j))
      (packLets (ls.map fun l => toField l.1 l.2) (packList f0 rest).2).2)
    (hfit : ∀ f ∈ shape.layout.slots, f.lo + f.width ≤ (packList f0 rest).1)
    (houtfit : ∀ o ∈ shape.layout.outs, o.lo + o.width ≤ (packList f0 rest).1)
    (hscoped : LetsScoped bpos vpos (bsIn.length + slotBs.length) letBs
      (ls.map fun l => toField l.1 l.2))
    (hn : slotBs.length = ss.length)
    (hnexts : (f0 :: rest).drop nOuts = nexts.fields)
    (hslots : SlotsFit (f0 :: rest) nOuts shape.layout.slots)
    (facts : TermFacts bsIn.length kb kv vw bpos vpos K ss ls)
    (nextsWF : ∀ g ∈ nexts.fields, g.2.WF kb kv vw) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = slotBs.length ∧
      ∃ lets : List String, lets.length = letBs.length ∧
      MachineWired declName shape ids cache m dsn regs lets ∧ X ids cache ∧
      ∀ {D : DomainConfig} (σ : Nat → HList (tys ss))
        (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)),
        (∀ i, encState ss (σ 0) i = (shape.layout.slots[i]?.map (·.init)).getD 0) →
        (∀ t, σ (t + 1) =
            evalTerms
              (fun j => (typedVal bsIn.length bpos vpos ss ls bools bits t (σ t)).b (bpos j))
              (fun j w => (typedVal bsIn.length bpos vpos ss ls bools bits t (σ t)).v
                (vpos j) w) nexts) →
        ∀ (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T → SourceInputs declName bsIn ids cache
          (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
          (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) →
        (∀ (i : Nat) (r : String) (f : SlotField), regs[i]? = some r →
          shape.layout.slots[i]? = some f → st0 r = f.init) →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          (∀ j (hj : j < envs.length), ∀ o ∈ shape.layout.outs,
            ∀ {s : SType} (ot : Term s), ot.WF kb kv vw → ∀ (k : Nat),
              (f0 :: rest)[k]? = some (toField s ot) →
              o.lo = (((f0 :: rest).drop (k + 1)).map (·.1)).sum →
              o.width = (toField s ot).1 →
              (envs[j]'hj) o.name = enc s (eval
                (fun i => (typedVal bsIn.length bpos vpos ss ls bools bits j (σ j)).b (bpos i))
                (fun i w => (typedVal bsIn.length bpos vpos ss ls bools bits j (σ j)).v
                  (vpos i) w) ot)) ∧
          -- a `let` wire shows its term on the typed valuation of the cycle
          ∀ j (hj : j < envs.length) (q : Nat) (name : String) (l : Σ s : SType, Term s),
            lets[q]? = some name → ls[q]? = some l →
            (envs[j]'hj) name = enc l.1 (eval
              (fun i => (typedVal bsIn.length bpos vpos ss ls bools bits j (σ j)).b (bpos i))
              (fun i w => (typedVal bsIn.length bpos vpos ss ls bools bits j (σ j)).v
                (vpos i) w) l.2) := by
  obtain ⟨ids, nd, len, cache, href⟩ := machine_ref_traceX h layW
  have href' := href dom kb kv vw bpos vpos (ls.map fun l => toField l.1 l.2)
    (packList f0 rest).2 hwf hb hv hbody hfit houtfit hscoped
  obtain ⟨regs, rnd, rlen, lets, llen, wired, hx, trace⟩ := href'
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, ?_⟩
  intro D σ bools bits hinit hstep T seed st0 mems inputs pass rst init
  obtain ⟨envs, hrun, hlen, hobs, hlet⟩ := trace T (fun τ p => (bools p).val τ)
    (fun τ p w => (bits p w).val τ) seed st0 mems inputs pass rst init
  have hslotsLen : shape.layout.slots.length = ss.length := by
    rw [← hn]; exact layW.length_eq
  have hstate := denote_state σ bools bits ls nexts f0 rest (packList f0 rest).2
    shape.layout.slots nOuts rfl hnexts hslots hslotsLen hinit facts nextsWF hstep
  refine ⟨envs, hrun, hlen, ?_, ?_⟩
  · intro j hj o ho s ot hot k hk hlo hw
    have hout := denote_out σ bools bits ls f0 rest (packList f0 rest).2
      shape.layout.slots rfl facts hstate ot hot k hk j
    rw [hobs j hj o ho, hout, hlo, hw, hn]
  · intro j hj q name l hname hl
    have hfq : (ls.map fun l => toField l.1 l.2)[q]? = some (toField l.1 l.2) := by
      rw [List.getElem?_map, hl]; rfl
    rw [hlet j hj q name _ hname hfq, eval_toField]
    have hwfl := LetsTyped.get facts.lets q l hl
    rw [eval_typed facts bools bits j (σ j) l.2 hwfl]
    simp only [RefMachine.valBAt, RefMachine.valVAt]
    rw [hn]
    show _ = enc l.1 (eval _ _ l.2)
    rw [hstate j]
    rfl

/-- `MachineTraceWith` and, for `let` observations `lsrc` (one per hardware
`let` of the transition, as far as given), the `let` wires: wire `q` shows
observation `q` at every cycle; and the module is wired to its children in
its design `dsn` (`MachineWired`). -/
def MachineTraceLBX (X : List FVarId → IO.Ref (ExprStructMap String) → Prop) (declName : Name) (d : MachineData) (m : Sparkle.IR.AST.Module)
    (dsn : Sparkle.IR.AST.Design)
    {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧
    ∃ lets : List String, lets.length = d.letBs.length ∧
    MachineWired declName d.shape ids cache m dsn regs lets ∧ X ids cache ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
        (fun j => (extB i bools bits j).val (T - 1 - t))
        (fun j n => (ext i bools bits j n).val (T - 1 - t))
        (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
        (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j) ∧
        ∀ j (hj : j < envs.length) (q : Nat) (name : String) (g : Nat → Nat),
          lets[q]? = some name → (lsrc i bools bits)[q]? = some g → q < d.ls.length →
          (envs[j]'hj) name = g j

/-- **The instance serving a call is a real child.** For the binder ids and
wire cache of the run: on the general closing (`instFields ≠ []`), an
instance statement one of whose output connections is call `k`'s port has as
its module (resolved by name) the built memory module of a memory call, or a
result of the real entry on call `k`'s declaration in these contexts. -/
def ServedRealG (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Sparkle.IR.AST.Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  shape.instFields ≠ [] →
  ∀ k (hk : k < shape.insts.length) (mc : Sparkle.IR.AST.Module) (iname : String)
    (argWs : List String) (outs : List (Nat × String)) (outWs : List String),
    Stmt.inst mc.name iname (Tools.ShippingMachineLinkedT.connsG mc argWs outs outWs) ∈ m.body →
    outs.mapM (fun (j, _) =>
      ((machPorts declName ids cache shape.binders).map (·.name))[machNIn shape + j]?) = some outWs →
    (∃ e ∈ outs, e.1 = k) →
    moduleByName dsn.modules mc.name = some mc →
    (∃ md, Sparkle.Compiler.MachMemory.memChild? (shape.insts[k]).1 = some md ∧ mc = md.1) ∨
      ∃ Dc, Tools.ShippingChildSynth.RealChild mctx mref cctx cref (shape.insts[k]).1 (mc, Dc)

/-- The one-output closing (`instFields = []`): the instance that is call `k`'s
statement (`CallStmt`, for the run's port names) has as its module the built
memory module of a memory call, or a result of the real entry on call `k`'s
declaration in these contexts. -/
def ServedReal1 (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Sparkle.IR.AST.Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  shape.instFields = [] →
  ∀ k (hk : k < shape.insts.length) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
    (shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
    Tools.ShippingMachineInst.CallStmt (machNIn shape) shape.insts.length shape.layout.slots.length
      ((machPorts declName ids cache shape.binders).map (·.name)) k args mc st →
    moduleByName dsn.modules mc.name = some mc →
    (∃ md, Sparkle.Compiler.MachMemory.memChild? (shape.insts[k]).1 = some md ∧ mc = md.1) ∨
      ∃ Dc, Tools.ShippingChildSynth.RealChild mctx mref cctx cref (shape.insts[k]).1 (mc, Dc)

/-- **The instances serving the calls are real children**, on either closing. -/
def ServedReal (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Sparkle.IR.AST.Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  ServedRealG mctx mref cctx cref declName shape m dsn ids cache ∧
    ServedReal1 mctx mref cctx cref declName shape m dsn ids cache

/-- An allocated name is not the clock or the reset. -/
theorem allocated_ne {x : String} (h : Sparkle.IR.NameHints.Allocated x) :
    x ≠ "clk" ∧ x ≠ "rst" := by
  constructor <;> (intro hx; subst hx; have := h.2; simp at this)

/-- **A state machine through the real entry, with its children.** The
one-cycle theorem of `synthesizeCombinationalCore_machine_sound`, with
`ServedReal` for the same ids and cache, under the `ChildSynthIs` boundary. -/
theorem synthesizeCombinationalCore_machine_soundR {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Design}
    {shape : MachineShape} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (hsyn : Tools.ShippingChildSynth.ChildSynthIs mctx mref cctx cref)
    (hbs : shape.binders = bsIn ++ slotBs ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outsOk : ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (shape.layout.outs.map (·.name)).Nodup) :
    MachinePreservesX (ServedReal mctx mref cctx cref declName shape m d)
      declName shape bsIn slotBs letBs m d := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := synthesizeFromConst_machine old miss run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w9, w10, hrun, hres⟩ := hmach shape hshape
  have hne := closes logProf _ _ _ hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, hmix, hcl, hmt⟩ := Tools.ShippingChildSynth.synthesizeMachineCertified_runs hrun hsyn
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
      obtain ⟨_, hkr⟩ := hreal
      obtain ⟨y', hy', hor⟩ := hkr k hk
      rw [hy] at hy'; cases hy'
      subst hmcy
      rcases hor with hmem | hrc
      · exact Or.inl ⟨y, hmem, rfl⟩
      · exact Or.inr ⟨y.2, hrc⟩
    case g =>
    intro hfe k hk mc iname argWs outs outWs hst hout hke hmod
    rcases hmt with ⟨h0, _, _⟩ | ⟨_, children, hcc, hreal⟩
    · rw [h0] at hk; exact absurd hk (Nat.not_lt_zero _)
    rcases hcc with ⟨hfe0, _⟩ | ⟨_, hG, _⟩
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
    obtain ⟨_, hkr⟩ := hreal
    obtain ⟨y', hy', hor⟩ := hkr k hk
    rw [hy] at hy'; cases hy'
    subst hmcy
    rcases hor with hmem | hrc
    · exact Or.inl ⟨y, hmem, rfl⟩
    · exact Or.inr ⟨y.2, hrc⟩

set_option maxHeartbeats 2000000 in
/-- **Source to RTL for a state machine, from data and a state stream.** The
check `ok`, the body equation and the reset check give the trace theorem of
every module a run of the real synthesis entry returns at the machine
boundary, for a source whose observations are the typed values of the
output terms on SOME stream of states that starts at the reset values and
advances by the typed values of the next-value terms. The stream is the
state loop of a `circuit do` (`machine_trace_of_data`) or the tuple of the
loops of a `circuit do` with sub-machines (ShippingMachineNest). -/
theorem machine_trace_lets_of_streamBR {declName : Name} (d : MachineData) {ι : Type}
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
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape)
    (hsyn : Tools.ShippingChildSynth.ChildSynthIs mctx mref cctx cref) :
    MachineTraceLBX (ServedReal mctx mref cctx cref declName d.shape m design)
      declName d m design dom src ext extB lsrc := by
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
  have hpres : MachinePreservesX (ServedReal mctx mref cctx cref declName d.shape m design)
      declName d.shape d.bsIn d.slotBs d.letBs m design :=
    synthesizeCombinationalCore_machine_soundR hr entry closes hsyn d.binders_split hlets
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



end Tools.ShippingMachineTraceX
