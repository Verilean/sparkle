import Tools.ShippingMachineEntry

/-! # The reference semantics of a state machine

`machine_trace` speaks about ANY valuation of the transition's binders over
time that starts in the registers, follows the transition and gives the
`let` binders the values of their fields. This file constructs that
valuation from the terms alone — the REFERENCE SEMANTICS of the machine:

* the state at time 0 is the reset values, and at time `τ + 1` the slot
  fields of the packed transition value at time `τ`;
* at every time the `let` binders are computed in order, each from the
  inputs, the slots and the earlier `let`s.

`machine_ref_trace` is then the statement with nothing left to supply but
decidable facts about the terms: a run of the emitted module shows, at every
cycle and on every output port, the field of the reference machine. What a
declaration still has to prove is that ITS Lean meaning is that reference
machine (`Tools/ShippingMachineSource.lean` for the `circuit do` side). -/
namespace Tools.ShippingMachineRef
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineClose Tools.ShippingMachineEntry

/-! ## What a term reads -/

/-- Every input index the term reads satisfies the predicates. -/
def reads (okB okV : Nat → Bool) : {s : SType} → Term s → Bool
  | _, .boolInput j => okB j
  | _, .bitsInput _ j => okV j
  | _, .boolLit _ => true
  | _, .bitsLit _ _ => true
  | _, .bitsNum _ _ => true
  | _, .binary _ a b => reads okB okV a && reads okB okV b
  | _, .compare _ a b => reads okB okV a && reads okB okV b
  | _, .boolBinary _ a b => reads okB okV a && reads okB okV b
  | _, .boolNot a => reads okB okV a
  | _, .boolEq a b => reads okB okV a && reads okB okV b
  | _, .mux c a b => reads okB okV c && reads okB okV a && reads okB okV b
  | _, .setw _ a => reads okB okV a
  | _, .appCompare _ a b => reads okB okV a && reads okB okV b
  | _, .appBool _ a b => reads okB okV a && reads okB okV b
  | _, .appBool2 _ a b => reads okB okV a && reads okB okV b
  | _, .slice _ _ _ a => reads okB okV a
  | _, .concat a b => reads okB okV a && reads okB okV b
  | _, .concatLitHi _ _ b => reads okB okV b
  | _, .concatLitLo a _ _ => reads okB okV a
  | _, .zextMap _ _ a => reads okB okV a
  | _, .sliceF _ _ _ a => reads okB okV a

/-- A term's value depends on the inputs it reads only. -/
theorem eval_congr_reads {okB okV : Nat → Bool} {b b' : Nat → Bool}
    {v v' : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, okB j = true → b j = b' j)
    (hv : ∀ j, okV j = true → ∀ w, v j w = v' j w) :
    ∀ {s : SType} (e : Term s), reads okB okV e = true → eval b v e = eval b' v' e := by
  intro s e
  induction e with
  | boolInput j => intro h; exact hb j h
  | bitsInput w j => intro h; exact hv j h w
  | boolLit _ => intro _; rfl
  | bitsLit _ _ => intro _; rfl
  | bitsNum _ _ => intro _; rfl
  | binary op a b iha ihb =>
    intro h; simp only [reads, Bool.and_eq_true] at h
    simp only [eval, iha h.1, ihb h.2]
  | compare op a b iha ihb =>
    intro h; simp only [reads, Bool.and_eq_true] at h
    simp only [eval, iha h.1, ihb h.2]
  | boolBinary op a b iha ihb =>
    intro h; simp only [reads, Bool.and_eq_true] at h
    simp only [eval, iha h.1, ihb h.2]
  | boolNot a iha => intro h; simp only [reads] at h; simp only [eval, iha h]
  | boolEq a b iha ihb =>
    intro h; simp only [reads, Bool.and_eq_true] at h
    simp only [eval, iha h.1, ihb h.2]
  | mux c a b ihc iha ihb =>
    intro h; simp only [reads, Bool.and_eq_true] at h
    simp only [eval, ihc h.1.1, iha h.1.2, ihb h.2]
  | setw w' a iha => intro h; simp only [reads] at h; simp only [eval, iha h]
  | appCompare op a b iha ihb =>
    intro h; simp only [reads, Bool.and_eq_true] at h
    simp only [eval, iha h.1, ihb h.2]
  | appBool op a b iha ihb =>
    intro h; simp only [reads, Bool.and_eq_true] at h
    simp only [eval, iha h.1, ihb h.2]
  | appBool2 f a b iha ihb =>
    intro h; simp only [reads, Bool.and_eq_true] at h
    simp only [eval, iha h.1, ihb h.2]
  | slice nm start len a iha => intro h; simp only [reads] at h; simp only [eval, iha h]
  | concat a b iha ihb =>
    intro h; simp only [reads, Bool.and_eq_true] at h
    simp only [eval, iha h.1, ihb h.2]
  | concatLitHi k v b ihb => intro h; simp only [reads] at h; simp only [eval, ihb h]
  | concatLitLo a k v iha => intro h; simp only [reads] at h; simp only [eval, iha h]
  | zextMap nm k a iha => intro h; simp only [reads] at h; simp only [eval, iha h]
  | sliceF nm start len a iha => intro h; simp only [reads] at h; simp only [eval, iha h]

/-! ## The valuation of a store -/

/-- The Bool valuation: the inputs' below `kIn`, the store's above. -/
def valB (kIn : Nat) (inB : Nat → Bool) (σ : Nat → Nat) : Nat → Bool :=
  fun p => if p < kIn then inB p else σ p == 1

/-- The BitVec valuation: the inputs' below `kIn`, the store's above. -/
def valV (kIn : Nat) (inV : (j : Nat) → (n : Nat) → BitVec n) (σ : Nat → Nat) :
    (j : Nat) → (n : Nat) → BitVec n :=
  fun p n => if p < kIn then inV p n else BitVec.ofNat n (σ p)

/-- A stored value below the binder's width is what the valuation encodes. -/
theorem posEnc_store {kIn : Nat} {inB : Nat → Bool} {inV : (j : Nat) → (n : Nat) → BitVec n}
    {σ : Nat → Nat} {p : Nat} {k : MixedGateBinder} (hp : kIn ≤ p) (hk : k ≠ .domain)
    (hlt : σ p < 2 ^ machWidth k) :
    posEnc (valB kIn inB σ) (valV kIn inV σ) p k = σ p := by
  have hnot : ¬ p < kIn := by omega
  cases k with
  | domain => exact absurd rfl hk
  | bool =>
    simp only [posEnc, valB, hnot, if_false, encodeBool]
    have : σ p = 0 ∨ σ p = 1 := by
      simp only [machWidth] at hlt; omega
    rcases this with h | h <;> simp [h]
  | bits n =>
    simp only [posEnc, valV, hnot, if_false, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlt

/-! ## The `let`s -/

/-- Compute the `let` binders in order: each field's value, from the
valuation of the store so far, goes to the next position. -/
def letStore (bpos vpos : Nat → Nat) (kIn : Nat) (inB : Nat → Bool)
    (inV : (j : Nat) → (n : Nat) → BitVec n) :
    List (Σ w : Nat, Term (.bits w)) → Nat → (Nat → Nat) → (Nat → Nat)
  | [], _, σ => σ
  | f :: fs, p, σ =>
    letStore bpos vpos kIn inB inV fs (p + 1) (fun q =>
      if q = p then (eval (fun j => valB kIn inB σ (bpos j))
        (fun j w => valV kIn inV σ (vpos j) w) f.2 : BitVec f.1).toNat
      else σ q)

theorem letStore_frame {bpos vpos : Nat → Nat} {kIn : Nat} {inB : Nat → Bool}
    {inV : (j : Nat) → (n : Nat) → BitVec n} :
    ∀ (fs : List (Σ w : Nat, Term (.bits w))) (p : Nat) (σ : Nat → Nat) (q : Nat), q < p →
      letStore bpos vpos kIn inB inV fs p σ q = σ q
  | [], _, _, _, _ => rfl
  | f :: fs, p, σ, q, h => by
    simp only [letStore]
    rw [letStore_frame fs (p + 1) _ q (by omega)]
    simp [Nat.ne_of_lt h]

/-- The `let`s of a store, as the entry theorem needs them: every field reads
positions below its own only, and is as wide as its binder. -/
def LetsScoped (bpos vpos : Nat → Nat) :
    Nat → List (Name × MixedGateBinder) → List (Σ w : Nat, Term (.bits w)) → Prop
  | _, [], [] => True
  | p, b :: bs, f :: fs =>
    reads (fun j => decide (bpos j < p)) (fun j => decide (vpos j < p)) f.2 = true ∧
      machWidth b.2 = f.1 ∧ b.2 ≠ .domain ∧ LetsScoped bpos vpos (p + 1) bs fs
  | _, _, _ => False

/-- The store `letStore` computes gives every `let` binder the value of its
field. -/
theorem letStore_holds {bpos vpos : Nat → Nat} {kIn : Nat} {inB : Nat → Bool}
    {inV : (j : Nat) → (n : Nat) → BitVec n} :
    ∀ (fs : List (Σ w : Nat, Term (.bits w))) (bs : List (Name × MixedGateBinder)) (p : Nat)
      (σ : Nat → Nat), kIn ≤ p → LetsScoped bpos vpos p bs fs →
      LetsHold bpos vpos (valB kIn inB (letStore bpos vpos kIn inB inV fs p σ))
        (valV kIn inV (letStore bpos vpos kIn inB inV fs p σ)) p bs fs
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, h => h.elim
  | f :: fs, b :: bs, p, σ, hp, ⟨hreads, hwidth, hkind, hrest⟩ => by
    -- the store after this `let`
    let σ1 : Nat → Nat := fun q =>
      if q = p then (eval (fun j => valB kIn inB σ (bpos j))
        (fun j w => valV kIn inV σ (vpos j) w) f.2 : BitVec f.1).toNat
      else σ q
    have hfinal : ∀ q, q ≤ p → letStore bpos vpos kIn inB inV (f :: fs) p σ q = σ1 q :=
      fun q hq => letStore_frame fs (p + 1) σ1 q (by omega)
    have hbelow : ∀ q, q < p → letStore bpos vpos kIn inB inV (f :: fs) p σ q = σ q := by
      intro q hq
      rw [hfinal q (by omega)]
      simp [σ1, Nat.ne_of_lt hq]
    -- the field evaluates the same under the final store
    have hev : (eval (fun j => valB kIn inB (letStore bpos vpos kIn inB inV (f :: fs) p σ) (bpos j))
        (fun j w => valV kIn inV (letStore bpos vpos kIn inB inV (f :: fs) p σ) (vpos j) w) f.2 :
          BitVec f.1) =
        eval (fun j => valB kIn inB σ (bpos j)) (fun j w => valV kIn inV σ (vpos j) w) f.2 := by
      apply eval_congr_reads (okB := fun j => decide (bpos j < p))
        (okV := fun j => decide (vpos j < p)) _ _ f.2 hreads
      · intro j hj
        have hj' : bpos j < p := by simpa using hj
        simp only [valB, hbelow _ hj']
      · intro j hj w
        have hj' : vpos j < p := by simpa using hj
        simp only [valV, hbelow _ hj']
    refine ⟨?_, hwidth, ?_⟩
    · rw [posEnc_store hp hkind (by
        rw [hfinal p (Nat.le_refl p)]
        simp only [σ1, if_true, hwidth]
        exact (eval (fun j => valB kIn inB σ (bpos j))
          (fun j w => valV kIn inV σ (vpos j) w) f.2 : BitVec f.1).isLt),
        hfinal p (Nat.le_refl p), hev]
      simp [σ1]
    · exact letStore_holds fs bs (p + 1) σ1 (by omega) hrest

/-! ## The reference machine -/

/-- Everything that defines a machine's reference semantics. -/
structure RefMachine where
  /-- The number of the declaration's binders (the positions of its inputs). -/
  kIn : Nat
  /-- The number of slots. -/
  nSlots : Nat
  bpos : Nat → Nat
  vpos : Nat → Nat
  lets : List (Σ w : Nat, Term (.bits w))
  coreWidth : Nat
  core : Term (.bits coreWidth)
  slots : List SlotField

namespace RefMachine

/-- The store of a cycle: the slots' values, then the `let`s computed from
them and the inputs. -/
def store (M : RefMachine) (inB : Nat → Bool) (inV : (j : Nat) → (n : Nat) → BitVec n)
    (st : Nat → Nat) : Nat → Nat :=
  letStore M.bpos M.vpos M.kIn inB inV M.lets (M.kIn + M.nSlots) (fun p => st (p - M.kIn))

/-- The packed transition value of a cycle. -/
def packed (M : RefMachine) (inB : Nat → Bool) (inV : (j : Nat) → (n : Nat) → BitVec n)
    (st : Nat → Nat) : Nat :=
  packedAt M.core M.bpos M.vpos (valB M.kIn inB (M.store inB inV st))
    (valV M.kIn inV (M.store inB inV st))

/-- The slots' values after a cycle. -/
def next (M : RefMachine) (inB : Nat → Bool) (inV : (j : Nat) → (n : Nat) → BitVec n)
    (st : Nat → Nat) : Nat → Nat :=
  fun i => match M.slots[i]? with
    | some f => mask f.width (M.packed inB inV st >>> f.lo)
    | none => 0

/-- **The state of the reference machine** at time `τ`, slot by slot: the
reset values, then the transition applied to the inputs of each cycle. -/
def state (M : RefMachine) (inB : Nat → Nat → Bool)
    (inV : Nat → (j : Nat) → (n : Nat) → BitVec n) : Nat → (Nat → Nat)
  | 0 => fun i => (M.slots[i]?.map (·.init)).getD 0
  | τ + 1 => M.next (inB τ) (inV τ) (M.state inB inV τ)

/-- The Bool binder values of the reference valuation at time `τ`. -/
def valBAt (M : RefMachine) (inB : Nat → Nat → Bool)
    (inV : Nat → (j : Nat) → (n : Nat) → BitVec n) (τ : Nat) : Nat → Bool :=
  valB M.kIn (inB τ) (M.store (inB τ) (inV τ) (M.state inB inV τ))

/-- The BitVec binder values of the reference valuation at time `τ`. -/
def valVAt (M : RefMachine) (inB : Nat → Nat → Bool)
    (inV : Nat → (j : Nat) → (n : Nat) → BitVec n) (τ : Nat) : (j : Nat) → (n : Nat) → BitVec n :=
  valV M.kIn (inV τ) (M.store (inB τ) (inV τ) (M.state inB inV τ))

/-- **The output of the reference machine** at time `τ`: the field
`[lo + width - 1 : lo]` of the packed transition value. -/
def out (M : RefMachine) (inB : Nat → Nat → Bool)
    (inV : Nat → (j : Nat) → (n : Nat) → BitVec n) (τ lo width : Nat) : Nat :=
  mask width (M.packed (inB τ) (inV τ) (M.state inB inV τ) >>> lo)

end RefMachine

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
theorem machine_ref_trace {declName shape m} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (h : MachinePreserves declName shape bsIn slotBs letBs m)
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
  obtain ⟨ids, nd, len, cache, h⟩ := machine_trace h slotsLen
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw bpos vpos fs c core he hb hv hbody hfit houtfit hscoped
  obtain ⟨regs, regsNd, regsLen, lets, letsLen, trace⟩ :=
    h dom kb kv vw bpos vpos fs core he hb hv hbody hfit houtfit
  refine ⟨regs, regsNd, regsLen, lets, letsLen, ?_⟩
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

end Tools.ShippingMachineRef
