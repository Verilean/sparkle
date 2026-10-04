/-
  FFT.Equiv — the proof layer.

  Three obligations, in increasing order of difficulty.  The first two
  are discharged here; the third is stated and reduced to a small set
  of ring/root lemmas.

  1. **Circuit = model.**  `ctWith` at the `Signal` carrier, sampled at
     time `t`, equals `ctWith` at the value carrier applied to the
     inputs sampled at time `t`.  This is the theorem that says the
     hardware description and the reference model are the same
     program — and because they *are* the same program, modulo the
     carrier, the proof is a one-line induction rather than a
     cross-language refinement.

  2. **Pipeline latency.**  The registered network at time `t + m`
     equals the combinational one at time `t`, where `m` is the number
     of radix-2 stages.  This is the statement that makes
     `ctPipelinedLatency` a specification rather than a comment.

  3. **Four-step = Cooley–Tukey.**  Genuinely algebraic: it needs
     commutativity, associativity, distributivity and the root-of-unity
     laws, none of which `FFTAlg` assumes (its instances are BitVec
     circuits, and the fixed-point one satisfies none of them exactly).
     `LawfulFFT` below is the extra hypothesis under which the claim is
     true, and `Zp` satisfies it while `Cx` does not — which is the
     honest statement of what a fixed-point FFT is.
-/
import FFT.Algebra
import FFT.Spec
import FFT.CooleyTukey
import FFT.FourStep

namespace FFTNTT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## 1. Circuit = model

    The combinational carrier's operations are pointwise in time, so
    sampling commutes with the whole butterfly network. -/

section CircuitEquiv
variable {α : Type} [FFTAlg α] {dom : DomainConfig}

/-- Sample a bundle of signals at one instant. -/
@[inline] def sampleAt (t : Nat) {n : Nat} (x : HVec (Signal dom α) n) : HVec α n :=
  fun i => (x i).val t

@[simp] theorem sampleAt_comap {m n : Nat} (t : Nat)
    (f : Fin m → Fin n) (x : HVec (Signal dom α) n) :
    sampleAt t (HVec.comap f x) = HVec.comap f (sampleAt t x) := rfl

/-! Each combinational carrier operation is pointwise in time.  All four
    hold by `rfl` — that is the whole reason the equivalence below is an
    induction and not an argument. -/

@[simp] theorem val_cadd (a b : Signal dom α) (t : Nat) :
    (cadd (α := α) a b).val t = cadd (α := α) (a.val t) (b.val t) := rfl

@[simp] theorem val_csub (a b : Signal dom α) (t : Nat) :
    (csub (α := α) a b).val t = csub (α := α) (a.val t) (b.val t) := rfl

@[simp] theorem val_cmul (w : α) (b : Signal dom α) (t : Nat) :
    (cmul (β := Signal dom α) w b).val t = cmul (β := α) w (b.val t) := rfl

@[simp] theorem val_creg (a : Signal dom α) (t : Nat) :
    (creg (α := α) a).val t = creg (α := α) (a.val t) := rfl

/-- The butterfly network commutes with sampling.

    Everything the combinational carrier does — `Signal.lift2` for
    add/sub, `Signal.map` for the twiddle multiply, `id` for `creg` —
    is defined pointwise on the time index, so this is a structural
    induction with `rfl` at every leaf.  The `if` on `k.val` is on a
    *time-independent* index, which is why it survives the commutation
    untouched; a data-dependent mux would not. -/
theorem ctWith_sampleAt (tw : Nat → Nat → α) :
    ∀ (m : Nat) (x : HVec (Signal dom α) (2 ^ m)) (t : Nat),
      sampleAt t (ctWith (β := Signal dom α) tw m x)
        = ctWith (β := α) tw m (sampleAt t x)
  | 0,     _, _ => rfl
  | m + 1, x, t => by
    funext k
    have hE : (ctWith (β := Signal dom α) tw m (HVec.comap evenIdx x) (halfIdx k)).val t
        = ctWith (β := α) tw m (HVec.comap evenIdx (sampleAt t x)) (halfIdx k) :=
      congrFun (ctWith_sampleAt tw m (HVec.comap evenIdx x) t) (halfIdx k)
    have hO : (ctWith (β := Signal dom α) tw m (HVec.comap oddIdx x) (halfIdx k)).val t
        = ctWith (β := α) tw m (HVec.comap oddIdx (sampleAt t x)) (halfIdx k) :=
      congrFun (ctWith_sampleAt tw m (HVec.comap oddIdx x) t) (halfIdx k)
    show (ctWith (β := Signal dom α) tw (m + 1) x k).val t
        = ctWith (β := α) tw (m + 1) (sampleAt t x) k
    by_cases hk : k.val < 2 ^ m <;>
      simp only [ctWith, HVec.map, hk, if_true, if_false,
                 val_cadd, val_csub, val_cmul, val_creg, hE, hO]

end CircuitEquiv

section CircuitEquivRoot
variable {α : Type} [FFTRoot α] {dom : DomainConfig}

/-- Specialisation to the forward transform: the NTT/FFT circuit
    computes, at every instant, exactly what the reference model
    computes on the inputs present at that instant. -/
theorem ct_sampleAt (m : Nat)
    (x : HVec (Signal dom α) (2 ^ m)) (t : Nat) :
    sampleAt t (ct (β := Signal dom α) m x) = ct (β := α) m (sampleAt t x) :=
  ctWith_sampleAt FFTRoot.twiddle m x t

end CircuitEquivRoot

/-! ## 2. Pipeline latency

    With the pipelined carrier every recursion level inserts one
    register on *both* legs, so the latency is uniform across the
    network and equal to the number of stages. -/

section Latency
variable {α : Type} [FFTAlg α] {dom : DomainConfig}

/-! The pipelined carrier differs from the combinational one in exactly
    one place — `creg` — so its add/sub/mul lemmas are the same `rfl`s,
    and the single interesting step is `val_creg_pipe`: a register read
    at `t+1` is its input at `t`. -/

@[simp] theorem val_cadd_pipe (a b : Signal dom α) (t : Nat) :
    (@cadd _ α (algOnSignalPipelined α) a b).val t
      = FFTAlg.add (a.val t) (b.val t) := rfl

@[simp] theorem val_csub_pipe (a b : Signal dom α) (t : Nat) :
    (@csub _ α (algOnSignalPipelined α) a b).val t
      = FFTAlg.sub (a.val t) (b.val t) := rfl

@[simp] theorem val_cmul_pipe (w : α) (b : Signal dom α) (t : Nat) :
    (@cmul _ α (algOnSignalPipelined α) w b).val t
      = FFTAlg.mul w (b.val t) := rfl

@[simp] theorem val_creg_pipe (a : Signal dom α) (t : Nat) :
    (@creg _ α (algOnSignalPipelined α) a).val (t + 1) = a.val t := rfl

@[simp] theorem val_cadd_comb (a b : Signal dom α) (t : Nat) :
    (cadd (α := α) a b).val t = FFTAlg.add (a.val t) (b.val t) := rfl

@[simp] theorem val_csub_comb (a b : Signal dom α) (t : Nat) :
    (csub (α := α) a b).val t = FFTAlg.sub (a.val t) (b.val t) := rfl

@[simp] theorem val_cmul_comb (w : α) (b : Signal dom α) (t : Nat) :
    (cmul (β := Signal dom α) w b).val t = FFTAlg.mul w (b.val t) := rfl

@[simp] theorem creg_comb (a : Signal dom α) :
    (creg (α := α) a) = a := rfl

/-- The pipelined network at time `t + m` agrees with the
    combinational one at time `t`.

    This is what licenses `ctPipelinedLatency`: a consumer that waits
    `m` cycles after presenting a sample sees the combinational
    answer, and — because the registers are balanced — every output
    bin becomes valid on the same cycle. -/
theorem ctWith_pipelined_delay (tw : Nat → Nat → α) :
    ∀ (m : Nat) (x : HVec (Signal dom α) (2 ^ m)) (t : Nat) (k : Fin (2 ^ m)),
      (@ctWith (Signal dom α) α (algOnSignalPipelined α) tw m x k).val (t + m)
        = (ctWith (β := Signal dom α) tw m x k).val t
  | 0,     _, _, _ => rfl
  | m + 1, x, t, k => by
    have hE := ctWith_pipelined_delay tw m (HVec.comap evenIdx x) t (halfIdx k)
    have hO := ctWith_pipelined_delay tw m (HVec.comap oddIdx  x) t (halfIdx k)
    have ht : t + (m + 1) = (t + m) + 1 := by omega
    rw [ht]
    by_cases hk : k.val < 2 ^ m <;>
      simp only [ctWith, HVec.map, hk, if_true, if_false,
                 val_cadd_pipe, val_csub_pipe, val_cmul_pipe, val_creg_pipe,
                 val_cadd_comb, val_csub_comb, val_cmul_comb, creg_comb,
                 hE, hO]

end Latency

section LatencyRoot
variable {α : Type} [FFTRoot α] {dom : DomainConfig}

/-- The forward pipelined FFT/NTT is the combinational one delayed by
    `ctPipelinedLatency m` cycles. -/
theorem ctPipelined_delay (m : Nat)
    (x : HVec (Signal dom α) (2 ^ m)) (t : Nat) (k : Fin (2 ^ m)) :
    (ctPipelined α m x k).val (t + ctPipelinedLatency m)
      = (ct (β := Signal dom α) m x k).val t := by
  exact ctWith_pipelined_delay FFTRoot.twiddle m x t k

/-- Composed with `ct_sampleAt`: what comes out of the pipelined
    circuit `m` cycles later is what the *value-level* model produces
    from the inputs that went in. -/
theorem ctPipelined_eq_model (m : Nat)
    (x : HVec (Signal dom α) (2 ^ m)) (t : Nat) :
    (fun k => (ctPipelined α m x k).val (t + ctPipelinedLatency m))
      = ct (β := α) m (sampleAt t x) := by
  funext k
  rw [ctPipelined_delay]
  exact congrFun (ct_sampleAt m x t) k

end LatencyRoot

/-! ## 3. Four-step = Cooley–Tukey

    The remaining obligation is algebraic, not structural, so it needs
    hypotheses that `FFTAlg` deliberately does not carry. -/

/-- The laws the four-step derivation actually uses.

    `Zp p w` satisfies all of these (its operations *are* `ZMod p`'s,
    and `twiddle n k = g^{k(p−1)/n}` makes the root laws hold by
    exponent arithmetic).  `Cx w f` satisfies none of them exactly:
    fixed-point addition wraps and fixed-point multiplication rounds,
    so it is neither associative nor distributive.  That asymmetry is
    the real content of "an NTT is exact and an FFT is not", and
    stating it as a separate class keeps it visible instead of hiding
    it in a comment. -/
class LawfulFFT (α : Type) extends FFTRoot α where
  add_comm    : ∀ a b : α, add a b = add b a
  add_assoc   : ∀ a b c : α, add (add a b) c = add a (add b c)
  add_zero    : ∀ a : α, add a zero = a
  mul_comm    : ∀ a b : α, mul a b = mul b a
  mul_assoc   : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  mul_one     : ∀ a : α, mul a one = a
  left_distrib : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  sub_eq      : ∀ a b : α, sub a b = add a (mul (twiddle 2 1) b)
  /-- `ω_n^0 = 1`. -/
  tw_zero     : ∀ n : Nat, twiddle n 0 = one
  /-- `ω_n^{j+k} = ω_n^j · ω_n^k`. -/
  tw_add      : ∀ n j k : Nat, twiddle n (j + k) = mul (twiddle n j) (twiddle n k)
  /-- `ω_n` has order `n`, so the exponent may be reduced mod `n`. -/
  tw_mod      : ∀ n k : Nat, twiddle n (k % n) = twiddle n k
  /-- Consistency across sizes: `ω_{n·m}^m = ω_n`. -/
  tw_split    : ∀ n m k : Nat, twiddle (n * m) (m * k) = twiddle n k

/-- The target theorem.

    `dftFourStep n1 n2 = dft (n1 * n2)` — the four-step index algebra
    is correct — and hence, composed with `ct = dft`,
    `ctFourStep m1 m2 = ct (m1 + m2)`.

    Proving it means reindexing a sum over `Fin (n1*n2)` as a double
    sum over `Fin n1 × Fin n2`, which over `Fin.foldr` (an *ordered*
    fold, chosen deliberately so the fixed-point instance is bit-exact)
    requires the commutativity and associativity above to justify the
    reordering.  That reindexing lemma is the next piece of work; the
    statement is fixed here so the two halves can be developed
    independently. -/
def dftFourStep_eq_dft_statement : Prop :=
  ∀ (α : Type) [LawfulFFT α] (n1 n2 : Nat) (x : HVec α (n1 * n2)),
    dftFourStep (β := α) n1 n2 x = dft (β := α) (n1 * n2) x

end FFTNTT
