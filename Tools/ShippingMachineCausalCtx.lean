import Tools.ShippingMachineCausal
import Tools.ShippingMachineLoop

/-! # Causality in the inputs AND the state: nested sequential children

`machine_trace_of_data_causal` asks a call's value to be causal in the
state, the inputs fixed. A module whose own endpoint goes through that
theorem (it calls sequential engines) is in turn a CHILD of a larger one
(the ECDSA demo top calls `wSignCore`, which calls the engines); there its
inputs are the parent's signals, and its source must be causal in them.
That needs its calls to be causal in the inputs and the state together.

A context `Ctx` carries the two input families and the state signal;
`CtxAgree x x' t` says they agree up to `t`. A call entry's causality over
contexts (`causal_of_pointwise_ctx`, `field_causal_ctx`) gives the joint
causality of the calls' extension (`machine_ext_causal`, generated), and
with it the source of such a module is causal in its inputs
(`src_causal_of_data_causal`). -/
namespace Tools.ShippingMachineCausal
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness

/-- The inputs and the state a call entry reads. -/
structure Ctx (D : DomainConfig) (σ : Type) where
  B : Nat → Signal D Bool
  V : (j : Nat) → (n : Nat) → Signal D (BitVec n)
  S : Signal D σ

/-- Two contexts agree up to `t`. -/
def CtxAgree {D : DomainConfig} {σ : Type} (x x' : Ctx D σ) (t : Nat) : Prop :=
  (∀ p c, c ≤ t → (x.B p).val c = (x'.B p).val c) ∧
  (∀ p n c, c ≤ t → (x.V p n).val c = (x'.V p n).val c) ∧
  (∀ c, c ≤ t → x.S.val c = x'.S.val c)

theorem CtxAgree.mono {D : DomainConfig} {σ : Type} {x x' : Ctx D σ} {t c : Nat}
    (h : CtxAgree x x' t) (hc : c ≤ t) : CtxAgree x x' c :=
  ⟨fun p c' h' => h.1 p c' (Nat.le_trans h' hc),
   fun p n c' h' => h.2.1 p n c' (Nat.le_trans h' hc),
   fun c' h' => h.2.2 c' (Nat.le_trans h' hc)⟩

theorem CtxAgree.b {D : DomainConfig} {σ : Type} {x x' : Ctx D σ} {t : Nat}
    (h : CtxAgree x x' t) : ∀ p, (x.B p).val t = (x'.B p).val t :=
  fun p => h.1 p t (Nat.le_refl t)

theorem CtxAgree.v {D : DomainConfig} {σ : Type} {x x' : Ctx D σ} {t : Nat}
    (h : CtxAgree x x' t) : ∀ p n, (x.V p n).val t = (x'.V p n).val t :=
  fun p n => h.2.1 p n t (Nat.le_refl t)

/-- Contexts with the same inputs agree when their states do. -/
theorem CtxAgree.of_state {D : DomainConfig} {σ : Type} (B : Nat → Signal D Bool)
    (V : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (S S' : Signal D σ) (t : Nat)
    (h : ∀ c, c ≤ t → S.val c = S'.val c) : CtxAgree ⟨B, V, S⟩ ⟨B, V, S'⟩ t :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, h⟩

/-- A value pointwise in the state and in input families that are causal in
the context is causal in the context. -/
theorem causal_of_pointwise_ctx {D : DomainConfig} {σ α : Type}
    (g : Signal D σ → (Nat → Signal D Bool) → ((j : Nat) → (n : Nat) → Signal D (BitVec n)) →
      Signal D α)
    (FB : Ctx D σ → Nat → Signal D Bool)
    (FV : Ctx D σ → (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (hpt : ∀ (S : Signal D σ) (B : Nat → Signal D Bool)
      (V : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (t : Nat),
      (g S B V).val t = (g ⟨fun _ => S.val t⟩ (fun p => ⟨fun _ => (B p).val t⟩)
        (fun p n => ⟨fun _ => (V p n).val t⟩)).val t)
    (hFB : ∀ (x x' : Ctx D σ) (t : Nat), CtxAgree x x' t → ∀ p, (FB x p).val t = (FB x' p).val t)
    (hFV : ∀ (x x' : Ctx D σ) (t : Nat), CtxAgree x x' t →
      ∀ p n, (FV x p n).val t = (FV x' p n).val t) :
    ∀ (x x' : Ctx D σ) (t : Nat), CtxAgree x x' t →
      (g x.S (FB x) (FV x)).val t = (g x'.S (FB x') (FV x')).val t := by
  intro x x' t h
  rw [hpt x.S (FB x) (FV x) t, hpt x'.S (FB x') (FV x') t, h.2.2 t (Nat.le_refl t)]
  have eB : (fun p => (⟨fun _ => (FB x p).val t⟩ : Signal D Bool)) =
      fun p => ⟨fun _ => (FB x' p).val t⟩ := by
    funext p; rw [hFB x x' t h p]
  have eV : (fun p n => (⟨fun _ => (FV x p n).val t⟩ : Signal D (BitVec n))) =
      fun p n => ⟨fun _ => (FV x' p n).val t⟩ := by
    funext p n; rw [hFV x x' t h p n]
  rw [eB, eV]

/-- `field_causal_call` over contexts. -/
theorem field_causal_ctx {D : DomainConfig} {σ : Type}
    (srcF : (Nat → Signal D Bool) → ((j : Nat) → (n : Nat) → Signal D (BitVec n)) → List (Nat → Nat))
    (famB : Ctx D σ → Nat → Signal D Bool)
    (famV : Ctx D σ → (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (hcall : ∀ (x x' : Ctx D σ) (t : Nat), CtxAgree x x' t →
      ∀ (k : Nat) (f f' : Nat → Nat), (srcF (famB x) (famV x))[k]? = some f →
        (srcF (famB x') (famV x'))[k]? = some f' → f t = f' t)
    (k : Nat) {w : Nat} (field : Ctx D σ → Signal D (BitVec w))
    (hobs : ∀ x, (srcF (famB x) (famV x))[k]? = some (fun t => ((field x).val t).toNat)) :
    ∀ (x x' : Ctx D σ) (t : Nat), CtxAgree x x' t → (field x).val t = (field x').val t := by
  intro x x' t h
  exact BitVec.eq_of_toNat_eq (hcall x x' t h k _ _ (hobs x) (hobs x'))

/-- `field_causal_ctx` for a Bool field. -/
theorem field_causalB_ctx {D : DomainConfig} {σ : Type}
    (srcF : (Nat → Signal D Bool) → ((j : Nat) → (n : Nat) → Signal D (BitVec n)) → List (Nat → Nat))
    (famB : Ctx D σ → Nat → Signal D Bool)
    (famV : Ctx D σ → (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (hcall : ∀ (x x' : Ctx D σ) (t : Nat), CtxAgree x x' t →
      ∀ (k : Nat) (f f' : Nat → Nat), (srcF (famB x) (famV x))[k]? = some f →
        (srcF (famB x') (famV x'))[k]? = some f' → f t = f' t)
    (k : Nat) (field : Ctx D σ → Signal D Bool)
    (hobs : ∀ x, (srcF (famB x) (famV x))[k]? =
      some (fun t => Tools.ShippingMuxLoweringSoundness.encodeBool ((field x).val t))) :
    ∀ (x x' : Ctx D σ) (t : Nat), CtxAgree x x' t → (field x).val t = (field x').val t := by
  intro x x' t h
  have hh : Tools.ShippingMuxLoweringSoundness.encodeBool ((field x).val t) =
      Tools.ShippingMuxLoweringSoundness.encodeBool ((field x').val t) :=
    hcall x x' t h k _ _ (hobs x) (hobs x')
  have e1 := Tools.ShippingMachineChild.encodeBool_ne ((field x).val t)
  have e2 := Tools.ShippingMachineChild.encodeBool_ne ((field x').val t)
  rw [← e1, ← e2, hh]

/-- Causality over contexts moves along an equation at every context. -/
theorem causal_congr_ctx {D : DomainConfig} {σ α : Type} (f g : Ctx D σ → Signal D α)
    (he : ∀ x, f x = g x)
    (hg : ∀ x x' t, CtxAgree x x' t → (g x).val t = (g x').val t) :
    ∀ x x' t, CtxAgree x x' t → (f x).val t = (f x').val t := by
  intro x x' t h; rw [he x, he x']; exact hg x x' t h

/-- **The source of a `circuit do` with causal calls is causal in its
inputs**, from its endpoint's facts and the joint causality of its calls'
extension (`hjoint`, generated as `machine_ext_causal`). -/
theorem src_causal_of_data_causal {declName : Name} (d : MachineData) {ι : Type}
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
    (_ok : d.ok = true)
    (_hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (_hinit : d.initOk inits = true)
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
    (_hcausal : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S S' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (∀ c, c ≤ t → S.val c = S'.val c) →
      (∀ p w, (ext i bools bits S p w).val t = (ext i bools bits S' p w).val t) ∧
      (∀ p, (extB i bools bits S p).val t = (extB i bools bits S' p).val t))
    (hjoint : ∀ (i : ι) (x x' : Ctx (dom i) (HList (tys d.ss))) (t : Nat), CtxAgree x x' t →
      (∀ p w, (ext i x.B x.V x.S p w).val t = (ext i x'.B x'.V x'.S p w).val t) ∧
      (∀ p, (extB i x.B x.V x.S p).val t = (extB i x'.B x'.V x'.S p).val t))
    (i : ι) (B B' : Nat → Signal (dom i) Bool)
    (V V' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat)
    (hb : ∀ p c, c ≤ t → (B p).val c = (B' p).val c)
    (hv : ∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) :
    ∀ (k : Nat) (f f' : Nat → Nat), (src i B V)[k]? = some f → (src i B' V')[k]? = some f' →
      f t = f' t := by
  -- the step of each loop: the next-value terms on its calls at the cycle
  have step : ∀ (Bx : Nat → Signal (dom i) Bool)
      (Vx : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∀ c, (stateLoop inits (body i Bx Vx)).val (c + 1) = evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls
          (extB i Bx Vx (stateLoop inits (body i Bx Vx)))
          (ext i Bx Vx (stateLoop inits (body i Bx Vx))) c
          ((stateLoop inits (body i Bx Vx)).val c)).b (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls
          (extB i Bx Vx (stateLoop inits (body i Bx Vx)))
          (ext i Bx Vx (stateLoop inits (body i Bx Vx))) c
          ((stateLoop inits (body i Bx Vx)).val c)).v (d.vpos j) w) d.nexts := by
    intro Bx Vx
    have hW : ∀ (l l' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
        (∀ c, c ≤ t → l.val c = l'.val c) →
        valsAt (tys d.ss) (writesOn (body i Bx Vx) l) t =
          valsAt (tys d.ss) (writesOn (body i Bx Vx) l') t := by
      intro l l' t h
      show valsAt (tys d.ss) (body i Bx Vx (mkRegList l (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) l)).snd t =
        valsAt (tys d.ss) (body i Bx Vx (mkRegList l' (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) l')).snd t
      obtain ⟨hv, hb⟩ := hjoint i ⟨Bx, Vx, l⟩ ⟨Bx, Vx, l'⟩ t (CtxAgree.of_state Bx Vx l l' t h)
      rw [writes i Bx Vx l t, writes i Bx Vx l' t, h t (Nat.le_refl t),
        typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls (extB i Bx Vx l) (extB i Bx Vx l')
          (ext i Bx Vx l) (ext i Bx Vx l') t (l'.val t) hb hv]
    obtain ⟨_, hs⟩ := circuit_state_causal inits (body i Bx Vx) hW
    intro c
    rw [hs c]
    exact writes i Bx Vx _ c
  -- the two loops agree up to `t`
  have hstate : ∀ c, c ≤ t → ∀ c', c' ≤ c →
      (stateLoop inits (body i B V)).val c' = (stateLoop inits (body i B' V')).val c' := by
    intro c
    induction c with
    | zero =>
      intro _ c' hc'
      have : c' = 0 := by omega
      subst this
      show (stateLoop inits (body i B V)).val 0 = (stateLoop inits (body i B' V')).val 0
      rw [(circuit_state_causal (dom := dom i) inits (body i B V) (fun l l' t h => by
          obtain ⟨hv, hb⟩ := hjoint i ⟨B, V, l⟩ ⟨B, V, l'⟩ t (CtxAgree.of_state B V l l' t h)
          show valsAt (tys d.ss) (body i B V (mkRegList l (tys d.ss) (fun s => s) (fun f => f))
              (mkHolds (tys d.ss) l)).snd t =
            valsAt (tys d.ss) (body i B V (mkRegList l' (tys d.ss) (fun s => s) (fun f => f))
              (mkHolds (tys d.ss) l')).snd t
          rw [writes i B V l t, writes i B V l' t, h t (Nat.le_refl t),
            typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls (extB i B V l) (extB i B V l')
              (ext i B V l) (ext i B V l') t (l'.val t) hb hv])).1,
        (circuit_state_causal (dom := dom i) inits (body i B' V') (fun l l' t h => by
          obtain ⟨hv, hb⟩ := hjoint i ⟨B', V', l⟩ ⟨B', V', l'⟩ t (CtxAgree.of_state B' V' l l' t h)
          show valsAt (tys d.ss) (body i B' V' (mkRegList l (tys d.ss) (fun s => s) (fun f => f))
              (mkHolds (tys d.ss) l)).snd t =
            valsAt (tys d.ss) (body i B' V' (mkRegList l' (tys d.ss) (fun s => s) (fun f => f))
              (mkHolds (tys d.ss) l')).snd t
          rw [writes i B' V' l t, writes i B' V' l' t, h t (Nat.le_refl t),
            typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls (extB i B' V' l) (extB i B' V' l')
              (ext i B' V' l) (ext i B' V' l') t (l'.val t) hb hv])).1]
    | succ c ih =>
      intro hc c' hc'
      by_cases hle : c' ≤ c
      · exact ih (by omega) c' hle
      · have : c' = c + 1 := by omega
        subst this
        have hag : CtxAgree (⟨B, V, stateLoop inits (body i B V)⟩ : Ctx (dom i) _)
            ⟨B', V', stateLoop inits (body i B' V')⟩ c :=
          ⟨fun p c'' h => hb p c'' (by omega), fun p n c'' h => hv p n c'' (by omega),
           fun c'' h => ih (by omega) c'' h⟩
        obtain ⟨hv', hb'⟩ := hjoint i _ _ c hag
        rw [step B V c, step B' V' c, ih (by omega) c (Nat.le_refl c),
          typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls _ _ _ _ c _ hb' hv']
  -- the observations at `t`
  intro k f f' hf hf'
  rw [hsrc i B V] at hf
  rw [hsrc i B' V'] at hf'
  have e1 := congrArg (fun l => l[k]?) (hres i B V (stateLoop inits (body i B V)) t)
  have e2 := congrArg (fun l => l[k]?) (hres i B' V' (stateLoop inits (body i B' V')) t)
  simp only [List.getElem?_map, hf, hf', Option.map_some] at e1 e2
  have hag : CtxAgree (⟨B, V, stateLoop inits (body i B V)⟩ : Ctx (dom i) _)
      ⟨B', V', stateLoop inits (body i B' V')⟩ t :=
    ⟨hb, hv, fun c h => hstate t (Nat.le_refl t) c h⟩
  obtain ⟨hv', hb'⟩ := hjoint i _ _ t hag
  rw [hstate t (Nat.le_refl t) t (Nat.le_refl t),
    typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls _ _ _ _ t _ hb' hv'] at e1
  exact Option.some.inj (e1.trans e2.symm)

/-- **The source of a hand-written `Signal.loop` is causal in its inputs**,
from its endpoint's facts (the arguments of `machine_trace_of_loop`): its
encoded state starts at the reset values and steps by the next-value terms on
the inputs of the cycle. -/
theorem src_causal_of_loop {declName : Name} (d : MachineData) {ι : Type}
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
    (_ok : d.ok = true)
    (_hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (_hinit : d.initOk inits = true)
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
    (i : ι) (B B' : Nat → Signal (dom i) Bool)
    (V V' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat)
    (hb : ∀ p c, c ≤ t → (B p).val c = (B' p).val c)
    (hv : ∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) :
    ∀ (k : Nat) (f₁ f₂ : Nat → Nat), (src i B V)[k]? = some f₁ → (src i B' V')[k]? = some f₂ →
      f₁ t = f₂ t := by
  have stream := fun (Bx : Nat → Signal (dom i) Bool)
      (Vx : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) =>
    Tools.ShippingMachineLoop.loop_stream (f i Bx Vx) (σ i) inits
      (fun t x => evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls Bx Vx t x).b (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls Bx Vx t x).v (d.vpos j) w)
        d.nexts)
      (h0 i Bx Vx) (writes i Bx Vx)
  -- the encoded states agree up to `t`
  have hstate : ∀ c, c ≤ t →
      σ i ((Signal.loop (f i B V)).val c) = σ i ((Signal.loop (f i B' V')).val c) := by
    intro c
    induction c with
    | zero => intro _; rw [(stream B V).1, (stream B' V').1]
    | succ c ih =>
      intro hc
      rw [(stream B V).2 c, (stream B' V').2 c, ih (by omega),
        typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls B B' V V' c _
          (fun p => hb p c (by omega)) (fun p n => hv p n c (by omega))]
  intro k f₁ f₂ hf hf'
  rw [hsrc i B V] at hf
  rw [hsrc i B' V'] at hf'
  have e1 := congrArg (fun l => l[k]?) (hres i B V (Signal.loop (f i B V)) t)
  have e2 := congrArg (fun l => l[k]?) (hres i B' V' (Signal.loop (f i B' V')) t)
  simp only [List.getElem?_map, hf, hf', Option.map_some] at e1 e2
  rw [hstate t (Nat.le_refl t),
    typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls B B' V V' t _
      (fun p => hb p t (Nat.le_refl t)) (fun p n => hv p n t (Nat.le_refl t))] at e1
  exact Option.some.inj (e1.trans e2.symm)

set_option maxHeartbeats 2000000 in
/-- **Source to RTL for a declaration without registers that calls
sequential children** (`machine_trace_of_comb` with the calls' extensions):
the state is the constant `inits`, the calls' values `ext`/`extB` are the
input families at their positions, whatever the children hold. -/
theorem machine_trace_of_comb_calls {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) (inits : HList (tys d.ss))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (hnext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      inits = evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits)
          t inits).b (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits)
          t inits).v (d.vpos j) w)
        d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      (src i bools bits).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits)
            t inits).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits) (ext i bools bits)
            t inits).v (d.vpos k) w)
          o.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceWithB declName d m dom src ext extB :=
  machine_trace_of_streamB d dom inits src ok hbody hinit ext extB
    (fun i bools bits => ⟨fun _ => inits, rfl, fun t => hnext i bools bits t, hres i bools bits⟩)
    hr entry closes

set_option maxHeartbeats 2000000 in
/-- **Source to RTL for a hand-written `Signal.loop` with causal calls**
(`machine_trace_of_loop` with the calls' extensions over the loop's state
signal, causal in it): the loop's step at `t + 1` sees the loop truncated
after `t`, on which causal calls agree with the loop itself up to `t`. -/
theorem machine_trace_of_loop_causal {declName : Name} (d : MachineData) {ι : Type}
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
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceWithB declName d m dom src
      (fun i bools bits => ext i bools bits (Signal.loop (f i bools bits)))
      (fun i bools bits => extB i bools bits (Signal.loop (f i bools bits))) := by
  refine machine_trace_of_streamB d dom inits src ok hbody hinit _ _ ?_ hr entry closes
  intro i bools bits
  refine ⟨fun t => σ i ((Signal.loop (f i bools bits)).val t), ?_, ?_, ?_⟩
  · show σ i (Signal.loopGo (f i bools bits) 0) = inits
    rw [Signal.loopGo_eq]
    exact h0 i bools bits _
  · intro t
    show σ i (Signal.loopGo (f i bools bits) (t + 1)) = _
    rw [Signal.loopGo_eq, writes]
    -- the truncated loop agrees with the loop up to `t`
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

end Tools.ShippingMachineCausal
