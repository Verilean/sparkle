import Sparkle.Core.Signal

/-! # Nested hand-written loops are one loop

A loop body made of registers is GUARDED: its value at `t` is fixed by its
argument at the cycles before `t`. A guarded body has exactly one fixpoint,
and `Signal.loop` is it (`loop_fix`, `loop_unique`). So a loop whose body
holds another loop over its state — the H.264 frame encoder's FSM around its
inlined encoder / decoder / CAVLC pipelines — equals ONE loop over the pair
of states (`loop_nest`): the pair (outer loop, inner loop on it) is a
fixpoint of the combined body, which is guarded when both bodies are. -/
namespace Tools.ShippingLoopFusion
open Sparkle.Core.Domain Sparkle.Core.Signal

variable {D : DomainConfig}

/-- The value at `t` is fixed by the argument before `t`. -/
def Guarded {α β : Type} (h : Signal D α → Signal D β) : Prop :=
  ∀ (x y : Signal D α) (t : Nat), (∀ s, s < t → x.val s = y.val s) → (h x).val t = (h y).val t

/-- A loop is a fixpoint of its guarded body. -/
theorem loop_fix {α : Type} [Inhabited α] (h : Signal D α → Signal D α) (hg : Guarded h) :
    h (Signal.loop h) = Signal.loop h := by
  cases hl : Signal.loop h with
  | mk lv =>
  have hv : ∀ t, lv t = Signal.loopGo h t := fun t => by
    have := congrArg (fun s => s.val t) hl
    exact this.symm
  show h ⟨lv⟩ = ⟨lv⟩
  cases hh : h ⟨lv⟩ with
  | mk hv' =>
  congr 1
  funext t
  have e1 := congrArg (fun s => s.val t) hh
  simp only at e1
  rw [← e1, hv t, Signal.loopGo_eq]
  apply hg
  intro s hs
  show lv s = if s < t then Signal.loopGo h s else default
  rw [if_pos hs, hv s]

/-- A guarded body has exactly one fixpoint: the loop. -/
theorem loop_unique {α : Type} [Inhabited α] (h : Signal D α → Signal D α) (hg : Guarded h)
    (x : Signal D α) (hx : h x = x) : x = Signal.loop h := by
  have key : ∀ t, ∀ s, s ≤ t → x.val s = Signal.loopGo h s := by
    intro t
    induction t with
    | zero =>
      intro s hs
      have : s = 0 := by omega
      subst this
      rw [← hx, Signal.loopGo_eq]
      apply hg
      intro s hs; omega
    | succ t ih =>
      intro s hs
      by_cases hle : s ≤ t
      · exact ih s hle
      · have : s = t + 1 := by omega
        subst this
        rw [← hx, Signal.loopGo_eq]
        apply hg
        intro s' hs'
        show x.val s' = if s' < t + 1 then Signal.loopGo h s' else default
        rw [if_pos hs', ih s' (by omega)]
  cases x with
  | mk xv =>
  show (⟨xv⟩ : Signal D α) = ⟨fun t => Signal.loopGo h t⟩
  congr 1
  funext t
  exact key t t (Nat.le_refl t)

/-- Guarded in two arguments jointly. -/
def Guarded2 {α β γ : Type} (h : Signal D α → Signal D β → Signal D γ) : Prop :=
  ∀ (x x' : Signal D α) (y y' : Signal D β) (t : Nat),
    (∀ s, s < t → x.val s = x'.val s ∧ y.val s = y'.val s) → (h x y).val t = (h x' y').val t

/-- A loop over a parameter is fixed, up to `t`, by the parameter before `t`. -/
theorem loop_param {α β : Type} [Inhabited β] (G : Signal D α → Signal D β → Signal D β)
    (hG : Guarded2 G) (l l' : Signal D α) (t : Nat) (hl : ∀ s, s < t → l.val s = l'.val s) :
    ∀ s, s ≤ t → (Signal.loop (G l)).val s = (Signal.loop (G l')).val s := by
  have key : ∀ n, ∀ s, s ≤ n → s ≤ t →
      (Signal.loop (G l)).val s = (Signal.loop (G l')).val s := by
    intro n
    induction n with
    | zero =>
      intro s hn hs
      have : s = 0 := by omega
      subst this
      show Signal.loopGo (G l) 0 = Signal.loopGo (G l') 0
      rw [Signal.loopGo_eq, Signal.loopGo_eq (G l')]
      apply hG
      intro s' hs'; omega
    | succ n ih =>
      intro s hn hs
      by_cases hle : s ≤ n
      · exact ih s hle hs
      · show Signal.loopGo (G l) s = Signal.loopGo (G l') s
        rw [Signal.loopGo_eq, Signal.loopGo_eq (G l')]
        apply hG
        intro s' hs'
        refine ⟨hl s' (by omega), ?_⟩
        show (if s' < s then Signal.loopGo (G l) s' else default) =
          (if s' < s then Signal.loopGo (G l') s' else default)
        rw [if_pos hs', if_pos hs']
        exact ih s' (by omega) (by omega)
  intro s hs
  exact key s s (Nat.le_refl s) hs

/-- The pair of two signals. -/
def pairS {α β : Type} (a : Signal D α) (b : Signal D β) : Signal D (α × β) :=
  ⟨fun t => (a.val t, b.val t)⟩

/-- The components of a pair signal. -/
def fstS {α β : Type} (p : Signal D (α × β)) : Signal D α := ⟨fun t => (p.val t).1⟩
def sndS {α β : Type} (p : Signal D (α × β)) : Signal D β := ⟨fun t => (p.val t).2⟩

/-- The combined body over the pair of states. -/
def fuse {α β : Type} (F : Signal D α → Signal D β → Signal D α)
    (G : Signal D α → Signal D β → Signal D β) (p : Signal D (α × β)) : Signal D (α × β) :=
  pairS (F (fstS p) (sndS p)) (G (fstS p) (sndS p))

theorem fuse_guarded {α β : Type} (F : Signal D α → Signal D β → Signal D α)
    (G : Signal D α → Signal D β → Signal D β) (hF : Guarded2 F) (hG : Guarded2 G) :
    Guarded (fuse F G) := by
  intro x y t h
  have h' : ∀ s, s < t → (fstS x).val s = (fstS y).val s ∧ (sndS x).val s = (sndS y).val s :=
    fun s hs => by
      have := h s hs
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  show ((F (fstS x) (sndS x)).val t, (G (fstS x) (sndS x)).val t) =
    ((F (fstS y) (sndS y)).val t, (G (fstS y) (sndS y)).val t)
  rw [hF _ _ _ _ t h', hG _ _ _ _ t h']

/-- **Nested loops are one loop**: a loop whose body reads an inner loop over
its state is the first component of the loop over the pair, and the inner
loop on it the second, when both bodies are guarded. -/
theorem loop_nest {α β : Type} [Inhabited α] [Inhabited β]
    (F : Signal D α → Signal D β → Signal D α) (G : Signal D α → Signal D β → Signal D β)
    (hF : Guarded2 F) (hG : Guarded2 G) :
    Signal.loop (fun l => F l (Signal.loop (G l))) = fstS (Signal.loop (fuse F G)) ∧
    Signal.loop (G (Signal.loop (fun l => F l (Signal.loop (G l))))) =
      sndS (Signal.loop (fuse F G)) := by
  -- the outer body is guarded: the inner loop is fixed by the state before `t`
  have hf : Guarded (fun l => F l (Signal.loop (G l))) := by
    intro x y t h
    apply hF
    intro s hs
    refine ⟨h s hs, ?_⟩
    exact loop_param G hG x y (t - 1) (fun s' hs' => h s' (by omega)) s (by omega)
  let A := Signal.loop (fun l => F l (Signal.loop (G l)))
  let B := Signal.loop (G A)
  have hA : F A B = A := loop_fix _ hf
  have hGA : Guarded (G A) := fun x y t h => hG A A x y t (fun s hs => ⟨rfl, h s hs⟩)
  have hB : G A B = B := loop_fix _ hGA
  have hP : fuse F G (pairS A B) = pairS A B := by
    show pairS (F A B) (G A B) = pairS A B
    rw [hA, hB]
  have hu := loop_unique _ (fuse_guarded F G hF hG) (pairS A B) hP
  constructor
  · show A = fstS (Signal.loop (fuse F G))
    rw [← hu]; rfl
  · show B = sndS (Signal.loop (fuse F G))
    rw [← hu]; rfl

/-! ## Guardedness from the body's shape -/

/-- Fixed by the argument up to `t` (inclusive). -/
def Causal {α γ : Type} (e : Signal D α → Signal D γ) : Prop :=
  ∀ (x y : Signal D α) (t : Nat), (∀ s, s ≤ t → x.val s = y.val s) → (e x).val t = (e y).val t

/-- A register over a causal input is guarded. -/
theorem register_guarded {α γ : Type} (init : γ) (e : Signal D α → Signal D γ) (he : Causal e) :
    Guarded (fun x => Signal.register init (e x)) := by
  intro x y t h
  cases t with
  | zero => rfl
  | succ n =>
    show (e x).val n = (e y).val n
    exact he x y n (fun s hs => h s (by omega))

/-- A pair of guarded values is guarded. -/
theorem bundle2_guarded {α β γ : Type} (a : Signal D α → Signal D β) (b : Signal D α → Signal D γ)
    (ha : Guarded a) (hb : Guarded b) : Guarded (fun x => Sparkle.Core.Signal.bundle2 (a x) (b x)) := by
  intro x y t h
  show ((a x).val t, (b x).val t) = ((a y).val t, (b y).val t)
  rw [ha x y t h, hb x y t h]

/-- Guarded is causal. -/
theorem Guarded.causal {α γ : Type} {h : Signal D α → Signal D γ} (hg : Guarded h) : Causal h :=
  fun x y t hxy => hg x y t (fun s hs => hxy s (Nat.le_of_lt hs))

/-- A loop over a causal parameter is causal in the parameter. -/
theorem loop_causal {α β : Type} [Inhabited β] (G : Signal D α → Signal D β → Signal D β)
    (hG : Guarded2 G) : Causal (fun l => Signal.loop (G l)) := by
  intro x y t h
  -- the parameter agrees up to `t`, so before `t + 1`
  exact loop_param G hG x y (t + 1) (fun s hs => h s (by omega)) t (by omega)

/-- `Guarded2` from `Guarded` of the pair. -/
theorem Guarded2.of_pair {α β γ : Type} (h : Signal D α → Signal D β → Signal D γ)
    (hp : Guarded (fun p : Signal D (α × β) => h (fstS p) (sndS p))) : Guarded2 h := by
  intro x x' y y' t hxy
  have := hp (pairS x y) (pairS x' y') t (fun s hs => by
    show (x.val s, y.val s) = (x'.val s, y'.val s)
    rw [(hxy s hs).1, (hxy s hs).2])
  exact this

/-- **Independent loops over one parameter are one loop over the product.** -/
theorem loop_prod {α β γ : Type} [Inhabited β] [Inhabited γ]
    (G₁ : Signal D α → Signal D β → Signal D β) (G₂ : Signal D α → Signal D γ → Signal D γ)
    (h₁ : Guarded2 G₁) (h₂ : Guarded2 G₂) (l : Signal D α) :
    pairS (Signal.loop (G₁ l)) (Signal.loop (G₂ l)) =
      Signal.loop (fun q => pairS (G₁ l (fstS q)) (G₂ l (sndS q))) := by
  apply loop_unique
  · intro x y t h
    show ((G₁ l (fstS x)).val t, (G₂ l (sndS x)).val t) = ((G₁ l (fstS y)).val t, (G₂ l (sndS y)).val t)
    rw [h₁ l l (fstS x) (fstS y) t (fun s hs => ⟨rfl, congrArg Prod.fst (h s hs)⟩),
      h₂ l l (sndS x) (sndS y) t (fun s hs => ⟨rfl, congrArg Prod.snd (h s hs)⟩)]
  · have e₁ : G₁ l (Signal.loop (G₁ l)) = Signal.loop (G₁ l) :=
      loop_fix _ (fun x y t h => h₁ l l x y t (fun s hs => ⟨rfl, h s hs⟩))
    have e₂ : G₂ l (Signal.loop (G₂ l)) = Signal.loop (G₂ l) :=
      loop_fix _ (fun x y t h => h₂ l l x y t (fun s hs => ⟨rfl, h s hs⟩))
    show pairS (G₁ l (Signal.loop (G₁ l))) (G₂ l (Signal.loop (G₂ l))) = _
    rw [e₁, e₂]

/-- Guarded in three arguments jointly. -/
def Guarded3 {α β γ δ : Type} (h : Signal D α → Signal D β → Signal D γ → Signal D δ) : Prop :=
  ∀ (x x' : Signal D α) (y y' : Signal D β) (z z' : Signal D γ) (t : Nat),
    (∀ s, s < t → x.val s = x'.val s ∧ y.val s = y'.val s ∧ z.val s = z'.val s) →
    (h x y z).val t = (h x' y' z').val t

/-- **A chain of loops over one parameter is one loop**: the second reads the
first's state; both are the components of one loop over the pair. -/
theorem loop_chain {α β γ : Type} [Inhabited β] [Inhabited γ]
    (G₁ : Signal D α → Signal D β → Signal D β)
    (G₂ : Signal D α → Signal D β → Signal D γ → Signal D γ)
    (h₁ : Guarded2 G₁) (h₂ : Guarded3 G₂) (l : Signal D α) :
    pairS (Signal.loop (G₁ l)) (Signal.loop (G₂ l (Signal.loop (G₁ l)))) =
      Signal.loop (fun q => pairS (G₁ l (fstS q)) (G₂ l (fstS q) (sndS q))) := by
  apply loop_unique
  · intro x y t h
    show ((G₁ l (fstS x)).val t, (G₂ l (fstS x) (sndS x)).val t) =
      ((G₁ l (fstS y)).val t, (G₂ l (fstS y) (sndS y)).val t)
    rw [h₁ l l (fstS x) (fstS y) t (fun s hs => ⟨rfl, congrArg Prod.fst (h s hs)⟩),
      h₂ l l (fstS x) (fstS y) (sndS x) (sndS y) t
        (fun s hs => ⟨rfl, congrArg Prod.fst (h s hs), congrArg Prod.snd (h s hs)⟩)]
  · have e₁ : G₁ l (Signal.loop (G₁ l)) = Signal.loop (G₁ l) :=
      loop_fix _ (fun x y t h => h₁ l l x y t (fun s hs => ⟨rfl, h s hs⟩))
    have e₂ : G₂ l (Signal.loop (G₁ l)) (Signal.loop (G₂ l (Signal.loop (G₁ l)))) =
        Signal.loop (G₂ l (Signal.loop (G₁ l))) :=
      loop_fix _ (fun x y t h => h₂ l l _ _ x y t (fun s hs => ⟨rfl, rfl, h s hs⟩))
    show pairS (G₁ l (Signal.loop (G₁ l))) (G₂ l (Signal.loop (G₁ l))
      (Signal.loop (G₂ l (Signal.loop (G₁ l))))) = _
    rw [e₁, e₂]

/-! ## Causality of a body's register inputs

A register input is pointwise in the state except for the memory reads in it
(their contents are the writes of earlier cycles). The memory values are read
from a family `V` at their positions; the rest is pointwise (a `rfl` per
declaration), so the input is causal when the memory reads are. -/

/-- `Guarded3` from `Guarded` of the nested pair. -/
theorem Guarded3.of_pair {α β γ δ : Type} (h : Signal D α → Signal D β → Signal D γ → Signal D δ)
    (hp : Guarded (fun p : Signal D (α × (β × γ)) => h (fstS p) (fstS (sndS p)) (sndS (sndS p)))) :
    Guarded3 h := by
  intro x x' y y' z z' t hxyz
  exact hp (pairS x (pairS y z)) (pairS x' (pairS y' z')) t (fun s hs => by
    show (x.val s, (y.val s, z.val s)) = (x'.val s, (y'.val s, z'.val s))
    rw [(hxyz s hs).1, (hxyz s hs).2.1, (hxyz s hs).2.2])

/-- Pointwise in the state and a family of memory values that is causal:
causal. -/
theorem causal_of_pointwise_V {σ γ : Type}
    (g : Signal D σ → ((j : Nat) → (n : Nat) → Signal D (BitVec n)) → Signal D γ)
    (FV : Signal D σ → (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (hpt : ∀ (S : Signal D σ) (V : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (t : Nat),
      (g S V).val t = (g ⟨fun _ => S.val t⟩ (fun p n => ⟨fun _ => (V p n).val t⟩)).val t)
    (hFV : ∀ (S S' : Signal D σ) (t : Nat), (∀ s, s ≤ t → S.val s = S'.val s) →
      ∀ p n, (FV S p n).val t = (FV S' p n).val t) :
    Causal (fun S => g S (FV S)) := by
  intro S S' t h
  show (g S (FV S)).val t = (g S' (FV S')).val t
  rw [hpt S (FV S) t, hpt S' (FV S') t, h t (Nat.le_refl t)]
  have eV : (fun p n => (⟨fun _ => (FV S p n).val t⟩ : Signal D (BitVec n))) =
      fun p n => ⟨fun _ => (FV S' p n).val t⟩ := by
    funext p n; rw [hFV S S' t h p n]
  rw [eV]

/-- A family extended at one position, agreeing where both parts agree. -/
def extV (V : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (pos w : Nat) (sig : Signal D (BitVec w)) :
    (j : Nat) → (n : Nat) → Signal D (BitVec n) :=
  fun j n => if h : j = pos ∧ n = w then cast (by rw [h.2]) sig else V j n

theorem extV_val {V V' : (j : Nat) → (n : Nat) → Signal D (BitVec n)} {pos w : Nat}
    {sig sig' : Signal D (BitVec w)} {t : Nat}
    (hV : ∀ j n, (V j n).val t = (V' j n).val t) (hs : sig.val t = sig'.val t) :
    ∀ j n, (extV V pos w sig j n).val t = (extV V' pos w sig' j n).val t := by
  intro j n
  unfold extV
  by_cases h : j = pos ∧ n = w
  · rw [dif_pos h, dif_pos h]
    obtain ⟨_, rfl⟩ := h
    exact hs
  · rw [dif_neg h, dif_neg h]; exact hV j n

theorem extV_self (V : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (pos w : Nat)
    (sig : Signal D (BitVec w)) : extV V pos w sig pos w = sig := by
  simp [extV]

theorem extV_ne (V : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (pos w : Nat)
    (sig : Signal D (BitVec w)) (j n : Nat) (h : j ≠ pos) : extV V pos w sig j n = V j n := by
  simp [extV, h]

/-- A combinational-read memory is causal in the state when its operands are. -/
theorem memoryComboRead_causal {σ : Type} {aw dw : Nat}
    (wa : Signal D σ → Signal D (BitVec aw)) (wd : Signal D σ → Signal D (BitVec dw))
    (we : Signal D σ → Signal D Bool) (ra : Signal D σ → Signal D (BitVec aw))
    (hwa : Causal wa) (hwd : Causal wd) (hwe : Causal we) (hra : Causal ra) :
    Causal (fun S => Signal.memoryComboRead (wa S) (wd S) (we S) (ra S)) := by
  intro S S' t h
  show Signal.memState _ (wa S) (wd S) (we S) t ((ra S).val t) =
    Signal.memState _ (wa S') (wd S') (we S') t ((ra S').val t)
  have hm : ∀ n, n ≤ t → Signal.memState (fun _ => 0#dw) (wa S) (wd S) (we S) n =
      Signal.memState (fun _ => 0#dw) (wa S') (wd S') (we S') n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      funext a
      have hc : ∀ s, s ≤ n → S.val s = S'.val s := fun s hs => h s (by omega)
      rw [Signal.memState_succ, Signal.memState_succ, hwa S S' n hc, hwd S S' n hc,
        hwe S S' n hc, ih (by omega)]
  rw [hm t (Nat.le_refl t), hra S S' t h]

/-- A registered-read memory is causal in the state when its operands are. -/
theorem memory_causal {σ : Type} {aw dw : Nat}
    (wa : Signal D σ → Signal D (BitVec aw)) (wd : Signal D σ → Signal D (BitVec dw))
    (we : Signal D σ → Signal D Bool) (ra : Signal D σ → Signal D (BitVec aw))
    (hwa : Causal wa) (hwd : Causal wd) (hwe : Causal we) (hra : Causal ra) :
    Causal (fun S => Signal.memory (wa S) (wd S) (we S) (ra S)) := by
  intro S S' t h
  cases t with
  | zero => rfl
  | succ n =>
    have hc : ∀ s, s ≤ n → S.val s = S'.val s := fun s hs => h s (by omega)
    have := memoryComboRead_causal wa wd we ra hwa hwd hwe hra S S' n hc
    show Signal.memState _ (wa S) (wd S) (we S) n ((ra S).val n) =
      Signal.memState _ (wa S') (wd S') (we S') n ((ra S').val n)
    exact this

end Tools.ShippingLoopFusion
