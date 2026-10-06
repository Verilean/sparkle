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

end Tools.ShippingLoopFusion
