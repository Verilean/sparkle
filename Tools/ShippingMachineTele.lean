import Tools.ShippingMachineFuse

/-! # Chains of sub-machines: each reading the earlier ones' results

`ShippingMachineFuse` covers sub-machines that read the enclosing handles
only. A chain — a parser bound by `let`, then an emitter whose input is the
parser's result (`hftStrategy`) — has a sub-machine reading an EARLIER
sub-machine's result. The compiler flattens it the same way (one machine,
the enclosing slots, then each sub-machine's in reading order), and the
emitter's transition reads the parser's slots.

A chain is a telescope (`Tele`): each sub-machine's body reads the enclosing
handles and the tuple of the earlier sub-machines' results (`pre`, the
latest first). With the per-declaration pointwiseness of all the writes in
all the states (one `rfl`, as for `Inner`), the tuple of all the loops'
values starts at the reset values and advances by the writes — the same
recurrence as `fused_state`, for a chain. -/
namespace Tools.ShippingMachineTele
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource Tools.ShippingMachineFuse

variable {dom : DomainConfig}

/-- Sub-machines in reading order over the enclosing slots `αs`, each body
reading the enclosing handles and the earlier results (`pre`, latest
first). -/
inductive Tele (dom : DomainConfig) (αs : List Type) : List Type → Type 1 where
  | nil {pre : List Type} : Tele dom αs pre
  | cons {pre : List Type} (βs : List Type) (inh : Inhabited (HList βs)) (ρ : Type)
      (inits : HList βs)
      (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList pre →
        RegList dom (HList βs) (Circuit.SigList dom βs) βs → Circuit dom (Circuit.SigList dom βs) ρ)
      (rest : Tele dom αs (ρ :: pre)) : Tele dom αs pre

namespace Tele
variable {αs : List Type}

/-- The result types, in reading order. -/
def ρs : {pre : List Type} → Tele dom αs pre → List Type
  | _, .nil => []
  | _, .cons _ _ ρ _ _ rest => ρ :: ρs rest

/-- The state types, in reading order. -/
def σs : {pre : List Type} → Tele dom αs pre → List Type
  | _, .nil => []
  | _, .cons βs _ _ _ _ rest => HList βs :: σs rest

/-- One state signal per sub-machine. -/
def Sigs : {pre : List Type} → Tele dom αs pre → Type
  | _, .nil => Unit
  | _, .cons βs _ _ _ _ rest => Signal dom (HList βs) × Sigs rest

/-- The results on given states, each sub-machine fed the earlier ones. -/
def resultsOn (regs : RegList dom (HList αs) (Circuit.SigList dom αs) αs) :
    {pre : List Type} → (t : Tele dom αs pre) → HList pre → Sigs t → HList (ρs t)
  | _, .nil, _, _ => ()
  | _, .cons βs _ _ _ body rest, prev, Ss =>
    let r := resOn (body regs prev) Ss.1
    (r, resultsOn regs rest (r, prev) Ss.2)

/-- Each sub-machine on its own loop, fed the earlier ones on theirs. -/
def loops (regs : RegList dom (HList αs) (Circuit.SigList dom αs) αs) :
    {pre : List Type} → (t : Tele dom αs pre) → HList pre → Sigs t
  | _, .nil, _ => ()
  | _, .cons βs inh _ inits body rest, prev =>
    let L := @stateLoop dom βs _ inh inits (body regs prev)
    (L, loops regs rest (resOn (body regs prev) L, prev))

/-- The values of the states at a cycle. -/
def valsOf : {pre : List Type} → (t : Tele dom αs pre) → Sigs t → Nat → HList (σs t)
  | _, .nil, _, _ => ()
  | _, .cons _ _ _ _ _ rest, Ss, n => (Ss.1.val n, valsOf rest Ss.2 n)

/-- Constant state signals. -/
def constOf : {pre : List Type} → (t : Tele dom αs pre) → HList (σs t) → Sigs t
  | _, .nil, _ => ()
  | _, .cons _ _ _ _ _ rest, xs => (⟨fun _ => xs.1⟩, constOf rest xs.2)

theorem valsOf_constOf : ∀ {pre : List Type} (t : Tele dom αs pre) (xs : HList (σs t)) (n : Nat),
    valsOf t (constOf t xs) n = xs
  | _, .nil, _, _ => rfl
  | _, .cons _ _ _ _ _ rest, xs, n => by
    show (xs.1, valsOf rest (constOf rest xs.2) n) = xs
    rw [valsOf_constOf rest xs.2 n]
    rfl

/-- The reset values. -/
def initsOf : {pre : List Type} → (t : Tele dom αs pre) → HList (σs t)
  | _, .nil => ()
  | _, .cons _ _ _ inits _ rest => (inits, initsOf rest)

/-- The values at a cycle of every sub-machine's pending writes, on given
states. -/
def writesAt (regs : RegList dom (HList αs) (Circuit.SigList dom αs) αs) :
    {pre : List Type} → (t : Tele dom αs pre) → HList pre → Sigs t → Nat → HList (σs t)
  | _, .nil, _, _, _ => ()
  | _, .cons βs _ _ _ body rest, prev, Ss, n =>
    (valsAt βs (writesOn (body regs prev) Ss.1) n,
      writesAt regs rest (resOn (body regs prev) Ss.1, prev) Ss.2 n)

end Tele

open Tele

/-- Pointwiseness of a chain's writes in the enclosing state and in all the
sub-machines' states (from the top, no earlier results): a `rfl` per
declaration, `F` the typed evaluation of the next-value terms. -/
def TelePointwise {αs : List Type} (t : Tele dom αs [])
    (F : HList αs → HList (σs t) → Nat → HList (σs t)) : Prop :=
  ∀ (S : Signal dom (HList αs)) (Ss : Sigs t) (n : Nat),
    writesAt (regsOf αs S) t () Ss n = F (S.val n) (valsOf t Ss n) n

/-- The loops' recurrence, for a chain fed given earlier results: if the
writes (fed those results computed on the given states) are a function `F`
of the values at the cycle, every loop starts at its reset value and steps
by `F`. Stated for any position in the chain (`prev` the earlier results as
a function of the earlier states, `xs₀` their values). -/
theorem loops_rec {αs : List Type} (S : Signal dom (HList αs)) :
    ∀ {pre : List Type} (t : Tele dom αs pre) (prev : HList pre)
      (F : HList (σs t) → Nat → HList (σs t)),
      (∀ (Ss : Sigs t) (n : Nat), writesAt (regsOf αs S) t prev Ss n = F (valsOf t Ss n) n) →
      valsOf t (loops (regsOf αs S) t prev) 0 = initsOf t ∧
      ∀ n, valsOf t (loops (regsOf αs S) t prev) (n + 1) =
        F (valsOf t (loops (regsOf αs S) t prev) n) n
  | _, .nil, _, _, _ => ⟨rfl, fun _ => rfl⟩
  | _, .cons βs inh ρ inits body rest, prev, F, hF => by
    -- the head's writes are pointwise in its own state (the rest held at its loops)
    let L := @stateLoop dom βs _ inh inits (body (regsOf αs S) prev)
    have hW : ∀ (l l' : Signal dom (HList βs)) (n : Nat), l.val n = l'.val n →
        valsAt βs (body (regsOf αs S) prev (mkRegList l βs (fun s => s) (fun f => f))
          (mkHolds βs l)).snd n =
        valsAt βs (body (regsOf αs S) prev (mkRegList l' βs (fun s => s) (fun f => f))
          (mkHolds βs l')).snd n := by
      intro l l' n h
      -- only the head component is compared: read the head's writes through
      -- state tuples with the SAME rest
      have g1 := hF (l, loops (regsOf αs S) rest (resOn (body (regsOf αs S) prev) L, prev)) n
      have g2 := hF (l', loops (regsOf αs S) rest (resOn (body (regsOf αs S) prev) L, prev)) n
      have hv : valsOf (.cons βs inh ρ inits body rest)
            (l, loops (regsOf αs S) rest (resOn (body (regsOf αs S) prev) L, prev)) n =
          valsOf (.cons βs inh ρ inits body rest)
            (l', loops (regsOf αs S) rest (resOn (body (regsOf αs S) prev) L, prev)) n := by
        show (l.val n, _) = (l'.val n, _)
        rw [h]
      rw [hv] at g1
      have := congrArg Prod.fst (g1.trans g2.symm)
      exact this
    obtain ⟨h0, hs⟩ := @circuit_state dom βs ρ inh inits (body (regsOf αs S) prev) hW
    -- the rest, fed the head's result on its loop
    obtain ⟨r0, rs⟩ := loops_rec S rest (resOn (body (regsOf αs S) prev) L, prev)
      (fun xs n => (F (L.val n, xs) n).2) (by
        intro Ss n
        have h := hF (L, Ss) n
        exact congrArg Prod.snd h)
    constructor
    · show (L.val 0, valsOf rest (loops (regsOf αs S) rest _) 0) = _
      rw [r0, h0]
      rfl
    · intro n
      show (L.val (n + 1), valsOf rest (loops (regsOf αs S) rest _) (n + 1)) = _
      rw [rs n, hs n]
      have h := hF (L, loops (regsOf αs S) rest (resOn (body (regsOf αs S) prev) L, prev)) n
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      show (_, _) = F (L.val n, valsOf rest _ n) n
      exact Prod.ext hfst rfl

/-- The chain's states at `n` are fixed by the enclosing state at the cycles
`< n`. -/
theorem loops_causal {αs : List Type} (t : Tele dom αs [])
    (F : HList αs → HList (σs t) → Nat → HList (σs t)) (hF : TelePointwise t F)
    (S S' : Signal dom (HList αs)) :
    ∀ n, (∀ i, i < n → S.val i = S'.val i) →
      valsOf t (loops (regsOf αs S) t ()) n = valsOf t (loops (regsOf αs S') t ()) n := by
  have r := fun (S : Signal dom (HList αs)) =>
    loops_rec S t () (fun xs n => F (S.val n) xs n) (fun Ss n => hF S Ss n)
  intro n
  induction n with
  | zero => intro _; rw [(r S).1, (r S').1]
  | succ n ih =>
    intro h
    rw [(r S).2, (r S').2, ih (fun i hi => h i (by omega)), h n (by omega)]

/-! ## The enclosing machine over a chain -/

/-- The enclosing body with the chain on its loops: the machine the
declaration is. -/
def fusedBody {αs : List Type} {ρ : Type} (t : Tele dom αs [])
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList (ρs t) →
      Circuit dom (Circuit.SigList dom αs) ρ) :
    RegList dom (HList αs) (Circuit.SigList dom αs) αs → Circuit dom (Circuit.SigList dom αs) ρ :=
  fun regs => body regs (resultsOn regs t () (loops regs t ()))

/-- The enclosing body's writes at `n` are a function `G` of the values at
`n` of the enclosing state and of the chain's states. -/
def OuterPointwise {αs : List Type} {ρ : Type} (t : Tele dom αs [])
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList (ρs t) →
      Circuit dom (Circuit.SigList dom αs) ρ)
    (G : HList αs → HList (σs t) → Nat → HList αs) : Prop :=
  ∀ (S : Signal dom (HList αs)) (Ss : Sigs t) (n : Nat),
    valsAt αs (body (regsOf αs S) (resultsOn (regsOf αs S) t () Ss) (mkHolds αs S)).snd n =
      G (S.val n) (valsOf t Ss n) n

theorem fusedBody_writes {αs : List Type} {ρ : Type} (t : Tele dom αs [])
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList (ρs t) →
      Circuit dom (Circuit.SigList dom αs) ρ)
    (G : HList αs → HList (σs t) → Nat → HList αs) (hG : OuterPointwise t body G)
    (S : Signal dom (HList αs)) (n : Nat) :
    valsAt αs (writesOn (fusedBody t body) S) n =
      G (S.val n) (valsOf t (loops (regsOf αs S) t ()) n) n :=
  hG S _ n

/-- **The state of a machine with a chain of sub-machines.** The enclosing
loop starts at its reset values and advances by `G`; the chain's loops,
driven by the enclosing loop, start at their reset values and advance by
`F`. -/
theorem fused_state {αs : List Type} {ρ : Type} [Inhabited (HList αs)] (inits : HList αs)
    (t : Tele dom αs [])
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList (ρs t) →
      Circuit dom (Circuit.SigList dom αs) ρ)
    (F : HList αs → HList (σs t) → Nat → HList (σs t)) (hF : TelePointwise t F)
    (G : HList αs → HList (σs t) → Nat → HList αs) (hG : OuterPointwise t body G) :
    let s := stateLoop inits (fusedBody t body)
    let xs := fun n => valsOf t (loops (regsOf αs s) t ()) n
    s.val 0 = inits ∧ xs 0 = initsOf t ∧
    ∀ n, s.val (n + 1) = G (s.val n) (xs n) n ∧ xs (n + 1) = F (s.val n) (xs n) n := by
  intro s xs
  have hW : ∀ (l₁ l₂ : Signal dom (HList αs)) (n : Nat), (∀ i, i ≤ n → l₁.val i = l₂.val i) →
      valsAt αs (writesOn (fusedBody t body) l₁) n =
        valsAt αs (writesOn (fusedBody t body) l₂) n := by
    intro l₁ l₂ n h
    rw [fusedBody_writes t body G hG, fusedBody_writes t body G hG, h n (Nat.le_refl n),
      loops_causal t F hF l₁ l₂ n (fun i hi => h i (Nat.le_of_lt hi))]
  obtain ⟨h0, hs⟩ := circuit_state_causal inits (fusedBody t body) hW
  obtain ⟨x0, xs'⟩ := loops_rec s t () (fun xs n => F (s.val n) xs n) (fun Ss n => hF s Ss n)
  refine ⟨h0, x0, fun n => ⟨?_, xs' n⟩⟩
  rw [hs n, fusedBody_writes t body G hG]

/-- The result of the declaration's machine on its loop. -/
theorem fusedBody_result {αs : List Type} {ρ : Type} (t : Tele dom αs [])
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList (ρs t) →
      Circuit dom (Circuit.SigList dom αs) ρ) (S : Signal dom (HList αs)) :
    resOn (fusedBody t body) S =
      (body (regsOf αs S) (resultsOn (regsOf αs S) t () (loops (regsOf αs S) t ()))
        (mkHolds αs S)).fst := rfl

end Tools.ShippingMachineTele
