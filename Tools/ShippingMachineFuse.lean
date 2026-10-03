import Tools.ShippingMachineSource

/-! # Nested `circuit do`s: the state of a machine with sub-machines

A `circuit do` body may use the result of another `circuit do` — a parser
bound by `let` in front of it, a controller called inside a `let` of the
body, a latch applied to a latch. After unfolding, the declaration is a
`runCircuitH` whose body contains further `runCircuitH`s, each on its own
state loop, whose inputs may read the enclosing machine's handles.

The compiler flattens such a declaration into ONE machine whose slots are
the enclosing machine's slots followed by the sub-machines' slots, in order.
This file proves what that flattening relies on, once and for any number of
sub-machines: the tuple of all the state loops' values is a stream that
starts at the tuple of reset values and advances by the tuple of the pending
writes — provided the writes are POINTWISE in the states (every `circuit do`
body is: its writes at a cycle are combinational in the live values at that
cycle), which per declaration is one `rfl`.

The enclosing body sees a sub-machine through its result only. To state the
theorem the enclosing body is a function of its handles and of the tuple of
the sub-machines' results (`Inner`, `results`); a declaration is written in
that form by abstracting each sub-machine application, which is a
beta-reduction away from the declaration as unfolded. -/
namespace Tools.ShippingMachineFuse
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource

/-- A sub-machine of a body over the slots `αs`: its slots `βs`, reset values
and body, which may read the enclosing handles. -/
structure Inner (dom : DomainConfig) (αs : List Type) where
  βs : List Type
  [inh : Inhabited (HList βs)]
  ρ : Type
  inits : HList βs
  body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
    RegList dom (HList βs) (Circuit.SigList dom βs) βs →
    Circuit dom (Circuit.SigList dom βs) ρ

attribute [instance] Inner.inh

variable {dom : DomainConfig}

/-- The handles over a state signal. -/
abbrev regsOf (αs : List Type) (S : Signal dom (HList αs)) :
    RegList dom (HList αs) (Circuit.SigList dom αs) αs :=
  mkRegList S αs (fun s => s) (fun f => f)

/-- The result of a body on a state signal. -/
abbrev resOn {αs : List Type} {ρ : Type}
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
      Circuit dom (Circuit.SigList dom αs) ρ) (S : Signal dom (HList αs)) : ρ :=
  (body (regsOf αs S) (mkHolds αs S)).fst

/-- The pending writes of a body on a state signal. -/
abbrev writesOn {αs : List Type} {ρ : Type}
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
      Circuit dom (Circuit.SigList dom αs) ρ) (S : Signal dom (HList αs)) :
    Circuit.SigList dom αs :=
  (body (regsOf αs S) (mkHolds αs S)).snd

/-- The result types of a list of sub-machines. -/
abbrev ρs {αs : List Type} (l : List (Inner dom αs)) : List Type := l.map (·.ρ)

/-- The state types of a list of sub-machines. -/
abbrev σs {αs : List Type} (l : List (Inner dom αs)) : List Type := l.map fun i => HList i.βs

/-- One state signal per sub-machine. -/
abbrev Sigs {αs : List Type} (l : List (Inner dom αs)) : Type :=
  HList (l.map fun i => Signal dom (HList i.βs))

/-- The state loop of a sub-machine, its inputs read from the enclosing
handles `regs`. -/
def innerLoop {αs : List Type} (i : Inner dom αs)
    (regs : RegList dom (HList αs) (Circuit.SigList dom αs) αs) : Signal dom (HList i.βs) :=
  stateLoop i.inits (i.body regs)

/-- The sub-machines' results, each on its own state loop: what the
enclosing body is applied to. `runCircuitH inits body = resOn body (stateLoop
inits body)` by definition (`runCircuitH_eq`), so a declaration is its
enclosing body applied to `results` by beta-reduction. -/
def results {αs : List Type} (regs : RegList dom (HList αs) (Circuit.SigList dom αs) αs) :
    (l : List (Inner dom αs)) → HList (ρs l)
  | [] => ()
  | i :: l => (resOn (i.body regs) (innerLoop i regs), results regs l)

/-- The sub-machines' results on GIVEN state signals, instead of their
loops: the form of the per-declaration `rfl`. -/
def resultsOn {αs : List Type} (regs : RegList dom (HList αs) (Circuit.SigList dom αs) αs) :
    (l : List (Inner dom αs)) → Sigs l → HList (ρs l)
  | [], _ => ()
  | i :: l, Ss => (resOn (i.body regs) Ss.1, resultsOn regs l Ss.2)

/-- The state loops of the sub-machines, as the tuple `resultsOn` reads. -/
def innerLoops {αs : List Type} (regs : RegList dom (HList αs) (Circuit.SigList dom αs) αs) :
    (l : List (Inner dom αs)) → Sigs l
  | [] => ()
  | i :: l => (innerLoop i regs, innerLoops regs l)

theorem results_eq {αs : List Type} (regs : RegList dom (HList αs) (Circuit.SigList dom αs) αs) :
    ∀ l : List (Inner dom αs), results regs l = resultsOn regs l (innerLoops regs l)
  | [] => rfl
  | i :: l => by
    show (_, results regs l) = (_, resultsOn regs l (innerLoops regs l))
    rw [results_eq regs l]
    rfl

/-- The values at a cycle of a tuple of state signals. -/
def valsOf {αs : List Type} : (l : List (Inner dom αs)) → Sigs l → Nat → HList (σs l)
  | [], _, _ => ()
  | _ :: l, Ss, t => (Ss.1.val t, valsOf l Ss.2 t)

/-- The pending writes of every sub-machine's body, on given state signals. -/
def innerWrites {αs : List Type} (regs : RegList dom (HList αs) (Circuit.SigList dom αs) αs) :
    (l : List (Inner dom αs)) → Sigs l → HList (l.map fun i => Circuit.SigList dom i.βs)
  | [], _ => ()
  | i :: l, Ss => (writesOn (i.body regs) Ss.1, innerWrites regs l Ss.2)

/-- The values at a cycle of the sub-machines' pending writes. -/
def innerValsAt {αs : List Type} : (l : List (Inner dom αs)) →
    HList (l.map fun i => Circuit.SigList dom i.βs) → Nat → HList (σs l)
  | [], _, _ => ()
  | i :: l, ws, t => (valsAt i.βs ws.1 t, innerValsAt l ws.2 t)

/-- The constant state signals holding one cycle's values. -/
def constOf {αs : List Type} : (l : List (Inner dom αs)) → HList (σs l) → Sigs l
  | [], _ => ()
  | _ :: l, xs => (⟨fun _ => xs.1⟩, constOf l xs.2)

theorem valsOf_constOf {αs : List Type} : ∀ (l : List (Inner dom αs)) (xs : HList (σs l)) (t : Nat),
    valsOf l (constOf l xs) t = xs
  | [], _, _ => rfl
  | _ :: l, xs, t => by
    show (xs.1, valsOf l (constOf l xs.2) t) = xs
    rw [valsOf_constOf l xs.2 t]
    rfl

/-- The reset values of the sub-machines. -/
def initsOf {αs : List Type} : (l : List (Inner dom αs)) → HList (σs l)
  | [] => ()
  | i :: l => (i.inits, initsOf l)

/-! ## The loop recurrence for a causal body

`loop_state` (ShippingMachineSource) asks the writes to be pointwise in the
live state. A body with a sub-machine inside is not: its writes at a cycle
read the sub-machine's result, which depends on the live state at the
EARLIER cycles too. The recurrence holds for any CAUSAL body — the writes at
`t` fixed by the live values at the cycles `≤ t` — because the loop's `t+1`
step sees the live state truncated after `t`. -/

theorem loop_state_causal (αs : List Type) [Inhabited (HList αs)]
    (inits : HList αs) (W : Signal dom (HList αs) → Circuit.SigList dom αs)
    (hW : ∀ (l l' : Signal dom (HList αs)) (t : Nat), (∀ i, i ≤ t → l.val i = l'.val i) →
      valsAt αs (W l) t = valsAt αs (W l') t) :
    (Signal.loop (fun live => packRegister αs inits (W live))).val 0 = inits ∧
    ∀ t, (Signal.loop (fun live => packRegister αs inits (W live))).val (t + 1) =
      valsAt αs (W (Signal.loop (fun live => packRegister αs inits (W live)))) t := by
  constructor
  · show Signal.loopGo _ 0 = inits
    rw [Signal.loopGo_eq]
    exact (packRegister_val αs inits _).1
  · intro t
    show Signal.loopGo _ (t + 1) = _
    rw [Signal.loopGo_eq, (packRegister_val αs inits _).2 t]
    apply hW
    intro i hi
    show (if i < t + 1 then Signal.loopGo _ i else default) = _
    rw [if_pos (by omega)]
    rfl

/-- `circuit_state` for a causal body. -/
theorem circuit_state_causal {αs : List Type} {ρ : Type} [Inhabited (HList αs)]
    (inits : HList αs)
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
      Circuit dom (Circuit.SigList dom αs) ρ)
    (hW : ∀ (l l' : Signal dom (HList αs)) (t : Nat), (∀ i, i ≤ t → l.val i = l'.val i) →
      valsAt αs (writesOn body l) t = valsAt αs (writesOn body l') t) :
    (stateLoop inits body).val 0 = inits ∧
    ∀ t, (stateLoop inits body).val (t + 1) =
      valsAt αs (writesOn body (stateLoop inits body)) t :=
  loop_state_causal αs inits (fun live => writesOn body live) hW

/-! ## The sub-machines' loops

Each sub-machine's loop is driven by the enclosing handles; with pointwise
writes its state at `t + 1` is its writes' values at `t`, and its state at
`t` is fixed by the enclosing state at the cycles `< t`. -/

/-- Pointwiseness of the sub-machines' writes, in the enclosing state and in
their own states: the writes at `t` are a function `F` of the values at `t`.
Per declaration this is a `rfl`, with `F` the typed evaluation of the
next-value terms. -/
def InnerPointwise {αs : List Type} (l : List (Inner dom αs))
    (F : HList αs → HList (σs l) → Nat → HList (σs l)) : Prop :=
  ∀ (S : Signal dom (HList αs)) (Ss : Sigs l) (t : Nat),
    innerValsAt l (innerWrites (regsOf αs S) l Ss) t = F (S.val t) (valsOf l Ss t) t

/-- The head sub-machine's writes are pointwise in its own state. -/
theorem InnerPointwise.head {αs : List Type} {i : Inner dom αs} {l : List (Inner dom αs)}
    {F : HList αs → HList (σs (i :: l)) → Nat → HList (σs (i :: l))}
    (hF : InnerPointwise (i :: l) F) (S : Signal dom (HList αs)) :
    ∀ (l₁ l₂ : Signal dom (HList i.βs)) (t : Nat), l₁.val t = l₂.val t →
      valsAt i.βs (writesOn (i.body (regsOf αs S)) l₁) t =
        valsAt i.βs (writesOn (i.body (regsOf αs S)) l₂) t := by
  intro l₁ l₂ t h
  have h1 := hF S (l₁, innerLoops (regsOf αs S) l) t
  have h2 := hF S (l₂, innerLoops (regsOf αs S) l) t
  have hv : valsOf (i :: l) (l₁, innerLoops (regsOf αs S) l) t =
      valsOf (i :: l) (l₂, innerLoops (regsOf αs S) l) t := by
    show (l₁.val t, _) = (l₂.val t, _)
    rw [h]
  rw [hv] at h1
  have := h1.trans h2.symm
  exact congrArg Prod.fst this

/-- The tail sub-machines' writes are pointwise, with the head's state held
at its reset value. -/
theorem InnerPointwise.tail {αs : List Type} {i : Inner dom αs} {l : List (Inner dom αs)}
    {F : HList αs → HList (σs (i :: l)) → Nat → HList (σs (i :: l))}
    (hF : InnerPointwise (i :: l) F) :
    InnerPointwise l (fun a xs t => (F a (i.inits, xs) t).2) := by
  intro S Ss t
  have h := hF S (⟨fun _ => i.inits⟩, Ss) t
  have hv : valsOf (i :: l) (⟨fun _ => i.inits⟩, Ss) t = (i.inits, valsOf l Ss t) := rfl
  rw [hv] at h
  exact congrArg Prod.snd h

/-- Every sub-machine's loop steps by its own writes. -/
theorem innerLoops_step {αs : List Type} (S : Signal dom (HList αs)) :
    ∀ (l : List (Inner dom αs)) (F : HList αs → HList (σs l) → Nat → HList (σs l)),
      InnerPointwise l F →
      valsOf l (innerLoops (regsOf αs S) l) 0 = initsOf l ∧
      ∀ t, valsOf l (innerLoops (regsOf αs S) l) (t + 1) =
        innerValsAt l (innerWrites (regsOf αs S) l (innerLoops (regsOf αs S) l)) t
  | [], _, _ => ⟨rfl, fun _ => rfl⟩
  | i :: l, F, hF => by
    obtain ⟨h0, hs⟩ := circuit_state i.inits (i.body (regsOf αs S)) (hF.head S)
    obtain ⟨ih0, ihs⟩ := innerLoops_step S l _ hF.tail
    constructor
    · show ((innerLoop i (regsOf αs S)).val 0, valsOf l (innerLoops (regsOf αs S) l) 0) = _
      rw [ih0]
      show ((stateLoop i.inits (i.body (regsOf αs S))).val 0, _) = _
      rw [h0]
      rfl
    · intro t
      show ((innerLoop i (regsOf αs S)).val (t + 1), valsOf l (innerLoops (regsOf αs S) l) (t + 1)) = _
      rw [ihs t]
      show ((stateLoop i.inits (i.body (regsOf αs S))).val (t + 1), _) = _
      rw [hs t]
      rfl

/-- The recurrence of the sub-machines' states, through `F`. -/
theorem innerLoops_rec {αs : List Type} (S : Signal dom (HList αs)) (l : List (Inner dom αs))
    (F : HList αs → HList (σs l) → Nat → HList (σs l)) (hF : InnerPointwise l F) :
    valsOf l (innerLoops (regsOf αs S) l) 0 = initsOf l ∧
    ∀ t, valsOf l (innerLoops (regsOf αs S) l) (t + 1) =
      F (S.val t) (valsOf l (innerLoops (regsOf αs S) l) t) t := by
  obtain ⟨h0, hs⟩ := innerLoops_step S l F hF
  exact ⟨h0, fun t => by rw [hs t, hF S _ t]⟩

/-- The sub-machines' states at `t` are fixed by the enclosing state at the
cycles `< t`. -/
theorem innerLoops_causal {αs : List Type} (l : List (Inner dom αs))
    (F : HList αs → HList (σs l) → Nat → HList (σs l)) (hF : InnerPointwise l F)
    (S S' : Signal dom (HList αs)) :
    ∀ t, (∀ i, i < t → S.val i = S'.val i) →
      valsOf l (innerLoops (regsOf αs S) l) t = valsOf l (innerLoops (regsOf αs S') l) t := by
  intro t
  induction t with
  | zero => intro _; rw [(innerLoops_rec S l F hF).1, (innerLoops_rec S' l F hF).1]
  | succ t ih =>
    intro h
    rw [(innerLoops_rec S l F hF).2, (innerLoops_rec S' l F hF).2,
      ih (fun i hi => h i (by omega)), h t (by omega)]

/-! ## The enclosing machine

The enclosing body `body` takes its handles and the tuple of the
sub-machines' results. The declaration's machine body is `body regs (results
regs l)`; with the results on their loops replaced by the results on given
states, its writes and result are pointwise (`OuterPointwise`, `OuterOut`,
both a `rfl` per declaration). -/

/-- The enclosing body with its sub-machines on their loops: the machine the
declaration is. -/
def fusedBody {αs : List Type} {ρ : Type} (l : List (Inner dom αs))
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList (ρs l) →
      Circuit dom (Circuit.SigList dom αs) ρ) :
    RegList dom (HList αs) (Circuit.SigList dom αs) αs → Circuit dom (Circuit.SigList dom αs) ρ :=
  fun regs => body regs (results regs l)

/-- The enclosing body's writes at `t` are a function `G` of the values at
`t` of the enclosing state and of the sub-machines' states. -/
def OuterPointwise {αs : List Type} {ρ : Type} (l : List (Inner dom αs))
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList (ρs l) →
      Circuit dom (Circuit.SigList dom αs) ρ)
    (G : HList αs → HList (σs l) → Nat → HList αs) : Prop :=
  ∀ (S : Signal dom (HList αs)) (Ss : Sigs l) (t : Nat),
    valsAt αs (body (regsOf αs S) (resultsOn (regsOf αs S) l Ss) (mkHolds αs S)).snd t =
      G (S.val t) (valsOf l Ss t) t

/-- The writes of the declaration's machine body, on a state signal. -/
theorem fusedBody_writes {αs : List Type} {ρ : Type} (l : List (Inner dom αs))
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList (ρs l) →
      Circuit dom (Circuit.SigList dom αs) ρ)
    (G : HList αs → HList (σs l) → Nat → HList αs) (hG : OuterPointwise l body G)
    (S : Signal dom (HList αs)) (t : Nat) :
    valsAt αs (writesOn (fusedBody l body) S) t =
      G (S.val t) (valsOf l (innerLoops (regsOf αs S) l) t) t := by
  show valsAt αs (body (regsOf αs S) (results (regsOf αs S) l) (mkHolds αs S)).snd t = _
  rw [results_eq, hG]

/-- **The state of a machine with sub-machines.** The enclosing loop starts
at its reset values and advances by `G`; the sub-machines' loops, driven by
the enclosing loop, start at their reset values and advance by `F`. -/
theorem fused_state {αs : List Type} {ρ : Type} [Inhabited (HList αs)] (inits : HList αs)
    (l : List (Inner dom αs))
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList (ρs l) →
      Circuit dom (Circuit.SigList dom αs) ρ)
    (F : HList αs → HList (σs l) → Nat → HList (σs l)) (hF : InnerPointwise l F)
    (G : HList αs → HList (σs l) → Nat → HList αs) (hG : OuterPointwise l body G) :
    let s := stateLoop inits (fusedBody l body)
    let xs := fun t => valsOf l (innerLoops (regsOf αs s) l) t
    s.val 0 = inits ∧ xs 0 = initsOf l ∧
    ∀ t, s.val (t + 1) = G (s.val t) (xs t) t ∧ xs (t + 1) = F (s.val t) (xs t) t := by
  intro s xs
  have hW : ∀ (l₁ l₂ : Signal dom (HList αs)) (t : Nat), (∀ i, i ≤ t → l₁.val i = l₂.val i) →
      valsAt αs (writesOn (fusedBody l body) l₁) t =
        valsAt αs (writesOn (fusedBody l body) l₂) t := by
    intro l₁ l₂ t h
    rw [fusedBody_writes l body G hG, fusedBody_writes l body G hG, h t (Nat.le_refl t),
      innerLoops_causal l F hF l₁ l₂ t (fun i hi => h i (Nat.le_of_lt hi))]
  obtain ⟨h0, hs⟩ := circuit_state_causal inits (fusedBody l body) hW
  obtain ⟨x0, xs'⟩ := innerLoops_rec s l F hF
  refine ⟨h0, x0, fun t => ⟨?_, xs' t⟩⟩
  rw [hs t, fusedBody_writes l body G hG]

/-- The result of the declaration's machine on its loop is the enclosing
result on the loop and the sub-machines' loops. -/
theorem fusedBody_result {αs : List Type} {ρ : Type} (l : List (Inner dom αs))
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs → HList (ρs l) →
      Circuit dom (Circuit.SigList dom αs) ρ) (S : Signal dom (HList αs)) :
    resOn (fusedBody l body) S =
      (body (regsOf αs S) (resultsOn (regsOf αs S) l (innerLoops (regsOf αs S) l))
        (mkHolds αs S)).fst := by
  show (body (regsOf αs S) (results (regsOf αs S) l) (mkHolds αs S)).fst = _
  rw [results_eq]

end Tools.ShippingMachineFuse
