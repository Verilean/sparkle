import Tools.ShippingLegacySemBinderBound
import Tools.ShippingLegacySemSignalFrame
import Tools.ShippingMixedEntrySoundness

/-! # The legacy binder walk over a LIST of scalar binders (`bits n` and `bool`)

`bindInputsLegacy_one_bound` (`Tools/ShippingLegacySemBinderBound.lean`)
turns the legacy walk over ONE variable into a run of the certified walk. For
several variables that form does not compose: the rest of the walk runs
INSIDE `bindInputPort`'s continuation, and a run of the certified walk cannot
be rebuilt from runs of its parts (`Returns` quantifies the world per run:
there is no introduction rule for `>>=`). What the harness needs of the
certified walk is only its INVERSION (`prepare_returns`: a run of the walk is
a run of the continuation from the prepared setup). So the legacy walk is
inverted to the same place directly.

**Proved here**

* `withVarMapping_runsIn`, `bindInputPort_runsIn` — the inversions of
  `Tools/ShippingEntrySoundness.lean` with the `Meta` context kept (the rest
  of the walk reads the local context again).
* `bindInputsLegacy_step` — ONE variable at any index `i`, any hardware type:
  in a context that declares `xs[i]`'s variable as `d0`, with the Signal
  test's frame, the type oracle's result `hw` on `d0.type` (`InfersHW`) and
  no catchable failure (`InfersNoCatch`), a successful run of the walk from
  `i` is a successful run — in the SAME context — of
  `bindInputPort id d0.userName.toString hw (walk from i + 1)`.
  (`bindInputsLegacy_one_bound_raw`'s walk, kept in `RunsIn` form.)
* `bindInputsLegacy_prepare` — the list: for binders `B` (name, kind,
  declared type), variables `ids`, the declarations at `xs[i ..]`
  (`DeclsAt`) and the oracle facts of each binder (`BinderOracle`), a
  successful run of the walk from `i` is a successful run of the
  continuation from `prepare bools bits ((bindersOf B).zip ids) a` — the
  conclusion of `prepare_returns` for the certified walk.

**Binder kinds.** `kindHW`: `.bits n ↦ .bitVector n`, `.bool ↦ .bit` — what
`bindMixedCertifiedInputs` binds for each kind. A `.domain` binder is
excluded by `BinderOracle` (the certified walk binds nothing for it; the
legacy walk would have to SKIP it, which is the outcome `InfersNoCatch`
excludes — a domain binder needs the opposite premise, not written).

**Bool and width one — read from the oracle** (`inferHWTypeStep`,
`Sparkle/Compiler/Elab.lean` 539–551, reached from `inferHWTypeFromSignal`
when not symbolic): `Bool ↦ .bit` — the same port as the certified `.bool`
binder, so a `Signal dom Bool` binder is covered with kind `.bool` and the
premise `InfersHW T .bit`. But `BitVec w ↦ if w == 1 then .bit else
.bitVector w`: a `Signal dom (BitVec 1)` binder gets a `.bit` port from the
legacy walk, while the certified `.bits 1` binder gets `.bitVector 1`. For
kind `.bits 1` the premise `InfersHW T (.bitVector 1)` is FALSE of the real
oracle, so a width-one vector binder is outside this theorem (the statement
stays true, its premise cannot be met). Covering it needs a bridge between a
`.bit` port and a one-bit vector value in `prepare` / `Admissible`; not
written.

**Program shapes**: as `Tools/ShippingLegacySemBinder.lean` (S0–S6, built),
with every inversion in `RunsIn` form. -/
namespace Tools.ShippingLegacySem
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.Builder
open Sparkle.IR.Type (HWType)
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-! ## Kinds and oracle premises -/

/-- The port type the certified walk binds for a binder kind. -/
def kindHW : MixedGateBinder → HWType
  | .bool => .bit
  | .bits n => .bitVector n
  | .domain => .bit

/-- Every successful run of the hardware-type oracle on `T` returns `hw` and
leaves the builder state (`InfersBits T n` is `InfersHW T (.bitVector n)`). -/
def InfersHW (T : Lean.Expr) (hw : HWType) : Prop :=
  ∀ (ctx : CompilerState) (s t : CircuitState) (h : HWType),
    Returns (inferHWTypeFromSignal T) ctx s h t → h = hw ∧ t = s

theorem InfersBits.hw {T : Lean.Expr} {n : Nat} (h : InfersBits T n) :
    InfersHW T (.bitVector n) := h

/-- The oracle facts of one binder `(name, kind, declared type)`: not a
domain binder; the type oracle returns the kind's port type and has no
catchable failure on the declared type. -/
def BinderOracle (q : Name × MixedGateBinder × Lean.Expr) : Prop :=
  q.2.1 ≠ MixedGateBinder.domain ∧ InfersHW q.2.2 (kindHW q.2.1) ∧ InfersNoCatch q.2.2

/-- The certified binder list of a binder specification. -/
def bindersOf (B : List (Name × MixedGateBinder × Lean.Expr)) :
    List (Name × MixedGateBinder) :=
  B.map fun q => (q.1, q.2.1)

/-- The telescope's variables from index `i` on are the variables `ids`,
declared in `mctx` with the names and types of `B`; nothing follows them. -/
def DeclsAt (mctx : Meta.Context) (xs : Array Lean.Expr) :
    Nat → List (Name × MixedGateBinder × Lean.Expr) → List FVarId → Prop
  | i, [], [] => xs.size ≤ i
  | i, q :: B, id :: ids =>
    (∃ h : i < xs.size, (xs[i]'h).fvarId! = id ∧
      ∃ d0 : LocalDecl, mctx.lctx.find? id = some d0 ∧ d0.userName = q.1 ∧ d0.type = q.2.2) ∧
    DeclsAt mctx xs (i + 1) B ids
  | _, _, _ => False

/-- `DeclsAt` pairs the variables with the binders one to one. -/
theorem DeclsAt.length {mctx : Meta.Context} {xs : Array Lean.Expr}
    (B : List (Name × MixedGateBinder × Lean.Expr)) :
    ∀ (ids : List FVarId) (i : Nat), DeclsAt mctx xs i B ids → ids.length = B.length := by
  induction B with
  | nil =>
    intro ids i hd
    cases ids with
    | nil => rfl
    | cons id ids => exact False.elim hd
  | cons q B ih =>
    intro ids i hd
    cases ids with
    | nil => exact False.elim hd
    | cons id ids =>
      obtain ⟨_, hrest⟩ := hd
      exact congrArg (· + 1) (ih ids (i + 1) hrest)

/-! ## Inversions with the context kept -/

theorem withVarMapping_runsIn {α : Type} {id : FVarId} {w : String} {k : CompilerM α}
    {mctx : Meta.Context} {ctx : CompilerState} {s s' : CircuitState} {a : α}
    (h : RunsIn (CompilerM.withVarMapping id w k) mctx ctx s a s') :
    RunsIn k mctx { ctx with varMap := (id, w) :: ctx.varMap } s a s' := by
  unfold CompilerM.withVarMapping at h
  obtain ⟨c, s1, hread, k1⟩ := RunsIn.bind h
  obtain ⟨hc, hs1⟩ := Returns.read (RunsIn.returns hread)
  subst hc hs1
  obtain ⟨mref, cctx, cref, w0, w', hrun⟩ := k1
  exact ⟨mref, cctx, cref, w0, w', hrun⟩

theorem bindInputPort_runsIn {α : Type} {id : FVarId} {nm : String} {ty : HWType}
    {k : CompilerM α} {mctx : Meta.Context} {ctx : CompilerState} {s s' : CircuitState} {a : α}
    (h : RunsIn (bindInputPort id nm ty k) mctx ctx s a s') :
    RunsIn k mctx { ctx with varMap := (id, (CircuitM.makeWire nm ty true s).1) :: ctx.varMap }
      (CircuitM.addInput (CircuitM.makeWire nm ty true s).1 ty
        (CircuitM.makeWire nm ty true s).2).2 a s' := by
  unfold bindInputPort at h
  obtain ⟨w, sA, hmk, k1⟩ := RunsIn.bind h
  obtain ⟨hw, hsA⟩ := makeWire_returns (RunsIn.returns hmk)
  obtain ⟨u, sB, hin, k2⟩ := RunsIn.bind k1
  have hsB := addInput_returns (RunsIn.returns hin)
  have k3 := withVarMapping_runsIn k2
  rw [hsB, hsA, hw] at k3
  exact k3

theorem bindInputPort_congr_id_in {α : Type} {a b : FVarId} {nm : String} {hw : HWType}
    {k : CompilerM α} {mctx : Meta.Context} {ctx : CompilerState} {s t : CircuitState} {r : α}
    (e : a = b) (h : RunsIn (bindInputPort a nm hw k) mctx ctx s r t) :
    RunsIn (bindInputPort b nm hw k) mctx ctx s r t := by
  subst e
  exact h

/-! ## One variable, at any index -/

/-- **One step of the legacy walk**: the variable at index `i` gets its port,
and the walk goes on from `i + 1` — in the same `Meta` context. -/
theorem bindInputsLegacy_step {xs : Array Lean.Expr} {i : Nat} {id : FVarId} {d0 : LocalDecl}
    {hw : HWType} {mctx : Meta.Context} {k : CompilerM String} {ctx : CompilerState}
    {s t : CircuitState} {r : String}
    (h0 : i < xs.size) (hx : (xs[i]'h0).fvarId! = id)
    (hfind : mctx.lctx.find? id = some d0)
    (hsig : SignalTestFrame d0.type) (hinf : InfersHW d0.type hw)
    (hnt : InfersNoCatch d0.type)
    (hrun : RunsIn (bindInputsLegacy [] false xs i k) mctx ctx s r t) :
    RunsIn (bindInputPort id d0.userName.toString hw (bindInputsLegacy [] false xs (i + 1) k))
      mctx ctx s r t := by
  -- S0
  first
    | unfold bindInputsLegacy at hrun
    | rw [bindInputsLegacy] at hrun
  have a1 := RunsIn.dite_pos hrun h0
  -- S1: the declaration, read from the context
  obtain ⟨decl, s1, hd, a2⟩ := RunsIn.bind a1
  obtain ⟨hdm, hs1⟩ := RunsIn.liftMetaM hd
  have hde : decl = d0 := getDecl_runsIn_find hx hfind hdm
  rw [hs1] at a2
  rw [hde] at a2
  -- S2: no parameter; the Signal test
  first
    | (obtain ⟨sg, s2, hsg, b1⟩ := RunsIn.bind a2)
    | (simp only [List.find?, Option.map] at a2
       obtain ⟨sg, s2, hsg, b1⟩ := RunsIn.bind a2)
  have hs2 : s2 = s := hsig ctx s s2 sg (RunsIn.returns hsg)
  rw [hs2] at b1
  -- S3: not symbolic
  rcases RunsIn.ite b1 with ⟨hsym, _⟩ | ⟨_, b2⟩
  · exact absurd (show false = true from hsym) Bool.false_ne_true
  -- S4: the `try` around the type oracle returned `true`
  obtain ⟨hwb, s3, htry, b3⟩ := RunsIn.bind b2
  have hs3 : s3 = s ∧ hwb = true := by
    rcases returns_tryCatch_throws (RunsIn.returns htry) with hbody | ⟨ex, hthrow, hcatch, _⟩
    · obtain ⟨hw0, s4, hi0, hp0⟩ := Returns.bind hbody
      obtain ⟨_, hs4⟩ := hinf ctx s s4 hw0 hi0
      rw [hs4] at hp0
      obtain ⟨hb, hs⟩ := Returns.pure hp0
      exact ⟨hs, hb⟩
    · rcases Throws.bind hthrow with hinfer | ⟨a0, s4, _, hpure⟩
      · exact absurd (hnt ctx s ex hinfer) hcatch
      · exact (Throws.pure hpure).elim
  rw [hs3.1] at b3
  -- S5: `isHWArg` is `true`
  rcases RunsIn.ite b3 with ⟨_, c1⟩ | ⟨hF, _⟩
  · obtain ⟨hw1, s5, hi1, c2⟩ := RunsIn.bind c1
    obtain ⟨hw1eq, hs5⟩ := hinf ctx s s5 hw1 (RunsIn.returns hi1)
    rw [hs5] at c2
    rw [hw1eq] at c2
    exact bindInputPort_congr_id_in hx c2
  · exact absurd hs3.2 hF

/-! ## The list -/

/-- **The legacy binder walk over a list of scalar binders reaches the
prepared setup**: the conclusion `prepare_returns` gives for the certified
walk over `(bindersOf B).zip ids`. -/
theorem bindInputsLegacy_prepare {mctx : Meta.Context} {bools : FVarId → Bool}
    {bits : (id : FVarId) → (n : Nat) → BitVec n} {xs : Array Lean.Expr}
    {k : CompilerM String} {r : String} {t : CircuitState}
    (B : List (Name × MixedGateBinder × Lean.Expr)) :
    ∀ (ids : List FVarId) (i : Nat) (a : Tools.ShippingMixedEntrySoundness.Setup),
      DeclsAt mctx xs i B ids → (∀ q, q ∈ B → BinderOracle q) →
      RunsIn (bindInputsLegacy [] false xs i k) mctx a.context a.state r t →
      Returns k
        (Tools.ShippingMixedEntrySoundness.prepare bools bits ((bindersOf B).zip ids) a).context
        (Tools.ShippingMixedEntrySoundness.prepare bools bits ((bindersOf B).zip ids) a).state
        r t := by
  induction B with
  | nil =>
    intro ids i a hd _ hrun
    cases ids with
    | nil =>
      have hle : xs.size ≤ i := hd
      exact bindInputsLegacy_done_returns (RunsIn.returns hrun) hle
    | cons id ids => exact False.elim hd
  | cons q B ih =>
    intro ids i a hd ho hrun
    cases ids with
    | nil => exact False.elim hd
    | cons id ids =>
      obtain ⟨nm, kind, T⟩ := q
      obtain ⟨⟨h0, hx, d0, hfind, hnm, hty⟩, hrest⟩ := hd
      obtain ⟨hnd, hinf, hnt⟩ := ho (nm, kind, T) (List.mem_cons.mpr (Or.inl rfl))
      have ho' : ∀ q, q ∈ B → BinderOracle q := fun q hq => ho q (List.mem_cons.mpr (Or.inr hq))
      have hnm' : d0.userName = nm := hnm
      have hty' : d0.type = T := hty
      have hinf' : InfersHW d0.type (kindHW kind) := by
        rw [hty']
        exact hinf
      have hnt' : InfersNoCatch d0.type := by
        rw [hty']
        exact hnt
      have c := bindInputPort_runsIn
        (bindInputsLegacy_step h0 hx hfind (isSignalBinderType_frame d0.type) hinf' hnt' hrun)
      rw [hnm'] at c
      cases kind with
      | domain => exact absurd rfl hnd
      | bool =>
        exact ih ids (i + 1)
          (Tools.ShippingMixedEntrySoundness.extend a ((nm, .bool), id) bools bits) hrest ho' c
      | bits n =>
        exact ih ids (i + 1)
          (Tools.ShippingMixedEntrySoundness.extend a ((nm, .bits n), id) bools bits) hrest ho' c

end Tools.ShippingLegacySem
