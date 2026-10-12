import Tools.ShippingLegacySemRunInCalc

/-! # The legacy binder walk on ONE `bits n` binder

`bindInputsLegacy parameters symbolicMode xs i k` (`Sparkle/Compiler/Elab.lean`)
walks the telescope's variables; for each it reads the declaration from the
`Meta` local context (`fvarId.getDecl`), asks two type oracles and binds an
input port — or SKIPS the variable. The certified walk
`bindMixedCertifiedInputs k [((nm, .bits n), id)]` is
`bindInputPort id nm.toString (.bitVector n) k`.

**Proved here** (`bindInputsLegacy_one`): with no parameters, not symbolic,
`xs = #[.fvar id]`, in a context `mctx` whose local context declares `id` as
`d0`, a successful run of the legacy walk is

* a successful run of the certified walk over `[((d0.userName, .bits n), id)]`
  — same compiler context, same builder states, same result —, OR
* a successful run of the continuation `k` alone from the same builder state:
  the binder was SKIPPED (third outcome, see below).

**Oracle premises, classified**

| Premise | Statement | Class |
|---|---|---|
| `hfind` | `mctx.lctx.find? id = some d0` | what the telescope installed (delivered by the Meta-library fact about `lambdaTelescope`) |
| `SignalTestFrame d0.type` | every successful run of `isSignalBinderType` on the binder's type leaves the builder state | PROVABLE (one lifted `whnf`, then a pure `match`); proved separately in `Tools/ShippingLegacySemSignalFrame.lean` so that a failure there does not block this file |
| `InfersBits d0.type n` | every successful run of `inferHWTypeFromSignal` on the binder's type returns `.bitVector n` and leaves the builder state | oracle result (reflection of `whnf` / the environment through the type oracle; same class as `hunfE`) |

**The third outcome, kept as a disjunct.** With `symbolicMode = false` the
walk first runs `try (inferHWTypeFromSignal ty; pure true) catch _ => pure
false`. If the oracle THROWS inside the `try`, the handler yields `false` and
the binder gets no port: the walk continues with `k`. `Returns` / `RunsIn`
describe successful runs only, so "the oracle did not throw in this run"
cannot be stated with them, and a premise "the oracle never throws" would be
false of some worlds (interrupts, heartbeats). The skipped run is therefore
the second disjunct of the conclusion. (In the proof it arises only from the
`else` branch of `if isHWArg`.)

**Program shapes EXPECTED at each inversion (not observed)** — after
`unfold bindInputsLegacy` at `parameters = []`, `symbolicMode = false`, `i = 0`:

```
S0  if h : 0 < xs.size then B h else k                                  (dite)
S1  B h = let x := xs[0]; let fvarId := x.fvarId!;
          CompilerM.liftMetaM fvarId.getDecl >>= fun decl => R decl      (bind, lifted oracle)
S2  R decl = let binderName := decl.userName; let binderType := decl.type;
             let parameterDefault? := ([].find? …).map (·.2);
             match parameterDefault? with | some _ => … | none => N
    the unifier must reduce `Option.map _ (List.find? _ [])` to `none` and
    the `match` on it, to see
    N = isSignalBinderType decl.type >>= fun isSignalArg => I isSignalArg   (bind)
S3  I b = if (false && b) = true then … else E                           (ite, terminal)
S4  E = tryCatch (inferHWTypeFromSignal decl.type >>= fun _ => pure true)
                 (fun _ => pure false) >>= fun isHWArg => J isHWArg       (bind of a tryCatch)
S5  J b = if b = true then
            inferHWTypeFromSignal decl.type >>= fun hwType =>
              bindInputPort fvarId decl.userName.toString hwType
                (bindInputsLegacy [] false xs (0 + 1) k)
          else bindInputsLegacy [] false xs (0 + 1) k                     (ite, terminal)
S6  bindInputsLegacy [] false xs (0 + 1) k = k   (second unfold, `dif_neg`)
```

If S2 fails, the alternative in the `first` normalises the two list/option
functions with `simp only` (on this small residual program only). -/
namespace Tools.ShippingLegacySem
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-! ## The oracle premises -/

/-- Every successful run of the Signal test on `T` leaves the builder state. -/
def SignalTestFrame (T : Lean.Expr) : Prop :=
  ∀ (ctx : CompilerState) (s t : CircuitState) (b : Bool),
    Returns (isSignalBinderType T) ctx s b t → t = s

/-- Every successful run of the hardware-type oracle on `T` returns
`.bitVector n` and leaves the builder state. -/
def InfersBits (T : Lean.Expr) (n : Nat) : Prop :=
  ∀ (ctx : CompilerState) (s t : CircuitState) (hw : Sparkle.IR.Type.HWType),
    Returns (inferHWTypeFromSignal T) ctx s hw t → hw = .bitVector n ∧ t = s

/-! ## Small steps -/

/-- An `if` at the head of a `CompilerM` program (as `returns_ite` of
`Tools/ShippingLegacySemSteps.lean`; repeated to keep this file's imports
small). -/
theorem returns_if {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    {ctx : CompilerState} {s t : CircuitState} {r : α}
    (h : Returns (if c then a else b) ctx s r t) :
    (c ∧ Returns a ctx s r t) ∨ (¬c ∧ Returns b ctx s r t) := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact Or.inl ⟨hc, h⟩
  · rw [if_neg hc] at h
    exact Or.inr ⟨hc, h⟩

/-- Past the last variable the walk is its continuation. -/
theorem bindInputsLegacy_done {parameters : List (String × Nat)} {symbolicMode : Bool}
    {xs : Array Lean.Expr} {i : Nat} {k : CompilerM String} (h : xs.size ≤ i) :
    bindInputsLegacy parameters symbolicMode xs i k = k := by
  first
    | (unfold bindInputsLegacy
       exact dif_neg (Nat.not_lt.mpr h))
    | (rw [bindInputsLegacy]
       exact dif_neg (Nat.not_lt.mpr h))
    | (rw [bindInputsLegacy, dif_neg (Nat.not_lt.mpr h)])

theorem bindInputsLegacy_done_returns {parameters : List (String × Nat)} {symbolicMode : Bool}
    {xs : Array Lean.Expr} {i : Nat} {k : CompilerM String} {ctx : CompilerState}
    {s t : CircuitState} {r : String}
    (hr : Returns (bindInputsLegacy parameters symbolicMode xs i k) ctx s r t)
    (h : xs.size ≤ i) : Returns k ctx s r t := by
  rw [bindInputsLegacy_done h] at hr
  exact hr

theorem bindInputPort_done_returns {parameters : List (String × Nat)} {symbolicMode : Bool}
    {xs : Array Lean.Expr} {i : Nat} {k : CompilerM String} {ctx : CompilerState}
    {s t : CircuitState} {r : String} {fid : FVarId} {nm : String}
    {hw : Sparkle.IR.Type.HWType}
    (hr : Returns (bindInputPort fid nm hw (bindInputsLegacy parameters symbolicMode xs i k))
      ctx s r t)
    (h : xs.size ≤ i) : Returns (bindInputPort fid nm hw k) ctx s r t := by
  rw [bindInputsLegacy_done h] at hr
  exact hr

/-- The port's variable, replaced along an equation (no rewriting at the use
site). -/
theorem bindInputPort_congr_id {α : Type} {a b : FVarId} {nm : String}
    {hw : Sparkle.IR.Type.HWType} {k : CompilerM α} {ctx : CompilerState} {s t : CircuitState}
    {r : α} (e : a = b) (h : Returns (bindInputPort a nm hw k) ctx s r t) :
    Returns (bindInputPort b nm hw k) ctx s r t := by
  subst e
  exact h

/-- The certified walk over one `bits n` binder is one `bindInputPort`. -/
theorem bindMixed_one_bits {α : Type} (k : CompilerM α) (nm : Name) (n : Nat) (id : FVarId) :
    bindMixedCertifiedInputs k [((nm, MixedGateBinder.bits n), id)] =
      bindInputPort id nm.toString (.bitVector n) k := by
  first
    | rfl
    | (unfold bindMixedCertifiedInputs
       rfl)
    | simp [bindMixedCertifiedInputs]

/-! ## The walk -/

/-- **The legacy walk on one variable**, the variable given by an equation on
`xs[0]` (so that the proof never rewrites the program's own `xs[0].fvarId!`). -/
theorem bindInputsLegacy_one_raw {xs : Array Lean.Expr} {id : FVarId} {d0 : LocalDecl}
    {n : Nat} {mctx : Meta.Context} {k : CompilerM String} {ctx : CompilerState}
    {s t : CircuitState} {r : String}
    (hsz : xs.size = 1)
    (hx : ∀ h : 0 < xs.size, (xs[0]'h).fvarId! = id)
    (hfind : mctx.lctx.find? id = some d0)
    (hsig : SignalTestFrame d0.type) (hinf : InfersBits d0.type n)
    (hrun : RunsIn (bindInputsLegacy [] false xs 0 k) mctx ctx s r t) :
    Returns (bindMixedCertifiedInputs k [((d0.userName, MixedGateBinder.bits n), id)])
        ctx s r t ∨
      Returns k ctx s r t := by
  -- (no `rw [hsz]` on these goals: `rw` closes a goal it can prove by `rfl`,
  -- and the next tactic would then find no goal)
  have h0 : 0 < xs.size := by
    first | omega | exact Nat.lt_of_lt_of_eq Nat.zero_lt_one hsz.symm
  have hle : xs.size ≤ 0 + 1 := by
    first | omega | exact Nat.le_of_eq hsz
  -- S0
  first
    | unfold bindInputsLegacy at hrun
    | rw [bindInputsLegacy] at hrun
  have a1 := RunsIn.dite_pos hrun h0
  -- S1: the declaration, read from the context
  obtain ⟨decl, s1, hd, a2⟩ := RunsIn.bind a1
  obtain ⟨hdm, hs1⟩ := RunsIn.liftMetaM hd
  have hde : decl = d0 := getDecl_runsIn_find (hx h0) hfind hdm
  rw [hs1] at a2
  rw [hde] at a2
  -- from here on the context is not read: `Returns`
  have b0 := RunsIn.returns a2
  -- S2: no parameter; the Signal test
  first
    | (obtain ⟨sg, s2, hsg, b1⟩ := Returns.bind b0)
    | (simp only [List.find?, Option.map] at b0
       obtain ⟨sg, s2, hsg, b1⟩ := Returns.bind b0)
  have hs2 : s2 = s := hsig ctx s s2 sg hsg
  rw [hs2] at b1
  -- S3: not symbolic
  rcases returns_if b1 with ⟨hsym, _⟩ | ⟨_, b2⟩
  · exact absurd (show false = true from hsym) Bool.false_ne_true
  -- S4: the `try` around the type oracle; both of its outcomes leave the state
  obtain ⟨hwb, s3, htry, b3⟩ := Returns.bind b2
  have hs3 : s3 = s := by
    rcases returns_tryCatch htry with hbody | ⟨ex, hhand⟩
    · obtain ⟨hw0, s4, hi0, hp0⟩ := Returns.bind hbody
      obtain ⟨_, hs4⟩ := hinf ctx s s4 hw0 hi0
      rw [hs4] at hp0
      exact (Returns.pure hp0).2
    · exact (Returns.pure hhand).2
  rw [hs3] at b3
  -- S5
  rcases returns_if b3 with ⟨_, c1⟩ | ⟨_, c1⟩
  · -- the port is bound
    obtain ⟨hw1, s5, hi1, c2⟩ := Returns.bind c1
    obtain ⟨hw1eq, hs5⟩ := hinf ctx s s5 hw1 hi1
    rw [hs5] at c2
    rw [hw1eq] at c2
    -- S6
    have c3 := bindInputPort_done_returns c2 hle
    have c4 := bindInputPort_congr_id (hx h0) c3
    refine Or.inl ?_
    rw [bindMixed_one_bits]
    exact c4
  · -- the binder is skipped
    exact Or.inr (bindInputsLegacy_done_returns c1 hle)

/-- **The legacy binder walk on one `bits n` binder.** In a context whose
local context declares `id` as `d0`, a successful run of the legacy walk over
`#[.fvar id]` is a run of the certified walk over
`[((d0.userName, .bits n), id)]`, or (the type oracle threw inside the walk's
`try`) a run of the continuation with no port bound. -/
theorem bindInputsLegacy_one {id : FVarId} {d0 : LocalDecl} {n : Nat} {mctx : Meta.Context}
    {k : CompilerM String} {ctx : CompilerState} {s t : CircuitState} {r : String}
    (hfind : mctx.lctx.find? id = some d0)
    (hsig : SignalTestFrame d0.type) (hinf : InfersBits d0.type n)
    (hrun : RunsIn (bindInputsLegacy [] false #[Lean.Expr.fvar id] 0 k) mctx ctx s r t) :
    Returns (bindMixedCertifiedInputs k [((d0.userName, MixedGateBinder.bits n), id)])
        ctx s r t ∨
      Returns k ctx s r t := by
  have hsz : (#[Lean.Expr.fvar id] : Array Lean.Expr).size = 1 := by
    first | rfl | simp
  have hx : ∀ h : 0 < (#[Lean.Expr.fvar id] : Array Lean.Expr).size,
      ((#[Lean.Expr.fvar id] : Array Lean.Expr)[0]'h).fvarId! = id := by
    intro h
    first | rfl | simp [Lean.Expr.fvarId!] | (simp; rfl)
  exact bindInputsLegacy_one_raw hsz hx hfind hsig hinf hrun

end Tools.ShippingLegacySem
