import Tools.ShippingLegacySemBinderList

/-! # The legacy binder walk over a list WITH non-hardware binders (the domain binder)

`bindInputsLegacy_prepare` (`Tools/ShippingLegacySemBinderList.lean`) covers
`bits n` / `bool` Signal binders and excludes the kind `.domain`. Every
legacy-route declaration for which the real entry returns has exactly one
domain binder (census, round 20: 90 of 90), so that theorem covers none of
them.

**What the walk does on a binder that is not a hardware Signal**
(`Sparkle/Compiler/Elab.lean`, `bindInputsLegacy`, 2110–2146; for
`{dom : DomainConfig}`):

1. `fvarId.getDecl` (2115);
2. no parameter matches (2118–2120, `parameters = []`);
3. `isSignalBinderType binderType` (2126): its RESULT is not used when
   `symbolicMode = false` (the test at 2127 is `symbolicMode && isSignalArg`),
   only its frame;
4. `try (inferHWTypeFromSignal binderType; pure true) catch _ => pure false`
   (2135–2138). For `DomainConfig`: `inferHWTypeFromSignal` → not a `Signal`
   application → `inferHWTypeWithDimensions` → (not symbolic) `inferHWType`
   (539–622) → the structure arm: a field of type `Nat` has no hardware type
   → `none` → `throwError "Cannot infer hardware type from …"` (762–773). The
   handler yields `false`;
5. `if isHWArg … else bindInputsLegacy … (i + 1) k` (2139–2144): the binder is
   SKIPPED — no port, no variable mapping.

So the binder is skipped exactly when the `try`'s body has no returning run
that… — precisely: `isHWArg = false` comes from the handler; `isHWArg = true`
comes from a returning run of the oracle. The premise that makes the skip
the ONLY outcome:

**`InfersNothing T`** — the hardware-type oracle has no returning run on `T`.
(The opposite of `InfersHW T hw`; the same class: the oracle on one type.
`Throws` is not needed: a returning walk whose `try` body did not return went
through the handler.)

**Defined here**: `InfersNothing`; `TypeOk k T` — the oracle facts of a
binder of kind `k` on its declared type (`.domain`: `InfersNothing T`;
`.bits n` / `.bool`: `InfersHW T (kindHW k) ∧ InfersNoCatch T`);
`DeclsAtD mctx xs i bs ids` — the variables from index `i` are `ids`,
declared in `mctx` with the names of `bs` and types satisfying `TypeOk`.
(The declared type is no longer a component of the binder list: in a real
telescope the type of a later binder mentions the domain VARIABLE, so it is
not a fixed expression; the facts about it are stated where the declaration
is.)

**Proved here**

* `bindInputsLegacy_step_skip` — one variable whose type has
  `InfersNothing`: a successful run of the walk from `i` is a successful run
  from `i + 1`, same context, same compiler context and states.
* `bindInputsLegacy_prepareD` — the list, with the three kinds: the
  conclusion of `prepare_returns` for `bs.zip ids` (`prepare`'s step for a
  `.domain` binder is the identity, as in the certified walk).

Program shapes: S0–S5 of `Tools/ShippingLegacySemBinder.lean` (built);
`bindInputsLegacy_step_skip` is `bindInputsLegacy_step` with S4 inverted by
`returns_tryCatch` and the other branch of S5 taken. -/
namespace Tools.ShippingLegacySem
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.Builder
open Sparkle.IR.Type (HWType)
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- The hardware-type oracle has no returning run on `T`. -/
def InfersNothing (T : Lean.Expr) : Prop :=
  ∀ (ctx : CompilerState) (s t : CircuitState) (h : HWType),
    ¬ Returns (inferHWTypeFromSignal T) ctx s h t

/-- The oracle facts of a binder of kind `k` on its declared type `T`. -/
def TypeOk : MixedGateBinder → Lean.Expr → Prop
  | .domain, T => InfersNothing T
  | .bool, T => InfersHW T .bit ∧ InfersNoCatch T
  | .bits n, T => InfersHW T (.bitVector n) ∧ InfersNoCatch T

/-- The telescope's variables from index `i` on are the variables `ids`,
declared in `mctx` with the names of `bs` and types on which the oracle
behaves as the binder's kind requires; nothing follows them. -/
def DeclsAtD (mctx : Meta.Context) (xs : Array Lean.Expr) :
    Nat → List (Name × MixedGateBinder) → List FVarId → Prop
  | i, [], [] => xs.size ≤ i
  | i, q :: bs, id :: ids =>
    (∃ h : i < xs.size, (xs[i]'h).fvarId! = id ∧
      ∃ d0 : LocalDecl, mctx.lctx.find? id = some d0 ∧ d0.userName = q.1 ∧
        TypeOk q.2 d0.type) ∧
    DeclsAtD mctx xs (i + 1) bs ids
  | _, _, _ => False

theorem DeclsAtD.length {mctx : Meta.Context} {xs : Array Lean.Expr}
    (bs : List (Name × MixedGateBinder)) :
    ∀ (ids : List FVarId) (i : Nat), DeclsAtD mctx xs i bs ids → ids.length = bs.length := by
  induction bs with
  | nil =>
    intro ids i hd
    cases ids with
    | nil => rfl
    | cons id ids => exact False.elim hd
  | cons q bs ih =>
    intro ids i hd
    cases ids with
    | nil => exact False.elim hd
    | cons id ids =>
      obtain ⟨_, hrest⟩ := hd
      exact congrArg (· + 1) (ih ids (i + 1) hrest)

/-- **One step of the legacy walk on a non-hardware binder**: the variable is
skipped. -/
theorem bindInputsLegacy_step_skip {xs : Array Lean.Expr} {i : Nat} {id : FVarId}
    {d0 : LocalDecl} {mctx : Meta.Context} {k : CompilerM String} {ctx : CompilerState}
    {s t : CircuitState} {r : String}
    (h0 : i < xs.size) (hx : (xs[i]'h0).fvarId! = id)
    (hfind : mctx.lctx.find? id = some d0)
    (hsig : SignalTestFrame d0.type) (hno : InfersNothing d0.type)
    (hrun : RunsIn (bindInputsLegacy [] false xs i k) mctx ctx s r t) :
    RunsIn (bindInputsLegacy [] false xs (i + 1) k) mctx ctx s r t := by
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
  -- S2: no parameter; the Signal test (only its frame is used)
  first
    | (obtain ⟨sg, s2, hsg, b1⟩ := RunsIn.bind a2)
    | (simp only [List.find?, Option.map] at a2
       obtain ⟨sg, s2, hsg, b1⟩ := RunsIn.bind a2)
  have hs2 : s2 = s := hsig ctx s s2 sg (RunsIn.returns hsg)
  rw [hs2] at b1
  -- S3: not symbolic
  rcases RunsIn.ite b1 with ⟨hsym, _⟩ | ⟨_, b2⟩
  · exact absurd (show false = true from hsym) Bool.false_ne_true
  -- S4: the `try` around the type oracle: its body has no returning run, so
  -- the handler ran and yielded `false`, from the same state
  obtain ⟨hwb, s3, htry, b3⟩ := RunsIn.bind b2
  have hs3 : s3 = s ∧ hwb = false := by
    rcases returns_tryCatch (RunsIn.returns htry) with hbody | ⟨ex, hhand⟩
    · obtain ⟨hw0, s4, hi0, _⟩ := Returns.bind hbody
      exact absurd hi0 (hno ctx s s4 hw0)
    · obtain ⟨hb, hs⟩ := Returns.pure hhand
      exact ⟨hs, hb⟩
  rw [hs3.1] at b3
  -- S5: `isHWArg` is `false`
  rcases RunsIn.ite b3 with ⟨hT, _⟩ | ⟨_, c1⟩
  · exact absurd (hs3.2.symm.trans hT) Bool.false_ne_true
  · exact c1

/-- **The legacy binder walk over a list of binders — `bits n`, `bool`, and
non-hardware (`.domain`) ones — reaches the prepared setup.** -/
theorem bindInputsLegacy_prepareD {mctx : Meta.Context} {bools : FVarId → Bool}
    {bits : (id : FVarId) → (n : Nat) → BitVec n} {xs : Array Lean.Expr}
    {k : CompilerM String} {r : String} {t : CircuitState}
    (bs : List (Name × MixedGateBinder)) :
    ∀ (ids : List FVarId) (i : Nat) (a : Tools.ShippingMixedEntrySoundness.Setup),
      DeclsAtD mctx xs i bs ids →
      RunsIn (bindInputsLegacy [] false xs i k) mctx a.context a.state r t →
      Returns k
        (Tools.ShippingMixedEntrySoundness.prepare bools bits (bs.zip ids) a).context
        (Tools.ShippingMixedEntrySoundness.prepare bools bits (bs.zip ids) a).state
        r t := by
  induction bs with
  | nil =>
    intro ids i a hd hrun
    cases ids with
    | nil =>
      have hle : xs.size ≤ i := hd
      exact bindInputsLegacy_done_returns (RunsIn.returns hrun) hle
    | cons id ids => exact False.elim hd
  | cons q bs ih =>
    intro ids i a hd hrun
    cases ids with
    | nil => exact False.elim hd
    | cons id ids =>
      obtain ⟨nm, kind⟩ := q
      obtain ⟨⟨h0, hx, d0, hfind, hnm, hto⟩, hrest⟩ := hd
      have hnm' : d0.userName = nm := hnm
      cases kind with
      | domain =>
        have hno : InfersNothing d0.type := hto
        have c := bindInputsLegacy_step_skip h0 hx hfind (isSignalBinderType_frame d0.type) hno
          hrun
        exact ih ids (i + 1) a hrest c
      | bool =>
        have hto' : InfersHW d0.type .bit ∧ InfersNoCatch d0.type := hto
        have c := bindInputPort_runsIn
          (bindInputsLegacy_step h0 hx hfind (isSignalBinderType_frame d0.type) hto'.1 hto'.2
            hrun)
        rw [hnm'] at c
        exact ih ids (i + 1)
          (Tools.ShippingMixedEntrySoundness.extend a ((nm, .bool), id) bools bits) hrest c
      | bits n =>
        have hto' : InfersHW d0.type (.bitVector n) ∧ InfersNoCatch d0.type := hto
        have c := bindInputPort_runsIn
          (bindInputsLegacy_step h0 hx hfind (isSignalBinderType_frame d0.type) hto'.1 hto'.2
            hrun)
        rw [hnm'] at c
        exact ih ids (i + 1)
          (Tools.ShippingMixedEntrySoundness.extend a ((nm, .bits n), id) bools bits) hrest c

end Tools.ShippingLegacySem
