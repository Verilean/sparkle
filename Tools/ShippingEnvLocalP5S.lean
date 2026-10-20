import Tools.ShippingEnvLocal

/-! # Which branch of `LocalStruct.p5s` is dischargeable without an environment law (reviewer task C)

BUILT as written (worker O-P5S, from poc 677f4cdb; integrator run gt1, no fixes). No `sorry`, no new axiom, no `native_decide`. New
file; nothing existing is changed; nothing is added to `RefLaws` or to any trusted / allowed-premise list;
no `envGet` / `envFrame` / `InstAgree`.

## Result (negative for real children)

`LocalStruct.p5s` is an implication with two hypotheses about the witnessed run `R`:
(a) `entryConst … R.ci … ≠ R.ci` (the run UNFOLDED) and (b) `declOuts?` of `userInliner R.envR dD.type`.

* **Branch (a) false — "the run keeps the declaration".** The ONLY environment-free sufficient condition
  for `entryConst true false [] ci isInst inl projs = ci` is that a gate accepts `ci` itself:
  `certifiedShape? false [] ci` (here `keepCheck`, a decidable `Bool` of the witnessed constant alone), or
  an `isInst`-free disjunct of `mixedCertifiedShape?`. Every other way of keeping `ci` is "all three
  readers miss `inlinedConst (userInliner envR) ci`", which needs the value of `userInliner`.
  `keepCheck` is SOUND (`entryConst_of_keepCheck`, `p5s_of_keepCheck`, `localStruct_of_keepCheck`: p5s
  eliminated), BUT it is UNSATISFIABLE for every machine child: `MachineDefines` says both gates miss the
  ENTRY constant, and `gates_miss_of_entryConst` (proved, general) shows they then miss `ci` itself;
  hence `keepCheck_false_of_defines : MachineDefines … c sc → ∀ R : ChildRunW … c sc, keepCheck R.ci = false`.
  The same argument kills the `isInst`-free mixed disjuncts (`gates_miss_of_entryConst`.2 is for the
  run's own `instancePredicate R.envR`, and those disjuncts do not read the predicate). So this branch
  discharges `p5s` for NO real child; it is recorded so that the route is closed, not as progress.

* **Branch (b) — "the inliner does not change `declOuts?` of the type".** NOT provable for any type,
  with or without a per-declaration syntactic check. Missing step: `userInliner env e` is
  `inlFoldNat (inlAbbrevs env 4 X)` with `X = rounds 64 e1` or `X = e1` (`e1` = `inlineDefs …`, total),
  chosen by `MachRecUnfold.relevantClosure`, and `rounds` iterates `MachRecUnfold.pass`. Both
  `relevantClosure` and `passM` (hence `pass`) are `partial def`s, i.e. logically OPAQUE constants: no
  equation about their values is derivable, so neither which branch is taken nor what `pass` returns can
  be proved (`rounds 64 e1 = e1` would need `pass … e1 = e1`). A check `userInliner R.envR dD.type == dD.type`
  is a Bool of the run, but it cannot be established by `decide`/kernel evaluation (it evaluates opaque
  constants on an `Environment`) and it is not recorded by the compiler; asserting it is a new runtime
  fact. So branch (b) needs either an equation for `relevantClosure`/`passM` (a new law about the
  compiled code) or a compiler change (e.g. a non-`partial` total pass, or the entry recording the
  unfolding's type) — both outside this task's rules.

* **`typeAgree` / `fieldsAgree`.** Each compares two DIFFERENT environments (`R.envC`/`R.envR` vs the
  parent's `envP`); `userStructure?` reads `getStructureInfo?`, `isClass`, `getModuleIdxFor?`, `find?` of
  the environment at every name, so no environment-free condition on the head `s` decides either side.
  Not dischargeable without `envGet`/`envFrame` (unchanged from `Tools/ShippingEnvLocal.lean`).
  (A scalar-result child — `resBody` head `Signal` — makes `StructRes` vacuous, but then `StructOrigin`,
  the hypothesis of every `ChildLinkStruct` use, is false too: no gain at the use site, so not added.)

## Premise accounting

| premise | status here |
|---|---|
| `p5s` | ELIMINATED only under `keepCheck R.ci = true` (`localStruct_of_keepCheck`); that premise is PROVED FALSE for every child with `MachineDefines` (`keepCheck_false_of_defines`). Net for real children: UNCHANGED (open) |
| `typeAgree`, `fieldsAgree` | UNCHANGED (open; need envGet/envFrame, not added) |
| `IS`, `NS`, `entry`, `hy`, `hS`, `hkid` | UNCHANGED (not touched) |

No new theorem restates an existing one with the same premises. -/
namespace Tools.ShippingEnvLocalP5S
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEnvLocal (ChildRunW LocalStruct)
open Tools.ShippingMachineEntry (MachineDefines)
open Tools.ShippingMachineShapeUnfold (declOuts?)

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The environment-free keep check** on the witnessed constant: the combinational gate accepts the
declaration as read. Decidable; reads nothing but `ci`. -/
def keepCheck (ci : ConstantInfo) : Bool :=
  (certifiedShape? false [] ci).isSome

/-- **Soundness of `keepCheck`**: the entry keeps the declaration, for EVERY predicate, inliner and
structure facts (no environment read). -/
theorem entryConst_of_keepCheck {ci : ConstantInfo} (hk : keepCheck ci = true)
    (isInst : Lean.Expr → Bool) (inl : Lean.Expr → Lean.Expr) (projs : StructEnv) :
    entryConst true false [] ci isInst inl projs = ci := by
  obtain ⟨a, hA⟩ := Option.isSome_iff_exists.mp hk
  simp [entryConst, hA]  -- UNSURE: closing the `if` after `(some a).isNone` rewrites to `false`

/-- **`p5s` field from `keepCheck`** (the unfolding hypothesis is refuted). -/
theorem p5s_of_keepCheck {c : Name} {sc : MachineShape} (R : ChildRunW mref cref c sc)
    (hk : keepCheck R.ci = true) :
    ∀ dD : DefinitionVal, R.ci = .defnInfo dD →
      entryConst true false [] R.ci (instancePredicate R.envR) (userInliner R.envR)
        (structEnv R.envR) ≠ R.ci →
      ∀ o, declOuts? (structEnv R.envR) (userInliner R.envR dD.type) = some o →
        declOuts? (structEnv R.envR) dD.type = some o := by
  intro dD _ hne
  exact absurd (entryConst_of_keepCheck hk _ _ _) hne

/-- **`LocalStruct` without the `p5s` premise**, under `keepCheck`. (See
`keepCheck_false_of_defines`: the premise never holds for a machine child.) -/
theorem localStruct_of_keepCheck {c : Name} {sc : MachineShape} {envP : Environment}
    {R : ChildRunW mref cref c sc} (hk : keepCheck R.ci = true)
    (hT : ∀ ci₁ ci₂ : ConstantInfo, R.envC.find? c = some ci₁ → envP.find? c = some ci₂ →
      ci₁.type = ci₂.type)
    (hF : ∀ (kinds : List MixedGateBinder) (ty : Lean.Expr),
      (structEnv envP).instS c = some (kinds, ty) →
      ∀ (s : Name) (ls : List Lean.Level),
        (Tools.ShippingCallWidthsStructRes.resBody ty).getAppFn = .const s ls →
        userStructure? envP s = userStructure? R.envR s) :
    LocalStruct envP R :=
  ⟨hT, hF, p5s_of_keepCheck R hk⟩

/-- **Gates that miss the entry constant miss the declaration** (general; no environment). -/
theorem gates_miss_of_entryConst {ci : ConstantInfo} {isInst : Lean.Expr → Bool}
    {inl : Lean.Expr → Lean.Expr} {projs : StructEnv}
    (h1 : certifiedShape? false [] (entryConst true false [] ci isInst inl projs) = none)
    (h2 : mixedCertifiedShape? false [] (entryConst true false [] ci isInst inl projs) isInst = none) :
    certifiedShape? false [] ci = none ∧ mixedCertifiedShape? false [] ci isInst = none := by
  cases hA : certifiedShape? false [] ci with
  | some a =>
    exfalso
    have hE : entryConst true false [] ci isInst inl projs = ci := by
      simp [entryConst, hA]
    rw [hE, hA] at h1
    cases h1
  | none =>
    refine ⟨rfl, ?_⟩
    cases hB : mixedCertifiedShape? false [] ci isInst with
    | none => rfl
    | some b =>
      exfalso
      have hE : entryConst true false [] ci isInst inl projs = ci := by
        simp [entryConst, hA, hB]
      rw [hE, hB] at h2
      cases h2

/-- **The keep check never fires on a machine child**: for every witnessed run of a callee with
`MachineDefines`, `keepCheck R.ci = false`. So `localStruct_of_keepCheck` discharges nothing real. -/
theorem keepCheck_false_of_defines {mctx : Meta.Context} {cctx : Core.Context} {c : Name}
    {sc : MachineShape} (entry : MachineDefines mctx mref cctx cref c sc)
    (R : ChildRunW mref cref c sc) : keepCheck R.ci = false := by
  have entry' : MachineDefines R.mctx mref R.cctx cref c sc :=
    Tools.ShippingReflectCtx.MachineDefines.ctx entry
  obtain ⟨h1, h2, -⟩ :=
    entry' R.w1 R.ci R.w2 R.w5 R.envR R.w6 R.w5 R.envR R.w6 R.get R.henv R.henv
  have hA := (gates_miss_of_entryConst h1 h2).1
  unfold keepCheck
  rw [hA]
  rfl

end Tools.ShippingEnvLocalP5S
