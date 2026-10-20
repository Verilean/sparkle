import Tools.ShippingEnvRead
import Tools.ShippingInstSubstModel

/-! # Run-local structure link, and an isolated model-reader variant of `instRes`

BUILT as written (worker O-ENVL, from poc 58b240ba; run el1 exit 0, no fixes; axioms run axl: all [propext, Classical.choice, Quot.sound] or fewer). `LocalStruct` is NOT discharged (needs envGet/envFrame, docs/parallel/O-env-audit.md; no new runtime law approved). No `sorry`, no new axiom, no
`native_decide`. New file; nothing existing is changed (the global theorems `structResAt_of_parts`,
`childLinkStruct_real_of_parts`, `declTypeRead_of_envAt`, `fieldsAt_of_envAt` are untouched). No field is
added to `RefLaws` or to any trusted / allowed-premise list.

## Part 1 — run-local DR / FA / P5S (`childLinkStruct_realL`)

`DeclTypeReadAt` (DR), `FieldsAt` (FA), `P5SAt` and `StructResAt` quantify over EVERY run of
`getConstInfo c` / `getEnv` from any world and any contexts. `childLinkStruct_real` only ever applies them to
ONE run: the callee's entry run that `entryLink_real` extracts from `RealChild` + `MachineDefines`.
`ChildRunW mref cref c sc` packages exactly that witnessed run (its `getConstInfo c` run at `w1` returning
`ci`, its `getEnv` run at `w5` returning `envR`, the entry constant `dE`, the shape), PLUS the environment
`envC` that `getConstInfo_find` (built) shows the `getConstInfo` run read (a `getEnv` run from the same `w1`,
`envC.find? c = some ci`). `childRunW_of_real` proves such a record exists for every real child.
`LocalStruct envP R` collects the remaining facts, each about the environments of THAT record only:

* `typeAgree` — the constant `envC` gives at the ONE name `c` has the type `envP` gives there
  (implied by `envC.find? c = envP.find? c`: `LocalStruct.ofFind`);
* `fieldsAgree` — `userStructure? envP s = userStructure? R.envR s` at the head constant `s` of `c`'s
  declared result body (one name, determined by `envP` and `c`);
* `p5s` — P5S for THIS run's entry constant on the unfolding branch only.

`localStruct_of_global` proves the old global premises imply `LocalStruct envP R` for every `R`, so the new
theorems are never weaker than the old ones (`childLinkStruct_real_of_parts` factors through them).

### Premise accounting, `childLinkStruct_real_of_parts` (before) → `childLinkStruct_realL` (after)

| before | after | kind of change |
|---|---|---|
| `DR : DeclTypeReadAt mref cref envP c` (all runs, all worlds) | `typeAgree` of the witnessed run: `R.envC.find? c = some ci₁ → envP.find? c = some ci₂ → ci₁.type = ci₂.type` | ELIMINATED as a lookup law (the `getConstInfo`-reads-`find?` part is PROVED by `getConstInfo_find`); the remaining environment agreement is LOCALISED to one environment (`R.envC`) and one name (`c`) |
| `FA : FieldsAt mref cref envP c` (all `getEnv` runs) | `fieldsAgree` at `R.envR` only | LOCALISED (one environment, one head constant) |
| `P5S : P5SAt mref cref c` (all runs) | `p5s` at `R.ci`, `R.envR` only | LOCALISED (one run) |
| `IS : InstSubst` | `IS : InstSubst` | UNCHANGED (derivable from `InstAgree` by `instSubst_of_agree`; not eliminated for the real reader — see Part 2) |
| `NS : userStructure? envP Signal = none` | same | UNCHANGED |
| `entry`, `hy`, `hS`, `hkid` | same | UNCHANGED |

Shape of the result: `childLinkStruct_realL` concludes `∃ R : ChildRunW …, LocalStruct envP R → ChildLinkStruct …`
— the local facts are asked of the run that EXISTS, not of all runs. A consumer that can discharge
`LocalStruct` only for a specific named run uses `childLinkStruct_of_run` directly. NOT discharged here:
`LocalStruct` itself. Discharging `typeAgree`/`fieldsAgree` for the actual runs needs the environment frame
facts identified in `docs/parallel/O-env-audit.md` (`envGet` + `envFrame`), which are NOT added (ruling: no new
runtime law); `p5s` has the same status as `P5At`.

## Part 2 — model-reader variant `instResM` (ISOLATED)

`instResM` is the candidate reader's `Tools.ShippingReaderFuel.instRes` with `Expr.instantiate1 b a`
replaced by the proved model `inst1M b 0 a`. `instResM_outs` / `instResM_head` / `structRes_of_declOutsM`
are proved directly from `instSubstM` (built, no hypothesis).

* ELIMINATED for the model variant: `InstSubst` (`structRes_of_declOutsM` has no substitution premise).
* NOTHING is claimed about production or about the candidate reader `instRes`: those call the extern
  `lean_expr_instantiate1`. `StructResM` is NOT `StructRes`. Connecting them still needs the open runtime
  boundary `InstAgree` (`instRes_eq_instResM : InstAgree → instRes ty args = instResM ty args`, stated only
  to locate the bridge; `InstAgree` is not established and not trusted). The production/runtime bridge
  status is unchanged.

## Unsure spots (not built)

See the report; marked `-- UNSURE` inline. -/
namespace Tools.ShippingEnvLocal
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv
open Tools.ShippingCallWidthsStrict Tools.ShippingCallWidthsDeclared Tools.ShippingCallWidthsEntry
open Tools.ShippingCallWidthsChildReal
open Tools.ShippingCallWidthsEntryFM
open Tools.ShippingCallWidthsStructLink
open Tools.ShippingCallWidthsStructRes
open Tools.ShippingEnvRead (getConstInfo_find)
open Tools.ShippingInstSubstModel (inst1M instSubstM InstAgree)
open Tools.ShippingMachineShapeUnfold (declOuts?)
open Tools.ShippingReaderFuelProv (StructOrigin)
open Tools.ShippingReaderFuel (instRes)
open Tools.ShippingInstSignature (instSignatureS?_some)

/-! ## Part 1: the witnessed child run -/

/-- **The callee's witnessed entry run** (what `entryLink_real` extracts), plus the environment `envC` the
`getConstInfo` run read (`getConstInfo_find`). -/
structure ChildRunW (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (c : Name) (sc : MachineShape) where
  mctx : Meta.Context
  cctx : Core.Context
  w1 : Void IO.RealWorld
  ci : ConstantInfo
  w2 : Void IO.RealWorld
  envC : Environment
  w3 : Void IO.RealWorld
  w5 : Void IO.RealWorld
  envR : Environment
  w6 : Void IO.RealWorld
  dE : DefinitionVal
  get : RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2
  readC : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w1 envC w3
  findC : envC.find? c = some ci
  henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6
  hE : entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) =
    .defnInfo dE
  hshape : machineShape? false [] (.defnInfo dE) (structEnv envR) = some sc

/-- **The local structure facts** of ONE witnessed run, against the parent's environment `envP`. -/
structure LocalStruct {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {sc : MachineShape} (envP : Environment) (R : ChildRunW mref cref c sc) : Prop where
  typeAgree : ∀ ci₁ ci₂ : ConstantInfo, R.envC.find? c = some ci₁ → envP.find? c = some ci₂ →
    ci₁.type = ci₂.type
  fieldsAgree : ∀ (kinds : List MixedGateBinder) (ty : Lean.Expr),
    (structEnv envP).instS c = some (kinds, ty) →
    ∀ (s : Name) (ls : List Lean.Level), (resBody ty).getAppFn = .const s ls →
      userStructure? envP s = userStructure? R.envR s
  p5s : ∀ dD : DefinitionVal, R.ci = .defnInfo dD →
    entryConst true false [] R.ci (instancePredicate R.envR) (userInliner R.envR)
      (structEnv R.envR) ≠ R.ci →
    ∀ o, declOuts? (structEnv R.envR) (userInliner R.envR dD.type) = some o →
      declOuts? (structEnv R.envR) dD.type = some o

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `typeAgree` from agreement of the two lookups at the one name `c`. -/
theorem LocalStruct.ofFind {c : Name} {sc : MachineShape} {envP : Environment}
    {R : ChildRunW mref cref c sc} (hfind : R.envC.find? c = envP.find? c)
    (hF : ∀ (kinds : List MixedGateBinder) (ty : Lean.Expr),
      (structEnv envP).instS c = some (kinds, ty) →
      ∀ (s : Name) (ls : List Lean.Level), (resBody ty).getAppFn = .const s ls →
        userStructure? envP s = userStructure? R.envR s)
    (hP : ∀ dD : DefinitionVal, R.ci = .defnInfo dD →
      entryConst true false [] R.ci (instancePredicate R.envR) (userInliner R.envR)
        (structEnv R.envR) ≠ R.ci →
      ∀ o, declOuts? (structEnv R.envR) (userInliner R.envR dD.type) = some o →
        declOuts? (structEnv R.envR) dD.type = some o) :
    LocalStruct envP R := by
  refine ⟨?_, hF, hP⟩
  intro ci₁ ci₂ h1 h2
  rw [hfind, h2] at h1
  obtain rfl := Option.some.inj h1
  rfl

/-- **Every real child has a witnessed run.** -/
theorem childRunW_of_real {c : Name} {sc : MachineShape} {y : Res}
    (entry : MachineDefines mctx mref cctx cref c sc) (hy : RealChild mref cref c y) :
    Nonempty (ChildRunW mref cref c sc) := by
  obtain ⟨mctx', cctx', w1, ci, w2, w5, envR, w6, dE, get, henv, hE, hshape⟩ :=
    entryLink_real entry hy
  obtain ⟨envC, w3, hC, hfind⟩ := getConstInfo_find c get  -- UNSURE: `getConstInfo` elaboration match
  exact ⟨⟨mctx', cctx', w1, ci, w2, envC, w3, w5, envR, w6, dE, get, hC, hfind, henv, hE, hshape⟩⟩

/-- **The local facts are implied by the old global premises** (so nothing is lost). -/
theorem localStruct_of_global {envP : Environment} {c : Name} {sc : MachineShape}
    (DR : DeclTypeReadAt mref cref envP c) (FA : FieldsAt mref cref envP c)
    (P5S : P5SAt mref cref c) (R : ChildRunW mref cref c sc) : LocalStruct envP R := by
  refine ⟨?_, ?_, ?_⟩
  · intro ci₁ ci₂ h1 h2
    rw [R.findC] at h1
    obtain rfl := Option.some.inj h1
    exact DR R.mctx R.cctx R.w1 R.ci R.w2 R.get ci₂ h2
  · intro kinds ty hI s ls hh
    exact FA R.mctx R.cctx R.w5 R.envR R.w6 R.henv kinds ty hI s ls hh
  · intro dD hci hne o hd
    exact P5S R.mctx R.cctx R.w1 R.ci R.w2 R.w5 R.envR R.w6 dD R.get R.henv hci hne o hd

/-- **`StructRes` at the witnessed run's entry constant**, from the local facts (no DR / FA / P5SAt). -/
theorem structRes_of_run {envP : Environment} {c : Name} {sc : MachineShape}
    (IS : InstSubst) (NS : userStructure? envP ``Sparkle.Core.Signal.Signal = none)
    (R : ChildRunW mref cref c sc) (L : LocalStruct envP R) :
    StructRes (structEnv envP) c (structEnv R.envR) R.dE := by
  refine structRes_of_declOuts (senvP := structEnv envP) (senvC := structEnv R.envR) (c := c)
    (dE := R.dE) IS NS ?_ ?_
  · intro kinds ty hI s ls hh
    exact L.fieldsAgree kinds ty hI s ls hh
  · intro kinds ty hI o hd
    have hI' : instSignatureS? envP c = some (kinds, ty) := hI
    obtain ⟨_, ci', hfind, _, hty, _⟩ := instSignatureS?_some hI'
    have hct : R.ci.type = ci'.type := L.typeAgree R.ci ci' R.findC hfind
    have hE := R.hE
    by_cases hne : entryConst true false [] R.ci (instancePredicate R.envR) (userInliner R.envR)
        (structEnv R.envR) = R.ci
    · rw [hne] at hE
      have hT : ty = R.dE.type := by
        rw [hty, ← hct, hE, defn_type]  -- UNSURE: rewriting the projection `R.ci`
      rw [hT]
      exact hd
    · rcases entryConst_cases R.ci (instancePredicate R.envR) (userInliner R.envR)
        (structEnv R.envR) with h | h
      · exact absurd h hne
      · rw [h] at hE
        obtain ⟨dD, hciD, hdty⟩ := inlinedConst_defn hE
        rw [hdty] at hd
        have hT : ty = dD.type := by
          rw [hty, ← hct, hciD, defn_type]
        rw [hT]
        exact L.p5s dD hciD hne o hd

/-- **`ChildLinkStruct` from ONE witnessed run and its local facts.** -/
theorem childLinkStruct_of_run {kidOuts : Nat → List OutField} {k : Nat}
    {envP : Environment} {c : Name} {r : MixedGateBinder} {nm : String} {sc : MachineShape}
    (IS : InstSubst) (NS : userStructure? envP ``Sparkle.Core.Signal.Signal = none)
    (R : ChildRunW mref cref c sc) (L : LocalStruct envP R)
    (hS : StructOrigin (structEnv envP) c r nm) (hkid : kidOuts k = sc.layout.outs) :
    ChildLinkStruct kidOuts k nm r :=
  childLinkStruct_of_origin hS (structRes_of_run IS NS R L) R.hshape hkid

/-- **`ChildLinkStruct` for the child really compiled, with run-LOCAL structure premises**: the real child
has a witnessed run `R`, and `LocalStruct envP R` (facts about `R`'s environments only) suffices. Replaces
`DR`, `FA`, `P5S` of `childLinkStruct_real_of_parts`. -/
theorem childLinkStruct_realL {kidOuts : Nat → List OutField} {k : Nat}
    {envP : Environment} {c : Name} {r : MixedGateBinder} {nm : String}
    {sc : MachineShape} {y : Res}
    (entry : MachineDefines mctx mref cctx cref c sc) (hy : RealChild mref cref c y)
    (IS : InstSubst) (NS : userStructure? envP ``Sparkle.Core.Signal.Signal = none)
    (hS : StructOrigin (structEnv envP) c r nm) (hkid : kidOuts k = sc.layout.outs) :
    ∃ R : ChildRunW mref cref c sc, LocalStruct envP R → ChildLinkStruct kidOuts k nm r := by
  obtain ⟨R⟩ := childRunW_of_real entry hy
  exact ⟨R, fun L => childLinkStruct_of_run IS NS R L hS hkid⟩

/-! ## Part 2: the model-reader variant (ISOLATED; nothing about production) -/

/-- `instRes` with the extern `Expr.instantiate1` replaced by the proved model `inst1M · 0 ·`. -/
def instResM : Lean.Expr → List Lean.Expr → Option Lean.Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: as => instResM (inst1M b 0 a) as
  | _, _ => none

theorem instResM_nil (e : Lean.Expr) : instResM e [] = some e := by
  first
    | rfl
    | (cases e <;> rfl)
    | simp [instResM]

theorem instResM_cons_forall (n : Name) (d b : Lean.Expr) (bi : BinderInfo)
    (a : Lean.Expr) (as : List Lean.Expr) :
    instResM (.forallE n d b bi) (a :: as) = instResM (inst1M b 0 a) as := by
  first | rfl | simp [instResM]

/-- **`instResM` keeps an output list that reads** (no substitution premise: `instSubstM`). -/
theorem instResM_outs {senv : StructEnv} (NS : senv.fields ``Sparkle.Core.Signal.Signal = none) :
    ∀ (args : List Lean.Expr) (ty resTy : Lean.Expr)
      (o : Option Name × List (String × MixedGateBinder)),
      machOuts? senv ty = some o → instResM ty args = some resTy → machOuts? senv resTy = some o
  | [], ty, resTy, o, hO, hR => by
    rw [instResM_nil] at hR
    cases hR
    exact hO
  | a :: as, ty, resTy, o, hO, hR => by
    cases ty with
    | forallE n d b bi =>
      rw [machOuts?_forall] at hO
      rw [instResM_cons_forall] at hR
      exact instResM_outs NS as (inst1M b 0 a) resTy o (instSubstM.outs senv NS b a o hO) hR
    | _ =>
      exfalso
      first
        | exact Option.noConfusion hR
        | (unfold instResM at hR; simp at hR)
        | simp [instResM] at hR

/-- **`instResM` keeps the head constant of the result body** (no premise). -/
theorem instResM_head :
    ∀ (args : List Lean.Expr) (ty resTy : Lean.Expr) (s : Name) (ls : List Lean.Level),
      (resBody ty).getAppFn = .const s ls → instResM ty args = some resTy →
      (resBody resTy).getAppFn = .const s ls
  | [], ty, resTy, s, ls, hh, hR => by
    rw [instResM_nil] at hR
    cases hR
    exact hh
  | a :: as, ty, resTy, s, ls, hh, hR => by
    cases ty with
    | forallE n d b bi =>
      have hh' : (resBody b).getAppFn = .const s ls := hh
      rw [instResM_cons_forall] at hR
      exact instResM_head as (inst1M b 0 a) resTy s ls (instSubstM.head b a s ls hh') hR
    | _ =>
      exfalso
      first
        | exact Option.noConfusion hR
        | (unfold instResM at hR; simp at hR)
        | simp [instResM] at hR

/-- `StructRes` for the MODEL reader (`instResM` in place of `instRes`). Not `StructRes`. -/
def StructResM (senvP : StructEnv) (c : Name) (senvC : StructEnv) (dE : DefinitionVal) : Prop :=
  ∀ (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (resTy : Lean.Expr)
    (ctor : Name) (fields : List (String × MixedGateBinder)),
    senvP.instS c = some (kinds, ty) → instResM ty args = some resTy →
    machOuts? senvP resTy = some (some ctor, fields) →
    ∀ (ctor? : Option Name) (outs : List (String × MixedGateBinder)),
      declOuts? senvC dE.type = some (ctor?, outs) → ∀ p ∈ fields, p ∈ outs

/-- **`structRes_of_declOuts` for the model reader, WITHOUT `InstSubst`.** -/
theorem structRes_of_declOutsM {senvP senvC : StructEnv} {c : Name} {dE : DefinitionVal}
    (NS : senvP.fields ``Sparkle.Core.Signal.Signal = none)
    (hF : ∀ (kinds : List MixedGateBinder) (ty : Lean.Expr), senvP.instS c = some (kinds, ty) →
      ∀ (s : Name) (ls : List Lean.Level), (resBody ty).getAppFn = .const s ls →
        senvP.fields s = senvC.fields s)
    (hD : ∀ (kinds : List MixedGateBinder) (ty : Lean.Expr), senvP.instS c = some (kinds, ty) →
      ∀ o, declOuts? senvC dE.type = some o → declOuts? senvC ty = some o) :
    StructResM senvP c senvC dE := by
  intro kinds ty args resTy ctor fields hI hR hO ctor? outs hd p hp
  have hd' := hD kinds ty hI _ hd
  unfold declOuts? at hd'
  generalize hk : machTupleKinds? ty = tup at hd'
  cases tup with
  | none =>
    have hC : machOuts? senvC ty = some (ctor?, outs) := hd'
    have hP : machOuts? senvP ty = some (ctor?, outs) :=
      (outs_congr ty (hF kinds ty hI)).trans hC
    have hRes := instResM_outs NS args ty resTy _ hP hR
    rw [hRes] at hO
    have h2 : outs = fields := (Prod.mk.inj (Option.some.inj hO)).2
    rw [h2]
    exact hp
  | some ks =>
    exfalso
    rw [tuple_body ty] at hk
    obtain ⟨us, hh⟩ := tuple_head (resBody_not_forall ty) hk
    exact outs_signal_head NS (instResM_head args ty resTy _ _ hh hR) ctor fields hO

/-- Where the bridge to the real reader sits (stated only to locate it): under the OPEN boundary
`InstAgree` the candidate's `instRes` IS `instResM`. `InstAgree` is not established. -/
theorem instRes_eq_instResM (A : InstAgree) :
    ∀ (args : List Lean.Expr) (ty : Lean.Expr), instRes ty args = instResM ty args
  | [], ty => by rw [instRes_nil, instResM_nil]
  | a :: as, ty => by
    cases ty with
    | forallE n d b bi =>
      rw [instRes_cons_forall, instResM_cons_forall, A b a]
      exact instRes_eq_instResM A as _
    | _ => first | rfl | simp [instRes, instResM]  -- UNSURE: non-`∀` equation closing

end Tools.ShippingEnvLocal
