import Tools.ShippingReflectCtx
import Tools.ShippingInstanceTag
import Tools.ShippingInstanceEntrySoundness

/-! # `GateDefines`: the per-world reflection of the mixed gate's acceptance (worker N, round 2)

WRITTEN, NOT BUILT. A PROOF-SIDE definition: it is NOT in
`Tools.ShippingFinalGoalCommand.allowed`; whether the classifier admits it is a
ruling the coordinator asks for. Until then a theorem that carries it carries
one NOT ALLOWED reflection premise.

    GateDefines mctx mref cctx cref f bs body :=
      ∀ w1 ci w2 w5 envR w6,
        RunsTo (getConstInfo f) … w1 ci w2 → RunsTo getEnv … w5 envR w6 →
        ∃ dv, entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)
                = .defnInfo dv ∧
              certifiedShape? false [] (.defnInfo dv) = none ∧
              mixedCertifiedShape? false [] (.defnInfo dv) (instancePredicate envR) = some (bs, body)

In this run, the entry constant of `f` — computed by `entryConst` from the
declaration and the environment the run reads, exactly as the entry computes
it — is a definition the first gate refuses and the mixed gate, UNDER THE
INSTANCE PREDICATE OF THAT SAME READ, accepts as `(bs, body)`.

Comparison (what each states):

| | `EntryDefines f v` | `MachineDefines f shape` | `GateDefines f bs body` |
|---|---|---|---|
| quantified over | every `getConstInfo` run, every `getEnv` run (this run's contexts and refs) | the same, and a SECOND `getEnv` run (the machine arm reads again) | the same as `EntryDefines` (one read: since the capture the entry reads once) |
| entry constant | `= .defnInfo d`, `d.value = v` | (left open) | `= .defnInfo dv` |
| first gate | — | refuses | refuses |
| mixed gate | — | refuses, under `instancePredicate envR` | ACCEPTS as `(bs, body)`, under `instancePredicate envR` |
| third reading | — | `machineShape? … (structEnv envR') = some shape` | — |
| depends on the contexts | no (`EntryDefines.ctx`) | no (`MachineDefines.ctx`) | no (`GateDefines.ctx`) |

So `GateDefines` is `MachineDefines` with the mixed gate's verdict flipped
from "refuses" to "accepts as (bs, body)" and no machine reading; compared
with `EntryDefines` it does not name the value but the gate's verdict on the
entry constant — which reads the value AND the type (`mixedGateResultScalar`)
AND, for a body with calls, the run's `@[hardware_module]` tags (the
predicate). A generator produces it per declaration as the machine generator
produces `MachineDefines`: as a BINDER of the generated endpoint (a
reflection is never proved), over reflected constants `f.gateBinders` /
`f.gateBody`, after deciding in the elaboration environment that
`mixedCertifiedShape? false [] (entryConst …) (instancePredicate env)` is
`some (bs, body)` and reflecting `(bs, body)`; the pure side facts the
theorems also ask (`mixedGateSel`, positions, `fallbackKind`, the head's
names) are kernel `rfl` / `decide` per declaration, like `#gate_child`'s.
`gateDefines_of_entry` (in `ShippingGateParentRunG`) shows the round-1
premises (`EntryDefines` + `tag` + `hscalar` + `old` + the pure acceptance)
imply it: it is not a stronger boundary than those.

What is here:
* `GateDefines`, `GateDefines.ctx`;
* `mixedGateCond` (the text of the gate's condition), `mixedShape_cond` (an
  acceptance is the peel and the condition);
* `MixedGateSel` (pure, per declaration: with the body NOT designated, the
  condition is false — i.e. only an instance disjunct can accept it) and
  `gate_pred` (acceptance under the run's predicate, plus that fact: the
  predicate designates the body);
* `lastBVar_tag`, `instEN_pred_tag`: the head of an `instEN` call whose last
  argument is a binder is tagged in the predicate's environment (the
  projection disjunct of `instancePredicate` is excluded by the binder:
  `spine_tag`'s argument). -/
namespace Tools.ShippingGateDefines
open Lean Meta Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingInstanceEntrySoundness (instEN instEN_getAppFn)

/-- **The gate reflection** (file header). -/
def GateDefines (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (bs : List (Name × MixedGateBinder)) (body : Lean.Expr) : Prop :=
  ∀ w1 ci w2 w5 envR w6,
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    ∃ dv : DefinitionVal,
      entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR) = .defnInfo dv ∧
      certifiedShape? false [] (.defnInfo dv) = none ∧
      mixedCertifiedShape? false [] (.defnInfo dv) (instancePredicate envR) = some (bs, body)

variable {mctx mctx' : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx cctx' : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`GateDefines` does not depend on the contexts** (the text of
`MachineDefines.ctx`). -/
theorem GateDefines.ctx {c : Name} {bs : List (Name × MixedGateBinder)} {body : Lean.Expr}
    (h : GateDefines mctx mref cctx cref c bs body) : GateDefines mctx' mref cctx' cref c bs body :=
  fun _ _ _ _ _ _ g e1 =>
    h _ _ _ _ _ _ (Tools.ShippingReflectCtx.getConstInfo_ctx c g)
      (Tools.ShippingReflectCtx.getEnv_ctx e1)

/-! ## The gate's condition -/

/-- The condition of `mixedCertifiedShape?` on a peeled body (its text). -/
def mixedGateCond (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder)
    (body : Lean.Expr) (scalar : Bool) : Bool :=
  (unifiedInstanceRoot isInst kinds body && scalar) ||
    mixedGateBoolBody kinds body ||
    mixedGateVectorRoot kinds body ||
    unifiedGateRoot kinds body ||
    unifiedRegisterRoot kinds body ||
    unifiedMemoryRoot kinds body ||
    (hierGateRoot isInst kinds body && scalar) ||
    (hierInstRoot isInst kinds body && scalar)

/-- An acceptance is the peel of the value and the condition. -/
theorem mixedShape_cond {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {body : Lean.Expr} {isInst : Lean.Expr → Bool}
    (h : mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, body)) :
    mixedGatePeel d.value = some (bs, body) ∧
      mixedGateCond isInst (bs.map (·.2)).toArray body (mixedGateResultScalar d.type) = true := by
  simp only [mixedCertifiedShape?, List.isEmpty_nil, Bool.not_true, Bool.or_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · rename_i bs' body' hp
    split at h
    · rename_i hc
      cases h
      exact ⟨hp, hc⟩
    · cases h
  · cases h

/-- **The selection fact of a root body** (pure, per declaration): if the
predicate does not designate the body, the gate's condition is false —
whatever the predicate and the scalar flag. Decided per declaration by
unfolding the two instance disjuncts and `rfl` (the other disjuncts do not
consult the predicate on such a body). -/
def MixedGateSel (kinds : Array MixedGateBinder) (body : Lean.Expr) : Prop :=
  ∀ (isInst : Lean.Expr → Bool) (sc : Bool), isInst body = false →
    mixedGateCond isInst kinds body sc = false

/-- **The predicate designates an accepted root body.** -/
theorem gate_pred {env : Environment} {d : DefinitionVal}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr}
    (hshape : mixedCertifiedShape? false [] (.defnInfo d) (instancePredicate env) = some (bs, body))
    (hsel : MixedGateSel (bs.map (·.2)).toArray body) :
    instancePredicate env body = true := by
  cases hb : instancePredicate env body with
  | true => rfl
  | false =>
    have hc := (mixedShape_cond hshape).2
    rw [hsel _ _ hb] at hc
    cases hc

/-! ## The tag of the head -/

/-- A non-empty list ends in an element. -/
theorem list_snoc_of_ne {α : Type} : ∀ (l : List α), l ≠ [] → ∃ init x, l = init ++ [x]
  | [], h => absurd rfl h
  | [x], _ => ⟨[], x, rfl⟩
  | x :: y :: rest, _ => by
    obtain ⟨init, z, hz⟩ := list_snoc_of_ne (y :: rest) (List.cons_ne_nil y rest)
    exact ⟨x :: init, z, by simp [hz]⟩

/-- A designated call whose last argument is a binder: its head is tagged
(the projection disjunct needs a call as the last argument). The text of the
built `spine_tag`'s `app`/`bvar` case. -/
theorem lastBVar_tag {env : Environment} {f : Lean.Expr} {i : Nat} {mn : Name}
    {us : List Level}
    (hfn : (Lean.Expr.app f (.bvar i)).getAppFn = .const mn us)
    (h : instancePredicate env (.app f (.bvar i)) = true) :
    Sparkle.Compiler.isHardwareModule env mn = true := by
  unfold instancePredicate at h
  rw [hfn] at h
  dsimp only at h
  rw [Bool.or_eq_true] at h
  rcases h with ht | hp
  · exact ht
  · exfalso
    cases hs : env.getProjectionStructureName? mn with
    | none =>
      rw [hs] at hp
      simp at hp
    | some s =>
      rw [hs] at hp
      simp [Lean.Expr.getAppFn] at hp

/-- **The head of a designated `instEN` call on binders is tagged.** -/
theorem instEN_pred_tag {env : Environment} {mn : Name} {lvls : List Level} {dE : Lean.Expr}
    {n : Nat} {poss : List Nat} (hne : poss ≠ [])
    (h : instancePredicate env (instEN mn lvls dE (poss.map (inputExpr n))) = true) :
    Sparkle.Compiler.isHardwareModule env mn = true := by
  obtain ⟨init, q, rfl⟩ := list_snoc_of_ne poss hne
  have he : instEN mn lvls dE ((init ++ [q]).map (inputExpr n)) =
      .app (instEN mn lvls dE (init.map (inputExpr n))) (.bvar (n - 1 - q)) := by
    unfold instEN
    rw [List.map_append, List.foldl_append]
    try rfl
  rw [he] at h
  exact lastBVar_tag (instEN_getAppFn mn lvls dE _) h

end Tools.ShippingGateDefines
