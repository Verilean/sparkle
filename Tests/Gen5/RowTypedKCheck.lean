import Tools.ShippingGen5RowTypedK
set_option autoImplicit false
/-! D.D-4 Rows (issue sparkle-ledger-dd4-rows): check of `Tools/ShippingGen5RowTypedK.lean`.
(1) the specs are satisfiable (a model table, so the per-key theorems are not vacuous) and the per-key theorems instantiate;
(2) the ENV FACTS the theorems take as hypotheses hold in the real environment (meta, mirrors of `EnvType` / `EnvClosedPi` / `¬ IsDefn`);
(3) negative controls; (4) axioms; (5) counts. No TRUSTED / axiom / sorry / native_decide; `PT` stays arbitrary in the theorems (the model table is only here). -/
namespace Tests.Gen5.RowTypedKCheck
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5RowTypedK

/-! ## (1) A model table satisfying the specs -/
def tyRowM (T : Type) : TyRow := ⟨[], fun _ => some T⟩
def tmRowM (ks : List Bool) {T : Type} (v : T) : TmRow := ⟨ks, fun _ => some ⟨T, v⟩⟩

theorem tmSpecM {PT : PrimTableK} {c : Name} {ls : List Level} {ks : List Bool} {T : Type} (v : T)
    (h : PT.tms c ls = some (tmRowM ks v)) : TmSpec PT c ls ks T :=
  ⟨_, h, rfl, fun _ d hd => by cases Option.some.inj hd; rfl⟩
theorem tySpecM {PT : PrimTableK} {D : Name} {Ls : List Level} (T : Type) (h : PT.tys D Ls = some (tyRowM T)) : TyConSpec PT D Ls T :=
  ⟨_, h, rfl, rfl⟩

open Sparkle.Core.Domain in
def PTm : PrimTableK :=
  ⟨fun D Ls =>
     if D == ``Nat && Ls.isEmpty then some (tyRowM Nat)
     else if D == ``Int && Ls.isEmpty then some (tyRowM Int)
     else if D == ``Bool && Ls.isEmpty then some (tyRowM Bool)
     else if D == ``PUnit && (match Ls with | [.succ .zero] => true | _ => false) then some (tyRowM PUnit.{1})
     else if D == `Sparkle.Core.Domain.ActiveEdge && Ls.isEmpty then some (tyRowM ActiveEdge)
     else if D == `Sparkle.IR.Type.ResetKind && Ls.isEmpty then some (tyRowM Sparkle.IR.Type.ResetKind)
     else if D == `Sparkle.Core.Domain.DomainConfig && Ls.isEmpty then some (tyRowM DomainConfig)
     else none,
   fun c ls =>
     if c == ``Nat.zero && ls.isEmpty then some (tmRowM [] (0 : Nat))
     else if c == ``Bool.false && ls.isEmpty then some (tmRowM [] false)
     else if c == ``Bool.true && ls.isEmpty then some (tmRowM [] true)
     else if c == ``PUnit.unit && (match ls with | [.succ .zero] => true | _ => false) then some (tmRowM [] PUnit.unit.{1})
     else if c == `Sparkle.Core.Domain.ActiveEdge.rising && ls.isEmpty then some (tmRowM [] ActiveEdge.rising)
     else if c == `Sparkle.IR.Type.ResetKind.synchronous && ls.isEmpty then some (tmRowM [] Sparkle.IR.Type.ResetKind.synchronous)
     else if c == ``Nat.succ && ls.isEmpty then some (tmRowM [true] (0 : Nat))
     else if c == ``Int.ofNat && ls.isEmpty then some (tmRowM [true] (0 : Int))
     else if c == ``Int.negSucc && ls.isEmpty then some (tmRowM [true] (0 : Int))
     else if c == `Sparkle.Core.Domain.DomainConfig.mk && ls.isEmpty then some (tmRowM [true, true, true] (⟨0, .rising, .synchronous⟩ : DomainConfig))
     else none⟩

-- the six argument-free keys: `RowTypedAt PTm env c ls` follows from the three ENV FACTS alone
example (env : Environment) (h1 : ¬ IsDefn env ``Nat) (h2 : EnvType env ``Nat.zero [] (.const ``Nat [])) : RowTypedAt PTm env ``Nat.zero [] :=
  rowTyped_Nat_zero PTm env (tmSpecM (0 : Nat) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env ``Bool) (h2 : EnvType env ``Bool.false [] (.const ``Bool [])) : RowTypedAt PTm env ``Bool.false [] :=
  rowTyped_Bool_false PTm env (tmSpecM false (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env ``Bool) (h2 : EnvType env ``Bool.true [] (.const ``Bool [])) : RowTypedAt PTm env ``Bool.true [] :=
  rowTyped_Bool_true PTm env (tmSpecM true (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env ``PUnit) (h2 : EnvType env ``PUnit.unit [.succ .zero] (.const ``PUnit [.succ .zero])) :
    RowTypedAt PTm env ``PUnit.unit [.succ .zero] :=
  rowTyped_PUnit_unit1 PTm env (tmSpecM PUnit.unit.{1} (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env `Sparkle.Core.Domain.ActiveEdge)
    (h2 : EnvType env `Sparkle.Core.Domain.ActiveEdge.rising [] (.const `Sparkle.Core.Domain.ActiveEdge [])) :
    RowTypedAt PTm env `Sparkle.Core.Domain.ActiveEdge.rising [] :=
  rowTyped_ActiveEdge_rising PTm env (tmSpecM Sparkle.Core.Domain.ActiveEdge.rising (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env `Sparkle.IR.Type.ResetKind)
    (h2 : EnvType env `Sparkle.IR.Type.ResetKind.synchronous [] (.const `Sparkle.IR.Type.ResetKind [])) :
    RowTypedAt PTm env `Sparkle.IR.Type.ResetKind.synchronous [] :=
  rowTyped_ResetKind_synchronous PTm env (tmSpecM Sparkle.IR.Type.ResetKind.synchronous (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2

-- the four closed-codomain keys, in the option-(a) shape, and their conversion to `RowTypedAt` through the named obligation
example (env : Environment) (h1 : ¬ IsDefn env ``Nat) (h2 : EnvClosedPi env ``Nat.succ [] 1 (.const ``Nat [])) : RowTypedAtS PTm env ``Nat.succ [] :=
  rowTypedS_Nat_succ PTm env (tmSpecM (0 : Nat) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env ``Int) (h2 : EnvClosedPi env ``Int.ofNat [] 1 (.const ``Int [])) : RowTypedAtS PTm env ``Int.ofNat [] :=
  rowTypedS_Int_ofNat PTm env (tmSpecM (0 : Int) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env ``Int) (h2 : EnvClosedPi env ``Int.negSucc [] 1 (.const ``Int [])) : RowTypedAtS PTm env ``Int.negSucc [] :=
  rowTypedS_Int_negSucc PTm env (tmSpecM (0 : Int) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env `Sparkle.Core.Domain.DomainConfig)
    (h2 : EnvClosedPi env `Sparkle.Core.Domain.DomainConfig.mk [] 3 (.const `Sparkle.Core.Domain.DomainConfig [])) :
    RowTypedAtS PTm env `Sparkle.Core.Domain.DomainConfig.mk [] :=
  rowTypedS_DomainConfig_mk PTm env (tmSpecM (⟨0, .rising, .synchronous⟩ : Sparkle.Core.Domain.DomainConfig) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (hi : OblInst1Agree) (env : Environment) (h : RowTypedAtS PTm env ``Nat.succ []) : RowTypedAt PTm env ``Nat.succ [] :=
  rowTypedAt_of_S hi PTm env _ _ h

/-! ## (3) Negative controls -/
-- (a) a spec with the wrong type is not available: the model row of `Bool` does not denote `Unit`
theorem boolSpec_not_unit : ¬ TyConSpec PTm ``Bool [] Unit := by
  rintro ⟨trow, h, -, hd⟩
  have h' : PTm.tys ``Bool [] = some (tyRowM Bool) := by simp [PTm]
  rw [h'] at h; cases h
  have hU : (Bool : Type) = Unit := Option.some.inj hd
  have : ∀ a b : Bool, a = b := by rw [hU]; exact fun _ _ => rfl
  exact absurd (this true false) (by decide)
-- (b) a dependent codomain is not a closed telescope (`∀ x : Nat, x = x`-like: the body mentions the binder)
theorem dep_not_closedPi (R : Expr) : ¬ ClosedPi (.forallE `x (.const `Nat []) (.bvar 0) .default) 1 R := by
  rintro ⟨x, A, B, bi, h, hB, -⟩
  cases h
  simp [lbr] at hB
-- (c) the closed-codomain lemma has a use: `instForallS` through a closed telescope is the result, while a dependent one is NOT (it substitutes)
theorem instForallS_dep : instForallS (.forallE `x (.const `Nat []) (.bvar 0) .default) [.const `c []] = .const `c [] := by
  simp [instForallS, substS, liftS]
theorem instForallS_closed_ne : instForallS (.forallE `x (.const `Nat []) (.const `Nat []) .default) [.const `c []] ≠ .const `c [] := by
  simp [instForallS, substS]
-- (d) without the env fact the conclusion is not forced: a hypothesis-free statement would be false (the empty environment has no `Nat.zero`, so the env fact is a real premise only when `find?` succeeds)
example (env : Environment) (h : env.find? ``Nat.zero = none) : EnvType env ``Nat.zero [] (.const ``Bool []) := fun ci hci => by rw [h] at hci; cases hci

/-! ## (2) The ENV FACTS hold in the real environment (meta mirrors of `EnvType` / `EnvClosedPi` / `¬ IsDefn`) -/
def closedPiB : Expr → Nat → Expr → Bool
  | T, 0, R => T == R
  | .forallE _ _ B _, n + 1, R => lbr B == 0 && closedPiB B n R
  | _, _, _ => false

def notDefn (env : Environment) (D : Name) : Bool :=
  match env.find? D with
  | some (.defnInfo _) => false
  | some _ => true
  | none => false   -- also require existence

run_meta do
  let env ← getEnv
  let u := Level.succ .zero
  let AE := `Sparkle.Core.Domain.ActiveEdge
  let RK := `Sparkle.IR.Type.ResetKind
  let DC := `Sparkle.Core.Domain.DomainConfig
  -- (c, ls, D, Ls)
  let nullary : List (Name × List Level × Name × List Level) :=
    [(``Nat.zero, [], ``Nat, []), (``Bool.false, [], ``Bool, []), (``Bool.true, [], ``Bool, []), (``PUnit.unit, [u], ``PUnit, [u]),
     (AE ++ `rising, [], AE, []), (RK ++ `synchronous, [], RK, [])]
  -- (c, ls, n, D, Ls)
  let nondep : List (Name × List Level × Nat × Name × List Level) :=
    [(``Nat.succ, [], 1, ``Nat, []), (``Int.ofNat, [], 1, ``Int, []), (``Int.negSucc, [], 1, ``Int, []), (DC ++ `mk, [], 3, DC, [])]
  let mut ok : Nat := 0
  for (c, ls, D, Ls) in nullary do
    let some ci := env.find? c | throwError "{c} absent"
    unless ci.type.instantiateLevelParams ci.levelParams ls == .const D Ls do throwError "EnvType fails for {c}"
    unless notDefn env D do throwError "{D} is a defnInfo or absent"
    ok := ok + 1
  for (c, ls, n, D, Ls) in nondep do
    let some ci := env.find? c | throwError "{c} absent"
    unless closedPiB (ci.type.instantiateLevelParams ci.levelParams ls) n (.const D Ls) do throwError "EnvClosedPi fails for {c}"
    unless notDefn env D do throwError "{D} is a defnInfo or absent"
    ok := ok + 1
  logInfo m!"env facts ok for {ok} keys ({nullary.length} argument-free, {nondep.length} closed-codomain)"
  -- negative controls of the mirror: dependent keys are rejected, a wrong result is rejected, a defn is rejected
  let some fin := env.find? ``Fin.mk | throwError "Fin.mk absent"
  if closedPiB (fin.type.instantiateLevelParams fin.levelParams []) 3 (.const ``Fin []) then throwError "negative control FAILED: Fin.mk is dependent"
  let some dec := env.find? ``Decidable.isTrue | throwError "absent"
  if closedPiB (dec.type.instantiateLevelParams dec.levelParams []) 2 (.const ``Decidable []) then throwError "negative control FAILED: Decidable.isTrue"
  let some succ := env.find? ``Nat.succ | throwError "absent"
  if closedPiB succ.type 1 (.const ``Int []) then throwError "negative control FAILED: wrong result accepted"
  if notDefn env ``Nat.add then throwError "negative control FAILED: Nat.add is a defnInfo"
  logInfo m!"negative controls ok: Fin.mk / Decidable.isTrue (dependent), wrong result, and a defnInfo are rejected"

/-! ## (4) Axioms -/
def stdAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def provedRowNames : List Name :=
  [``rowTyped_Nat_zero, ``rowTyped_Bool_false, ``rowTyped_Bool_true, ``rowTyped_PUnit_unit1, ``rowTyped_ActiveEdge_rising, ``rowTyped_ResetKind_synchronous]
def shapeRowNames : List Name :=
  [``rowTypedS_Nat_succ, ``rowTypedS_Int_ofNat, ``rowTypedS_Int_negSucc, ``rowTypedS_DomainConfig_mk]
run_meta do
  let proved : List Name := provedRowNames ++ shapeRowNames ++
    [``rowTypedAt_nullary_const, ``instForallS_closedPi, ``rowTypedAtS_closedPi, ``instForallS_eq, ``rowTypedAt_of_S,
     ``boolSpec_not_unit, ``dep_not_closedPi, ``instForallS_dep, ``instForallS_closed_ne, ``tmSpecM, ``tySpecM]
  let env ← getEnv
  let mut bad : Array Name := #[]
  for n in proved do
    unless env.contains n do throwError "{n} absent"
    let ax ← Lean.collectAxioms n
    if ax.any (fun a => !stdAx.contains a) then bad := bad.push n
  unless bad.isEmpty do throwError "non-standard axiom (or sorryAx) in: {bad}"
  logInfo m!"axiom check ok: {proved.length} declarations use only propext / Classical.choice / Quot.sound"
axiom negControlAxiom : False
theorem negControlUsesAxiom : (1 : Nat) = 2 := negControlAxiom.elim
run_meta do
  let ax ← Lean.collectAxioms ``negControlUsesAxiom
  unless ax.contains ``negControlAxiom do throwError "negative control FAILED: detector missed the axiom"
  logInfo m!"negative control ok: detector flags {ax.toList}"

/-! ## (5) Counts

Rows proved (`RowTypedAt`, no bridge): `provedRowNames.length`. Rows in the option-(a) shape (`RowTypedAtS`, waiting for D1): `shapeRowNames.length`. The class counts of the 115 term keys
come from the corpus audit (5 drivers merged by `scripts/gen5/merge_row_typed_audit.py`; they are not recomputable here because the corpus is the union of the driver imports):
term keys 115 = Type 0: 40 (argument-free 6, closed codomain 4, dependent 30) + Prop 9 + higher 66. `den = none` / Prop: 75. Bridge-waiting: 34 (= 4 closed + 30 dependent). -/
run_meta do
  let proved : Nat := provedRowNames.length
  let shape : Nat := shapeRowNames.length
  let dep : Nat := 30
  let waiting : Nat := shape + dep
  let denNone : Nat := 9 + 66
  let total : Nat := proved + waiting + denNone
  unless total == 115 do throwError "partition of the 115 term keys fails"
  logInfo m!"rows proved (RowTypedAt): {proved}; bridge-waiting (D1): {waiting} (shape proved {shape}, dependent {dep}); den = none / Prop: {denNone}; total {total}"

end Tests.Gen5.RowTypedKCheck

#print axioms Tools.ShippingGen5RowTypedK.rowTypedAt_nullary_const
#print axioms Tools.ShippingGen5RowTypedK.rowTyped_Nat_zero
#print axioms Tools.ShippingGen5RowTypedK.rowTyped_PUnit_unit1
#print axioms Tools.ShippingGen5RowTypedK.rowTypedS_DomainConfig_mk
#print axioms Tools.ShippingGen5RowTypedK.rowTypedAt_of_S
#print axioms Tests.Gen5.RowTypedKCheck.boolSpec_not_unit
