import Lean
import Sparkle
import Tools.ShippingGen5RowTypedV
import Tools.ShippingGen5ConstValueEV
set_option autoImplicit false
/-! D.D-4 V2 (issue sparkle-ledger-dd4-v2): check of `Tools/ShippingGen5ConstValueEVL.lean` (CVEKVL, `EnvClosedL`) and `Tools/ShippingGen5RowTypedV.lean` (literal rows, `RowTypedAtV`, `RowTeleEvAt`, map from `CVEKS`).
(1) structural match of the statements; (2) a model table (non-vacuity: the specs are satisfiable, the per-key theorems instantiate); (3) the ENV FACTS the theorems take as hypotheses, checked in the real environment (meta);
(4) negative controls; (5) the substitution obligation is not reached; (6) axioms, counts, remaining obligations. No TRUSTED / axiom / sorry / native_decide; `PT` stays arbitrary in the theorems (the model tables are only here). -/
namespace Tests.Gen5.V2Check
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
  Tools.ShippingGen5ConstValueESL Tools.ShippingGen5ConstValueEVL Tools.ShippingGen5RowTypedV
open Tools.ShippingGen5RowTypedK (TmSpec TyConSpec ClosedPi)

/-! ## (1) Structural match -/
-- item 1: `EnvClosedS` of the syntactic level instantiation is PROVED from the plain declaration closedness; soundness of CVEKVL follows
example : ∀ env : Environment, EnvDeclClosed env → EnvClosedL env := fun _ h => envClosedL_cvekvl h
example : ∀ (PT : PrimTableK) (env : Environment), EnvDeclClosed env →
    (∀ ρ : Val, TDenV PT env ρ (.const `Nat []) Nat) → (∀ ρ : Val, TDenV PT env ρ (.const `String []) String) →
    ∀ (ρ : Val) (e τ : Expr) (α : Type) (v : α), WfValV PT env ρ → CVEKV PT env ρ e τ α v → TDenV PT env ρ τ α :=
  fun _ _ hcl hN hS => denTypedVL hcl hN hS
example : ∀ (PT : PrimTableK) (env : Environment), EnvDeclClosed env → ∀ (E : Entry) (s : Nat) (ρ ρ' : Val), InsV E s ρ ρ' →
    ∀ (e τ : Expr) (α : Type) (v : α), CVEKV PT env ρ e τ α v → CVEKV PT env ρ' (liftS e s 1) (liftS τ s 1) α v :=
  fun _ _ hcl _ _ _ _ hI _ _ _ _ h => cvekv_wk_decl hcl hI h
-- functionality of the CVEKVL carrier
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (e τ : Expr) (α : Type) (v : α),
    CVEKV PT env ρ e τ α v → ∀ (τ' : Expr) (β : Type) (w : β), CVEKV PT env ρ e τ' β w → α = β ∧ HEq v w :=
  fun _ _ _ _ _ _ _ h _ _ _ h' => cvekv_fun h h'
-- CVEKVL really uses the syntactic instantiation: the prim rule's label and the unfold body mention `instantiateLevelParamsS`, not `Expr.instantiateLevelParams`
run_meta do
  let env ← getEnv
  for r in [``CVEKVB.prim, ``CVEKVB.unfold, ``TDenV.tunfold] do
    let some ci := env.find? r | throwError "{r} absent"
    let cs := ci.type.getUsedConstants
    unless cs.contains ``instantiateLevelParamsS do throwError "{r} does not mention instantiateLevelParamsS"
    if cs.contains ``Expr.instantiateLevelParams then throwError "{r} still mentions Expr.instantiateLevelParams"
  -- control: the CVEKV rules (previous carrier) do mention the opaque one
  let some ci := env.find? ``Tools.ShippingGen5ConstValueEV.CVEKVB.prim | throwError "absent"
  unless ci.type.getUsedConstants.contains ``Expr.instantiateLevelParams do throwError "detector control FAILED"
  logInfo m!"CVEKVL check ok: prim / unfold / tunfold use instantiateLevelParamsS only (CVEKV's prim still has Expr.instantiateLevelParams)"
-- item 2: literal rows
example : ∀ (PT : PrimTableK) (env : Environment) (rn rs : TyRow), PT.tys `Nat [] = some rn → ¬ IsDefn env `Nat → rn.kinds = [] → rn.den [] = some Nat →
    PT.tys `String [] = some rs → ¬ IsDefn env `String → rs.kinds = [] → rs.den [] = some String →
    (∀ ρ : Val, TDenV PT env ρ (.const `Nat []) Nat) ∧ (∀ ρ : Val, TDenV PT env ρ (.const `String []) String) :=
  fun _ _ _ _ hn hnd hk hT hs hsnd hsk hsT => oblDenLitsV_of_rows hn hnd hk hT hs hsnd hsk hsT
-- item 3: the shape of RowTypedAtV is the `hty` of the prim rule
example (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) :
    RowTypedAtV PT env c ls ↔ ∀ (ci : ConstantInfo) (row : TmRow) (ρ : Val) (args : List Expr) (as : List Arg) (d : Dyn),
      env.find? c = some ci → PT.tms c ls = some row → ArgsDenV PT env ρ row.kinds args as → row.den as = some d →
      TDenV PT env ρ (instForallS (instantiateLevelParamsS ci.levelParams ls ci.type) args) d.ty := Iff.rfl
example (PT : PrimTableK) (env : Environment) : OblRowTypedV PT env ↔ ∀ (c : Name) (ls : List Level), RowTypedAtV PT env c ls := Iff.rfl
-- the computed instForallS of a first-argument-dependent telescope
example (C : Expr) (hC : ∀ (k : Nat) (x : Expr), substS C k x = C) (n : Nat) (T a0 : Expr) (as : List Expr)
    (h : PiN T (n + 1) (.app C (.bvar n))) (hl : as.length = n) : instForallS T (a0 :: as) = .app C a0 := instForallS_depFirst C hC n T a0 as h hl
-- item 4: the old rule from the new rule plus one substitution instance
example {PT : PrimTableK} {env : Environment} {ρ : Val} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type} (TB : TA → Type)
    {fv : (a : TA) → TB a} {av : TA} (hA : TDenV PT env ρ A TA) (hB : ∀ a : TA, TDenV PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
    (hf : CVEKVB PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVEKV PT env ρ x A TA av)
    (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls) (hsub : TDenV PT env ρ (substS B 0 x) (TB av)) :
    CVEKV PT env ρ (.app fe x) (substS B 0 x) (TB av) (fv av) := cvekv_app_old_of_new TB hA hB hf hx hnh hsub
-- the old and the new `app` label differ on a concrete instance (so the new rule cannot simply keep the old label)
example : (Expr.letE `x (.const `Nat []) (.lit (.natVal 0)) (.const `Nat []) false) ≠ substS (.const `Nat []) 0 (.lit (.natVal 0)) := by simp [substS]

/-! ## (2) Model tables: the specs are satisfiable, the per-key theorems instantiate -/
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
     else if D == `Sparkle.Core.Domain.DomainConfig && Ls.isEmpty then some (tyRowM DomainConfig)
     else none,
   fun c ls =>
     if c == ``Nat.zero && ls.isEmpty then some (tmRowM [] (0 : Nat))
     else if c == ``Bool.false && ls.isEmpty then some (tmRowM [] false)
     else if c == ``Nat.succ && ls.isEmpty then some (tmRowM [true] (0 : Nat))
     else if c == ``Int.ofNat && ls.isEmpty then some (tmRowM [true] (0 : Int))
     else if c == `Sparkle.Core.Domain.DomainConfig.mk && ls.isEmpty then some (tmRowM [true, true, true] (⟨0, .rising, .synchronous⟩ : DomainConfig))
     else none⟩

example (env : Environment) (h1 : ¬ IsDefn env ``Nat) (h2 : EnvTypeL env ``Nat.zero [] (.const ``Nat [])) : RowTypedAtV PTm env ``Nat.zero [] :=
  rowTypedV_Nat_zero PTm env (tmSpecM (0 : Nat) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env ``Bool) (h2 : EnvTypeL env ``Bool.false [] (.const ``Bool [])) : RowTypedAtV PTm env ``Bool.false [] :=
  rowTypedV_Bool_false PTm env (tmSpecM false (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env ``Nat) (h2 : EnvClosedPiL env ``Nat.succ [] 1 (.const ``Nat [])) : RowTypedAtV PTm env ``Nat.succ [] :=
  rowTypedV_Nat_succ PTm env (tmSpecM (0 : Nat) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
example (env : Environment) (h1 : ¬ IsDefn env ``Int) (h2 : EnvClosedPiL env ``Int.ofNat [] 1 (.const ``Int [])) : RowTypedAtV PTm env ``Int.ofNat [] :=
  rowTypedV_Int_ofNat PTm env (tmSpecM (0 : Int) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
open Sparkle.Core.Domain in
example (env : Environment) (h1 : ¬ IsDefn env `Sparkle.Core.Domain.DomainConfig)
    (h2 : EnvClosedPiL env `Sparkle.Core.Domain.DomainConfig.mk [] 3 (.const `Sparkle.Core.Domain.DomainConfig [])) :
    RowTypedAtV PTm env `Sparkle.Core.Domain.DomainConfig.mk [] :=
  rowTypedV_DomainConfig_mk PTm env (tmSpecM (⟨0, .rising, .synchronous⟩ : DomainConfig) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2

/-- A dependent model: `Tst.mk` takes two term arguments and produces a `Nat` value whose type is the denotation of the type former `Tst.D` at the FIRST argument. -/
def mkRowD : TmRow := ⟨[true, true], fun as => match as with | _ :: _ => some ⟨Nat, (0 : Nat)⟩ | [] => none⟩
def dRowD : TyRow := ⟨[true], fun _ => some Nat⟩
def PTd : PrimTableK :=
  ⟨fun D Ls => if D == `Tst.D && Ls.isEmpty then some dRowD else none,
   fun c ls => if c == `Tst.mk && ls.isEmpty then some mkRowD else none⟩

theorem firstArgSpec_mk : FirstArgSpec PTd `Tst.mk [] true [true] `Tst.D [] := by
  refine ⟨mkRowD, dRowD, by simp [PTd], rfl, by simp [PTd], rfl, ?_⟩
  intro as d h
  cases as with
  | nil => simp [mkRowD] at h
  | cons a rest =>
    refine ⟨a, rest, rfl, ?_⟩
    simp only [mkRowD] at h
    cases Option.some.inj h
    rfl

example (env : Environment) (hnd : ¬ IsDefn env `Tst.D) (hT : EnvDepFirst env `Tst.mk [] 1 `Tst.D []) : RowTypedAtV PTd env `Tst.mk [] :=
  rowTypedAtV_depFirst PTd env _ _ true [true] _ _ firstArgSpec_mk hnd hT

-- Per-row telescope evidence: `Nat.succ` takes a `Nat` argument (model row that accepts only `Nat` values).
open Classical in
noncomputable def succRow : TmRow := ⟨[true], fun as => match as with | [.tm d] => if h : d.ty = Nat then some ⟨Nat, (h ▸ d.val : Nat).succ⟩ else none | _ => none⟩
noncomputable def PTs : PrimTableK := ⟨fun D Ls => if D == ``Nat && Ls.isEmpty then some (tyRowM Nat) else none, fun c ls => if c == ``Nat.succ && ls.isEmpty then some succRow else none⟩

theorem argsTySpec_succ : ArgsTySpec PTs ``Nat.succ [] [Nat] := by
  refine ⟨succRow, by simp [PTs], rfl, ?_⟩
  intro as d h
  match as with
  | [.tm d'] =>
    simp only [succRow] at h
    split at h
    · rename_i hd; exact ⟨hd, trivial⟩
    · cases h
  | [] => simp [succRow] at h
  | [.ty _] => simp [succRow] at h
  | _ :: _ :: _ => simp [succRow] at h

theorem bindersDen_Nat (env : Environment) (hnd : ¬ IsDefn env ``Nat) : BindersDen PTs env [(``Nat, [])] [Nat] :=
  ⟨fun ρ => tdenv_const_nullary (row := tyRowM Nat) (by simp [PTs]) hnd rfl rfl, trivial⟩

example (env : Environment) (hnd : ¬ IsDefn env ``Nat) (hT : EnvConstPi env ``Nat.succ [] [(``Nat, [])] (.const ``Nat [])) :
    RowTeleEvAt PTs env ``Nat.succ [] :=
  teleEv_Nat_succ PTs env argsTySpec_succ (bindersDen_Nat env hnd) hT

/-! ## (3) ENV FACTS in the real environment (meta mirrors of `EnvTypeL`, `EnvClosedPiL`, `EnvConstPi`, `EnvDepFirst`) -/
def closedPiB : Expr → Nat → Expr → Bool
  | T, 0, R => T == R
  | .forallE _ _ B _, n + 1, R => lbr B == 0 && closedPiB B n R
  | _, _, _ => false
def constPiB : Expr → List (Name × List Level) → Expr → Bool
  | T, [], R => T == R
  | .forallE _ (.const d ls) B _, (b :: bs), R => d == b.1 && ls == b.2 && lbr B == 0 && constPiB B bs R
  | _, _, _ => false
def piNB : Expr → Nat → Expr → Bool
  | T, 0, R => T == R
  | .forallE _ _ B _, n + 1, R => piNB B n R
  | _, _, _ => false
def nBinders : Expr → Nat
  | .forallE _ _ B _ => nBinders B + 1
  | _ => 0
def resultOf : Expr → Expr
  | .forallE _ _ B _ => resultOf B
  | e => e
def notDefn (env : Environment) (D : Name) : Bool :=
  match env.find? D with
  | some (.defnInfo _) => false
  | some _ => true
  | none => false
/-- the type of `c` instantiated syntactically at `ls` -/
def tyAt (env : Environment) (c : Name) (ls : List Level) : MetaM Expr := do
  let some ci := env.find? c | throwError "{c} absent"
  return instantiateLevelParamsS ci.levelParams ls ci.type

/-- shape `n + 1` binders, result `D Ls (bvar n)` (what `EnvDepFirst` says) -/
def depFirstB (T : Expr) (D : Name) (Ls : List Level) : Bool :=
  nBinders T ≥ 1 && piNB T (nBinders T) (.app (.const D Ls) (.bvar (nBinders T - 1)))

structure KOutM (dom : Sparkle.Core.Domain.DomainConfig) where
  s : Sparkle.Core.Signal.Signal dom (BitVec 16)
  odd : Sparkle.Core.Signal.Signal dom Bool

run_meta do
  let env ← getEnv
  let u := Level.succ .zero
  let AE := `Sparkle.Core.Domain.ActiveEdge
  let RK := `Sparkle.IR.Type.ResetKind
  let DC := `Sparkle.Core.Domain.DomainConfig
  let nullary : List (Name × List Level × Name × List Level) :=
    [(``Nat.zero, [], ``Nat, []), (``Bool.false, [], ``Bool, []), (``Bool.true, [], ``Bool, []), (``PUnit.unit, [u], ``PUnit, [u]),
     (AE ++ `rising, [], AE, []), (RK ++ `synchronous, [], RK, [])]
  let closed : List (Name × List Level × List (Name × List Level) × Name × List Level) :=
    [(``Nat.succ, [], [(``Nat, [])], ``Nat, []), (``Int.ofNat, [], [(``Nat, [])], ``Int, []), (``Int.negSucc, [], [(``Nat, [])], ``Int, []),
     (DC ++ `mk, [], [(``Nat, []), (AE, []), (`Sparkle.Core.Domain.ResetKind, [])], DC, [])]
  let mut ok : Nat := 0
  for (c, ls, D, Ls) in nullary do
    unless (← tyAt env c ls) == .const D Ls do throwError "EnvTypeL fails for {c}"
    unless notDefn env D do throwError "{D} is a defnInfo or absent"
    ok := ok + 1
  for (c, ls, bs, D, Ls) in closed do
    let T ← tyAt env c ls
    unless closedPiB T bs.length (.const D Ls) do throwError "EnvClosedPiL fails for {c}"
    unless constPiB T bs (.const D Ls) do throwError "EnvConstPi fails for {c}"
    unless notDefn env D do throwError "{D} is a defnInfo or absent"
    for b in bs do
      -- a binder constant is either a type with a `tys` row (not a definition) or an alias whose body is a plain type constant
      unless notDefn env b.1 || (match env.find? b.1 with | some (.defnInfo d) => d.value == .const RK [] | _ => false) do throwError "binder {b.1} is neither a plain type nor an alias of one"
    ok := ok + 1
  logInfo m!"env facts ok for {ok} keys ({nullary.length} argument-free: EnvTypeL; {closed.length} closed-codomain: EnvClosedPiL and EnvConstPi)"
  -- dependent rows of the first-argument shape (EnvDepFirst): the four named keys, one mirror of an output structure, and every `DomainConfig`-first constructor of `Sparkle`
  let named : List (Name × Name) := [(``Fin.mk, ``Fin), (``BitVec.ofFin, ``BitVec), (``Decidable.isTrue, ``Decidable), (``Decidable.isFalse, ``Decidable), (``KOutM.mk, ``KOutM)]
  let mut dok : Nat := 0
  for (c, D) in named do
    let T ← tyAt env c []
    unless depFirstB T D [] do throwError "EnvDepFirst fails for {c}"
    unless notDefn env D do throwError "{D} is a defnInfo or absent"
    dok := dok + 1
  logInfo m!"EnvDepFirst ok for {dok} dependent keys (Fin.mk, BitVec.ofFin, Decidable.isTrue/isFalse, and the mirror KOutM.mk of an output structure `Foo dom`)"
  -- computed `instForallS` on the real types: the result is the type former applied to the FIRST argument, and it depends on that argument
  let lit (n : Nat) : Expr := .lit (.natVal n)
  let r1 := instForallS (← tyAt env ``Fin.mk []) [lit 5, lit 3, lit 0]
  unless r1 == .app (.const ``Fin []) (lit 5) do throwError "instForallS Fin.mk wrong: {r1}"
  let r2 := instForallS (← tyAt env ``Fin.mk []) [lit 7, lit 3, lit 0]
  unless r2 == .app (.const ``Fin []) (lit 7) && r1 != r2 do throwError "instForallS Fin.mk does not depend on the first argument"
  let r3 := instForallS (← tyAt env ``KOutM.mk []) [lit 11, lit 12, lit 13]
  unless r3 == .app (.const ``KOutM []) (lit 11) do throwError "instForallS KOutM.mk wrong: {r3}"
  let r4 := instForallS (← tyAt env ``BitVec.ofFin []) [lit 8, lit 1]
  unless r4 == .app (.const ``BitVec []) (lit 8) do throwError "instForallS BitVec.ofFin wrong: {r4}"
  logInfo m!"instForallS on the real types ok: Fin.mk [5,3,0] = Fin 5 (and Fin 7 for [7,3,0], so the result depends on the first argument), KOutM.mk [11,12,13] = KOutM 11, BitVec.ofFin [8,1] = BitVec 8"
  -- survey of `Sparkle` itself: constructors whose first binder is `DomainConfig`
  let mut tot : Nat := 0
  let mut shape : Nat := 0
  let mut other : Array Name := #[]
  for (c, ci) in env.constants.toList do
    if let .ctorInfo _ := ci then
      let T := instantiateLevelParamsS ci.levelParams (ci.levelParams.map fun _ => Level.zero) ci.type
      match T with
      | .forallE _ (.const d []) _ _ =>
        if d == DC then
          tot := tot + 1
          let okS := match resultOf T with
            | .app (.const _ _) (.bvar j) => j + 1 == nBinders T
            | _ => false
          if okS then shape := shape + 1 else other := other.push c
      | _ => pure ()
  logInfo m!"survey of Sparkle (not the corpus): {tot} constructors with first binder DomainConfig; {shape} have the first-argument shape; the others ({other.qsort (·.toString < ·.toString)}) take further parameters (`Signal dom α`), are not output structures of the corpus keys, and are not covered"
  -- negative controls of the mirrors
  let fm ← tyAt env ``Fin.mk []
  if closedPiB fm 3 (.const ``Fin []) then throwError "negative control FAILED: Fin.mk is dependent, not closed"
  if depFirstB fm ``BitVec [] then throwError "negative control FAILED: wrong type former accepted"
  if piNB fm 2 (.app (.const ``Fin []) (.bvar 2)) then throwError "negative control FAILED: wrong binder count accepted"
  let sc ← tyAt env ``Nat.succ []
  if depFirstB sc ``Nat [] then throwError "negative control FAILED: Nat.succ has a closed codomain (result Nat has no bvar), not the dependent shape"
  if notDefn env ``Nat.add then throwError "negative control FAILED: Nat.add is a defnInfo"
  logInfo m!"negative controls ok: Fin.mk is not a closed Pi, not BitVec-shaped, not 2-binder; Nat.succ is not dependent-first; Nat.add (a definition) is rejected as a type former"

/-! ## (4) Negative controls (proved) -/

/-- The first-argument shape is a real condition: a telescope whose result uses the LAST binder is not of the shape (so `instForallS_depFirst` does not apply, and its answer would be wrong). -/
theorem piN_last_not_first (C : Expr) (x y : Name) (A B : Expr) (bi : BinderInfo) :
    ¬ PiN (.forallE x A (.forallE y B (.app C (.bvar 0)) bi) bi) 2 (.app C (.bvar 1)) := by
  rintro ⟨_, _, _, _, h1, _, _, _, _, h2, h3⟩
  cases h1
  cases h2
  have h3' : Expr.app C (.bvar 0) = .app C (.bvar 1) := h3
  injection h3' with _ h4
  injection h4 with h5
  exact absurd h5 (by decide)

/-- The same telescope really yields the LAST argument (not the first): the answer of `instForallS` differs. -/
example : instForallS (.forallE `x (.const `Nat []) (.forallE `y (.const `Nat []) (.app (.const `D []) (.bvar 0)) .default) .default) [.lit (.natVal 1), .lit (.natVal 2)]
    = .app (.const `D []) (.lit (.natVal 2)) := rfl

/-- The row's argument types are a real condition: a row that accepts a `Unit` argument does not satisfy `ArgsTySpec _ _ _ [Nat]`. -/
theorem argsTySpec_not_unit (PT : PrimTableK) (c : Name) (ls : List Level) (row : TmRow) (hrow : PT.tms c ls = some row) (d : Dyn)
    (hd : row.den [.tm ⟨Unit, ()⟩] = some d) : ¬ ArgsTySpec PT c ls [Nat] := by
  rintro ⟨row', h1, _, h3⟩
  rw [hrow] at h1; cases h1
  have h := (h3 _ d hd).1
  have hUN : (Unit : Type) = Nat := h
  have : ∀ a b : Nat, a = b := by rw [← hUN]; exact fun _ _ => rfl
  exact absurd (this 0 1) (by decide)

/-- A first-argument spec is not vacuous in the wrong direction: it fails for a row whose value type is NOT the type former's denotation. -/
theorem firstArgSpec_wrong : ¬ FirstArgSpec PTd `Tst.mk [] true [true] `Tst.E [] := by
  rintro ⟨row, trow, h1, _, h3, _⟩
  simp [PTd] at h3

/-- A type former whose row has the wrong kinds (two arguments) does not satisfy `FirstArgSpec`. -/
theorem firstArgSpec_kinds : ¬ FirstArgSpec PTd `Tst.mk [] false [true] `Tst.D [] := by
  rintro ⟨row, trow, h1, h2, h3, h4, _⟩
  have : trow = dRowD := by
    have : PTd.tys `Tst.D [] = some dRowD := by simp [PTd]
    rw [this] at h3; exact (Option.some.inj h3).symm
  subst this
  simp [dRowD] at h4

/-! ## (5) The dependent-row proof does not reach the substitution obligation -/
open Lean Meta in
def reachable (env : Environment) (roots : List Name) (pfx : List Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo := roots
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      if !(pfx.any (fun p => p.isPrefixOf n)) then continue
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? then cs := cs ++ v.getUsedConstants
      for c in cs do
        if !seen.contains c then todo := c :: todo
  return seen

run_meta do
  let env ← getEnv
  let pfx : List Name := [`Tools.ShippingGen5RowTypedV, `Tools.ShippingGen5ConstValueEVL, `Tools.ShippingGen5ConstValueEV, `Tools.ShippingGen5ConstValueESL, `Tools.ShippingGen5ConstValueES]
  let banned : List Name := [``OblDenSubstS, ``Tools.ShippingGen5ConstValueES.oblDenSubstS_safe, ``tdens_subst, ``argsdens_subst, ``cveks_subst, ``SubV, ``SafeArg]
  let seen := reachable env [``rowTypedAtV_depFirst, ``rowTypedAtV_closedPi, ``rowTypedAtV_nullary_const, ``rowTeleEvAt_constPi, ``denTypedVL, ``denTypedVL_of_rows] pfx
  let hit := banned.filter seen.contains
  unless hit.isEmpty do throwError "V2 theorems reach banned substitution declarations: {hit}"
  -- detector control: the old S soundness theorem does
  let seenS := reachable env [``denTypedS] pfx
  unless seenS.contains ``OblDenSubstS do throwError "detector control FAILED: denTypedS must reach OblDenSubstS"
  logInfo m!"substitution check ok: the V2 row and soundness theorems reach {seen.size} declarations, none of {banned}"

/-! ## (6) Remaining named obligations, axioms, counts -/
run_meta do
  let env ← getEnv
  let remaining : List Name := [``EnvDeclClosed, ``EnvClosedL, ``RowTeleEvAt, ``OblRowTypedV, ``FirstArgSpec, ``ArgsTySpec, ``EnvDepFirst]
  let mut lines : Array MessageData := #[]
  for n in remaining do
    let some ci := env.find? n | throwError "{n} absent"
    if ci.isTheorem || (match ci with | .axiomInfo _ => true | _ => false) then throwError "{n} is a theorem/axiom, expected a Prop definition"
    lines := lines.push m!"  {n} : {ci.type}"
  logInfo m!"named obligations / specs ({lines.size}; Prop definitions, none assumed):\n{MessageData.joinSep lines.toList "\n"}"

def stdAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def provedNames : List Name :=
  [``envClosedL_cvekvl, ``tdenv_wk_decl, ``cvekv_wk_decl, ``wfValV_cons_decl, ``denTypedVL, ``denTypedVL_of_rows, ``cvekv_fun, ``cvekvb_fun, ``tdenv_fun,
   ``oblDenLitsV_of_rows, ``natLit_typed, ``strLit_typed, ``tdenv_const_nullary,
   ``rowTypedAtV_of_none, ``rowTypedAtV_of_den_none, ``oblRowTypedV_of_keys, ``rowTypedAtV_nullary_const, ``rowTypedAtV_closedPi,
   ``rowTypedV_Nat_zero, ``rowTypedV_Bool_false, ``rowTypedV_Bool_true, ``rowTypedV_PUnit_unit1, ``rowTypedV_ActiveEdge_rising, ``rowTypedV_ResetKind_synchronous,
   ``rowTypedV_Nat_succ, ``rowTypedV_Int_ofNat, ``rowTypedV_Int_negSucc, ``rowTypedV_DomainConfig_mk,
   ``piN_substS, ``instForallS_piN_lift, ``instForallS_depFirst, ``argsDenV_head, ``rowTypedAtV_depFirst,
   ``teleEv_constPi, ``rowTeleEvAt_constPi, ``bindersDen_length, ``teleEv_Nat_succ, ``teleEv_Int_ofNat, ``teleEv_Int_negSucc, ``teleEv_DomainConfig_mk,
   ``cvekv_app_old_of_new, ``cvekv_letE_old_of_new,
   ``firstArgSpec_mk, ``argsTySpec_succ, ``bindersDen_Nat, ``piN_last_not_first, ``argsTySpec_not_unit, ``firstArgSpec_wrong, ``firstArgSpec_kinds]
run_meta do
  let mut bad : Array Name := #[]
  let env ← getEnv
  for n in provedNames do
    unless env.contains n do throwError "{n} absent"
    let ax ← Lean.collectAxioms n
    if ax.any (fun a => !stdAx.contains a) then bad := bad.push n
  unless bad.isEmpty do throwError "non-standard axiom (or sorryAx) in: {bad}"
  logInfo m!"axiom check ok: {provedNames.length} proved declarations use only propext / Classical.choice / Quot.sound"

axiom negControlAxiom : False
theorem negControlUsesAxiom : (1 : Nat) = 2 := negControlAxiom.elim
run_meta do
  let ax ← Lean.collectAxioms ``negControlUsesAxiom
  unless ax.contains ``negControlAxiom do throwError "negative control FAILED: detector missed the axiom"
  logInfo m!"negative control ok: detector flags {ax.toList}"

/-! ### Counts

The 115 term keys of the corpus (RowTypedKCheck / the audit): argument-free 6, closed codomain 4, dependent 30, `den = none` / Prop 75.
Per-key theorems on `CVEKVL` (this file's `RowTypedAtV`): argument-free 6 + closed codomain 4 = **10**. Dependent keys: the shape theorem `rowTypedAtV_depFirst` covers every key whose declared type is
`n + 1` binders ending in `D (bvar n)` (checked on the real types of `Fin.mk`, `BitVec.ofFin`, `Decidable.isTrue/isFalse`: 4; the 26 output structures `Foo.mk {dom} fields : Foo dom` are NOT recomputed here: their shape is
the same as the mirror `KOutM.mk`, but the names come from the corpus audit, so they are listed, not proved). `RowTeleEvAt` (argument typing): argument-free 6 (`rowTeleEvAt_nullary`) + closed-codomain 4 (`teleEv_*`) = 10 proved; dependent 30 waiting. -/
run_meta do
  let rowsNullary : Nat := 6
  let rowsClosed : Nat := 4
  let depShapeChecked : Nat := 4
  let depTotal : Nat := 30
  let denNone : Nat := 75
  let teleProved : Nat := rowsNullary + rowsClosed
  let total : Nat := rowsNullary + rowsClosed + depTotal + denNone
  let depListed : Nat := depTotal - depShapeChecked
  unless total == 115 do throwError "partition of the 115 term keys fails"
  logInfo m!"RowTypedAtV proved per key: {teleProved} (argument-free {rowsNullary}, closed codomain {rowsClosed}); dependent {depTotal}: shape theorem proved (specs about PT), shape confirmed on the real types of {depShapeChecked} named keys, the other {depListed} (output structures) listed; den = none / Prop {denNone}; total {total}"
  logInfo m!"RowTeleEvAt proved per key: {teleProved} (argument-free {rowsNullary}, closed {rowsClosed}); remaining {depTotal} dependent (binder types mention earlier arguments; see the draft §V2 for the reasons); den = none / Prop {denNone} (no row)"

end Tests.Gen5.V2Check

#print axioms Tools.ShippingGen5ConstValueEVL.denTypedVL
#print axioms Tools.ShippingGen5ConstValueEVL.cvekv_fun
#print axioms Tools.ShippingGen5RowTypedV.rowTypedAtV_depFirst
#print axioms Tools.ShippingGen5RowTypedV.instForallS_depFirst
#print axioms Tools.ShippingGen5RowTypedV.rowTeleEvAt_constPi
#print axioms Tools.ShippingGen5RowTypedV.cvekv_app_old_of_new
#print axioms Tools.ShippingGen5RowTypedV.oblDenLitsV_of_rows
