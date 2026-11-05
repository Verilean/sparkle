import Tools.ShippingGen5ConstValueEKey
import Tools.ShippingGen5FG
set_option autoImplicit false
-- D.D-4 Key: structural check of the level-indexed table (`Name × List Level`), 13-name collision controls, `#print axioms`.

namespace Tests.Gen5.KeyCheck
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG

/-! ## Structural match: the carrier keeps the type `ConstValueRel`, and functionality needs no hypothesis beyond the derivations -/
example (PT : PrimTableK) : ConstValueRel := CVLSK PT
example (PT : PrimTableK) : ConstValueRel := fun env X α v => ConstValueEKAt PT env X (LS env X) α v
example : ∀ PT : PrimTableK, ConstValueFunctional (CVLSK PT) :=
  fun PT env X _ _ _ _ h h' => constValueEKAt_functional PT env X (LS env X) h h'
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (e τ τ' : Expr) (α β : Type) (v : α) (w : β),
    CVEK PT env ρ e τ α v → CVEK PT env ρ e τ' β w → τ = τ' ∧ α = β ∧ HEq v w := fun _ _ _ _ _ _ _ _ _ _ h h' => cvek_fun h h'
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (τ : Expr) (T T' : Type),
    TDenK PT env ρ τ T → TDenK PT env ρ τ T' → T = T' := fun _ _ _ _ _ _ h h' => tdenk_fun h h'
-- every old (Name-keyed) derivation is a new derivation; a Name-keyed `PT` is the special case that ignores levels
example (PT : PrimTable) (env : Environment) (ρ : Val) (e τ : Expr) (α : Type) (v : α) :
    CVE PT env ρ e τ α v → CVEK PT.toK env ρ e τ α v := cve_toK
-- the level-polymorphic reading is also a special case (one row per name, a function of `ls`)
example (a : Name → Option (List Level → TyRow)) (b : Name → Option (List Level → TmRow)) (c : Name) (ls : List Level) :
    (PrimTableK.ofPoly a b).tms c ls = (b c).map (· ls) := rfl

/-! ## Two rows for one name at different `ls` (stand-ins for `Bool.rec.{0}` / `Bool.rec.{1}`; `kinds` differ so the rows are distinguishable) -/
def rowA : TmRow := ⟨[true], fun _ => none⟩
def rowB : TmRow := ⟨[true, true], fun _ => none⟩
theorem rowA_ne_rowB : rowA ≠ rowB := fun h => by
  have := congrArg TmRow.kinds h
  simp [rowA, rowB] at this

def l0 : List Level := [Level.zero]
def l1 : List Level := [Level.succ Level.zero]
def l2 : List Level := [Level.succ (Level.succ Level.zero)]

/-- Levels of the form `succ^n zero` as numbers (`Level`'s `BEq` is extern, so the kernel cannot evaluate it; this is structural). -/
def lvNat : Level → Option Nat
  | .zero => some 0
  | .succ l => (lvNat l).map (· + 1)
  | _ => none
def lsNats (ls : List Level) : Option (List Nat) := ls.mapM lvNat

/-- A level-keyed table holding `Bool.rec` at `[0]` and at `[1]`, `Nat.rec` at `[1]` and `[2]`, with different rows. -/
def TK : PrimTableK where
  tys := fun _ _ => none
  tms := fun c ls =>
    if c == ``Bool.rec && lsNats ls == some [0] then some rowA
    else if c == ``Bool.rec && lsNats ls == some [1] then some rowB
    else if c == ``Nat.rec && lsNats ls == some [1] then some rowA
    else if c == ``Nat.rec && lsNats ls == some [2] then some rowB
    else none

def kindsAt (c : Name) (ls : List Level) : Option (List Bool) := (TK.tms c ls).map TmRow.kinds
example : kindsAt ``Bool.rec l0 = some [true] := by decide +kernel
example : kindsAt ``Bool.rec l1 = some [true, true] := by decide +kernel
example : kindsAt ``Nat.rec l1 = some [true] := by decide +kernel
example : kindsAt ``Nat.rec l2 = some [true, true] := by decide +kernel
example : kindsAt ``Bool.rec l2 = none := by decide +kernel
/-- Both rows are present at once and are different: no collision. -/
theorem TK_two_rows : ∃ r r' : TmRow, TK.tms ``Bool.rec l0 = some r ∧ TK.tms ``Bool.rec l1 = some r' ∧ r ≠ r' := by
  have h0 : kindsAt ``Bool.rec l0 = some [true] := by decide +kernel
  have h1 : kindsAt ``Bool.rec l1 = some [true, true] := by decide +kernel
  unfold kindsAt at h0 h1
  cases e0 : TK.tms ``Bool.rec l0 with
  | none => rw [e0] at h0; simp at h0
  | some r =>
    cases e1 : TK.tms ``Bool.rec l1 with
    | none => rw [e1] at h1; simp at h1
    | some r' =>
      rw [e0] at h0; rw [e1] at h1
      simp at h0 h1
      exact ⟨r, r', rfl, rfl, fun h => by rw [h] at h0; rw [h0] at h1; simp at h1⟩
theorem TK_two_rows_nat : ∃ r r' : TmRow, TK.tms ``Nat.rec l1 = some r ∧ TK.tms ``Nat.rec l2 = some r' ∧ r ≠ r' := by
  have h0 : kindsAt ``Nat.rec l1 = some [true] := by decide +kernel
  have h1 : kindsAt ``Nat.rec l2 = some [true, true] := by decide +kernel
  unfold kindsAt at h0 h1
  cases e0 : TK.tms ``Nat.rec l1 with
  | none => rw [e0] at h0; simp at h0
  | some r =>
    cases e1 : TK.tms ``Nat.rec l2 with
    | none => rw [e1] at h1; simp at h1
    | some r' =>
      rw [e0] at h0; rw [e1] at h1
      simp at h0 h1
      exact ⟨r, r', rfl, rfl, fun h => by rw [h] at h0; rw [h0] at h1; simp at h1⟩

/-! ## Negative control: with a `Name`-only key two rows for one name collide -/
/-- No `Name`-keyed table holds two different rows for the same name: the lookup is a function of the name alone. -/
theorem nameKey_collides (PT : PrimTable) (c : Name) (r r' : TmRow) (h : PT.tms c = some r) (h' : PT.tms c = some r') : r = r' := by
  rw [h] at h'; exact Option.some.inj h'
/-- So `TK`'s two-row situation is NOT representable by any `Name`-keyed `PT`. -/
theorem TK_not_nameKeyed : ¬ ∃ PT : PrimTable, ∃ r r' : TmRow, PT.tms ``Bool.rec = some r ∧ PT.tms ``Bool.rec = some r' ∧ r ≠ r' :=
  fun ⟨PT, r, r', h, h', hne⟩ => hne (nameKey_collides PT _ r r' h h')
/-- And the embedding of a `Name`-keyed table is blind to levels: it cannot tell `[0]` from `[1]`. -/
theorem toK_level_blind (PT : PrimTable) (c : Name) : PT.toK.tms c l0 = PT.toK.tms c l1 := rfl

/-! ## Real constants: the 13-name situation exists in the environment (`Bool.rec`, `Nat.rec`, `PProd.mk`, `List.rec`):
the instantiated type differs with `ls`, which is exactly what `OblRowTypedK` is indexed by. -/
run_meta do
  let env ← getEnv
  let mut n : Nat := 0
  for c in [``Bool.rec, ``Nat.rec, ``List.rec, ``PProd.mk, ``PUnit.unit, ``False.rec] do
    let some ci := env.find? c | throwError "{c} absent"
    let lp := ci.levelParams.length
    unless lp ≥ 1 do throwError "{c}: expected a level-polymorphic constant"
    -- two level lists of the right length; the declared types instantiate differently
    let ls0 := ci.levelParams.map fun _ => Level.zero
    let ls1 := ci.levelParams.map fun _ => Level.succ Level.zero
    unless ci.type.instantiateLevelParams ci.levelParams ls0 != ci.type.instantiateLevelParams ci.levelParams ls1 do
      throwError "{c}: types coincide at [0] and [1]"
    n := n + 1
  logInfo m!"Key controls ok: {n} level-polymorphic constants have distinct types at distinct ls"

end Tests.Gen5.KeyCheck

#print axioms Tools.ShippingGen5ConstValueEKey.cvek_fun
#print axioms Tools.ShippingGen5ConstValueEKey.tdenk_fun
#print axioms Tools.ShippingGen5ConstValueEKey.argsdenk_fun
#print axioms Tools.ShippingGen5ConstValueEKey.constValueEKAt_functional
#print axioms Tools.ShippingGen5ConstValueEKey.cve_toK
#print axioms Tests.Gen5.KeyCheck.TK_two_rows
#print axioms Tests.Gen5.KeyCheck.TK_two_rows_nat
#print axioms Tests.Gen5.KeyCheck.TK_not_nameKeyed
#print axioms Tests.Gen5.KeyCheck.toK_level_blind
