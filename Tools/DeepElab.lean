/-
  The GENERAL Signal↔IR theorem — the deep-embedding track (E0–E2).

  `#verify_elab` proves the Signal↔IR link per circuit, by generating a
  proof each time.  This file proves it ONCE, for every circuit in a
  closed deep grammar:

      CExpr Γ w      typed deep expressions (de Bruijn context Γ of
                     widths; const/var/add/sub/mux/eq in v0)
      Cdo Γr Γi w    a circuit: register inits, one next-state
                     expression per register, one output expression

  and four theorems, each a single induction / composition:

      CExpr.compile_correct   evalExpr (compile e) = (denote e).toNat
      Cdo.stateSig_eq         the Signal-level loop fixpoint equals the
                              spec recurrence  (via `loop_trace`, once)
      Cdo.irState_eq          the IR-side recurrence equals the spec
      Cdo.elab_general        the capstone: for EVERY deep circuit,
                              every input stream, every cycle, the
                              Signal output equals the compiled output
                              cone under the PROVEN `evalExpr`

  The only per-circuit obligation is injectivity of the slot names —
  decidable, discharged by `decide` on concrete circuits.

  What remains for full CompCert-shape (E3): reifying the `circuit do`
  surface syntax into `Cdo` values inside the macro, so user-written
  circuits are instances by construction; and growing the expression
  grammar op by op (each op = one constructor + three cases).  Circuits
  outside the grammar (e.g. arbitrary Lean functions under `.map`)
  keep the per-instance `#verify_elab` fallback.
-/

import Sparkle.IR.Semantics
import Tools.VerifyElab
import Tools.ConcatNorm
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core

/-! E0: typed deep expression embedding.  Context Γ = widths of the
    variables in scope (registers ++ inputs), de Bruijn indexed. -/

inductive CExpr : List Nat → Nat → Type where
  | const {Γ} (w : Nat) (v : Nat) : CExpr Γ w
  | var   {Γ} (i : Fin Γ.length) : CExpr Γ (Γ.get i)
  | add   {Γ w} (a b : CExpr Γ w) : CExpr Γ w
  | sub   {Γ w} (a b : CExpr Γ w) : CExpr Γ w
  | mux   {Γ w} (c : CExpr Γ 1) (t e : CExpr Γ w) : CExpr Γ w
  | eq    {Γ w} (a b : CExpr Γ w) : CExpr Γ 1
  | and   {Γ w} (a b : CExpr Γ w) : CExpr Γ w
  | or    {Γ w} (a b : CExpr Γ w) : CExpr Γ w
  | xor   {Γ w} (a b : CExpr Γ w) : CExpr Γ w
  | mul   {Γ w} (a b : CExpr Γ w) : CExpr Γ w
  | shl   {Γ w} (a b : CExpr Γ w) : CExpr Γ w
  | shr   {Γ w} (a b : CExpr Γ w) : CExpr Γ w
  | lt    {Γ w} (a b : CExpr Γ w) : CExpr Γ 1
  | le    {Γ w} (a b : CExpr Γ w) : CExpr Γ 1
  | cat   {Γ w₁ w₂} (a : CExpr Γ w₁) (b : CExpr Γ w₂) :
      CExpr Γ (w₁ + w₂)
  | slt   {Γ w} (a b : CExpr Γ w) : CExpr Γ 1
  | sle   {Γ w} (a b : CExpr Γ w) : CExpr Γ 1
  | slice {Γ w} (a : CExpr Γ w) (hi lo : Nat) :
      CExpr Γ (hi - lo + 1)
  | not   {Γ w} (a : CExpr Γ w) : CExpr Γ w
  | neg   {Γ w} (a : CExpr Γ w) : CExpr Γ w

/-- Shallow denotation: BitVec values for the variables, BitVec out. -/
def CEnv (Γ : List Nat) := ∀ i : Fin Γ.length, BitVec (Γ.get i)

def CExpr.denote {Γ w} (ρ : CEnv Γ) : CExpr Γ w → BitVec w
  | .const _ v => BitVec.ofNat _ v
  | .var i => ρ i
  | .add a b => a.denote ρ + b.denote ρ
  | .sub a b => a.denote ρ - b.denote ρ
  | .mux c t e => if c.denote ρ = 1#1 then t.denote ρ else e.denote ρ
  | .eq a b => if a.denote ρ = b.denote ρ then 1#1 else 0#1
  | .and a b => a.denote ρ &&& b.denote ρ
  | .or a b => a.denote ρ ||| b.denote ρ
  | .xor a b => a.denote ρ ^^^ b.denote ρ
  | .mul a b => a.denote ρ * b.denote ρ
  | .shl a b => a.denote ρ <<< (b.denote ρ).toNat
  | .shr a b => a.denote ρ >>> (b.denote ρ).toNat
  | .lt a b => if a.denote ρ < b.denote ρ then 1#1 else 0#1
  | .le a b => if a.denote ρ ≤ b.denote ρ then 1#1 else 0#1
  | .cat a b => a.denote ρ ++ b.denote ρ
  | .slt a b => if (a.denote ρ).toInt < (b.denote ρ).toInt
      then 1#1 else 0#1
  | .sle a b => if (a.denote ρ).toInt ≤ (b.denote ρ).toInt
      then 1#1 else 0#1
  | .slice a hi lo => (a.denote ρ).extractLsb' lo (hi - lo + 1)
  | .not a => ~~~(a.denote ρ)
  | .neg a => -(a.denote ρ)

/-- Compilation to the IR, with a naming of the context slots. -/
def CExpr.compile {Γ w} (names : Fin Γ.length → String) :
    CExpr Γ w → Expr
  | .const w v => .const (Int.ofNat v) w
  | .var i => .ref (names i)
  | .add a b => .op .add [a.compile names, b.compile names]
  | .sub a b => .op .sub [a.compile names, b.compile names]
  | .mux c t e => .op .mux [c.compile names, t.compile names,
      e.compile names]
  | .eq a b => .op .eq [a.compile names, b.compile names]
  | .and a b => .op .and [a.compile names, b.compile names]
  | .or a b => .op .or [a.compile names, b.compile names]
  | .xor a b => .op .xor [a.compile names, b.compile names]
  | .mul a b => .op .mul [a.compile names, b.compile names]
  | .shl a b => .op .shl [a.compile names, b.compile names]
  | .shr a b => .op .shr [a.compile names, b.compile names]
  | .lt a b => .op .lt_u [a.compile names, b.compile names]
  | .le a b => .op .le_u [a.compile names, b.compile names]
  | .cat a b => .concat [a.compile names, b.compile names]
  | .slt a b => .op .lt_s [a.compile names, b.compile names]
  | .sle a b => .op .le_s [a.compile names, b.compile names]
  | .slice a hi lo => .slice (a.compile names) hi lo
  | .not a => .op .not [a.compile names]
  | .neg a => .op .neg [a.compile names]

/-- The IR's signed reading of a bit pattern IS `BitVec.toInt`. -/
theorem toSigned_toNat {w : Nat} (x : BitVec w) :
    Sparkle.IR.Semantics.toSigned w x.toNat = x.toInt := by
  unfold Sparkle.IR.Semantics.toSigned
  rw [BitVec.toInt_eq_toNat_cond]
  rcases Nat.eq_zero_or_pos w with h | h
  · subst h
    have h0 : x.toNat = 0 := by have := x.isLt; omega
    simp [h0]
  · have h2 : 2 ^ w = 2 ^ (w - 1) * 2 := by
      have hp := Nat.pow_succ 2 (w - 1)
      have h1 : (w - 1).succ = w := Nat.succ_pred_eq_of_pos h
      rw [h1] at hp
      exact hp
    have hx := x.isLt
    split <;> split <;> omega

/-- NOT is XOR with all-ones, at the `toNat` level — bridges
    `evalOp`'s not-formula to `BitVec.not`. -/
theorem toNat_not_xor {w : Nat} (x : BitVec w) :
    x.toNat ^^^ (2 ^ w - 1) = (~~~x).toNat := by
  have h : ~~~x = x ^^^ BitVec.allOnes w := by
    ext i h
    simp
  rw [h, BitVec.toNat_xor, BitVec.toNat_allOnes]

/-- Compiled expressions carry their type-level width — the companion
    fact that pins `evalOp`'s node mask. -/
theorem CExpr.compile_width {Γ w} (names : Fin Γ.length → String)
    (we : WEnv) (hw : ∀ i, we (names i) = Γ.get i) :
    ∀ e : CExpr Γ w,
      Sparkle.IR.Semantics.widthOf we (e.compile names) = w := by
  intro e
  induction e with
  | const w v => simp [CExpr.compile, Sparkle.IR.Semantics.widthOf]
  | var i => simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, hw]
  | add a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha, ihb]
  | sub a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha, ihb]
  | mux c t e ihc iht ihe =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iht, ihe]
  | eq a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf]
  | and a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha, ihb]
  | or a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha, ihb]
  | xor a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha, ihb]
  | mul a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha, ihb]
  | shl a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha, ihb]
  | shr a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha]
  | lt a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf]
  | le a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf]
  | cat a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf,
      Sparkle.IR.Semantics.widthOf.go, iha, ihb]
  | slt a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf]
  | sle a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf]
  | slice a hi lo iha =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf]
  | not a iha =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha]
  | neg a iha =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha]

/-- E1, THE general theorem: for any deep expression, the compiled IR
    under the PROVEN semantics computes the denotation — one structural
    induction, all circuits in the grammar at once. -/
theorem CExpr.compile_correct {Γ w} (names : Fin Γ.length → String)
    (we : WEnv) (env : Env) (ρ : CEnv Γ)
    (hw : ∀ i, we (names i) = Γ.get i)
    (hv : ∀ i : Fin Γ.length, env (names i) = (ρ i).toNat) :
    ∀ e : CExpr Γ w,
      evalExpr we env (e.compile names) = some (e.denote ρ).toNat := by
  intro e
  induction e with
  | const w v =>
    simp only [CExpr.compile, CExpr.denote, evalExpr, mask,
      BitVec.toNat_ofNat, Int.add_emod_right, ← Int.natCast_pow,
      ← Int.natCast_emod, Int.ofNat_eq_natCast, Int.toNat_natCast,
      Option.some_inj, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  | var i =>
    simp [CExpr.compile, CExpr.denote, evalExpr, hv]
  | add a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask, BitVec.toNat_add,
      CExpr.compile_width names we hw]
  | sub a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask, BitVec.toNat_sub,
      CExpr.compile_width names we hw, Nat.add_comm]
  | mux c t e ihc iht ihe =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      ihc, iht, ihe, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw]
    by_cases hc : denote ρ c = 1#1
    · simp [hc]
    · have h0 : (denote ρ c).toNat = 0 := by
        have hlt := (denote ρ c).isLt
        have h1 : (denote ρ c).toNat ≠ 1 := fun h =>
          hc (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      simp [hc, h0]
  | eq a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw]
    by_cases he : denote ρ a = denote ρ b
    · simp [he]
    · have hne : (denote ρ a).toNat ≠ (denote ρ b).toNat := fun h =>
        he (BitVec.eq_of_toNat_eq h)
      simp [he, hne]
  | and a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw, ← BitVec.toNat_and]
  | or a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw, ← BitVec.toNat_or]
  | xor a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw, ← BitVec.toNat_xor]
  | mul a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask, BitVec.toNat_mul,
      CExpr.compile_width names we hw]
  | shl a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      BitVec.toNat_shiftLeft, CExpr.compile_width names we hw]
  | shr a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      BitVec.toNat_ushiftRight, CExpr.compile_width names we hw]
  | lt a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw]
    by_cases hlt : denote ρ a < denote ρ b
    · simp [hlt, BitVec.lt_def.mp hlt]
    · have : ¬ (denote ρ a).toNat < (denote ρ b).toNat := fun h =>
        hlt (BitVec.lt_def.mpr h)
      simp [hlt, this]
  | le a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw]
    by_cases hle : denote ρ a ≤ denote ρ b
    · simp [hle, BitVec.le_def.mp hle]
    · have : ¬ (denote ρ a).toNat ≤ (denote ρ b).toNat := fun h =>
        hle (BitVec.le_def.mpr h)
      simp [hle, this]
  | cat a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList,
      Sparkle.IR.Semantics.evalExpr.go, iha, ihb, mask,
      CExpr.compile_width names we hw, BitVec.toNat_append,
      BitVec.toNat_mod_cancel]
  | slt a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw, toSigned_toNat]
    by_cases hlt : (denote ρ a).toInt < (denote ρ b).toInt
    · simp [hlt]
    · simp [hlt]
  | sle a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw, toSigned_toNat]
    by_cases hle : (denote ρ a).toInt ≤ (denote ρ b).toInt
    · simp [hle]
    · simp [hle]
  | slice a hi lo iha =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, iha,
      mask, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  | not a iha =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw, toNat_not_xor,
      BitVec.toNat_mod_cancel, BitVec.toNat_not]
    exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos w; omega)
  | neg a iha =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw, BitVec.toNat_neg,
      BitVec.toNat_mod_cancel]

/-! E2: the statement layer.  A deep circuit = register widths Γr,
    input widths Γi, one next-state expression per register, one
    output expression — all over the joined context Γr ++ Γi. -/

structure Cdo (Γr Γi : List Nat) (wOut : Nat) where
  inits : CEnv Γr
  next  : ∀ i : Fin Γr.length, CExpr (Γr ++ Γi) (Γr.get i)
  out   : CExpr (Γr ++ Γi) wOut

/-- Join a register valuation and an input valuation. -/
def CEnv.join {Γr Γi : List Nat} (ρr : CEnv Γr) (ρi : CEnv Γi) :
    CEnv (Γr ++ Γi) := fun i =>
  if h : i.val < Γr.length then
    have hw : (Γr ++ Γi).get i = Γr.get ⟨i.val, h⟩ :=
      List.getElem_append_left h
    hw ▸ ρr ⟨i.val, h⟩
  else
    have hj : i.val - Γr.length < Γi.length := by
      have := i.isLt; simp [List.length_append] at this; omega
    have hw : (Γr ++ Γi).get i = Γi.get ⟨i.val - Γr.length, hj⟩ := by
      simp [List.getElem_append_right (by omega : Γr.length ≤ i.val)]
    hw ▸ ρi ⟨i.val - Γr.length, hj⟩

/-- The Nat-level state recurrence (the SPEC side). -/
def Cdo.stateAt {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inp : Nat → CEnv Γi) : Nat → CEnv Γr
  | 0 => c.inits
  | t+1 => fun i =>
    (c.next i).denote (CEnv.join (c.stateAt inp t) (inp t))

/-- Output value at cycle t. -/
def Cdo.outAt {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inp : Nat → CEnv Γi) (t : Nat) : BitVec wOut :=
  c.out.denote (CEnv.join (c.stateAt inp t) (inp t))

/-! E2b: the Signal-level semantics of a `Cdo`, and the ONCE-proven
    bridge to the spec recurrence, via `loop_trace`. -/

instance {Γ : List Nat} : Inhabited (CEnv Γ) := ⟨fun _ => default⟩

variable {dom : Sparkle.Core.Domain.DomainConfig}

/-- The loop body: registers delay by one, next-state from the deep
    expressions over the previous state and the inputs. -/
def Cdo.loopF {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) :
    Sparkle.Core.Signal.Signal dom (CEnv Γr) →
    Sparkle.Core.Signal.Signal dom (CEnv Γr) :=
  fun live => ⟨fun t => match t with
    | 0 => c.inits
    | t+1 => fun i => (c.next i).denote
        (CEnv.join (live.val t) (fun j => (inpS j).val t))⟩

/-- Signal-level register state = the pure loop fixpoint. -/
def Cdo.stateSig {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) :
    Sparkle.Core.Signal.Signal dom (CEnv Γr) :=
  Sparkle.Core.Signal.Signal.loop (c.loopF inpS)

/-- ONCE: the Signal state equals the spec recurrence at every cycle. -/
theorem Cdo.stateSig_eq {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) (t : Nat) :
    (c.stateSig (dom := dom) inpS).val t
      = c.stateAt (fun t j => (inpS j).val t) t := by
  unfold Cdo.stateSig
  rw [loop_trace_at _ (fun s => c.stateAt (fun t j => (inpS j).val t) s)
    ?hstep]
  case hstep =>
    intro u pre hpre
    cases u with
    | zero => rfl
    | succ n =>
      show (fun i => (c.next i).denote
          (CEnv.join (pre.val n) (fun j => (inpS j).val n))) = _
      rw [hpre n (Nat.lt_succ_self n)]
      rfl

/-! E2a: compilation to the IR and the general spec↔IR theorem. -/

/-- A total map from names, built as an if-chain over an index list —
    the same shape `#verify_elab` generates.  Injectivity of `names`
    is a hypothesis here; concrete circuits discharge it by `decide`. -/
def chainMap {n : Nat} (names : Fin n → String) (val : Fin n → Nat) :
    List (Fin n) → String → Nat
  | [], _ => 0
  | i :: rest, s =>
    if names i == s then val i else chainMap names val rest s

theorem chainMap_lookup {n : Nat} (names : Fin n → String)
    (val : Fin n → Nat)
    (hinj : ∀ i j, names i = names j → i = j) :
    ∀ (l : List (Fin n)) (i : Fin n), i ∈ l →
      chainMap names val l (names i) = val i := by
  intro l
  induction l with
  | nil => intro i hi; simp at hi
  | cons j rest ih =>
    intro i hi
    by_cases hj : names j == names i
    · have : j = i := hinj _ _ (by simpa using hj)
      subst this
      simp [chainMap]
    · have hne : i ≠ j := fun h => by subst h; simp at hj
      simp only [chainMap, hj, if_neg (by simpa using hj)]
      exact ih i (by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm (fun h => hne h.symm)
        · exact h)

/-- Width and value environments for a valuation over the context. -/
def weOfC {n : Nat} (names : Fin n → String) (Γget : Fin n → Nat) :
    WEnv := chainMap names Γget (List.finRange n)

def envOfC {n : Nat} (names : Fin n → String) (v : Fin n → Nat) :
    Env := chainMap names v (List.finRange n)

theorem weOfC_names {n} (names) (Γget : Fin n → Nat)
    (hinj : ∀ i j, names i = names j → i = j) (i : Fin n) :
    weOfC names Γget (names i) = Γget i :=
  chainMap_lookup names Γget hinj _ i (List.mem_finRange i)

theorem envOfC_names {n} (names) (v : Fin n → Nat)
    (hinj : ∀ i j, names i = names j → i = j) (i : Fin n) :
    envOfC names v (names i) = v i :=
  chainMap_lookup names v hinj _ i (List.mem_finRange i)

/-- `toNat` is invariant under width-cast. -/
theorem toNat_cast {a b : Nat} (h : a = b) (x : BitVec a) :
    (h ▸ x).toNat = x.toNat := by cases h; rfl

/-- The joined valuation at the Nat level. -/
def natJoin {Γr Γi : List Nat} (r : Fin Γr.length → Nat)
    (x : Fin Γi.length → Nat) : Fin (Γr ++ Γi).length → Nat := fun j =>
  if h : j.val < Γr.length then r ⟨j.val, h⟩
  else x ⟨j.val - Γr.length, by
    have := j.isLt; simp [List.length_append] at this; omega⟩

theorem natJoin_eq_join {Γr Γi : List Nat} (ρr : CEnv Γr) (ρi : CEnv Γi)
    (j : Fin (Γr ++ Γi).length) :
    natJoin (fun i => (ρr i).toNat) (fun i => (ρi i).toNat) j
      = (CEnv.join ρr ρi j).toNat := by
  unfold natJoin CEnv.join
  by_cases h : j.val < Γr.length <;> simp [h, toNat_cast]

/- ---- envOfC as a stepModule seed: boundedness and the "not a
        register/input" default (deep-bridge replay) ---- -/

theorem chainMap_bounded {n : Nat} (names : Fin n → String)
    (val : Fin n → Nat) (we : WEnv)
    (hv : ∀ i, val i < 2 ^ we (names i)) :
    ∀ (l : List (Fin n)) (s : String), chainMap names val l s < 2 ^ we s
  | [], s => by simp [chainMap]; exact Nat.two_pow_pos _
  | i :: rest, s => by
    simp only [chainMap]
    split
    · rename_i h
      have h' : names i = s := by simpa using h
      rw [← h']
      exact hv i
    · exact chainMap_bounded names val we hv rest s

/-- A `chainMap`-built environment is width-bounded when every listed
    valuation is (unlisted names read 0). -/
theorem envOfC_bounded {n : Nat} (names : Fin n → String)
    (val : Fin n → Nat) (we : WEnv)
    (hv : ∀ i, val i < 2 ^ we (names i)) :
    ∀ s, envOfC names val s < 2 ^ we s :=
  fun s => chainMap_bounded names val we hv _ s

theorem chainMap_notin {n : Nat} (names : Fin n → String)
    (val : Fin n → Nat) (s : String) (hs : ∀ i, names i ≠ s) :
    ∀ (l : List (Fin n)), chainMap names val l s = 0
  | [] => rfl
  | i :: rest => by
    simp only [chainMap]
    rw [if_neg (by simpa using hs i)]
    exact chainMap_notin names val s hs rest

/-- Names outside the register/input family read 0. -/
theorem envOfC_notin {n : Nat} (names : Fin n → String)
    (val : Fin n → Nat) (s : String) (hs : ∀ i, names i ≠ s) :
    envOfC names val s = 0 :=
  chainMap_notin names val s hs _

/-- The IR-side state recurrence: each register's compiled cone under
    the PROVEN `evalExpr`, in the compiled module's environments. -/
def Cdo.irState {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (names : Fin (Γr ++ Γi).length → String)
    (inp : Nat → CEnv Γi) : Nat → Fin Γr.length → Nat
  | 0 => fun i => (c.inits i).toNat
  | t+1 => fun i =>
    (evalExpr (weOfC names (fun j => (Γr ++ Γi).get j))
      (envOfC names (natJoin (c.irState names inp t)
        (fun j => (inp t j).toNat)))
      ((c.next i).compile names)).getD 0

/-- `irState` reads only `next` and `inits`: the per-port `Cdo`s of a
    struct-returning circuit (same registers, different `out`) share
    one IR recurrence.  (`wOut` may differ, so two output widths.) -/
theorem Cdo.irState_congr {Γr Γi wOut wOut'} (c : Cdo Γr Γi wOut)
    (c' : Cdo Γr Γi wOut')
    (names : Fin (Γr ++ Γi).length → String) (inp : Nat → CEnv Γi)
    (hn : c.next = c'.next) (hi : c.inits = c'.inits) :
    c.irState names inp = c'.irState names inp := by
  funext t
  induction t with
  | zero => funext i; simp [Cdo.irState, hi]
  | succ t ih => funext i; simp only [Cdo.irState, ih, hn]

/-- **E2a, general**: the IR recurrence equals the spec, for EVERY deep
    circuit — one induction, `compile_correct` doing the per-register
    step. -/
theorem Cdo.irState_eq {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (names : Fin (Γr ++ Γi).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (inp : Nat → CEnv Γi) (t : Nat) (i : Fin Γr.length) :
    c.irState names inp t i = (c.stateAt inp t i).toNat := by
  induction t generalizing i with
  | zero => rfl
  | succ n ih =>
    show (evalExpr _ _ ((c.next i).compile names)).getD 0 = _
    rw [CExpr.compile_correct names _ _
      (CEnv.join (c.stateAt inp n) (inp n))
      (fun j => weOfC_names names _ hinj j)
      (fun j => by
        rw [envOfC_names names _ hinj j, ← natJoin_eq_join]
        congr 1
        funext k
        exact ih k)]
    · rfl

/-- The Signal-level OUTPUT of a deep circuit. -/
def Cdo.outSig {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) :
    Sparkle.Core.Signal.Signal dom (BitVec wOut) :=
  ⟨fun t => c.out.denote
    (CEnv.join ((c.stateSig inpS).val t) (fun j => (inpS j).val t))⟩

/-- **THE GENERAL SIGNAL↔IR THEOREM (E2 capstone).**  For EVERY deep
    circuit, every input stream, and every cycle: the Signal-level
    output equals the compiled output cone under the PROVEN IR
    semantics, evaluated at the IR-side state recurrence.  One proof;
    no per-instance obligations beyond `decide`-able name injectivity. -/
theorem Cdo.elab_general {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (names : Fin (Γr ++ Γi).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) (t : Nat) :
    ((c.outSig (dom := dom) inpS).val t).toNat
      = (evalExpr (weOfC names (fun j => (Γr ++ Γi).get j))
          (envOfC names (natJoin
            (c.irState names (fun t j => (inpS j).val t) t)
            (fun j => ((inpS j).val t).toNat)))
          (c.out.compile names)).getD 0 := by
  rw [CExpr.compile_correct names _ _
    (CEnv.join (c.stateAt (fun t j => (inpS j).val t) t)
      (fun j => (inpS j).val t))
    (fun j => weOfC_names names _ hinj j)
    (fun j => by
      rw [envOfC_names names _ hinj j, ← natJoin_eq_join]
      congr 1
      funext k
      exact c.irState_eq names hinj _ t k)]
  show ((c.outSig (dom := dom) inpS).val t).toNat
      = (c.out.denote _).toNat
  unfold Cdo.outSig
  simp only [c.stateSig_eq inpS t]

/-! E3: reifying elaborated circuits into `Cdo` values.

The meta side lives here: turn an inlined IR cone back into a `CExpr`
term (well-defined on the compiler's image — the cones `#verify_elab`
already computes), so a circuit's deep value can be GENERATED and the
general theorem applied, leaving only the Signal-side bridge as a
per-instance proof. -/

namespace Tools.DeepElab

open Lean Elab Command

/-- Build the `CExpr Γ w` term for an inlined cone.  `slot` maps a ref
    name to its context index; widths are checked by the elaborator
    when the generated definition elaborates. -/
partial def toCExpr (slot : String → Option Nat) :
    Sparkle.IR.AST.Expr → CommandElabM Term
  | .const v w => do
    if v < 0 then throwError "#verify_elab_deep: negative const"
    `(CExpr.const $(quote w) $(quote v.toNat))
  | .ref n => do
    match slot n with
    | some i => `(CExpr.var ⟨$(quote i), by decide⟩)
    | none => throwError "#verify_elab_deep: unknown ref {n}"
  | .op .add [a, b] => do
    `(CExpr.add $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .sub [a, b] => do
    `(CExpr.sub $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .mux [c, t, e] => do
    `(CExpr.mux $(← toCExpr slot c) $(← toCExpr slot t)
        $(← toCExpr slot e))
  | .op .eq [a, b] => do
    `(CExpr.eq $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .and [a, b] => do
    `(CExpr.and $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .or [a, b] => do
    `(CExpr.or $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .xor [a, b] => do
    `(CExpr.xor $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .mul [a, b] => do
    `(CExpr.mul $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .shl [a, b] => do
    `(CExpr.shl $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .shr [a, b] => do
    `(CExpr.shr $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .lt_u [a, b] => do
    `(CExpr.lt $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .le_u [a, b] => do
    `(CExpr.le $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .lt_s [a, b] => do
    `(CExpr.slt $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .le_s [a, b] => do
    `(CExpr.sle $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .gt_s [a, b] => do
    `(CExpr.slt $(← toCExpr slot b) $(← toCExpr slot a))
  | .op .ge_s [a, b] => do
    `(CExpr.sle $(← toCExpr slot b) $(← toCExpr slot a))
  | .slice e hi lo => do
    `(CExpr.slice $(← toCExpr slot e) $(quote hi) $(quote lo))
  | .op .not [a] => do
    `(CExpr.not $(← toCExpr slot a))
  | .op .neg [a] => do
    `(CExpr.neg $(← toCExpr slot a))
  -- gt/ge reify as their lt/le mirror (`evalOp` defines them so)
  | .op .gt_u [a, b] => do
    `(CExpr.lt $(← toCExpr slot b) $(← toCExpr slot a))
  | .op .ge_u [a, b] => do
    `(CExpr.le $(← toCExpr slot b) $(← toCExpr slot a))
  -- n-ary concat becomes right-nested binary cats (widths add up
  -- identically; the capstone theorem is about the COMPILED form)
  | .concat [a] => toCExpr slot a
  | .concat (a :: rest) => do
    `(CExpr.cat $(← toCExpr slot a)
        $(← toCExpr slot (.concat rest)))
  | .op o args => throwError
      "#verify_elab_deep: operator {o.toString}/{args.length} outside the deep grammar"
  | e => throwError "#verify_elab_deep: {repr e} outside the deep grammar"

/-- The literal-width SHALLOW term of an inlined cone: the same tree
    `toCExpr` builds, but written directly as a BitVec expression over
    the register readers (`rdOf i`) and the input values (`inOf j`),
    constructor-for-constructor the way `CExpr.denote` unfolds each
    node.  `denote (toCExpr e) ρ` and `toShallow e` are therefore
    definitionally equal — `rfl` proves the per-register step lemmas —
    while every width in the shallow term is a literal.  Mirror
    `toCExpr` exactly (n-ary concat nesting, gt/ge mirroring): a
    divergence makes those `rfl`s fail loudly, never silently. -/
partial def toShallow (slot : String → Option Nat) (nR : Nat)
    (rdOf : Nat → CommandElabM Term) (inOf : Nat → CommandElabM Term) :
    Sparkle.IR.AST.Expr → CommandElabM Term
  | .const v w => do
    if v < 0 then throwError "#verify_elab_deep: negative const"
    `((BitVec.ofNat $(quote w) $(quote v.toNat)))
  | .ref n => do
    match slot n with
    | some i => if i < nR then rdOf i else inOf (i - nR)
    | none => throwError "#verify_elab_deep: unknown ref {n}"
  | .op .add [a, b] => do `(($(← go a) + $(← go b)))
  | .op .sub [a, b] => do `(($(← go a) - $(← go b)))
  | .op .mux [c, t, e] => do
    let c ← go c; let t ← go t; let e ← go e
    `((if $c = 1#1 then $t else $e))
  | .op .eq [a, b] => do
    let a ← go a; let b ← go b
    `((if $a = $b then 1#1 else 0#1))
  | .op .and [a, b] => do `(($(← go a) &&& $(← go b)))
  | .op .or [a, b] => do `(($(← go a) ||| $(← go b)))
  | .op .xor [a, b] => do `(($(← go a) ^^^ $(← go b)))
  | .op .mul [a, b] => do `(($(← go a) * $(← go b)))
  | .op .shl [a, b] => do `(($(← go a) <<< ($(← go b)).toNat))
  | .op .shr [a, b] => do `(($(← go a) >>> ($(← go b)).toNat))
  | .op .lt_u [a, b] => do
    let a ← go a; let b ← go b
    `((if $a < $b then 1#1 else 0#1))
  | .op .le_u [a, b] => do
    let a ← go a; let b ← go b
    `((if $a ≤ $b then 1#1 else 0#1))
  | .op .lt_s [a, b] => do
    let a ← go a; let b ← go b
    `((if ($a).toInt < ($b).toInt then 1#1 else 0#1))
  | .op .le_s [a, b] => do
    let a ← go a; let b ← go b
    `((if ($a).toInt ≤ ($b).toInt then 1#1 else 0#1))
  | .op .gt_s [a, b] => do
    let a ← go a; let b ← go b
    `((if ($b).toInt < ($a).toInt then 1#1 else 0#1))
  | .op .ge_s [a, b] => do
    let a ← go a; let b ← go b
    `((if ($b).toInt ≤ ($a).toInt then 1#1 else 0#1))
  | .slice e hi lo => do
    `((($(← go e)).extractLsb' $(quote lo) $(quote (hi - lo + 1))))
  | .op .not [a] => do `((~~~$(← go a)))
  | .op .neg [a] => do `((-$(← go a)))
  | .op .gt_u [a, b] => do
    let a ← go a; let b ← go b
    `((if $b < $a then 1#1 else 0#1))
  | .op .ge_u [a, b] => do
    let a ← go a; let b ← go b
    `((if $b ≤ $a then 1#1 else 0#1))
  | .concat [a] => go a
  | .concat (a :: rest) => do `(($(← go a) ++ $(← go (.concat rest))))
  | .op o args => throwError
      "#verify_elab_deep: operator {o.toString}/{args.length} outside the deep grammar"
  | e => throwError "#verify_elab_deep: {repr e} outside the deep grammar"
where go := toShallow slot nR rdOf inOf

/-- One `runCircuitH` node of the definition (the top-level `circuit do`
    or a NESTED one reached through a helper / an inline sub-circuit):
    its register slots as the Signal side sees them.  `widths`/`inits`
    are the IR-side signature used to locate the node's register block
    among the flattened module's registers. -/
structure LoopNode where
  isBool : Array Bool
  widths : Array Nat
  inits  : Array Nat
  /-- element types, as syntax (`BitVec 8`, `Bool`) -/
  tys    : Array Term
  isTop  : Bool
  deriving Inhabited

end Tools.DeepElab

namespace Tools.DeepElab

open Lean Elab Command
open Tools.VerifyElab (theRegisters dataInputs resolveSlicesW)
open Tools.SVParser.VerifyEmit (inlineCone widthTable)
open Sparkle.IR.Optimize (buildDefMap)

set_option maxHeartbeats 1000000 in
/-- `#verify_elab_deep f` — reify `f`'s elaborated circuit into a deep
    `Cdo` value and certify it through the GENERAL theorem
    `Cdo.elab_general`.  The only per-circuit proof left is the
    Signal-side bridge (the validated recipe); everything about the IR
    is the one general theorem.  v0 scope: BitVec inputs. -/
elab "#verify_elab_deep" id:ident : command =>
  -- the sorryAx audit inspects each generated theorem right after its
  -- elabCommand; under async proof elaboration the tactic errors (and
  -- the recovery sorry) land only later, and a failed bridge would be
  -- reported PROVEN — so everything here elaborates synchronously
  withScope (fun sc => { sc with opts := Lean.Elab.async.set sc.opts false }) do
  let declName ← liftTermElabM <|
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  let design ← liftTermElabM
    (Sparkle.Compiler.Elab.synthesizeHierarchical declName)
  let m ← match design.modules with
    | [m] => pure m
    | _ => throwError "#verify_elab_deep: single-module designs only"
  let regs := theRegisters m
  let nR := regs.length
  if nR == 0 then throwError "#verify_elab_deep: no registers"
  let ins := dataInputs m
  let nI := ins.length
  let wt := widthTable m
  let regWs := regs.map fun (n, _, _) => wt.getD n 0
  let inWs := ins.map fun (_, w) => w
  let stopAt : Std.HashMap String Bool :=
    (ins.foldl (fun (h : Std.HashMap String Bool) (n, _) =>
      h.insert n true) {})
    |> regs.foldl (fun h (n, _, _) => h.insert n true)
  let dm := buildDefMap m.body
  let slotIdx : String → Option Nat := fun s =>
    match (regs.map (·.1)).idxOf? s with
    | some i => some i
    | none => (ins.map (·.1)).idxOf? s |>.map (· + nR)
  let conesIR ← regs.mapM fun (n, input, _) => do
    match Tools.ConeFold.inlineConeT dm stopAt 10000 input with
    | .ok c => pure (Tools.ConeFold.resolveSlicesT wt 10000 c)
    | .error e => throwError "#verify_elab_deep: cone of {n}: {e}"
  let cones ← conesIR.mapM (toCExpr slotIdx)
  -- ALL output ports.  A struct-returning `circuit do` flattens its
  -- fields into one port per field, named after the field; each port
  -- gets its own Cdo (sharing the register cones) and its own theorem.
  if m.outputs.isEmpty then
    throwError "#verify_elab_deep: no outputs"
  let outPorts : List (String × Nat) := m.outputs.map fun p =>
    (p.name, wt.getD p.name p.ty.bitWidth)
  let outIRs ← outPorts.mapM fun (n, _) => do
    match Tools.ConeFold.inlineConeT dm stopAt 10000 (.ref n) with
    | .ok c => pure (Tools.ConeFold.resolveSlicesT wt 10000 c)
    | .error e => throwError "#verify_elab_deep: output cone {n}: {e}"
  let outCs ← outIRs.mapM (toCExpr slotIdx)
  -- names / syntax scaffolding
  let base := declName.componentsRev.headD (Name.mkSimple "x") |>.toString
  let mkI (s : String) : Ident := mkIdent (Name.mkSimple s)
  let nmId := mkI s!"{base}_nm"
  let regWsT : Array Term := regWs.toArray.map fun w => quote w
  let inWsT : Array Term := inWs.toArray.map fun w => quote w
  let ΓrT : Term ← `([$regWsT,*])
  let ΓiT : Term ← `([$inWsT,*])
  -- param binders from the DSL signature
  let paramOf (n : String) : String :=
    match n.dropPrefix? "_gen_" with
    | some sub => sub.toString | none => n
  let paramIds : Array Ident :=
    (ins.map fun (n, _) => mkI (paramOf n)).toArray
  -- Parameter types from the DSL signature.  A generic
  -- `{dom : DomainConfig}` binder is instantiated at `defaultDomain`
  -- BEFORE delaboration — the remaining types would otherwise mention
  -- a free `dom` and the generated statement could not elaborate.
  let (paramTys, paramIsBool, retTy) ← liftTermElabM do
    let info ← getConstInfo declName
    let rec walk (ty : Lean.Expr) (tys : Array Term)
        (bools : Array Bool) (fuel : Nat := 64) :
        Lean.Elab.TermElabM (Array Term × Array Bool × Lean.Expr) := do
      match fuel with
      | 0 => pure (tys, bools, ty)
      | fuel + 1 =>
      match ty with
      | .forallE _ dty body _ =>
        if dty.isConstOf ``Sparkle.Core.Domain.DomainConfig then
          walk (body.instantiate1
            (Lean.mkConst ``Sparkle.Core.Domain.defaultDomain))
            tys bools fuel
        else
          let stx ← Lean.PrettyPrinter.delab dty
          let isB := (← Lean.Meta.whnf dty).getAppArgs.any
            fun a => a.isConstOf ``Bool
          Lean.Meta.withLocalDeclD `p dty fun x =>
            walk (body.instantiate1 x) (tys.push stx) (bools.push isB)
              fuel
      | _ => pure (tys, bools, ty)
    walk info.type #[] #[]
  -- Output shape: a `Signal dom τ` return is single-port (τ decides
  -- the Bool encoding); anything else must be a structure whose
  -- fields ARE the ports (matched by name), each field a Signal.
  let retHead := retTy.getAppFn
  let structName? : Option Name ←
    if retHead.isConstOf ``Sparkle.Core.Signal.Signal then pure none
    else match retHead with
      | .const n _ => pure (some n)
      | _ => throwError
          "#verify_elab_deep: unsupported return type {retTy}"
  -- per-port: (projection ident?, Bool-encoded?)
  let portMeta : List (Option Ident × Bool) ←
    match structName? with
    | none => do
      if outPorts.length != 1 then
        throwError "#verify_elab_deep: Signal return but {outPorts.length} ports"
      let isB := Option.isSome <| retTy.find? (·.isConstOf ``Bool)
      pure [(none, isB)]
    | some sn => do
      let env ← getEnv
      outPorts.mapM fun (pn, _) => do
        let projN := sn ++ Name.mkSimple pn
        let some ci := env.find? projN
          | throwError "#verify_elab_deep: output port {pn} has no field {projN} in {sn}"
        let isB := Option.isSome <| ci.type.find? (·.isConstOf ``Bool)
        pure (some ⟨Lean.mkCIdentFrom Lean.Syntax.missing projN
          (canonical := true)⟩, isB)
  let paramBinders ← (paramIds.zip paramTys).mapM fun (pid, ty) => do
    `(Lean.Parser.Term.bracketedBinderF| ($pid : $ty))
  let appArgs : Array Term := paramIds.map fun p => ⟨p.raw⟩
  -- shared arms: register inits and next-state cones
  let initArms ← (List.range nR).toArray.mapM fun i => do
    let (_, _, init) := regs[i]!
    `(Lean.Parser.Term.matchAltExpr|
      | ⟨$(quote i), _⟩ => BitVec.ofNat _ $(quote init.toNat))
  let nextArms ← (List.range nR).toArray.mapM fun i => do
    `(Lean.Parser.Term.matchAltExpr|
      | ⟨$(quote i), _⟩ => $(cones[i]!))
  -- slot names
  let nmArms ← (List.range (nR + nI)).toArray.mapM fun i => do
    let s := if h : i < nR then (regs[i]!).1 else (ins[i - nR]!).1
    `(Lean.Parser.Term.matchAltExpr| | ⟨$(quote i), _⟩ => $(quote s))
  elabCommand (← `(def $nmId :
      Fin (($ΓrT ++ $ΓiT : List Nat).length) → String := fun i =>
    match i with $nmArms:matchAlt*))
  -- the input family from the params
  let inpRhs : Array Term ← (List.range nI).toArray.mapM fun j => do
    let pj : Ident := paramIds.getD j (mkI "unreachable")
    if paramIsBool.getD j false then
      -- a Bool signal enters the deep circuit as its 1-bit encoding
      `((Sparkle.Core.Signal.Signal.map
          (fun b => bif b then (1 : BitVec 1) else 0) $pj))
    else
      `(($pj))
  let inpSArms ← (List.range nI).toArray.mapM fun j => do
    `(Lean.Parser.Term.matchAltExpr|
      | ⟨$(quote j), _⟩ => $(inpRhs[j]!))
  -- The input family is a NAMED def: a `fun j => match j with …`
  -- term spliced into several places elaborates a fresh auxiliary
  -- matcher constant at each site, so the same state read appears in
  -- syntactically different forms and abstracts into different
  -- variables (kabstract's keyed matching cannot cross matcher
  -- constants).  One def = one matcher = one form everywhere.
  let inpId := mkI s!"{base}_inp"
  if nI == 0 then
    elabCommand (← `(def $inpId :
        ∀ j : Fin ($ΓiT : List Nat).length,
          Sparkle.Core.Signal.Signal
            Sparkle.Core.Domain.defaultDomain
            (BitVec (($ΓiT : List Nat).get j)) :=
      fun j => nomatch j))
  else
    elabCommand (← `(def $inpId $paramBinders* :
        ∀ j : Fin ($ΓiT : List Nat).length,
          Sparkle.Core.Signal.Signal
            Sparkle.Core.Domain.defaultDomain
            (BitVec (($ΓiT : List Nat).get j)) :=
      fun j => match j with $inpSArms:matchAlt*))
  let inpS : Term ← if nI == 0 then `(($inpId))
    else `(($inpId $appArgs*))
  -- rfl application lemmas: `inp args j = <arm>` for each literal j.
  -- The def's match does not iota-reduce on an OfNat-form scrutinee
  -- and simp cannot rewrite inside a match scrutinee, so residual
  -- `(inp args j).val t` conditions in the bridge are rewritten by
  -- these instead of unfolding the def
  -- the lemmas are stated at the `.val t` level, all the way to the
  -- encoded VALUE (`bif (p.val t) then 1#1 else 0#1` for Bool inputs,
  -- `p.val t` otherwise): a term-level `inp k = Signal.map …` RHS
  -- stops at the map and the split hypotheses' contradictions
  -- (`p.val n = true` vs `¬(inp k).val n = 1`) never connect
  let inpValRhs : Array (Lean.TSyntax `term → Lean.Elab.Command.CommandElabM Term) :=
    (List.range nI).toArray.map fun j tv => do
      let pj : Ident := paramIds.getD j (mkI "unreachable")
      if paramIsBool.getD j false then
        `((bif ($pj).val $tv then (1 : BitVec 1) else 0))
      else
        `((($pj).val $tv))
  let inpAtIds : Array Ident ← (List.range nI).toArray.flatMapM fun j => do
    let rhs ← inpValRhs[j]! (← `(tv))
    let atId := mkI s!"{base}_inp_at_{j}"
    elabCommand (← `(theorem $atId $paramBinders* (tv : Nat) :
      ($inpId $appArgs* $(quote j)).val tv = $rhs := rfl))
    -- the applied index appears in BOTH OfNat-literal and Fin.mk
    -- forms depending on which normalization reached it; cover both
    let atMkId := mkI s!"{base}_inp_at_mk_{j}"
    elabCommand (← `(theorem $atMkId $paramBinders* (tv : Nat) :
      ($inpId $appArgs* ⟨$(quote j), by decide⟩).val tv = $rhs := rfl))
    pure #[atId, atMkId]
  -- Helper Signal functions called from the body (e.g. a private
  -- `crc32StepSig`) inline on the IR side but stay FOLDED on the
  -- Signal side unless the bridge unfolds them.  Collect the def's
  -- transitive Signal/Circuit-typed dependencies outside the core
  -- namespaces and splice them (preresolved, so private mangled
  -- names hit the environment directly) into the top-level unfold.
  let helperIds : Array Ident ← liftTermElabM do
    let env ← getEnv
    let isCore (n : Name) : Bool :=
      -- keep the Sparkle core/compiler namespaces and the stdlib out;
      -- user circuits stay (IP.*, Tests.*, and anything else a design
      -- defines — a helper circuit under `Sparkle.Tests` is a helper)
      let base := (privateToUserName? n).getD n
      let r := base.getRoot
      r == `Init || r == `Lean || r == `Std
        || r == `Nat || r == `BitVec || r == `List || r == `Tools
        || (`Sparkle.Core).isPrefixOf base
        || (`Sparkle.IR).isPrefixOf base
        || (`Sparkle.Compiler).isPrefixOf base
        || (`Sparkle.Backend).isPrefixOf base
    let mentionsSignal (e : Lean.Expr) : Bool :=
      Option.isSome <| e.find? fun x =>
        match x with
        | .const n _ =>
          n == ``Sparkle.Core.Signal.Signal
          || n.eraseMacroScopes.components.contains `Circuit
        | _ => false
    let rec go (fuel : Nat) (work : List Name) (seen : List Name)
        (acc : Array Name) : Array Name :=
      match fuel, work with
      | 0, _ | _, [] => acc
      | fuel + 1, c :: rest =>
        if seen.contains c then go fuel rest seen acc else
        let seen := c :: seen
        -- hygiene suffixes (`._@._internal…`) name compiler-internal
        -- twins; the simp-facing constant is the scope-erased one
        let c := c.eraseMacroScopes
        if (Lean.Meta.Match.Extension.getMatcherInfo? env c).isSome
        then go fuel rest seen acc else
        match env.find? c with
        | some (.defnInfo v) =>
          -- closed BitVec constants (`private abbrev poly : BitVec 32
          -- := …`) ride along: the shallow side carries the literal,
          -- and bv_decide treats an un-unfolded constant as an atom
          let isBvConst := v.type.isAppOf ``BitVec
          if !isCore c && (mentionsSignal v.type || isBvConst) then
            let deps := v.value.getUsedConstants.toList
            go fuel (deps ++ rest) seen (acc.push c)
          else go fuel rest seen acc
        | _ => go fuel rest seen acc
    let root ← getConstInfo declName
    let deps := (root.value?.getD root.type).getUsedConstants.toList
    let names := go 512 deps [declName] #[]
    pure <| names.map fun n =>
      -- preresolved constant ident: resolves even for private names
      ⟨Lean.mkCIdentFrom Lean.Syntax.missing n (canonical := true)⟩
  if (← IO.getEnv "SPARKLE_DEEP_DEBUG").isSome then
    logInfo m!"#verify_elab_deep helpers: {helperIds.map (·.getId)}"
  -- ===== loop nodes: the top `runCircuitH` and every NESTED one =====
  -- The IR flattens nested `circuit do`s into one register list, but the
  -- Signal side keeps one `Signal.loop` per `runCircuitH` node — and
  -- `runCircuitH` evaluates its body TWICE (next-state and output), so a
  -- nested circuit's registers appear twice in the IR (the copies are
  -- identical recurrences).  Each node's slot signature (width, init,
  -- Bool-ness) locates its candidate register blocks in the IR; the
  -- Signal-side proof tries the candidates.
  let (loopNodes, headChain) ← liftTermElabM do
    let env ← getEnv
    -- open a definition's leading lambdas; a `DomainConfig` binder is
    -- instantiated at `defaultDomain` (the statement's domain), the rest
    -- become fvars
    let rec openLams (e : Lean.Expr) (fuel : Nat)
        (k : Lean.Expr → Lean.MetaM (Array (Lean.Expr × Bool))) :
        Lean.MetaM (Array (Lean.Expr × Bool)) := do
      match fuel, e with
      | fuel + 1, .lam n ty b bi =>
        if ty.isConstOf ``Sparkle.Core.Domain.DomainConfig then
          openLams (b.instantiate1
            (Lean.mkConst ``Sparkle.Core.Domain.defaultDomain)) fuel k
        else
          Lean.Meta.withLocalDecl n bi ty fun x => openLams (b.instantiate1 x) fuel k
      | _, _ => k e
    let rec openLams' (e : Lean.Expr) (fuel : Nat)
        (k : Lean.Expr → Lean.MetaM (Array (Lean.Expr × Bool) × Array Name)) :
        Lean.MetaM (Array (Lean.Expr × Bool) × Array Name) := do
      match fuel, e with
      | fuel + 1, .lam n ty b bi =>
        if ty.isConstOf ``Sparkle.Core.Domain.DomainConfig then
          openLams' (b.instantiate1
            (Lean.mkConst ``Sparkle.Core.Domain.defaultDomain)) fuel k
        else
          Lean.Meta.withLocalDecl n bi ty fun x => openLams' (b.instantiate1 x) fuel k
      | _, _ => k e
    -- the head application of a body (through lets and outer apps)
    let rec findRC (e : Lean.Expr) (fuel : Nat) : Option Lean.Expr :=
      match fuel with
      | 0 => none
      | fuel + 1 =>
        let e := e.headBeta
        match e with
        | .letE _ _ v body _ => findRC (body.instantiate1 v) fuel
        | _ =>
          if e.getAppFn.isConstOf ``Sparkle.Core.runCircuitH then some e
          else match e with
            | .app f _ => findRC f fuel
            | _ => none
    -- every saturated runCircuitH application in a term (DAG-aware)
    let collect (root : Lean.Expr) : Array Lean.Expr := Id.run do
      let mut seen : Std.HashSet Lean.Expr := {}
      let mut acc : Array Lean.Expr := #[]
      let mut work : List Lean.Expr := [root]
      let mut fuel := 200000
      while fuel > 0 do
        fuel := fuel - 1
        match work with
        | [] => break
        | e :: rest =>
          work := rest
          if seen.contains e then continue
          seen := seen.insert e
          if e.isAppOf ``Sparkle.Core.runCircuitH && e.getAppNumArgs ≥ 8 then
            acc := acc.push e
          match e with
          | .app f a => work := f :: a :: work
          | .lam _ t b _ | .forallE _ t b _ => work := t :: b :: work
          | .letE _ t v b _ => work := t :: v :: b :: work
          | .mdata _ b | .proj _ _ b => work := b :: work
          | _ => pure ()
      return acc
    let elemTys (αs : Lean.Expr) : Lean.MetaM (Array Lean.Expr) := do
      let mut e ← Lean.Meta.whnf αs
      let mut acc := #[]
      for _ in [0:64] do
        match e.getAppFnArgs with
        | (``List.cons, #[_, hd, tl]) =>
          acc := acc.push hd
          e ← Lean.Meta.whnf tl
        | _ => break
      return acc
    let initVals (h : Lean.Expr) (k : Nat) : Lean.MetaM (Option (Array Nat)) := do
      let mut e ← Lean.Meta.whnf h
      let mut acc : Array Nat := #[]
      for _ in [0:k] do
        match e.getAppFnArgs with
        | (``Prod.mk, #[_, _, a, rest]) =>
          -- reducible whnf only: default transparency would unfold
          -- `BitVec.ofNat` itself into its `ofFin` body
          let a ← Lean.Meta.whnfR a
          let v? ← match a.getAppFnArgs with
            | (``BitVec.ofNat, #[_, v]) => Lean.Meta.evalNat v
            | (``Bool.true, _) => pure (some 1)
            | (``Bool.false, _) => pure (some 0)
            | _ => pure none
          match v? with
          | some v => acc := acc.push v
          | none => return none
          e ← Lean.Meta.whnf rest
        | _ => return none
      return some acc
    let nodeOf (rc : Lean.Expr) (isTop : Bool) : Lean.MetaM (Option LoopNode) := do
      let args := rc.getAppArgs
      let αs := args[1]!
      let inits := args[6]!
      if αs.hasLooseBVars || inits.hasLooseBVars then return none
      let tysE ← elemTys αs
      let mut isBool := #[]
      let mut widths := #[]
      let mut tys := #[]
      for ty in tysE do
        if ty.isConstOf ``Bool then
          isBool := isBool.push true; widths := widths.push 1
        else
          let ty' ← Lean.Meta.whnf ty
          match ty'.getAppFnArgs with
          | (``BitVec, #[w]) =>
            match ← Lean.Meta.evalNat w with
            | some n => isBool := isBool.push false; widths := widths.push n
            | none => return none
          | _ => return none
        tys := tys.push (← Lean.PrettyPrinter.delab ty)
      let some inits ← initVals inits tysE.size | return none
      return some { isBool, widths, inits, tys, isTop }
    let mut nodes : Array LoopNode := #[]
    -- the definition itself: head node = top, the rest nested.  A
    -- SPECIALIZED WRAPPER (`def accK15 d := accK 0x0F#8 d`, the pattern
    -- for circuits with non-Signal value parameters) has no runCircuitH
    -- at its head: follow the head application by delta-unfolding
    -- (arguments substituted, so the inner circuit's `inits` are
    -- closed) and remember the unfolded constants for the proof
    let rec headChain (e : Lean.Expr) (acc : Array Name) (fuel : Nat) :
        Lean.MetaM (Option Lean.Expr × Array Name) := do
      match fuel with
      | 0 => pure (none, acc)
      | fuel + 1 =>
        match findRC e 64 with
        | some rc => pure (some rc, acc)
        | none =>
          let e := e.headBeta
          match e.getAppFn with
          | .const c _ =>
            let base := (privateToUserName? c).getD c
            if (`Sparkle.Core).isPrefixOf base || (`Sparkle.IR).isPrefixOf base then
              pure (none, acc)
            else match ← Lean.Meta.unfoldDefinition? e with
              | some e' => headChain e' (acc.push c) fuel
              | none => pure (none, acc)
          | _ => pure (none, acc)
    let root ← getConstInfo declName
    let mut chain : Array Name := #[]
    if let some val := root.value? then
      let (apps, ch) ← openLams' val 64 fun body => do
        let (top?, ch) ← headChain body #[] 16
        let all := collect body
        let nested := all.map fun a => (a, false)
        pure ((match top? with | some t => #[(t, true)] | none => #[]) ++ nested, ch)
      chain := ch
      for (a, isTop) in apps do
        if let some n ← nodeOf a isTop then nodes := nodes.push n
    -- the helpers: every runCircuitH inside is nested
    for hid in helperIds do
      match env.find? hid.getId.eraseMacroScopes with
      | some (.defnInfo v) =>
        let apps ← openLams v.value 64 fun body =>
          pure <| (collect body).map (·, false)
        for (a, _) in apps do
          if let some n ← nodeOf a false then nodes := nodes.push n
      | _ => pure ()
    -- dedupe by signature (a helper instantiated twice is one node)
    let mut out : Array LoopNode := #[]
    for n in nodes do
      if out.any (fun m => m.isTop == n.isTop && m.isBool == n.isBool
          && m.widths == n.widths && m.inits == n.inits) then continue
      out := out.push n
    pure (out, chain)
  if (← IO.getEnv "SPARKLE_DEEP_DEBUG").isSome then
    for n in loopNodes do
      logInfo m!"#verify_elab_deep loop node (top={n.isTop}): widths {n.widths} inits {n.inits} bool {n.isBool}"
  let some topNode := loopNodes.find? (·.isTop)
    | throwError "#verify_elab_deep: could not locate the top-level runCircuitH (register types / initial values must be closed literals)"
  -- the top node is also collected as an ordinary application of the
  -- body; a nested node with the top's own signature is that echo
  let nestedNodes := loopNodes.filter fun n => !n.isTop &&
    !(n.isBool == topNode.isBool && n.widths == topNode.widths && n.inits == topNode.inits)
  if (← IO.getEnv "SPARKLE_DEEP_DEBUG").isSome && !headChain.isEmpty then
    logInfo m!"#verify_elab_deep head chain: {headChain}"
  -- candidate register blocks of a node: contiguous IR registers whose
  -- (width, init) signature matches slot for slot
  let blocksFor (n : LoopNode) : List Nat :=
    let k := n.widths.size
    (List.range (nR + 1 - k)).filter fun s =>
      (List.range k).all fun j =>
        regWs[s + j]! == n.widths[j]! &&
        (regs[s + j]!).2.2.toNat == n.inits[j]!
  let topBlocks := blocksFor topNode
  if topBlocks.isEmpty then
    throwError "#verify_elab_deep: no IR register block matches the top-level circuit's registers {topNode.widths} / {topNode.inits}"
  -- fidelity quoting (see the FIDELITY comment below)
  let quoteIR (e : Sparkle.IR.AST.Expr) : CommandElabM Term := do
    match Lean.Parser.runParserCategory (← getEnv) `term
        (toString (repr e)) with
    | .ok stx => pure ⟨stx⟩
    | .error err => throwError "#verify_elab_deep: fidelity quote: {err}"
  -- ================= per-output-port generation =================
  let jobs := ((outPorts.zip portMeta).zip (outCs.zip outIRs))
  let mut portIdx := 0
  let mut deep0Id : Ident := mkI s!"{base}_deep"
  for (((portName, wOut), proj?, isBoolOut), outC, outIR) in jobs do
    let k := portIdx
    portIdx := portIdx + 1
    let suffix := if structName?.isSome then s!"_{portName}" else ""
    let deepId := mkI s!"{base}{suffix}_deep"
    if k == 0 then deep0Id := deepId
    let thId := mkI s!"{base}{suffix}_deep_trace"
    let nextEqId := mkI s!"{base}{suffix}_deep_next"
    let initsEqId := mkI s!"{base}{suffix}_deep_inits"
    let outEqId := mkI s!"{base}{suffix}_deep_out"
    elabCommand (← `(def $deepId : Cdo $ΓrT $ΓiT $(quote wOut) where
      inits := fun i => match i with $initArms:matchAlt*
      next := fun i => match i with $nextArms:matchAlt*
      out := $outC))
    -- projection equations (rfl): rewrite `f_deep.next` etc. WITHOUT
    -- ever exposing the anonymous structure literal — a literal that
    -- appears in some hypotheses but not others (the pack references
    -- the NAME) leaves simp_all unable to see two forms of one fact
    elabCommand (← `(theorem $nextEqId :
      Cdo.next $deepId = fun i => match i with $nextArms:matchAlt* := rfl))
    elabCommand (← `(theorem $initsEqId :
      Cdo.inits $deepId = fun i => match i with $initArms:matchAlt* := rfl))
    elabCommand (← `(theorem $outEqId : Cdo.out $deepId = $outC := rfl))
    -- FIDELITY: the compiled reification IS the elaborated cone.
    -- Without this the capstone talks about `compile (toCExpr cone)`,
    -- an intended-identical but unverified twin of the elaborator's
    -- actual IR.  toCExpr's normalizations (n-ary concat → nested
    -- cats, gt/ge → mirrored lt/le) make it fail LOUDLY where compile
    -- can't reproduce the original.  Register cones are checked once
    -- (they're shared syntax across the per-port Cdos).
    let fidIds ← if k == 0 then
        (List.range nR).toArray.mapM fun i => do
          let fidId := mkI s!"{base}{suffix}_deep_fidelity_r{i}"
          let coneQ ← quoteIR (Tools.ConcatNorm.concatNorm 10000 conesIR[i]!)
          elabCommand (← `(theorem $fidId :
            CExpr.compile $nmId (Cdo.next $deepId ⟨$(quote i), by decide⟩)
              = $coneQ := by
            simp only [$nextEqId:ident, CExpr.compile, $nmId:ident]
            -- residual `Expr.const v (Γr.get ⟨i, _⟩) = Expr.const v w`
            -- width shapes: closed, so `rfl`; simp alone strands
            -- `Fin.val` of literals ≥ 3 (no `Fin.val_three`)
            all_goals (first | rfl | (simp; done) | (simp; rfl))))
          pure fidId
      else pure #[]
    let fidOutId := mkI s!"{base}{suffix}_deep_fidelity_out"
    let outQ ← quoteIR (Tools.ConcatNorm.concatNorm 10000 outIR)
    elabCommand (← `(theorem $fidOutId :
      CExpr.compile $nmId (Cdo.out $deepId) = $outQ := by
      simp only [$outEqId:ident, CExpr.compile, $nmId:ident]
      all_goals (first | rfl | (simp; done) | (simp; rfl))))
    -- ===== deep-side seam glue (G1) =====
    -- The capstone / Cdo.irState evaluate cones as
    -- `evalExpr (weOfC …) env (CExpr.compile nm (next/out))`; these
    -- lemmas rewrite each such term to plain `evalExpr weM env cone`
    -- over the RESOLVED cone constant and the FULL width-table env —
    -- fidelity ∘ concatNorm_eval (singleton-freedom by native_decide)
    -- ∘ evalExpr_we_congr (the cone's refs are stop-set names, where
    -- the register+input-keyed weOfC agrees with weM).  This lands the
    -- deep conclusions on exactly the expressions and width env the
    -- ConeFold bridge theorems consume.
    let weMId := mkI s!"{base}_deep_weM"
    let bodyId := mkI s!"{base}_deep_body"
    let stopLId := mkI s!"{base}_deep_stopL"
    let stopAtMId := mkI s!"{base}_deep_stopAtM"
    let wtLId := mkI s!"{base}_deep_wtL"
    let wtMId := mkI s!"{base}_deep_wtM"
    if k == 0 then
      let weBody ← do
        let mut acc ← `((0 : Nat))
        for (n, w) in wt.toList do
          acc ← `(if n == $(quote n) then $(quote w) else $acc)
        pure acc
      elabCommand (← `(def $weMId : Sparkle.IR.Semantics.WEnv :=
        fun n => $weBody))
      liftCoreM <| addAndCompile <| .defnDecl {
        name := bodyId.getId, levelParams := []
        type := mkApp (mkConst ``List [levelZero])
          (mkConst ``Sparkle.IR.AST.Stmt)
        value := toExpr (Tools.SVParser.Lower.topoSortBody m.body),
        hints := .abbrev, safety := .safe }
      liftCoreM <| Lean.enableRealizationsForConst bodyId.getId
      let stopL : List String := (ins.map (·.1)) ++ (regs.map (·.1))
      liftCoreM <| addAndCompile <| .defnDecl {
        name := stopLId.getId, levelParams := []
        type := mkApp (mkConst ``List [levelZero]) (mkConst ``String)
        value := toExpr stopL, hints := .abbrev, safety := .safe }
      liftCoreM <| Lean.enableRealizationsForConst stopLId.getId
      elabCommand (← `(def $stopAtMId : Std.HashMap String Bool :=
        ($stopLId).foldl (fun h n => h.insert n true) {}))
      liftCoreM <| addAndCompile <| .defnDecl {
        name := wtLId.getId, levelParams := []
        type := mkApp (mkConst ``List [levelZero])
          (mkApp2 (mkConst ``Prod [levelZero, levelZero])
            (mkConst ``String) (mkConst ``Nat))
        value := toExpr wt.toList, hints := .abbrev, safety := .safe }
      liftCoreM <| Lean.enableRealizationsForConst wtLId.getId
      elabCommand (← `(def $wtMId : Std.HashMap String Nat :=
        ($wtLId).foldl (fun m p => m.insert p.1 p.2) {}))
      for i in List.range nR do
        let (rn, input, _) := regs[i]!
        let sanit := Sparkle.Backend.Verilog.sanitizeName rn
        let coneRawId := mkI s!"{base}_deep_coneRaw_{sanit}"
        let coneId := mkI s!"{base}_deep_cone_{sanit}"
        let regInId := mkI s!"{base}_deep_regIn_{sanit}"
        let craw ← match Tools.ConeFold.inlineConeT dm stopAt 10000 input with
          | .ok c => pure c
          | .error e => throwError "#verify_elab_deep bridge: cone of {rn}: {e}"
        liftCoreM <| addAndCompile <| .defnDecl {
          name := coneRawId.getId, levelParams := []
          type := mkConst ``Sparkle.IR.AST.Expr
          value := toExpr craw, hints := .abbrev, safety := .safe }
        liftCoreM <| Lean.enableRealizationsForConst coneRawId.getId
        liftCoreM <| addAndCompile <| .defnDecl {
          name := coneId.getId, levelParams := []
          type := mkConst ``Sparkle.IR.AST.Expr
          value := toExpr conesIR[i]!, hints := .abbrev, safety := .safe }
        liftCoreM <| Lean.enableRealizationsForConst coneId.getId
        liftCoreM <| addAndCompile <| .defnDecl {
          name := regInId.getId, levelParams := []
          type := mkConst ``Sparkle.IR.AST.Expr
          value := toExpr input, hints := .abbrev, safety := .safe }
        liftCoreM <| Lean.enableRealizationsForConst regInId.getId
        let fidId := fidIds[i]!
        let g1Id := mkI s!"{base}_deep_coneEval_r{i}"
        elabCommand (← `(theorem $g1Id (env : Sparkle.IR.Semantics.Env) :
            Sparkle.IR.Semantics.evalExpr
                (weOfC $nmId (fun j => (($ΓrT ++ $ΓiT : List Nat)).get j))
                env (CExpr.compile $nmId
                  (Cdo.next $deepId ⟨$(quote i), by decide⟩))
              = Sparkle.IR.Semantics.evalExpr $weMId env $coneId := by
          have hnorm : CExpr.compile $nmId
              (Cdo.next $deepId ⟨$(quote i), by decide⟩)
              = Tools.ConcatNorm.concatNorm 10000 $coneId := by
            rw [$fidId:ident]
            native_decide
          have hinl : Tools.ConeFold.inlineConeT
              (Sparkle.IR.Optimize.buildDefMap $bodyId) $stopAtMId 10000
              $regInId = .ok $coneRawId := by native_decide
          have hres : $coneId
              = Tools.ConeFold.resolveSlicesT $wtMId 10000 $coneRawId := by
            native_decide
          have hag : ∀ n ∈ $stopLId,
              (weOfC $nmId
                (fun j => (($ΓrT ++ $ΓiT : List Nat)).get j)) n
                = $weMId n := by native_decide
          rw [hnorm,
            Tools.ConeFold.concatNorm_eval _ env 10000 $coneId
              (by native_decide)]
          refine Tools.ConeFold.evalExpr_we_congr _ $weMId env $coneId ?_
          intro n hn
          have h1 : n ∈ Sparkle.IR.Reorder.refsOf
              (Tools.ConeFold.resolveSlicesT $wtMId 10000 $coneRawId) := by
            rw [← hres]; exact hn
          have href := Tools.ConeFold.inlineConeT_refs
            (Sparkle.IR.Optimize.buildDefMap $bodyId) $stopAtMId 10000
            $regInId $coneRawId hinl n
            (Tools.ConeFold.resolveSlicesT_refs $wtMId 10000 $coneRawId
              n h1)
          have hmem : n ∈ $stopLId := by
            rcases Tools.ConeFold.stopFold_mem $stopLId {} n href
              with h | h
            · exact h
            · simp at h
          exact hag n hmem))
    -- per-port: the output cone's G1
    let outConeRawId := mkI s!"{base}{suffix}_deep_coneRaw_out"
    let outConeId := mkI s!"{base}{suffix}_deep_cone_out"
    let outRawIR ← match Tools.ConeFold.inlineConeT dm stopAt 10000
        (.ref portName) with
      | .ok c => pure c
      | .error e => throwError "#verify_elab_deep bridge: out cone: {e}"
    liftCoreM <| addAndCompile <| .defnDecl {
      name := outConeRawId.getId, levelParams := []
      type := mkConst ``Sparkle.IR.AST.Expr
      value := toExpr outRawIR, hints := .abbrev, safety := .safe }
    liftCoreM <| Lean.enableRealizationsForConst outConeRawId.getId
    liftCoreM <| addAndCompile <| .defnDecl {
      name := outConeId.getId, levelParams := []
      type := mkConst ``Sparkle.IR.AST.Expr
      value := toExpr outIR, hints := .abbrev, safety := .safe }
    liftCoreM <| Lean.enableRealizationsForConst outConeId.getId
    let g1OutId := mkI s!"{base}{suffix}_deep_coneEval_out"
    elabCommand (← `(theorem $g1OutId (env : Sparkle.IR.Semantics.Env) :
        Sparkle.IR.Semantics.evalExpr
            (weOfC $nmId (fun j => (($ΓrT ++ $ΓiT : List Nat)).get j))
            env (CExpr.compile $nmId (Cdo.out $deepId))
          = Sparkle.IR.Semantics.evalExpr $weMId env $outConeId := by
      have hnorm : CExpr.compile $nmId (Cdo.out $deepId)
          = Tools.ConcatNorm.concatNorm 10000 $outConeId := by
        rw [$fidOutId:ident]
        native_decide
      have hinl : Tools.ConeFold.inlineConeT
          (Sparkle.IR.Optimize.buildDefMap $bodyId) $stopAtMId 10000
          (.ref $(quote portName)) = .ok $outConeRawId := by
        native_decide
      have hres : $outConeId
          = Tools.ConeFold.resolveSlicesT $wtMId 10000 $outConeRawId := by
        native_decide
      have hag : ∀ n ∈ $stopLId,
          (weOfC $nmId
            (fun j => (($ΓrT ++ $ΓiT : List Nat)).get j)) n
            = $weMId n := by native_decide
      rw [hnorm,
        Tools.ConeFold.concatNorm_eval _ env 10000 $outConeId
          (by native_decide)]
      refine Tools.ConeFold.evalExpr_we_congr _ $weMId env $outConeId ?_
      intro n hn
      have h1 : n ∈ Sparkle.IR.Reorder.refsOf
          (Tools.ConeFold.resolveSlicesT $wtMId 10000 $outConeRawId) := by
        rw [← hres]; exact hn
      have href := Tools.ConeFold.inlineConeT_refs
        (Sparkle.IR.Optimize.buildDefMap $bodyId) $stopAtMId 10000
        (.ref $(quote portName)) $outConeRawId hinl n
        (Tools.ConeFold.resolveSlicesT_refs $wtMId 10000 $outConeRawId
          n h1)
      have hmem : n ∈ $stopLId := by
        rcases Tools.ConeFold.stopFold_mem $stopLId {} n href with h | h
        · exact h
        · simp at h
      exact hag n hmem))
    -- ===== literal-width state readers (the shallow bridge) =====
    -- `Cdo.stateAt … ⟨i, _⟩ : BitVec (Γr.get ⟨i, _⟩)` — a width that is
    -- defeq to the literal but never syntactically it, and every
    -- Signal-side closer needs the literal: simp refuses the mixed
    -- goal ("not type-correct under instances transparency"),
    -- bv_decide / bv_omega reject the atom outright, and simp cannot
    -- normalise the width in dependent positions anyway (`Fin.val` of
    -- a literal ≥ 3 has no simp lemma at all — only
    -- `Fin.val_zero/one/two` exist, so 4+ registers were unreachable).
    -- So the bridge never sees `stateAt`: per register a reader
    -- `rd_i : params → Nat → BitVec w_i` (definitionally `stateAt`),
    -- its initial value, and its one-step unfolding as the shallow
    -- literal-width BitVec expression of the cone (`toShallow`), each
    -- proven by `rfl` — the deep semantics is structural and
    -- `CEnv.join`'s casts K-reduce on closed widths.  The output cone
    -- gets the same treatment against `Cdo.outSig`.  The trace
    -- theorem's pack, hypotheses and closers then live entirely in
    -- literal-width land.
    let sId := mkI "s"
    let nId := mkI "n"
    let rdIds : Array Ident := (List.range nR).toArray.map fun i =>
      mkI s!"{base}{suffix}_deep_rd{i}"
    let rdZeroIds : Array Ident := (List.range nR).toArray.map fun i =>
      mkI s!"{base}{suffix}_deep_rd{i}_zero"
    let rdSuccIds : Array Ident := (List.range nR).toArray.map fun i =>
      mkI s!"{base}{suffix}_deep_rd{i}_succ"
    let gIds : Array Ident := (List.range nR).toArray.map fun i =>
      mkI s!"g{i}"
    let shallowAt (tv : Term) (e : Sparkle.IR.AST.Expr) :
        CommandElabM Term :=
      toShallow slotIdx nR
        (fun i => do let rdId : Ident := rdIds[i]!; `(($rdId $appArgs* $tv)))
        (fun j => inpValRhs[j]! tv) e
    -- all readers first: a register's step lemma mentions every
    -- register its cone reads
    for i in List.range nR do
      let w := regWs[i]!
      let rdId : Ident := rdIds[i]!
      elabCommand (← `(def $rdId $paramBinders* ($sId : Nat) :
          BitVec $(quote w) :=
        Cdo.stateAt $deepId (fun t j => (($inpS) j).val t) $sId
          ⟨$(quote i), by decide⟩))
    for i in List.range nR do
      let (_, _, init) := regs[i]!
      let w := regWs[i]!
      let rdId : Ident := rdIds[i]!
      let rdZeroId : Ident := rdZeroIds[i]!
      let rdSuccId : Ident := rdSuccIds[i]!
      elabCommand (← `(theorem $rdZeroId $paramBinders* :
        $rdId $appArgs* 0
          = BitVec.ofNat $(quote w) $(quote init.toNat) := rfl))
      let rhs ← shallowAt (← `($sId)) conesIR[i]!
      elabCommand (← `(theorem $rdSuccId $paramBinders* ($sId : Nat) :
        $rdId $appArgs* ($sId + 1) = $rhs := rfl))
    let outSId := mkI s!"{base}{suffix}_deep_outS"
    let outRhs ← shallowAt (← `($sId)) outIR
    elabCommand (← `(theorem $outSId $paramBinders* ($sId : Nat) :
        (Cdo.outSig $deepId $inpS).val $sId = $outRhs := by
      show CExpr.denote _ _ = _
      rw [Cdo.stateSig_eq]
      rfl))
    -- ===== packs, duplicate copies, and the nested-loop machinery =====
    let uId := mkI "u"
    let mId := mkI "m"
    let preId := mkI "pre"
    let hpreId := mkI "hpre"
    let qId := mkI "q"
    let hqId := mkI "hq"
    let hgId := mkI "hg"
    let LId := mkI "L"
    let hLId := mkI "hL"
    let hLtId := mkI "hLt"
    let iId := mkI "i"
    let hiId := mkI "hi"
    let ihId := mkI "ih"
    -- the pack of a node's register block starting at IR register `b`,
    -- at time `tv`: the HList of its readers (a Bool register's slot is
    -- `Bool`, the reader yields `BitVec 1` — decode it)
    let packOf (node : LoopNode) (b : Nat) (tv : Term) : CommandElabM Term := do
      let k := node.widths.size
      let mut acc : Term ← `(())
      for j in (List.range k).reverse do
        let rdId : Ident := rdIds[b + j]!
        let slot ← `($rdId $appArgs* $tv)
        let slot ← if node.isBool[j]! then `(($slot == 1#1)) else pure slot
        acc ← `(($slot, $acc))
      pure acc
    -- Duplicate copies of a nested node's block (runCircuitH evaluates
    -- its body twice): identical recurrences — cones equal modulo the
    -- block's own register names — so every copy equals the canonical
    -- (first) one, cycle by cycle, by induction on the readers' step
    -- lemmas.  The Signal-side proof picks SOME copy for each inner
    -- loop; these equalities normalise the choice.
    let projOf (baseT : Term) (j : Nat) : CommandElabM Term := do
      let mut rest : Term := baseT
      for _ in [0:j] do rest ← `(($rest).2)
      `(($rest).1)
    let mut dupIds : Array Ident := #[]
    for node in nestedNodes do
      match blocksFor node with
      | [] => pure ()
      | b0 :: others =>
        let k := node.widths.size
        for b in others do
          let subst : Std.HashMap String String :=
            (List.range k).foldl (fun m j =>
              m.insert (regs[b + j]!).1 (regs[b0 + j]!).1) {}
          let same := (List.range k).all fun j =>
            Sparkle.IR.Optimize.renameRefs subst conesIR[b + j]! == conesIR[b0 + j]!
          if !same then continue
          let dupId := mkI s!"{base}{suffix}_deep_dup_b{b}"
          let stmt ← do
            let mut acc : Term ← `(True)
            for j in (List.range k).reverse do
              let r1 : Ident := rdIds[b + j]!
              let r0 : Ident := rdIds[b0 + j]!
              acc ← `(($r1 $appArgs* $nId = $r0 $appArgs* $nId) ∧ $acc)
            pure acc
          let ihT : Term ← `($ihId)
          let projs : Array Term ← (List.range k).toArray.mapM fun j =>
            projOf ihT j
          let zeroIdsB : Array Ident := (List.range k).toArray.map fun j => rdZeroIds[b + j]!
          let zeroIds0 : Array Ident := (List.range k).toArray.map fun j => rdZeroIds[b0 + j]!
          let succIdsB : Array Ident := (List.range k).toArray.map fun j => rdSuccIds[b + j]!
          let succIds0 : Array Ident := (List.range k).toArray.map fun j => rdSuccIds[b0 + j]!
          let zeroTs : Array Term := (zeroIdsB ++ zeroIds0).map fun i => ⟨i.raw⟩
          let succTs : Array Term := ((succIdsB ++ succIds0).map fun i => (⟨i.raw⟩ : Term)) ++ projs
          elabCommand (← `(theorem $dupId $paramBinders* : ∀ ($nId : Nat), $stmt := by
            intro $nId:ident
            induction $nId:ident with
            | zero =>
              simp only [$[$zeroTs:term],*]
              all_goals (repeat' apply And.intro)
              all_goals (first | rfl | trivial)
            | succ $nId $ihId =>
              simp only [$[$succTs:term],*]
              all_goals (repeat' apply And.intro)
              all_goals (first | rfl | trivial)))
          for j in List.range k do
            let dupRId := mkI s!"{base}{suffix}_deep_dup_r{b + j}"
            let r1 : Ident := rdIds[b + j]!
            let r0 : Ident := rdIds[b0 + j]!
            let pj ← projOf (← `($dupId $appArgs* $sId)) j
            elabCommand (← `(theorem $dupRId $paramBinders* ($sId : Nat) :
              $r1 $appArgs* $sId = $r0 $appArgs* $sId := $pj))
            dupIds := dupIds.push dupRId
    let dupSimp : Lean.TSyntax `tactic ← if dupIds.isEmpty then `(tactic| skip)
      else `(tactic| all_goals (try simp only [$[$dupIds:ident],*]))
    -- After the step lemmas the only state terms left are the readers
    -- at the previous cycle; abstract them to plain literal-width
    -- variables (the time index is left to unification) so the
    -- closers see atoms.  Done BEFORE any split, so the split
    -- hypotheses are about the variables too.
    let genLines : Array (Lean.TSyntax `tactic) ←
      (List.range nR).toArray.mapM fun i => do
        let rdId : Ident := rdIds[i]!
        let gId : Ident := gIds[i]!
        let rdApp ← `($rdId $appArgs* _)
        `(tactic| all_goals (try generalize $rdApp = $gId))
    -- `sigval_append`'s LHS type is `Signal dom (BitVec (m + n))`; a
    -- user ascription `(a ++ b : Signal dom (BitVec 10))` leaves the
    -- literal in the instance's type argument, which simp's
    -- discrimination tree indexes — so the lemma is never even
    -- retrieved.  `-index` matches on the head symbol and defeq.
    let appendFix : Lean.TSyntax `tactic ←
      `(tactic| all_goals (try simp -index only [sigval_append,
          sigval_append_c, sigval_c_append]))
    -- Every goal is now a literal-width BitVec/Bool identity over the
    -- reader variables and the input values; bv_decide is the closer,
    -- rfl/simp for the degenerate ones, bv_omega for Nat-cast shapes.
    let closers : Lean.TSyntax `tactic ←
      `(tactic| all_goals (first
        | rfl
        | bv_decide
        | (simp_all [BitVec.toNat_eq, BitVec.toNat_add,
            BitVec.toNat_ofNat, bif_beq_ofBool, bif_beq_ofBool_toNat,
            $[$inpAtIds:ident],*]; done)
        | bv_omega
        | (simp; done)
        | fail "#verify_elab_deep: closers exhausted on this goal"))
    -- stage 1: unfold a loop body down to `.val`-level Signal plumbing.
    -- The sigval_* family pushes each operator instance pointwise;
    -- unfolding the `H*` class projections instead would rewrite the
    -- BitVec level too and leave the goal's two sides in different head
    -- forms (`XorOp.xor` vs `^^^`), blinding both simp and bv_decide.
    let stage1 (extra : Array Term) : CommandElabM (Lean.TSyntax `tactic) := do
      let extraAll : Array Term := (inpAtIds.map fun i => (⟨i.raw⟩ : Term)) ++ extra
      `(tactic| simp [loopFOf, packRegister, Signal.register, Circuit.next,
        Circuit.pure', Circuit.bind, mkHolds, Signal.map,
        Signal.mux, bundle2, Signal.pure, Functor.map, Seq.seq,
        Signal.ap, Signal.seq, sigval_add, sigval_sub, sigval_mul, sigval_and, sigval_or, sigval_xor, sigval_shl, sigval_shr, sigval_append, sigval_add_c, sigval_sub_c, sigval_mul_c, sigval_and_c, sigval_or_c, sigval_xor_c, sigval_shl_c, sigval_shr_c, sigval_append_c, sigval_c_add, sigval_c_sub, sigval_c_mul, sigval_c_and, sigval_c_or, sigval_c_xor, sigval_c_shl, sigval_c_shr, sigval_c_append, sigval_and_b, sigval_or_b, sigval_xor_b, sigval_not, sigval_not_b, sigval_neg, sigval_mux, sigval_beq, sigval_pure,
        $[$extraAll:term],*])
    -- NESTED loops (`runCircuitH` inside the body, via helpers or
    -- inline): after stage 1 each appears as `(Signal.loop F).val n`
    -- (under a `Signal.map Prod.fst` output projection).  Its body may
    -- read the enclosing live signal, about which only the prefix
    -- `guard` is known, so `loop_trace_guarded_at` replaces it by the
    -- pack of one of its candidate register blocks; the step obligation
    -- is the same recipe.  Candidates are tried in turn — a wrong block
    -- fails its step proof and the next is tried — until no loop is left.
    -- The prefix knowledge about the ENCLOSING live signals is one
    -- predicate `G i` (a conjunction of prefix equations, one per
    -- enclosing loop) with a proof `guard : ∀ i < t, G i`; the step
    -- obligation receives it (`loop_trace_guardedP_at`) and, one level
    -- down, extends it with its own live signal's prefix and discharges
    -- ITS nested loops the same way.  Term nesting can exceed circuit
    -- nesting (an inner circuit's input carries the mid loop's term,
    -- whose body carries the inner circuit again), so the recursion goes
    -- `depth` levels below the current one.
    let rec innerBlock (gBody : Term) (guard : Term) (depth : Nat) (lvl : Nat) :
        CommandElabM (Lean.TSyntax `tactic) := do
      -- level-indexed names: a deeper level's `intro` must not shadow the
      -- enclosing level's `q`/`hg`, which the handed-down guard refers to
      let qId := mkI s!"q{lvl}"
      let hqId := mkI s!"hq{lvl}"
      let hgId := mkI s!"hg{lvl}"
      let uId := mkI s!"u{lvl}"
      let mId := mkI s!"m{lvl}"
      let hsId := mkI s!"hs{lvl}"
      let mut alts : Array (Lean.TSyntax `tactic) := #[]
      for node in nestedNodes do
        for b in blocksFor node do
          let packS ← packOf node b (← `($sId))
          let packI ← packOf node b (← `($iId))
          let st1z ← stage1 #[]
          -- `hg m _ : G m` is a conjunction; simp splits it into rewrites
          let st1s ← stage1 #[← `($hqId $mId (Nat.lt_succ_self $mId)),
            ← `($hgId $mId (Nat.lt_succ_self $mId))]
          -- one level down: this loop's own prefix, then everything known
          let deeper ← match depth with
            | 0 => `(tactic| skip)
            | d + 1 =>
              innerBlock (← `((($qId).val $iId = $packI) ∧ $gBody))
                (← `((fun $iId $hiId => ⟨$hqId $iId (by omega), $hgId $iId (by omega)⟩))) d (lvl + 1)
          alts := alts.push (← `(tactic| (
            rw [loop_trace_guardedP_at _ (fun $sId => $packS) (fun $iId => $gBody) ?$hsId _ $guard]
            case $hsId:ident =>
              intro $uId:ident $qId:ident $hqId:ident $hgId:ident
              cases $uId:ident with
              | zero =>
                $st1z:tactic
                $appendFix:tactic
                all_goals (try simp only [$[$rdZeroIds:ident],*])
                $closers:tactic
              | succ $mId =>
                $st1s:tactic
                $appendFix:tactic
                $deeper:tactic
                all_goals (try simp only [$[$rdSuccIds:ident],*])
                $dupSimp:tactic
                ($[$genLines:tactic]*)
                $closers:tactic)))
      if alts.isEmpty then `(tactic| skip) else do
      -- SPARKLE_DEEP_NOFIRST=k: debugging aid — run alternative k alone,
      -- unguarded, so its failure surfaces instead of being backtracked
      if let some k := (← IO.getEnv "SPARKLE_DEEP_NOFIRST") then
        let k := k.toNat!
        let a := alts[k % alts.size]!
        let expose ← stage1 #[← `(runCircuitH_eq), ← `(outFOf)]
        return ← `(tactic| (
          all_goals (try $expose:tactic)
          $appendFix:tactic
          $a:tactic))
      let mut alt : Lean.TSyntax `tactic := alts.back!
      for a in alts.pop.reverse do
        alt ← `(tactic| first | $a:tactic | $alt:tactic)
      -- expose the nested loops: unfold their runCircuitH and push the
      -- inner body's OUTPUT expression (which surfaces here for the
      -- first time) down to `.val` level with the stage-1 set, so each
      -- loop appears as `(Signal.loop F).val n`
      let expose ← stage1 #[← `(runCircuitH_eq), ← `(outFOf)]
      `(tactic| (
        all_goals (try $expose:tactic)
        $appendFix:tactic
        all_goals (repeat $alt:tactic)))
    -- LHS signal: struct ports project their field; Bool-typed
    -- outputs enter as their 1-bit encoding (same as Bool inputs)
    let lhsSig : Term ← match proj? with
      | some projId => `(($projId ($(id) $appArgs*)))
      | none => `(($(id) $appArgs*))
    let lhsSig : Term ← if isBoolOut then
        -- annotate the projected signal as `Signal … Bool` so the
        -- encode lambda's `b` is inferred `Bool` (else Lean reads the
        -- `if` as a Prop-if and demands `Decidable b`)
        `((Sparkle.Core.Signal.Signal.map
            (fun b => bif b then (1 : BitVec 1) else 0)
            ($lhsSig : Sparkle.Core.Signal.Signal
              Sparkle.Core.Domain.defaultDomain Bool)))
      else pure lhsSig
    -- struct outputs: the projection (e.g. TwoOut.sum) must unfold
    -- alongside the function so `TwoOut.sum (f d)` β-reduces to the
    -- field value before runCircuitH_eq can fire
    let eq1Id : Ident := mkIdent (declName ++ `eq_1)
    let idUnfold : Lean.TSyntax `tactic ← match proj? with
      | some _ =>
        -- `simp only [f]` reducible-reduces runCircuitH THROUGH the
        -- field projection into `Signal.map Prod.fst (loop …)`, past
        -- which runCircuitH_proj_eq can't fire.  The def's `.eq_1`
        -- unfolds only to the `runCircuitH` application, keeping it
        -- matchable.
        `(tactic| rw [$eq1Id:ident])
      | none => `(tactic| simp only [$id:ident])
    -- a specialized wrapper's head chain: each constant's first
    -- equation exposes the next application, down to runCircuitH
    let chainUnfold : Array (Lean.TSyntax `tactic) ← headChain.mapM fun c => do
      let eqId : Ident := mkIdent (c ++ `eq_1)
      `(tactic| rw [$eqId:ident])
    let projRw : Lean.TSyntax `tactic ← match proj? with
      | some pj => `(tactic| rw [runCircuitH_proj_eq $pj])
      | none => `(tactic| rw [runCircuitH_eq])
    let outUnfoldIds : Array Ident := match proj? with
      | some pj => helperIds.push pj
      | none => helperIds
    -- The top loop, per candidate block: abstract the loop signal as
    -- `L`, prove its trace once (`hLt`, via loop_trace_at with the
    -- step recipe — nested loops inside the step are discharged with
    -- the `hpre` prefix as guard), then the output side against the
    -- shallow output equation, with `hLt` itself as the guard for the
    -- nested loops the output reads.
    let retTyStx : Term ← liftTermElabM (Lean.PrettyPrinter.delab retTy)
    let topTys := topNode.tys
    let mkTopProof (b : Nat) : CommandElabM (Lean.TSyntax `tactic) := do
      let packS ← packOf topNode b (← `($sId))
      let packU ← packOf topNode b (← `($uId))
      let packI ← packOf topNode b (← `($iId))
      let hpreGuard ← `((fun $iId $hiId => $hpreId $iId (by omega)))
      let hLtGuard ← `((fun $iId _ => $hLtId $iId))
      -- nested loops: term nesting exceeds circuit nesting (an inner
      -- circuit's input carries the mid loop's term, whose body carries
      -- the inner circuit again — a two-level design needs four), so
      -- recurse as deep as the alternative count allows: the generated
      -- script has (#alternatives)^depth leaves, kept ≤ 64, depth ≤ 5
      let nAlts := nestedNodes.foldl (fun acc n => acc + (blocksFor n).length) 0
      let depth := Id.run do
        let mut d := 1
        for k in [2:6] do
          if nAlts ^ k ≤ 64 then d := k
        return d
      let innerHpre ← innerBlock (← `(($preId).val $iId = $packI)) hpreGuard depth 0
      let innerHLt ← innerBlock (← `(($LId).val $iId = $packI)) hLtGuard depth 0
      let st1z ← stage1 #[]
      let st1s ← stage1 #[← `($hpreId $nId (Nat.lt_succ_self $nId))]
      `(tactic| (
        generalize $hLId : Signal.loop (loopFOf
          (dom := Sparkle.Core.Domain.defaultDomain)
          (αs := [$topTys,*]) (ρ := $retTyStx) _ _) = $LId
        have $hLtId : ∀ ($uId : Nat), ($LId).val $uId = $packU := by
          intro $uId:ident
          rw [← $hLId:ident]
          refine loop_trace_at _ (fun $sId => $packS) ?_ $uId
          intro $uId:ident $preId:ident $hpreId:ident
          cases $uId:ident with
          | zero =>
            $st1z:tactic
            $appendFix:tactic
            -- stage 2: the spec side is the readers at cycle 0
            all_goals (try simp only [$[$rdZeroIds:ident],*])
            $closers:tactic
          | succ $nId =>
            $st1s:tactic
            $appendFix:tactic
            $innerHpre:tactic
            -- stage 2: one step of the spec recurrence, as the shallow
            -- literal-width expressions over the readers at cycle n
            all_goals (try simp only [$[$rdSuccIds:ident],*])
            $dupSimp:tactic
            ($[$genLines:tactic]*)
            $closers:tactic
        -- the output side: outSig against the packed projection, via
        -- the shallow output equation
        rw [$outSId:ident]
        all_goals (try simp only [$hLtId:ident])
        $innerHLt:tactic
        $dupSimp:tactic
        ($[$genLines:tactic]*)
        $closers:tactic))
    let topProof : Lean.TSyntax `tactic ← do
      let alts ← topBlocks.toArray.mapM mkTopProof
      let mut alt : Lean.TSyntax `tactic := alts.back!
      for a in alts.pop.reverse do
        alt ← `(tactic| first | $a:tactic | $alt:tactic)
      pure alt
    -- the theorem: general theorem + per-instance Signal bridge
    let thmCmd ← `(set_option maxRecDepth 65536 in
      set_option maxHeartbeats 1600000 in
      theorem $thId $paramBinders* (t : Nat) :
        (($lhsSig).val t).toNat
        = (Sparkle.IR.Semantics.evalExpr
            (weOfC $nmId (fun j => (($ΓrT ++ $ΓiT : List Nat)).get j))
            (envOfC $nmId (natJoin
              (Cdo.irState $deepId $nmId (fun t j => (($inpS) j).val t) t)
              (fun j => ((($inpS) j).val t).toNat)))
            (CExpr.compile $nmId (Cdo.out $deepId))).getD 0 := by
      rw [← Cdo.elab_general $deepId $nmId (by decide) $inpS t]
      congr 1
      -- the Signal-side bridge: f's runCircuitH loop against the deep
      -- spec recurrence, both through loop_trace.  For a struct
      -- output we unfold the function to expose runCircuitH, then push
      -- the field projection onto the output via runCircuitH_proj_eq
      -- (the loop's STATE is projection-independent), landing on the
      -- same outFOf shape a single Signal output produces.
      $idUnfold:tactic
      ($[$chainUnfold:tactic]*)
      $projRw:tactic
      simp only [outFOf, mkHolds, Signal.map, sigval_add, sigval_sub, sigval_mul, sigval_and, sigval_or, sigval_xor, sigval_shl, sigval_shr, sigval_append, sigval_add_c, sigval_sub_c, sigval_mul_c, sigval_and_c, sigval_or_c, sigval_xor_c, sigval_shl_c, sigval_shr_c, sigval_append_c, sigval_c_add, sigval_c_sub, sigval_c_mul, sigval_c_and, sigval_c_or, sigval_c_xor, sigval_c_shl, sigval_c_shr, sigval_c_append, sigval_and_b, sigval_or_b, sigval_xor_b, sigval_not, sigval_not_b, sigval_neg, sigval_mux, sigval_beq, sigval_pure,
        $[$outUnfoldIds:ident],*]
      $appendFix:tactic
      $topProof:tactic)
    if (← IO.getEnv "SPARKLE_DEEP_DEBUG").isSome then
      logInfo m!"{thmCmd}"
    if (← IO.getEnv "SPARKLE_DEEP_NOTHM").isSome then
      logInfo m!"#verify_elab_deep {declName}.{portName}: defs only (SPARKLE_DEEP_NOTHM)"
      continue
    elabCommand thmCmd
    -- DEEP-BRIDGE (first landing): rewrite the capstone's RHS through
    -- the G1_out glue so the Signal value is stated as
    -- `evalExpr weM (envOfC …) outCone` — the ConeFold bridge's
    -- language (full width-table env, resolved cone constant), the
    -- same object #verify_elab's chain consumes.  The env is still the
    -- deep `envOfC (natJoin (irState t) inp)`; matching it to a
    -- stepModule seed and replaying regstep/state_trace is the next
    -- deep step.
    let outConeId := mkI s!"{base}{suffix}_deep_cone_out"
    let g1OutId := mkI s!"{base}{suffix}_deep_coneEval_out"
    let sigMId := mkI s!"{base}{suffix}_deep_signalM"
    elabCommand (← `(theorem $sigMId $paramBinders* (t : Nat) :
        (($lhsSig).val t).toNat
        = (Sparkle.IR.Semantics.evalExpr $weMId
            (envOfC $nmId (natJoin
              (Cdo.irState $deepId $nmId (fun t j => (($inpS) j).val t) t)
              (fun j => ((($inpS) j).val t).toNat)))
            $outConeId).getD 0 := by
      rw [$thId $appArgs* t, $g1OutId _]))
    -- ===== DEEP-BRIDGE REPLAY =====
    -- The #verify_elab chain (step / regstep / state_trace /
    -- signal_fold / signal_run) replayed over the general-theorem
    -- route's recurrence `Cdo.irState`.  The seed the deep recurrence
    -- evaluates cones in is `envOfC nm (natJoin (irState t) inp)`;
    -- pointwise readers (register / input / other) identify it with a
    -- stepModule map-state seed, boundedness comes free from
    -- `irState_eq` (irState = stateAt.toNat < 2^w), and the register
    -- phase's mask is killed the same way.  Hypotheses are discharged
    -- by native_decide on the emitted body/stop/width constants.
    let deepEnvAtId := mkI s!"{base}_deep_envAt"
    let irFunextId := mkI s!"{base}_deep_irState_funext"
    let seedBndId := mkI s!"{base}_deep_seed_bounded"
    let rdOtherId := mkI s!"{base}_deep_envAt_other"
    let dRegstepId := mkI s!"{base}_deep_regstep"
    let dEnvStId := mkI s!"{base}_deep_envSt"
    let dSt0Id := mkI s!"{base}_deep_st0"
    let dEnvStBndId := mkI s!"{base}_deep_envSt_bounded"
    let dStateTraceId := mkI s!"{base}_deep_state_trace"
    let inpFam : Term ← `((fun t j => (($inpS) j).val t))
    let regRstsD : List String := m.body.filterMap fun st =>
      match st with
      | .register _ _ (rstName, _) _ _ => some rstName
      | _ => none
    let refWiresD? : Option (List String) := regs.foldr
      (fun (r : String × Sparkle.IR.AST.Expr × Int) acc =>
        match r.2.1, acc with
        | .ref w, some l => some (w :: l)
        | _, _ => none) (some [])
    -- nm order: registers 0..nR-1, then inputs nR..nR+nI-1
    let nmNames : List String :=
      (regs.map (·.1)) ++ (ins.map (·.1))
    let hneIds : Array Ident :=
      (List.range (nR + nI)).toArray.map fun idx => mkI s!"hne_{idx}"
    let rdIds : Array Ident := (List.range (nR + nI)).toArray.map fun idx =>
      if idx < nR then mkI s!"{base}_deep_envAt_r{idx}"
      else mkI s!"{base}_deep_envAt_i{idx - nR}"
    -- the induction conjunction's name must be UNHYGIENIC on both the
    -- `have` and its uses (mkHenv builds its uses in a separate
    -- quotation; a literal `ihc` in the outer quotation would get a
    -- macro scope the inner reference cannot see)
    let ihcId := mkI "ihc"
    -- the seed identity `deep_envSt t st = deep_envAt t` under the
    -- induction conjunction, as a reusable tactic block
    let mkHenv (ihcId : Ident) (hbndIds : Array Ident) :
        CommandElabM (Array (Lean.TSyntax `tactic)) := do
      let mut tacs : Array (Lean.TSyntax `tactic) := #[]
      tacs := tacs.push (← `(tactic| funext n))
      tacs := tacs.push (← `(tactic| simp only [$dEnvStId:ident]))
      for idx in List.range (nR + nI) do
        let nmS := nmNames[idx]!
        let hne := hneIds[idx]!
        let rd := rdIds[idx]!
        tacs := tacs.push (← `(tactic| by_cases $hne:ident : n = $(quote nmS)))
        if idx < nR then
          let bnds : Array Term ← hbndIds.mapM fun b => `(Nat.mod_eq_of_lt $b)
          let exs : Array (Lean.TSyntax `tactic) ← hbndIds.mapM fun b =>
            `(tactic| all_goals (try exact $b))
          tacs := tacs.push (← `(tactic| case pos =>
            subst $hne:ident
            simp [$rd:ident, $ihcId:ident, Sparkle.IR.Semantics.mask,
              $[$bnds:term],*]
            $[$exs:tactic]*))
        else
          tacs := tacs.push (← `(tactic| case pos =>
            subst $hne:ident
            simp [$rd:ident]))
      let hneTerms : Array Term := hneIds.map fun h => ⟨h.raw⟩
      let rdApp : Term ← `($rdOtherId $appArgs* t n $hneTerms*)
      tacs := tacs.push (← `(tactic| simp [$rdApp:term, $[$hneTerms:term],*]))
      pure tacs
    let bridgeOk := nR > 0 && refWiresD?.isSome && regRstsD.length == nR
    let mut bridgeAudit : Array Ident := #[]
    if bridgeOk && k == 0 then
      let regWiresD := refWiresD?.getD []
      elabCommand (← `(def $deepEnvAtId $paramBinders* (t : Nat) :
          Sparkle.IR.Semantics.Env :=
        envOfC $nmId (natJoin
          (Cdo.irState $deepId $nmId $inpFam t)
          (fun j => ((($inpS) j).val t).toNat))))
      elabCommand (← `(theorem $irFunextId $paramBinders* (t : Nat) :
          Cdo.irState $deepId $nmId $inpFam t
            = fun i => (Cdo.stateAt $deepId $inpFam t i).toNat := by
        funext i
        exact Cdo.irState_eq _ _ (by decide) _ t i))
      elabCommand (← `(theorem $seedBndId $paramBinders* (t : Nat) :
          ∀ n, $deepEnvAtId $appArgs* t n < 2 ^ $weMId n := by
        intro n
        unfold $deepEnvAtId
        apply envOfC_bounded
        intro i
        have hag : ∀ i : Fin (($ΓrT ++ $ΓiT : List Nat)).length,
            $weMId ($nmId i) = (($ΓrT ++ $ΓiT : List Nat)).get i := by
          native_decide
        rw [hag i, $irFunextId $appArgs*]
        rw [natJoin_eq_join (Cdo.stateAt $deepId $inpFam t)
          (fun j => (($inpS) j).val t) i]
        exact BitVec.isLt _))
      -- pointwise readers
      for idx in List.range (nR + nI) do
        let nmS := nmNames[idx]!
        let rdId := rdIds[idx]!
        let rhs : Term ← if idx < nR then
            `(Cdo.irState $deepId $nmId $inpFam t ⟨$(quote idx), by decide⟩)
          else
            `(((($inpS) ⟨$(quote (idx - nR)), by decide⟩).val t).toNat)
        elabCommand (← `(theorem $rdId $paramBinders* (t : Nat) :
            $deepEnvAtId $appArgs* t $(quote nmS) = $rhs := by
          unfold $deepEnvAtId
          rw [show $(quote nmS) = $nmId ⟨$(quote idx), by decide⟩ from rfl,
            envOfC_names _ _ (by decide)]
          rfl))
      -- names outside the register/input family read 0
      let hneBinders ← (List.range (nR + nI)).toArray.mapM fun idx => do
        let h : Ident := hneIds[idx]!
        `(Lean.Parser.Term.bracketedBinderF| ($h:ident : n ≠ $(quote nmNames[idx]!)))
      let hneSymm : Array Term ← (List.range (nR + nI)).toArray.mapM
        fun idx => do
          let h : Ident := hneIds[idx]!
          `(Ne.symm $h:ident)
      elabCommand (← `(theorem $rdOtherId $paramBinders* (t : Nat)
          (n : String) $hneBinders* :
          $deepEnvAtId $appArgs* t n = 0 := by
        simp [$deepEnvAtId:ident, envOfC, chainMap, List.finRange,
          $nmId:ident, $[$hneSymm:term],*]))
      -- per-register step + the register phase
      let mut stepIds : Array Ident := #[]
      for i in List.range nR do
        let (rn, _, _) := regs[i]!
        let sanit := Sparkle.Backend.Verilog.sanitizeName rn
        let coneId := mkI s!"{base}_deep_cone_{sanit}"
        let coneRawId := mkI s!"{base}_deep_coneRaw_{sanit}"
        let regInId := mkI s!"{base}_deep_regIn_{sanit}"
        let stepId := mkI s!"{base}_deep_step_{sanit}"
        stepIds := stepIds.push stepId
        bridgeAudit := bridgeAudit.push stepId
        elabCommand (← `(theorem $stepId $paramBinders* (t : Nat)
            {env1 : Sparkle.IR.Semantics.Env} {v : Nat}
            (hrun : Sparkle.IR.Semantics.evalAssigns $weMId (fun _ _ => 0)
              $bodyId ($deepEnvAtId $appArgs* t) = some env1)
            (hv : Sparkle.IR.Semantics.evalExpr $weMId env1 $regInId
              = some v) :
            Sparkle.IR.Semantics.evalExpr $weMId ($deepEnvAtId $appArgs* t)
              $coneId = some v := by
          have hres : $coneId
              = Tools.ConeFold.resolveSlicesT $wtMId 10000 $coneRawId := by
            native_decide
          rw [hres]
          exact Tools.ConeFold.cone_resolved_agrees_at_seed $weMId
            (fun _ _ => 0) $stopAtMId $wtMId
            (Sparkle.IR.Reorder.woCheck_sound [] $bodyId (by native_decide))
            (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))
            (Tools.ConeFold.noSelfReadCheck_sound _ (by native_decide))
            hrun
            (Tools.ConeFold.hwfCheck_sound $weMId $stopAtMId $bodyId
              (by native_decide))
            (Tools.ConeFold.hwt_of_assoc $weMId $wtLId (by native_decide))
            ($seedBndId $appArgs* t)
            (Tools.ConeFold.stopAtFrozenCheck_sound $stopAtMId $bodyId
              (by native_decide))
            (fuel := 10000) (e := $regInId)
            (hinl := by native_decide)
            10000 hv))
      -- regstep
      let mut nextsItems : Array Term := #[]
      let mut pre : Array (Lean.TSyntax `tactic) := #[]
      let mut finalArgs : Array Term := #[]
      let mut closers : Array (Lean.TSyntax `tactic) := #[]
      for i in List.range nR do
        let (rn, _, _) := regs[i]!
        let sanit := Sparkle.Backend.Verilog.sanitizeName rn
        let coneId := mkI s!"{base}_deep_cone_{sanit}"
        let regInId := mkI s!"{base}_deep_regIn_{sanit}"
        let g1Id := mkI s!"{base}_deep_coneEval_r{i}"
        let rstName := regRstsD[i]!
        let w := regWiresD[i]!
        let hrstId := mkI s!"hrst{i}"
        let hstepId := mkI s!"hstep{i}"
        let hnextId := mkI s!"hnext{i}"
        let hbndId := mkI s!"hbnd{i}"
        nextsItems := nextsItems.push (← `(($(quote rn),
          Cdo.irState $deepId $nmId $inpFam (t + 1) ⟨$(quote i), by decide⟩)))
        pre := pre.push (← `(tactic| have $hrstId:ident :
            env1 $(quote rstName) = 0 := by
          have hfr := Tools.ConeFold.evalAssigns_frame $weMId (fun _ _ => 0)
            $bodyId _ env1 hrun
            (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))
            $(quote rstName) (by native_decide)
          rw [hfr]
          simp [$deepEnvAtId:ident, envOfC, chainMap, List.finRange,
            $nmId:ident]))
        pre := pre.push (← `(tactic| have $hstepId:ident :=
          $(stepIds[i]!) $appArgs* t hrun
            (show Sparkle.IR.Semantics.evalExpr $weMId env1 $regInId
                = some (env1 $(quote w)) by
              simp [$regInId:ident, Sparkle.IR.Semantics.evalExpr])))
        pre := pre.push (← `(tactic| have $hnextId:ident :
            Cdo.irState $deepId $nmId $inpFam (t + 1) ⟨$(quote i), by decide⟩
              = env1 $(quote w) := by
          simp only [Cdo.irState]
          rw [$g1Id:ident]
          show (Sparkle.IR.Semantics.evalExpr $weMId
            ($deepEnvAtId $appArgs* t) $coneId).getD 0 = _
          rw [$hstepId:ident]
          rfl))
        pre := pre.push (← `(tactic| have $hbndId:ident :
            env1 $(quote w) < 2 ^ $(quote regWs[i]!) := by
          rw [← $hnextId:ident, Cdo.irState_eq _ _ (by decide)]
          exact BitVec.isLt _))
        finalArgs := finalArgs.push (← `(Nat.mod_eq_of_lt $hbndId:ident))
        finalArgs := finalArgs.push (← `($hrstId:ident))
        finalArgs := finalArgs.push (← `($hnextId:ident))
        closers := closers.push (← `(tactic| all_goals (try exact ($hnextId:ident).symm)))
        closers := closers.push (← `(tactic| all_goals (try exact $hnextId:ident)))
      elabCommand (← `(theorem $dRegstepId $paramBinders* (t : Nat)
          {env1 : Sparkle.IR.Semantics.Env}
          (hrun : Sparkle.IR.Semantics.evalAssigns $weMId (fun _ _ => 0)
            $bodyId ($deepEnvAtId $appArgs* t) = some env1) :
          Sparkle.IR.Semantics.regNexts $weMId (fun _ _ => 0) $bodyId env1
            = some [$nextsItems,*] := by
        $[$pre:tactic]*
        simp only [$bodyId:ident, Sparkle.IR.Semantics.regNexts,
          Sparkle.IR.Semantics.evalExpr, Option.bind_eq_bind,
          Option.bind_some]
        simp [Sparkle.IR.Semantics.mask, $weMId:ident, -Fin.zero_eta,
          -Fin.mk_zero, -Fin.mk_one, $[$finalArgs:term],*]
        repeat' (apply And.intro)
        $[$closers:tactic]*))
      -- map-state seed, initial state, boundedness
      let envStBody ← do
        let mut acc ← `((0 : Nat))
        for j in (List.range nI).reverse do
          let (n, _) := ins[j]!
          acc ← `(if n == $(quote n) then
            ((($inpS) ⟨$(quote j), by decide⟩).val t).toNat else $acc)
        for i in (List.range nR).reverse do
          let (rn, _, _) := regs[i]!
          acc ← `(if n == $(quote rn) then
            Sparkle.IR.Semantics.mask $(quote regWs[i]!) (st $(quote rn))
            else $acc)
        pure acc
      elabCommand (← `(def $dEnvStId $paramBinders* (t : Nat)
          (st : String → Nat) : Sparkle.IR.Semantics.Env :=
        fun n => $envStBody))
      let st0Body ← do
        let mut acc ← `((0 : Nat))
        for i in (List.range nR).reverse do
          let (rn, _, _) := regs[i]!
          acc ← `(if n == $(quote rn) then
            (Cdo.inits $deepId ⟨$(quote i), by decide⟩).toNat else $acc)
        pure acc
      elabCommand (← `(def $dSt0Id : String → Nat := fun n => $st0Body))
      elabCommand (← `(theorem $dEnvStBndId $paramBinders* (t : Nat)
          (st : String → Nat) :
          ∀ n, $dEnvStId $appArgs* t st n < 2 ^ $weMId n := by
        intro n
        simp only [$dEnvStId:ident]
        repeat' split
        all_goals
          first
            | exact Nat.two_pow_pos _
            | (simp only [beq_iff_eq] at *
               subst_vars
               simp only [$weMId:ident]
               first
                 | exact Nat.mod_lt _ (Nat.two_pow_pos _)
                 | exact BitVec.isLt _
                 | (simp
                    first
                      | done
                      | exact Nat.mod_lt _ (Nat.two_pow_pos _)
                      | exact BitVec.isLt _
                      | omega))))
      -- state_trace
      let stateConj ← do
        let mut conjs : Array Term := #[]
        for i in List.range nR do
          let (rn, _, _) := regs[i]!
          conjs := conjs.push (← `(st $(quote rn)
            = Cdo.irState $deepId $nmId $inpFam t ⟨$(quote i), by decide⟩))
        let mut acc : Term := conjs.back!
        for c in conjs.pop.reverse do
          acc ← `($c ∧ $acc)
        pure acc
      let hbndIds : Array Ident :=
        (List.range nR).toArray.map fun i => mkI s!"hbnd{i}"
      let mut hbndTacs : Array (Lean.TSyntax `tactic) := #[]
      for i in List.range nR do
        hbndTacs := hbndTacs.push (← `(tactic| have $(hbndIds[i]!):ident :
            Cdo.irState $deepId $nmId $inpFam t ⟨$(quote i), by decide⟩
              < 2 ^ $(quote regWs[i]!) := by
          rw [Cdo.irState_eq _ _ (by decide)]
          exact BitVec.isLt _))
      let henvTacs ← mkHenv ihcId hbndIds
      elabCommand (← `(theorem $dStateTraceId $paramBinders* :
          ∀ (t : Nat) {st : String → Nat},
          Tools.ConeFold.stepIter $weMId $bodyId ($dEnvStId $appArgs*)
            $dSt0Id t = some st → $stateConj := by
        intro t
        induction t with
        | zero =>
          intro st h
          simp only [Tools.ConeFold.stepIter, Option.some_inj] at h
          subst h
          simp [$dSt0Id:ident, Cdo.irState]
        | succ t ih =>
          intro st' h
          simp only [Tools.ConeFold.stepIter, Option.bind_eq_bind] at h
          cases hprev : Tools.ConeFold.stepIter $weMId $bodyId
              ($dEnvStId $appArgs*) $dSt0Id t with
          | none => rw [hprev] at h; simp at h
          | some st =>
            rw [hprev] at h
            simp only [Option.bind_some] at h
            have $ihcId:ident := ih hprev
            $[$hbndTacs:tactic]*
            have henv : $dEnvStId $appArgs* t st
                = $deepEnvAtId $appArgs* t := by
              $[$henvTacs:tactic]*
            rw [henv] at h
            simp only [Sparkle.IR.Semantics.stepModule,
              Option.bind_eq_bind] at h
            cases hrun : Sparkle.IR.Semantics.evalAssigns $weMId
                (fun _ _ => 0) $bodyId ($deepEnvAtId $appArgs* t) with
            | none => rw [hrun] at h; simp at h
            | some env1 =>
              rw [hrun] at h
              simp only [Option.bind_some] at h
              rw [$dRegstepId $appArgs* t hrun] at h
              rw [Tools.ConeFold.memNexts_memFree $weMId $bodyId
                (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))]
                at h
              simp only [Option.bind_some, Option.some_inj] at h
              subst h
              simp [Sparkle.IR.Semantics.applyNexts]))
    if bridgeOk && k == 0 then
      bridgeAudit := bridgeAudit ++ #[seedBndId, rdOtherId, dRegstepId,
        dEnvStBndId, dStateTraceId]
    -- per-port: the output cone at the seed, and the Signal-level chain
    if bridgeOk then
      let dStepOutId := mkI s!"{base}{suffix}_deep_step_out"
      let dSigFoldId := mkI s!"{base}{suffix}_deep_signal_fold"
      let dSigRunId := mkI s!"{base}{suffix}_deep_signal_run"
      -- this port's Signal value over the SHARED recurrence (the first
      -- port's Cdo): irState only reads next/inits, which every port's
      -- Cdo of a struct circuit shares syntactically
      let sigM0Id := mkI s!"{base}{suffix}_deep_signalM0"
      if k == 0 then
        elabCommand (← `(theorem $sigM0Id $paramBinders* (t : Nat) :
            (($lhsSig).val t).toNat
            = (Sparkle.IR.Semantics.evalExpr $weMId
                (envOfC $nmId (natJoin
                  (Cdo.irState $deep0Id $nmId $inpFam t)
                  (fun j => ((($inpS) j).val t).toNat)))
                $outConeId).getD 0 := $sigMId $appArgs* t))
      else
        elabCommand (← `(theorem $sigM0Id $paramBinders* (t : Nat) :
            (($lhsSig).val t).toNat
            = (Sparkle.IR.Semantics.evalExpr $weMId
                (envOfC $nmId (natJoin
                  (Cdo.irState $deep0Id $nmId $inpFam t)
                  (fun j => ((($inpS) j).val t).toNat)))
                $outConeId).getD 0 := by
          rw [$sigMId $appArgs* t,
            Cdo.irState_congr $deepId $deep0Id $nmId $inpFam rfl rfl]))
      elabCommand (← `(theorem $dStepOutId $paramBinders* (t : Nat)
          {env1 : Sparkle.IR.Semantics.Env} {v : Nat}
          (hrun : Sparkle.IR.Semantics.evalAssigns $weMId (fun _ _ => 0)
            $bodyId ($deepEnvAtId $appArgs* t) = some env1)
          (hv : Sparkle.IR.Semantics.evalExpr $weMId env1
            (.ref $(quote portName)) = some v) :
          Sparkle.IR.Semantics.evalExpr $weMId ($deepEnvAtId $appArgs* t)
            $outConeId = some v := by
        have hres : $outConeId
            = Tools.ConeFold.resolveSlicesT $wtMId 10000 $outConeRawId := by
          native_decide
        rw [hres]
        exact Tools.ConeFold.cone_resolved_agrees_at_seed $weMId
          (fun _ _ => 0) $stopAtMId $wtMId
          (Sparkle.IR.Reorder.woCheck_sound [] $bodyId (by native_decide))
          (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))
          (Tools.ConeFold.noSelfReadCheck_sound _ (by native_decide))
          hrun
          (Tools.ConeFold.hwfCheck_sound $weMId $stopAtMId $bodyId
            (by native_decide))
          (Tools.ConeFold.hwt_of_assoc $weMId $wtLId (by native_decide))
          ($seedBndId $appArgs* t)
          (Tools.ConeFold.stopAtFrozenCheck_sound $stopAtMId $bodyId
            (by native_decide))
          (fuel := 10000) (e := .ref $(quote portName))
          (hinl := by native_decide)
          10000 hv))
      let hbndIds : Array Ident :=
        (List.range nR).toArray.map fun i => mkI s!"hbnd{i}"
      let mut hbndTacs : Array (Lean.TSyntax `tactic) := #[]
      for i in List.range nR do
        hbndTacs := hbndTacs.push (← `(tactic| have $(hbndIds[i]!):ident :
            Cdo.irState $deep0Id $nmId $inpFam t ⟨$(quote i), by decide⟩
              < 2 ^ $(quote regWs[i]!) := by
          rw [Cdo.irState_eq _ _ (by decide)]
          exact BitVec.isLt _))
      let henvTacs ← mkHenv ihcId hbndIds
      elabCommand (← `(theorem $dSigFoldId $paramBinders* (t : Nat)
          {st : String → Nat} {env1 : Sparkle.IR.Semantics.Env}
          (hstep : Tools.ConeFold.stepIter $weMId $bodyId
            ($dEnvStId $appArgs*) $dSt0Id t = some st)
          (hrun : Sparkle.IR.Semantics.evalAssigns $weMId (fun _ _ => 0)
            $bodyId ($dEnvStId $appArgs* t st) = some env1) :
          (($lhsSig).val t).toNat = env1 $(quote portName) := by
        have $ihcId:ident := $dStateTraceId $appArgs* t hstep
        $[$hbndTacs:tactic]*
        have henv : $dEnvStId $appArgs* t st = $deepEnvAtId $appArgs* t := by
          $[$henvTacs:tactic]*
        rw [henv] at hrun
        have hout := $dStepOutId $appArgs* t hrun
          (show Sparkle.IR.Semantics.evalExpr $weMId env1
              (.ref $(quote portName)) = some (env1 $(quote portName)) by
            simp [Sparkle.IR.Semantics.evalExpr])
        rw [$sigM0Id $appArgs* t]
        show (Sparkle.IR.Semantics.evalExpr $weMId ($deepEnvAtId $appArgs* t)
          $outConeId).getD 0 = _
        rw [hout]
        rfl))
      elabCommand (← `(theorem $dSigRunId $paramBinders* (K : Nat) :
          ∃ envs, Sparkle.IR.Semantics.runModule $weMId $bodyId
              (fun td s => $dEnvStId $appArgs* (K - 1 - td) s) K $dSt0Id
              (fun _ _ => 0) = some envs
            ∧ ∀ t, t < K → ∃ env1, envs[t]? = some env1
              ∧ (($lhsSig).val t).toNat = env1 $(quote portName) := by
        obtain ⟨envs, henvs⟩ := Option.isSome_iff_exists.mp
          (Tools.ConeFold.runModule_isSome $weMId $bodyId
            (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))
            (by native_decide)
            (fun td s => $dEnvStId $appArgs* (K - 1 - td) s) K $dSt0Id)
        refine ⟨envs, henvs, ?_⟩
        intro t ht
        have henvs' : Sparkle.IR.Semantics.runModule $weMId $bodyId
            (fun td s => $dEnvStId $appArgs* (0 + (K - 1 - td)) s) K $dSt0Id
            (fun _ _ => 0) = some envs := by
          rw [Tools.ConeFold.runModule_seed_congr $weMId $bodyId K
            (fun td s => $dEnvStId $appArgs* (0 + (K - 1 - td)) s)
            (fun td s => $dEnvStId $appArgs* (K - 1 - td) s)
            (fun td htd => by simp only [Nat.zero_add])]
          exact henvs
        obtain ⟨st', env1, hsi, hev, hget⟩ :=
          Tools.ConeFold.runModule_stepIter $weMId $bodyId
            (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))
            ($dEnvStId $appArgs*) K 0 $dSt0Id envs henvs' t ht
        refine ⟨env1, hget, ?_⟩
        have hsi' : Tools.ConeFold.stepIter $weMId $bodyId
            ($dEnvStId $appArgs*) $dSt0Id t = some st' := by
          rw [Tools.ConeFold.stepIter_seed_congr $weMId $bodyId
            ($dEnvStId $appArgs*)
            (fun tt s => $dEnvStId $appArgs* (0 + tt) s) $dSt0Id t
            (fun tt htt => by simp only [Nat.zero_add])]
          exact hsi
        have hev' : Sparkle.IR.Semantics.evalAssigns $weMId (fun _ _ => 0)
            $bodyId ($dEnvStId $appArgs* t st') = some env1 := by
          have h0 : (0 : Nat) + t = t := by omega
          rw [← h0]
          exact hev
        exact $dSigFoldId $appArgs* t hsi' hev'))
      bridgeAudit := bridgeAudit ++ #[sigM0Id, dStepOutId, dSigFoldId, dSigRunId]
    -- audit the capstone AND every fidelity theorem: elabCommand
    -- recovers failed tactic blocks as sorry, and a sorry'd fidelity
    -- proof would silently demote the result to the unverified twin
    for aud in #[thId] ++ fidIds ++ #[fidOutId] ++ bridgeAudit do
      let axioms ← liftCoreM <| Lean.collectAxioms aud.getId
      if axioms.contains ``sorryAx then
        throwError "#verify_elab_deep {declName}: generated proof {aud.getId} FAILED (sorryAx) — see the errors above"
    logInfo m!"#verify_elab_deep {declName}{if structName?.isSome then s!".{portName}" else ""}: PROVEN via Cdo.elab_general — {thId.getId} ({nR} registers, {nI} inputs; axioms clean; fidelity: {fidIds.size} register cones + out = the elaborated IR, by unfolding)"

end Tools.DeepElab
