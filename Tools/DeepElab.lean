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
import Tools.ConeFoldMem
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

/-! E2m: deep circuits WITH synchronous memories.

A `Signal.memory` in a `circuit do` body lowers to an IR `.memory`
statement: contents (state, updated by the write port after the cycle)
plus a read-data wire that LATCHES `contents[readAddr]` at the clock
edge (read-old — the IR's `syncReadLatches`, the Verilog `always_ff`,
and `Signal.memState`).  `CdoM` extends `Cdo` with a memory context:
a state slot's next value is either a combinational cone or such a
latch, and every memory carries one write port.  A
`Signal.memoryComboRead` reads the contents combinationally instead
(`comboReads`, same cycle, read-old): its read-data wire is not state
but a READ SLOT — one more context entry for the cones (`Γc`), valued
from the contents at the address cone (which lives over registers and
inputs only).  Cones never read a memory directly (only its latch or
read slot), so `CExpr`, `compile` and `compile_correct` are unchanged;
only the state recurrence and the cone environment change. -/

/-- (address width, data width) -/
abbrev MemSig := Nat × Nat

/-- Memory contents: one array per memory. -/
def CMem (Γm : List MemSig) :=
  ∀ k : Fin Γm.length, BitVec (Γm.get k).1 → BitVec (Γm.get k).2

instance {Γm : List MemSig} : Inhabited (CMem Γm) := ⟨fun _ _ => default⟩

/-- Next value of a state slot of width `w`. -/
inductive NextM (Γ : List Nat) (Γm : List MemSig) : Nat → Type where
  | cone {w : Nat} (e : CExpr Γ w) : NextM Γ Γm w
  | latch (k : Fin Γm.length) (addr : CExpr Γ (Γm.get k).1) : NextM Γ Γm (Γm.get k).2

def NextM.denote {Γ : List Nat} {Γm : List MemSig} {w : Nat}
    (ρ : CEnv Γ) (μ : CMem Γm) : NextM Γ Γm w → BitVec w
  | .cone e => e.denote ρ
  | .latch k a => μ k (a.denote ρ)

/-- The IR cone of a cone slot (fidelity checks); a latch has none. -/
def NextM.compileCone {Γ : List Nat} {Γm : List MemSig} {w : Nat}
    (names : Fin Γ.length → String) : NextM Γ Γm w → Option Expr
  | .cone e => some (e.compile names)
  | .latch _ _ => none

/-! E2m-replay: the IR-side view of a `CdoM` step.

`Cdo.irState` is DEFINED through `evalExpr`, so the memory-free replay
reads a register's next value off it by unfolding.  `CdoM.irState` is
`toNat` of the BitVec recurrence; the lemmas below give the replay the
same three facts through `compile_correct`: a cone slot's next value is
its compiled cone's IR evaluation, a latch slot's is the contents at the
IR-evaluated address, and the contents after a cycle — seen through
`CMem.natView`, the `MEnv` view where in-range indices read the array
and out-of-range ones 0 — are exactly `memWritePorts`' single
enabled-port update. -/

/-- The latch slot's memory and address (a cone slot has none). -/
def NextM.latchAddr? {Γ : List Nat} {Γm : List MemSig} {w : Nat} :
    NextM Γ Γm w → Option (Σ k : Fin Γm.length, CExpr Γ (Γm.get k).1)
  | .cone _ => none
  | .latch k a => some ⟨k, a⟩

/-- A cone slot's next value, read off the IR evaluation of its compiled
    cone (the `NextM` analogue of `Cdo.irState`'s defining clause). -/
theorem NextM.toNat_denote_cone {Γ : List Nat} {Γm : List MemSig} {w : Nat}
    (nx : NextM Γ Γm w) (names : Fin Γ.length → String)
    (we : WEnv) (env : Env) (ρ : CEnv Γ) (μ : CMem Γm)
    (hw : ∀ i, we (names i) = Γ.get i)
    (hv : ∀ i : Fin Γ.length, env (names i) = (ρ i).toNat)
    {ir : Expr} {v : Nat}
    (hc : nx.compileCone names = some ir)
    (h : evalExpr we env ir = some v) :
    (nx.denote ρ μ).toNat = v := by
  cases nx with
  | cone e =>
    simp only [NextM.compileCone, Option.some.injEq] at hc
    subst hc
    rw [CExpr.compile_correct names we env ρ hw hv e] at h
    exact Option.some.inj h
  | latch k a => simp [NextM.compileCone] at hc

/-- A latch slot's next value: the contents at the (IR-evaluated) address. -/
theorem NextM.toNat_denote_latch {Γ : List Nat} {Γm : List MemSig} {w : Nat}
    (nx : NextM Γ Γm w) (names : Fin Γ.length → String)
    (we : WEnv) (env : Env) (ρ : CEnv Γ) (μ : CMem Γm)
    (hw : ∀ i, we (names i) = Γ.get i)
    (hv : ∀ i : Fin Γ.length, env (names i) = (ρ i).toNat)
    (k : Fin Γm.length) (a : CExpr Γ (Γm.get k).1) {v : Nat}
    (hl : nx.latchAddr? = some ⟨k, a⟩)
    (h : evalExpr we env (a.compile names) = some v) :
    (nx.denote ρ μ).toNat = (μ k (BitVec.ofNat _ v)).toNat := by
  cases nx with
  | cone e => simp [NextM.latchAddr?] at hl
  | latch k' a' =>
    simp only [NextM.latchAddr?, Option.some.injEq, Sigma.mk.injEq] at hl
    obtain ⟨hk, ha⟩ := hl
    subst hk
    cases eq_of_heq ha
    simp only [NextM.denote]
    rw [CExpr.compile_correct names we env ρ hw hv _] at h
    rw [← Option.some.inj h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A combinational read port: the memory and the address cone (over the
    registers and inputs — a read address never reads another
    combinational read, v1). -/
structure CRead (Γ : List Nat) (Γm : List MemSig) where
  k : Fin Γm.length
  addr : CExpr Γ (Γm.get k).1

structure CdoM (Γr Γi : List Nat) (Γm : List MemSig) (Γc : List Nat) (wOut : Nat) where
  inits  : CEnv Γr
  minits : CMem Γm
  /-- the combinational read ports, one context slot each -/
  reads  : Fin Γc.length → CRead (Γr ++ Γi) Γm
  hreads : ∀ c, (Γm.get (reads c).k).2 = Γc.get c
  next   : ∀ i : Fin Γr.length, NextM (Γr ++ Γi ++ Γc) Γm (Γr.get i)
  writes : ∀ k : Fin Γm.length,
    CExpr (Γr ++ Γi ++ Γc) (Γm.get k).1 × CExpr (Γr ++ Γi ++ Γc) (Γm.get k).2
      × CExpr (Γr ++ Γi ++ Γc) 1
  out    : CExpr (Γr ++ Γi ++ Γc) wOut

/-- The combinational reads, this cycle: contents at the address. -/
def CdoM.readsEnv {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (ρ0 : CEnv (Γr ++ Γi)) (μ : CMem Γm) : CEnv Γc :=
  fun j => (c.hreads j) ▸ μ (c.reads j).k ((c.reads j).addr.denote ρ0)

/-- The full cone environment: registers, inputs, then the reads. -/
def CdoM.fullEnv {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (ρ0 : CEnv (Γr ++ Γi)) (μ : CMem Γm) : CEnv (Γr ++ Γi ++ Γc) :=
  CEnv.join ρ0 (c.readsEnv ρ0 μ)

def CdoM.memUpd {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (ρ : CEnv (Γr ++ Γi ++ Γc)) (μ : CMem Γm) : CMem Γm := fun k =>
  let wa := (c.writes k).1
  let wd := (c.writes k).2.1
  let we := (c.writes k).2.2
  fun addr =>
    if we.denote ρ = 1#1 ∧ addr = wa.denote ρ then wd.denote ρ else μ k addr

def CdoM.stateAt {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inp : Nat → CEnv Γi) : Nat → CEnv Γr × CMem Γm
  | 0 => (c.inits, c.minits)
  | t+1 =>
    let st := c.stateAt inp t
    let ρ := c.fullEnv (CEnv.join st.1 (inp t)) st.2
    (fun i => (c.next i).denote ρ st.2, c.memUpd ρ st.2)

def CdoM.loopF {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) :
    Sparkle.Core.Signal.Signal dom (CEnv Γr × CMem Γm) →
    Sparkle.Core.Signal.Signal dom (CEnv Γr × CMem Γm) :=
  fun live => ⟨fun t => match t with
    | 0 => (c.inits, c.minits)
    | t+1 =>
      let ρ := c.fullEnv (CEnv.join (live.val t).1 (fun j => (inpS j).val t)) (live.val t).2
      (fun i => (c.next i).denote ρ (live.val t).2, c.memUpd ρ (live.val t).2)⟩

def CdoM.stateSig {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) :
    Sparkle.Core.Signal.Signal dom (CEnv Γr × CMem Γm) :=
  Sparkle.Core.Signal.Signal.loop (c.loopF inpS)

theorem CdoM.stateSig_eq {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) (t : Nat) :
    (c.stateSig (dom := dom) inpS).val t
      = c.stateAt (fun t j => (inpS j).val t) t := by
  unfold CdoM.stateSig
  rw [loop_trace_at _ (fun s => c.stateAt (fun t j => (inpS j).val t) s)
    ?hstep]
  case hstep =>
    intro u pre hpre
    cases u with
    | zero => rfl
    | succ n =>
      show (fun i => (c.next i).denote
            (c.fullEnv (CEnv.join (pre.val n).1 (fun j => (inpS j).val n)) (pre.val n).2) (pre.val n).2,
          c.memUpd (c.fullEnv (CEnv.join (pre.val n).1 (fun j => (inpS j).val n)) (pre.val n).2) (pre.val n).2)
        = _
      rw [hpre n (Nat.lt_succ_self n)]
      rfl

def CdoM.outSig {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) :
    Sparkle.Core.Signal.Signal dom (BitVec wOut) :=
  ⟨fun t => c.out.denote
    (c.fullEnv (CEnv.join ((c.stateSig inpS).val t).1 (fun j => (inpS j).val t))
      ((c.stateSig inpS).val t).2)⟩

def CdoM.irState {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inp : Nat → CEnv Γi) (t : Nat) : Fin Γr.length → Nat :=
  fun i => ((c.stateAt inp t).1 i).toNat

/-- The IR-side view of the combinational reads at cycle `t`. -/
def CdoM.irReads {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inp : Nat → CEnv Γi) (t : Nat) : Fin Γc.length → Nat :=
  fun j => (c.readsEnv (CEnv.join (c.stateAt inp t).1 (inp t)) (c.stateAt inp t).2 j).toNat

/-- The IR seed at cycle `t`: registers, inputs, reads. -/
def CdoM.irEnv {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inp : Nat → CEnv Γi) (t : Nat) : Fin (Γr ++ Γi ++ Γc).length → Nat :=
  natJoin (natJoin (c.irState inp t) (fun j => (inp t j).toNat)) (c.irReads inp t)

/-- The IR seed is the `toNat` of the full deep environment, slot by slot. -/
theorem CdoM.irEnv_eq {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inp : Nat → CEnv Γi) (t : Nat) (j : Fin (Γr ++ Γi ++ Γc).length) :
    c.irEnv inp t j
      = (c.fullEnv (CEnv.join (c.stateAt inp t).1 (inp t)) (c.stateAt inp t).2 j).toNat := by
  have h1 : natJoin (c.irState inp t) (fun j => (inp t j).toNat)
      = fun i => ((CEnv.join (c.stateAt inp t).1 (inp t)) i).toNat := by
    funext i; rw [← natJoin_eq_join]; rfl
  show natJoin (natJoin (c.irState inp t) (fun j => (inp t j).toNat)) (c.irReads inp t) j = _
  rw [h1]
  exact natJoin_eq_join _ _ j

theorem CdoM.envOfC_irEnv {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (names : Fin (Γr ++ Γi ++ Γc).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (inp : Nat → CEnv Γi) (t : Nat) (j : Fin (Γr ++ Γi ++ Γc).length) :
    envOfC names (c.irEnv inp t) (names j)
      = (c.fullEnv (CEnv.join (c.stateAt inp t).1 (inp t)) (c.stateAt inp t).2 j).toNat := by
  rw [envOfC_names names _ hinj j]
  exact c.irEnv_eq inp t j

theorem CdoM.elab_general {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (names : Fin (Γr ++ Γi ++ Γc).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) (t : Nat) :
    ((c.outSig (dom := dom) inpS).val t).toNat
      = (evalExpr (weOfC names (fun j => (Γr ++ Γi ++ Γc).get j))
          (envOfC names (c.irEnv (fun t j => (inpS j).val t) t))
          (c.out.compile names)).getD 0 := by
  rw [CExpr.compile_correct names _ _
    (c.fullEnv (CEnv.join (c.stateAt (fun t j => (inpS j).val t) t).1
      (fun j => (inpS j).val t)) (c.stateAt (fun t j => (inpS j).val t) t).2)
    (fun j => weOfC_names names _ hinj j)
    (c.envOfC_irEnv names hinj _ t)]
  show ((c.outSig (dom := dom) inpS).val t).toNat
      = (c.out.denote _).toNat
  unfold CdoM.outSig
  simp only [c.stateSig_eq inpS t]

theorem CdoM.irState_zero {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inp : Nat → CEnv Γi) (i : Fin Γr.length) :
    c.irState inp 0 i = (c.inits i).toNat := rfl

theorem CdoM.irState_succ_cone {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (names : Fin (Γr ++ Γi ++ Γc).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (inp : Nat → CEnv Γi) (t : Nat) (i : Fin Γr.length) {ir : Expr} {v : Nat}
    (hc : (c.next i).compileCone names = some ir)
    (h : evalExpr (weOfC names (fun j => (Γr ++ Γi ++ Γc).get j))
      (envOfC names (c.irEnv inp t)) ir = some v) :
    c.irState inp (t + 1) i = v :=
  NextM.toNat_denote_cone (c.next i) names _ _ _ (c.stateAt inp t).2
    (fun j => weOfC_names names _ hinj j) (c.envOfC_irEnv names hinj inp t) hc h

theorem CdoM.irState_succ_latch {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (names : Fin (Γr ++ Γi ++ Γc).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (inp : Nat → CEnv Γi) (t : Nat) (i : Fin Γr.length)
    (k : Fin Γm.length) (a : CExpr (Γr ++ Γi ++ Γc) (Γm.get k).1) {v : Nat}
    (hl : (c.next i).latchAddr? = some ⟨k, a⟩)
    (h : evalExpr (weOfC names (fun j => (Γr ++ Γi ++ Γc).get j))
      (envOfC names (c.irEnv inp t)) (a.compile names) = some v) :
    c.irState inp (t + 1) i = ((c.stateAt inp t).2 k (BitVec.ofNat _ v)).toNat :=
  NextM.toNat_denote_latch (c.next i) names _ _ _ (c.stateAt inp t).2
    (fun j => weOfC_names names _ hinj j) (c.envOfC_irEnv names hinj inp t) k a hl h

theorem CdoM.toNat_denote {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (names : Fin (Γr ++ Γi ++ Γc).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (inp : Nat → CEnv Γi) (t : Nat) {w : Nat} (e : CExpr (Γr ++ Γi ++ Γc) w) {v : Nat}
    (h : evalExpr (weOfC names (fun j => (Γr ++ Γi ++ Γc).get j))
      (envOfC names (c.irEnv inp t)) (e.compile names) = some v) :
    (e.denote (c.fullEnv (CEnv.join (c.stateAt inp t).1 (inp t)) (c.stateAt inp t).2)).toNat = v := by
  rw [CExpr.compile_correct names _ _ _ (fun j => weOfC_names names _ hinj j)
    (c.envOfC_irEnv names hinj inp t) e] at h
  exact Option.some.inj h

/-- A read address's `toNat` at the deep state: read addresses live over
    registers and inputs only, compiled with the names restricted to that
    prefix (`names0`). -/
theorem CdoM.toNat_denote0 {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (names : Fin (Γr ++ Γi ++ Γc).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (names0 : Fin (Γr ++ Γi).length → String)
    (h0 : ∀ i : Fin (Γr ++ Γi).length, names0 i
      = names ⟨i.val, by have := i.isLt; simp only [List.length_append] at *; omega⟩)
    (inp : Nat → CEnv Γi) (t : Nat) {w : Nat} (e : CExpr (Γr ++ Γi) w) {v : Nat}
    (h : evalExpr (weOfC names (fun j => (Γr ++ Γi ++ Γc).get j))
      (envOfC names (c.irEnv inp t)) (e.compile names0) = some v) :
    (e.denote (CEnv.join (c.stateAt inp t).1 (inp t))).toNat = v := by
  rw [CExpr.compile_correct names0 _ _ (CEnv.join (c.stateAt inp t).1 (inp t))
    (fun i => by
      rw [h0 i, weOfC_names names _ hinj]
      exact List.getElem_append_left _)
    (fun i => by
      rw [h0 i, envOfC_names names _ hinj]
      show natJoin (natJoin (c.irState inp t) (fun j => (inp t j).toNat)) (c.irReads inp t) ⟨i.val, _⟩ = _
      unfold natJoin
      rw [dif_pos i.isLt]
      exact natJoin_eq_join _ _ i) e] at h
  exact Option.some.inj h

/-- The IR (`MEnv`) view of one memory's contents: in-range indices read
    the array, out-of-range ones 0 (the IR never writes them). -/
def CMem.natView {Γm : List MemSig} (μ : CMem Γm) (k : Fin Γm.length) (i : Nat) : Nat :=
  if i < 2 ^ (Γm.get k).1 then (μ k (BitVec.ofNat _ i)).toNat else 0

theorem CdoM.stateAt_succ_mem {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inp : Nat → CEnv Γi) (t : Nat) :
    (c.stateAt inp (t + 1)).2
      = c.memUpd (c.fullEnv (CEnv.join (c.stateAt inp t).1 (inp t)) (c.stateAt inp t).2)
          (c.stateAt inp t).2 := rfl

theorem CdoM.memUpd_natView {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (ρ : CEnv (Γr ++ Γi ++ Γc)) (μ : CMem Γm) (k : Fin Γm.length) {av dv ev : Nat}
    (hwa : ((c.writes k).1.denote ρ).toNat = av)
    (hwd : ((c.writes k).2.1.denote ρ).toNat = dv)
    (hwe : ((c.writes k).2.2.denote ρ).toNat = ev) (i : Nat) :
    (c.memUpd ρ μ).natView k i
      = if ev ≠ 0 then
          (if i = mask (Γm.get k).1 av then mask (Γm.get k).2 dv else μ.natView k i)
        else μ.natView k i := by
  have hav : av < 2 ^ (Γm.get k).1 := hwa ▸ BitVec.isLt _
  have hdv : dv < 2 ^ (Γm.get k).2 := hwd ▸ BitVec.isLt _
  have hev : ev < 2 := hwe ▸ BitVec.isLt _
  have hen : ((c.writes k).2.2.denote ρ = 1#1) ↔ ev ≠ 0 := by
    rw [BitVec.toNat_eq, hwe]
    show _ ↔ ev ≠ 0
    simp only [BitVec.toNat_ofNat, Nat.pow_one]
    omega
  simp only [CMem.natView, CdoM.memUpd, mask, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hdv]
  by_cases hi : i < 2 ^ (Γm.get k).1
  · rw [if_pos hi, if_pos hi]
    have haddr : (BitVec.ofNat (Γm.get k).1 i = (c.writes k).1.denote ρ) ↔ i = av := by
      rw [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, hwa]
    by_cases he : ev ≠ 0
    · rw [if_pos he]
      by_cases hia : i = av
      · rw [if_pos hia, if_pos ⟨hen.mpr he, haddr.mpr hia⟩, hwd]
      · rw [if_neg hia, if_neg (fun h => hia (haddr.mp h.2))]
    · rw [if_neg he, if_neg (fun h => he (hen.mp h.1))]
  · have : ¬ i = av := by omega
    rw [if_neg hi, if_neg this, ite_self, if_neg hi]

/-- The IR's synchronous read: the latched `mask dw (mems name (mask aw
    av))` is the contents at the address `av` (in the deep view). -/
theorem CMem.natView_latch {Γm : List MemSig} (μ : CMem Γm) (k : Fin Γm.length)
    {aw dw : Nat} (haw : (Γm.get k).1 = aw) (hdw : (Γm.get k).2 = dw) (av : Nat) :
    mask dw (μ.natView k (mask aw av)) = (μ k (BitVec.ofNat _ av)).toNat := by
  subst haw; subst hdw
  simp only [CMem.natView, mask]
  rw [if_pos (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.mod_eq_of_lt (BitVec.isLt _)]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mod_mod]

/-- The IR's combinational read at the deep seed: `mask dw (mems name
    (mask aw av))` with `av` the address's value is the read slot's
    value. -/
theorem CdoM.irReads_eq {Γr Γi Γm Γc wOut} (c : CdoM Γr Γi Γm Γc wOut)
    (inp : Nat → CEnv Γi) (t : Nat) (j : Fin Γc.length) {aw dw : Nat}
    (haw : (Γm.get (c.reads j).k).1 = aw) (hdw : (Γm.get (c.reads j).k).2 = dw) {av : Nat}
    (hav : (((c.reads j).addr).denote (CEnv.join (c.stateAt inp t).1 (inp t))).toNat = av) :
    mask dw (((c.stateAt inp t).2).natView (c.reads j).k (mask aw av)) = c.irReads inp t j := by
  rw [CMem.natView_latch _ _ haw hdw, ← hav, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [CdoM.irReads, CdoM.readsEnv, toNat_cast]

theorem CdoM.stateAt_congr {Γr Γi Γm Γc wOut wOut'} (c : CdoM Γr Γi Γm Γc wOut)
    (c' : CdoM Γr Γi Γm Γc wOut') (inp : Nat → CEnv Γi)
    (hn : c.next = c'.next) (hi : c.inits = c'.inits)
    (hw : c.writes = c'.writes) (hm : c.minits = c'.minits)
    (hr : c.reads = c'.reads) :
    c.stateAt inp = c'.stateAt inp := by
  obtain ⟨i1, m1, r1, h1, n1, w1, o1⟩ := c
  obtain ⟨i2, m2, r2, h2, n2, w2, o2⟩ := c'
  simp only at hn hi hw hm hr
  subst hn hi hw hm hr
  have hh : h1 = h2 := rfl
  subst hh
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [CdoM.stateAt, ih]
    rfl

theorem CdoM.irState_congr {Γr Γi Γm Γc wOut wOut'} (c : CdoM Γr Γi Γm Γc wOut)
    (c' : CdoM Γr Γi Γm Γc wOut') (inp : Nat → CEnv Γi)
    (hn : c.next = c'.next) (hi : c.inits = c'.inits)
    (hw : c.writes = c'.writes) (hm : c.minits = c'.minits)
    (hr : c.reads = c'.reads) :
    c.irState inp = c'.irState inp := by
  funext t i
  simp only [CdoM.irState, CdoM.stateAt_congr c c' inp hn hi hw hm hr]

theorem CdoM.irEnv_congr {Γr Γi Γm Γc wOut wOut'} (c : CdoM Γr Γi Γm Γc wOut)
    (c' : CdoM Γr Γi Γm Γc wOut') (inp : Nat → CEnv Γi)
    (hn : c.next = c'.next) (hi : c.inits = c'.inits)
    (hw : c.writes = c'.writes) (hm : c.minits = c'.minits)
    (hr : c.reads = c'.reads) :
    c.irEnv inp = c'.irEnv inp := by
  have hs := CdoM.stateAt_congr c c' inp hn hi hw hm hr
  obtain ⟨i1, m1, r1, h1, n1, w1, o1⟩ := c
  obtain ⟨i2, m2, r2, h2, n2, w2, o2⟩ := c'
  simp only at hn hi hw hm hr
  subst hn hi hw hm hr
  have hh : h1 = h2 := rfl
  subst hh
  funext t
  unfold CdoM.irEnv CdoM.irState CdoM.irReads CdoM.readsEnv
  rw [hs]


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
partial def toShallow (slot : String → Option Nat) (nR nI : Nat)
    (rdOf : Nat → CommandElabM Term) (inOf : Nat → CommandElabM Term)
    (rdcOf : Nat → CommandElabM Term) :
    Sparkle.IR.AST.Expr → CommandElabM Term
  | .const v w => do
    if v < 0 then throwError "#verify_elab_deep: negative const"
    `((BitVec.ofNat $(quote w) $(quote v.toNat)))
  | .ref n => do
    match slot n with
    | some i =>
      if i < nR then rdOf i
      else if i < nR + nI then inOf (i - nR)
      else rdcOf (i - nR - nI)
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
where go := toShallow slot nR nI rdOf inOf rdcOf

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

/-- Body order for the deep route's IR.  `topoSortBody` puts every
    memory statement first — right for a synchronous read (its data is
    state) but wrong for a combinational read whose address is a local
    wire: `evalAssigns` evaluates `comboReads` in the environment at the
    statement's position, so the read must come after its address's
    definers and before its data's readers.  Synchronous memories first,
    then the combinational items (assignments AND combinational reads)
    in dependency order (Kahn, stable), then the registers. -/
def deepOrderBody (body : List Sparkle.IR.AST.Stmt) : List Sparkle.IR.AST.Stmt := Id.run do
  let sorted := Tools.SVParser.Lower.topoSortBody body
  let mut syncMems : Array Sparkle.IR.AST.Stmt := #[]
  let mut items : Array Sparkle.IR.AST.Stmt := #[]
  let mut regs : Array Sparkle.IR.AST.Stmt := #[]
  let mut others : Array Sparkle.IR.AST.Stmt := #[]
  for st in sorted do
    match st with
    | .memory _ _ _ _ _ _ _ _ _ true _ _ => items := items.push st
    | .memory .. => syncMems := syncMems.push st
    | .assign .. => items := items.push st
    | .register .. => regs := regs.push st
    | _ => others := others.push st
  let defOf : Sparkle.IR.AST.Stmt → Option String := fun st => match st with
    | .assign l _ => some l
    | .memory _ _ _ _ _ _ _ _ rd _ _ _ => some rd
    | _ => none
  let depsOf : Sparkle.IR.AST.Stmt → List String := fun st => match st with
    | .assign _ r => Sparkle.IR.Reorder.refsOf r
    | .memory _ _ _ _ _ _ _ ra _ _ _ _ => Sparkle.IR.Reorder.refsOf ra
    | _ => []
  let defined : Std.HashMap String Bool := items.foldl (init := {}) fun h st =>
    match defOf st with | some n => h.insert n true | none => h
  let mut emitted : Std.HashMap String Bool := {}
  let mut remaining := items.toList
  let mut ordered : Array Sparkle.IR.AST.Stmt := #[]
  let mut fuel := items.size + 1
  while !remaining.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let ready? := remaining.find? fun st =>
      (depsOf st).all fun n => !defined.contains n || emitted.contains n
    match ready? with
    | some st =>
      remaining := remaining.erase st
      ordered := ordered.push st
      if let some n := defOf st then emitted := emitted.insert n true
    | none => break
  -- a cycle (never for an elaborated body): keep the remainder as is
  return syncMems.toList ++ ordered.toList ++ remaining ++ regs.toList ++ others.toList

/-- `gen_occ e = x` — `generalize e = x`, but FAILING when `e` (with its
    `_` holes) does not occur in the goal.  Plain `generalize` of a
    non-occurring pattern succeeds vacuously and leaves the holes as
    unassigned metavariables in the proof term — the kernel then rejects
    the whole theorem ("declaration has metavariables") with no tactic
    error to point at.  The generated bridge abstracts every state reader
    under `try`, and a reader can be absent from a goal (a latch of a
    second memory, say), so the vacuous case is real. -/
elab "gen_occ " e:term:51 " = " x:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let tgt ← Lean.instantiateMVars (← goal.getType)
    let e ← Lean.Elab.Tactic.elabTerm e none
    let abst ← Lean.Meta.kabstract tgt e
    unless abst.hasLooseBVars do
      throwError "gen_occ: pattern does not occur in the goal"
    let e ← Lean.instantiateMVars e
    if e.hasMVar then
      throwError "gen_occ: pattern still has metavariables after matching"
    let (_, goal') ← goal.generalize #[{ expr := e, xName? := x.getId, hName? := none }]
    Lean.Elab.Tactic.replaceMainGoal [goal']

set_option maxHeartbeats 1000000 in
-- the generator is one long `do` block; its desugaring exceeds the
-- default recursion depth
set_option maxRecDepth 8192 in
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
  -- Every generated theorem is elaborated and kernel-checked
  -- SYNCHRONOUSLY (`set_option Elab.async false in`): the sorryAx /
  -- kernel audit below reads the constant right after its command, and
  -- an asynchronously elaborated theorem is not there yet (the audit
  -- then silently passed, or reported a kernel-rejected proof PROVEN).
  -- every generated declaration: synchronous (a failed or kernel-rejected
  -- one is then ABSENT, so the audit's lookup throws) and with the
  -- recursion depth raised — a `match i with | ⟨0, _⟩ … | ⟨17, _⟩` over
  -- `Fin 18` (a real IP's 13 registers + 5 inputs) exhausts the default
  -- depth in the match compiler ("Missing cases")
  let elabSync (c : Lean.TSyntax `command) : CommandElabM Unit := do
    elabCommand (← `(set_option maxRecDepth 65536 in
      set_option Elab.async false in $c:command))
  let declName ← liftTermElabM <|
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  let design ← liftTermElabM
    (Sparkle.Compiler.Elab.synthesizeHierarchical declName)
  let m ← match design.modules with
    | [m] => pure m
    | _ => throwError "#verify_elab_deep: single-module designs only"
  let regsOnly := theRegisters m
  if (← IO.getEnv "SPARKLE_DEEP_DEBUG").isSome then
    logInfo m!"#verify_elab_deep STAGE ok: synthesis + single module"
  -- Synchronous single-port memories (`Signal.memory`): contents state
  -- plus a read latch.  The latch wire becomes a STATE SLOT after the
  -- registers (init 0; its "cone" is the read address, a `.latch`).
  let memsRaw := m.body.filterMap fun st => match st with
    | .memory name aw dw _ wa wd we ra rd cr ew er =>
      some (name, aw, dw, wa, wd, we, ra, rd, cr, ew.length + er.length)
    | _ => none
  for (name, _, _, _, _, _, _, _, _, extra) in memsRaw do
    if extra != 0 then throwError "#verify_elab_deep: memory {name}: multi-port memories are outside the deep grammar"
  -- all memories, in body order (`Γm` index = position here)
  let mems : List (String × Nat × Nat × Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr
      × Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr × String) :=
    memsRaw.map fun (name, aw, dw, wa, wd, we, ra, rd, _, _) => (name, aw, dw, wa, wd, we, ra, rd)
  let memCr : List Bool := memsRaw.map fun (_, _, _, _, _, _, _, _, cr, _) => cr
  let memClks : List String := m.body.filterMap fun st => match st with
    | .memory _ _ _ clk _ _ _ _ _ _ _ _ => some clk
    | _ => none
  let hasMem := !mems.isEmpty
  let nM := mems.length
  -- synchronous reads: a latch STATE slot per memory (after the
  -- registers); combinational reads (`Signal.memoryComboRead`): a READ
  -- slot per memory (after the inputs), valued from the contents
  let syncIdx : List Nat := (List.range nM).filter fun kk => !memCr[kk]!
  let comboIdx : List Nat := (List.range nM).filter fun kk => memCr[kk]!
  let nC := comboIdx.length
  let hasCombo := nC > 0
  let nReg := regsOnly.length
  let regs : List (String × Sparkle.IR.AST.Expr × Int) :=
    regsOnly ++ syncIdx.map fun kk =>
      let (_, _, _, _, _, _, ra, rd) := mems[kk]!
      (rd, ra, (0 : Int))
  let nR := regs.length
  if nR == 0 then throwError "#verify_elab_deep: no registers"
  let ins := dataInputs m
  let nI := ins.length
  let wt := widthTable m
  let regWs := (regsOnly.map fun (n, _, _) => wt.getD n 0)
    ++ syncIdx.map fun kk => (mems[kk]!).2.2.1
  let inWs := ins.map fun (_, w) => w
  -- read slots: (memory index, read-data wire, read address, widths)
  let combos : List (Nat × String × Sparkle.IR.AST.Expr × Nat × Nat) := comboIdx.map fun kk =>
    let (_, aw, dw, _, _, _, ra, rd) := mems[kk]!
    (kk, rd, ra, aw, dw)
  let comboWs := combos.map fun (_, _, _, _, dw) => dw
  let stopAt : Std.HashMap String Bool :=
    (ins.foldl (fun (h : Std.HashMap String Bool) (n, _) =>
      h.insert n true) {})
    |> regs.foldl (fun h (n, _, _) => h.insert n true)
    |> combos.foldl (fun h (_, rd, _, _, _) => h.insert rd true)
  let dm := buildDefMap m.body
  let slotIdx : String → Option Nat := fun s =>
    match (regs.map (·.1)).idxOf? s with
    | some i => some i
    | none => match (ins.map (·.1)).idxOf? s with
      | some j => some (nR + j)
      | none => (combos.map (·.2.1)).idxOf? s |>.map (· + nR + nI)
  let conesIR ← regs.mapM fun (n, input, _) => do
    match Tools.ConeFold.inlineConeT dm stopAt 10000 input with
    | .ok c => pure (Tools.ConeFold.resolveSlicesT wt 10000 c)
    | .error e => throwError "#verify_elab_deep: cone of {n}: {e}"
  let cones ← conesIR.mapM (toCExpr slotIdx)
  -- write ports (address, data, enable) per memory, as resolved cones
  let memConesIR ← mems.mapM fun (name, _, _, wa, wd, we, _, _) => do
    let cone (e : Sparkle.IR.AST.Expr) : CommandElabM Sparkle.IR.AST.Expr :=
      match Tools.ConeFold.inlineConeT dm stopAt 10000 e with
      | .ok c => pure (Tools.ConeFold.resolveSlicesT wt 10000 c)
      | .error err => throwError "#verify_elab_deep: write port of memory {name}: {err}"
    pure (← cone wa, ← cone wd, ← cone we)
  let memCs ← memConesIR.mapM fun (wa, wd, we) => do
    pure (← toCExpr slotIdx wa, ← toCExpr slotIdx wd, ← toCExpr slotIdx we)
  -- combinational read addresses: resolved cones over registers and
  -- inputs ONLY (a read address reading another combinational read is
  -- outside v1 — the read slots are valued before the cones see them)
  let comboConesIR ← combos.mapM fun (_, rd, ra, _, _) => do
    match Tools.ConeFold.inlineConeT dm stopAt 10000 ra with
    | .ok c =>
      let c := Tools.ConeFold.resolveSlicesT wt 10000 c
      for (_, rd', _, _, _) in combos do
        if (Sparkle.IR.Reorder.refsOf c).contains rd' then
          throwError "#verify_elab_deep: the read address of {rd} reads the combinational read {rd'} — outside the deep grammar (v1)"
      pure c
    | .error e => throwError "#verify_elab_deep: read address of {rd}: {e}"
  let comboCs ← comboConesIR.mapM (toCExpr slotIdx)
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
  let memSigT : Array Term ← mems.toArray.mapM fun (_, aw, dw, _, _, _, _, _) =>
    `((($(quote aw), $(quote dw)) : Nat × Nat))
  let ΓmT : Term ← `([$memSigT,*])
  let comboWsT : Array Term := comboWs.toArray.map fun w => quote w
  let ΓcT : Term ← `(([$comboWsT,*] : List Nat))
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
          if dty.hasFVar then
            throwError "#verify_elab_deep: parameter type mentions an earlier binder (dependent DSL signature): {dty}"
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
  if (← IO.getEnv "SPARKLE_DEEP_DEBUG").isSome then
    logInfo m!"#verify_elab_deep STAGE ok: param types + retTy"
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
  -- CdoM form: register slots are cones, latch slots read their memory
  let nextArmsM ← (List.range nR).toArray.mapM fun i => do
    if i < nReg then
      `(Lean.Parser.Term.matchAltExpr|
        | ⟨$(quote i), _⟩ => NextM.cone $(cones[i]!))
    else
      `(Lean.Parser.Term.matchAltExpr|
        | ⟨$(quote i), _⟩ => NextM.latch ⟨$(quote syncIdx[i - nReg]!), by decide⟩ $(cones[i]!))
  let writesArms ← (List.range nM).toArray.mapM fun k => do
    let (wa, wd, we) := memCs[k]!
    `(Lean.Parser.Term.matchAltExpr|
      | ⟨$(quote k), _⟩ => ($wa, $wd, $we))
  -- read slots: memory index and address cone; the width side condition
  -- (`hreads`) is `rfl` slot by slot
  let readsArms ← (List.range nC).toArray.mapM fun c => do
    let (kk, _, _, _, _) := combos[c]!
    `(Lean.Parser.Term.matchAltExpr|
      | ⟨$(quote c), _⟩ => ⟨⟨$(quote kk), by decide⟩, $(comboCs[c]!)⟩)
  let hreadsArms ← (List.range nC).toArray.mapM fun c => do
    `(Lean.Parser.Term.matchAltExpr| | ⟨$(quote c), _⟩ => rfl)
  let readsFn : Term ← if nC == 0 then `(fun c => Fin.elim0 c)
    else `(fun c => match c with $readsArms:matchAlt*)
  let hreadsFn : Term ← if nC == 0 then `(fun c => Fin.elim0 c)
    else `(fun c => match c with $hreadsArms:matchAlt*)
  -- the cone context: registers, inputs, then the read slots (CdoM)
  let ΓAllT : Term ← if hasMem then `(($ΓrT ++ $ΓiT ++ $ΓcT : List Nat))
    else `(($ΓrT ++ $ΓiT : List Nat))
  -- slot names
  let nmArms ← (List.range (nR + nI + nC)).toArray.mapM fun i => do
    let s := if i < nR then (regs[i]!).1
      else if i < nR + nI then (ins[i - nR]!).1
      else (combos[i - nR - nI]!).2.1
    `(Lean.Parser.Term.matchAltExpr| | ⟨$(quote i), _⟩ => $(quote s))
  -- The arms match on the `Fin` PATTERN (`⟨i, _⟩`) with NO catch-all.
  -- Both alternatives were tried and both break the bridge: matching on
  -- `i.val` stops `nm ⟨i, _⟩` from iota-reducing (the pointwise reader
  -- proofs are `rfl` on it), and appending `| _ => ""` defeats the
  -- `simp` that discharges the "n is none of the slots" reader.  The
  -- consequence is a hard slot ceiling: past 15 arms the match compiler
  -- stops enumerating `Fin` literals and reports the tail as a missing
  -- case, so a circuit with ≥ 16 state slots + inputs (the memcached
  -- engine: 13 + 5) cannot be reified yet.  The fix is a name table
  -- that is not a `match` at all (a `List String` with `getD`, whose
  -- lookups reduce by `decide`) — a separate change.
  elabSync (← `(def $nmId :
      Fin (($ΓAllT).length) → String := fun i =>
    match i with $nmArms:matchAlt*))
  -- the names restricted to registers and inputs (read addresses are
  -- compiled with these) and their agreement with `nm`
  let nm0Id := mkI s!"{base}_nm0"
  let nm0EqId := mkI s!"{base}_nm0_eq"
  if hasCombo then
    let nm0Arms ← (List.range (nR + nI)).toArray.mapM fun i => do
      let s := if i < nR then (regs[i]!).1 else (ins[i - nR]!).1
      `(Lean.Parser.Term.matchAltExpr| | ⟨$(quote i), _⟩ => $(quote s))
    elabSync (← `(def $nm0Id :
        Fin (($ΓrT ++ $ΓiT : List Nat).length) → String := fun i =>
      match i with $nm0Arms:matchAlt*))
    elabSync (← `(theorem $nm0EqId : ∀ i : Fin (($ΓrT ++ $ΓiT : List Nat).length),
        $nm0Id i = $nmId ⟨i.val, by have := i.isLt; simp only [List.length_append] at *; omega⟩ := by
      decide))
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
    elabSync (← `(def $inpId :
        ∀ j : Fin ($ΓiT : List Nat).length,
          Sparkle.Core.Signal.Signal
            Sparkle.Core.Domain.defaultDomain
            (BitVec (($ΓiT : List Nat).get j)) :=
      fun j => nomatch j))
  else
    elabSync (← `(def $inpId $paramBinders* :
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
    elabSync (← `(theorem $atId $paramBinders* (tv : Nat) :
      ($inpId $appArgs* $(quote j)).val tv = $rhs := rfl))
    -- the applied index appears in BOTH OfNat-literal and Fin.mk
    -- forms depending on which normalization reached it; cover both
    let atMkId := mkI s!"{base}_inp_at_mk_{j}"
    elabSync (← `(theorem $atMkId $paramBinders* (tv : Nat) :
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
  if (← IO.getEnv "SPARKLE_DEEP_DEBUG").isSome then
    logInfo m!"#verify_elab_deep STAGE ok: helpers collected"
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
        -- `have x := v; body` is NOT a `letE`: it elaborates to
        -- `letFun`, an application of `letFun` whose body is a lambda.
        -- Missing this made the walk stop at the `have` and report
        -- `unknown free variable` downstream instead of finding the
        -- loop — the register-init-from-a-value-parameter defect.
        | _ =>
          if e.getAppFn.isConstOf ``letFun then
            match e.getAppArgs with
            | #[_, _, v, body] => findRC (body.headBeta.instantiate1 v) fuel
            | _ => none
          else
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
        if ty.hasFVar then
          throwError "#verify_elab_deep: loop element type mentions a local binder: {ty}"
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
  if (← IO.getEnv "SPARKLE_DEEP_DEBUG").isSome then
    logInfo m!"#verify_elab_deep STAGE ok: loop nodes discovered"
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
  if (← IO.getEnv "SPARKLE_DEEP_DEBUG").isSome then
    logInfo m!"#verify_elab_deep STAGE ok: pre-port setup (nm, inp, cones)"
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
    let writesEqId := mkI s!"{base}{suffix}_deep_writes"
    let minitsEqId := mkI s!"{base}{suffix}_deep_minits"
    let readsEqId := mkI s!"{base}{suffix}_deep_reads"
    if hasMem then
      elabSync (← `(def $deepId : CdoM $ΓrT $ΓiT $ΓmT $ΓcT $(quote wOut) where
        inits := fun i => match i with $initArms:matchAlt*
        minits := fun _ _ => 0
        reads := $readsFn
        hreads := $hreadsFn
        next := fun i => match i with $nextArmsM:matchAlt*
        writes := fun k => match k with $writesArms:matchAlt*
        out := $outC))
      if hasCombo then
        elabSync (← `(theorem $readsEqId :
          CdoM.reads $deepId = $readsFn := rfl))
      elabSync (← `(theorem $nextEqId :
        CdoM.next $deepId = fun i => match i with $nextArmsM:matchAlt* := rfl))
      elabSync (← `(theorem $initsEqId :
        CdoM.inits $deepId = fun i => match i with $initArms:matchAlt* := rfl))
      elabSync (← `(theorem $writesEqId :
        CdoM.writes $deepId = fun k => match k with $writesArms:matchAlt* := rfl))
      elabSync (← `(theorem $minitsEqId :
        CdoM.minits $deepId = fun _ _ => 0 := rfl))
      elabSync (← `(theorem $outEqId : CdoM.out $deepId = $outC := rfl))
    else
      elabSync (← `(def $deepId : Cdo $ΓrT $ΓiT $(quote wOut) where
        inits := fun i => match i with $initArms:matchAlt*
        next := fun i => match i with $nextArms:matchAlt*
        out := $outC))
      -- projection equations (rfl): rewrite `f_deep.next` etc. WITHOUT
      -- ever exposing the anonymous structure literal — a literal that
      -- appears in some hypotheses but not others (the pack references
      -- the NAME) leaves simp_all unable to see two forms of one fact
      elabSync (← `(theorem $nextEqId :
        Cdo.next $deepId = fun i => match i with $nextArms:matchAlt* := rfl))
      elabSync (← `(theorem $initsEqId :
        Cdo.inits $deepId = fun i => match i with $initArms:matchAlt* := rfl))
      elabSync (← `(theorem $outEqId : Cdo.out $deepId = $outC := rfl))
    -- FIDELITY: the compiled reification IS the elaborated cone.
    -- Without this the capstone talks about `compile (toCExpr cone)`,
    -- an intended-identical but unverified twin of the elaborator's
    -- actual IR.  toCExpr's normalizations (n-ary concat → nested
    -- cats, gt/ge → mirrored lt/le) make it fail LOUDLY where compile
    -- can't reproduce the original.  Register cones are checked once
    -- (they're shared syntax across the per-port Cdos).
    let fidIds ← if k == 0 then
        (List.range nR).toArray.filterMapM fun i => do
          let fidId := mkI s!"{base}{suffix}_deep_fidelity_r{i}"
          let coneQ ← quoteIR (Tools.ConcatNorm.concatNorm 10000 conesIR[i]!)
          if hasMem then
            if i < nReg then
              elabSync (← `(theorem $fidId :
                NextM.compileCone $nmId (CdoM.next $deepId ⟨$(quote i), by decide⟩)
                  = some $coneQ := by
                simp only [$nextEqId:ident, NextM.compileCone, CExpr.compile, $nmId:ident]
                all_goals (first | rfl | (simp; done) | (simp; rfl))))
              pure (some fidId)
            else
              -- latch slot: the reified read address compiles back to the
              -- elaborated address cone, and the slot IS that latch
              -- the address is ascribed the memory's address width (the
              -- type the slot's `latchAddr?` carries), so the replay's
              -- rewrites match syntactically
              let kk := syncIdx[i - nReg]!
              let compT ← `(@CExpr.compile $ΓAllT
                (($ΓmT : List MemSig).get ⟨$(quote kk), by decide⟩).1
                $nmId $(cones[i]!))
              elabSync (← `(theorem $fidId :
                $compT = $coneQ := by
                simp only [CExpr.compile, $nmId:ident]
                all_goals (first | rfl | (simp; done) | (simp; rfl))))
              let fidLId := mkI s!"{base}{suffix}_deep_fidelity_latch{i}"
              elabSync (← `(theorem $fidLId :
                NextM.latchAddr? (CdoM.next $deepId ⟨$(quote i), by decide⟩)
                  = some ⟨⟨$(quote kk), by decide⟩, $(cones[i]!)⟩ := by
                first
                  | rfl
                  | (simp only [$nextEqId:ident, NextM.latchAddr?])))
              pure (some fidId)
          else
            elabSync (← `(theorem $fidId :
              CExpr.compile $nmId (Cdo.next $deepId ⟨$(quote i), by decide⟩)
                = $coneQ := by
              simp only [$nextEqId:ident, CExpr.compile, $nmId:ident]
              -- residual `Expr.const v (Γr.get ⟨i, _⟩) = Expr.const v w`
              -- width shapes: closed, so `rfl`; simp alone strands
              -- `Fin.val` of literals ≥ 3 (no `Fin.val_three`)
              all_goals (first | rfl | (simp; done) | (simp; rfl))))
            pure (some fidId)
      else pure #[]
    let fidLIds : Array Ident := if k == 0 && hasMem then
        (List.range nR).toArray.filterMap fun i =>
          if i < nReg then none else some (mkI s!"{base}{suffix}_deep_fidelity_latch{i}")
      else #[]
    -- read-address fidelity (combinational reads): the reified address
    -- compiles (with the register/input names) back to the elaborated cone
    let fidCIds ← if k == 0 && hasCombo then
        (List.range nC).toArray.mapM fun c => do
          let (kk, _, _, _, _) := combos[c]!
          let fidId := mkI s!"{base}{suffix}_deep_fidelity_c{c}"
          let coneQ ← quoteIR (Tools.ConcatNorm.concatNorm 10000 comboConesIR[c]!)
          let compT ← `(@CExpr.compile ($ΓrT ++ $ΓiT)
            (($ΓmT : List MemSig).get ⟨$(quote kk), by decide⟩).1
            $nm0Id $(comboCs[c]!))
          elabSync (← `(theorem $fidId : $compT = $coneQ := by
            simp only [CExpr.compile, $nm0Id:ident]
            all_goals (first | rfl | (simp; done) | (simp; rfl))))
          pure fidId
      else pure #[]
    -- write-port fidelity (memories): the reified address/data/enable
    -- cones compile back to the elaborated ones
    let fidMemIds ← if k == 0 && hasMem then
        (List.range nM).toArray.flatMapM fun kk => do
          let (waIR, wdIR, weIR) := memConesIR[kk]!
          let mk (tag : String) (ir : Sparkle.IR.AST.Expr) (proj : Term) : CommandElabM Ident := do
            let fid := mkI s!"{base}{suffix}_deep_fidelity_m{kk}_{tag}"
            let q ← quoteIR (Tools.ConcatNorm.concatNorm 10000 ir)
            elabSync (← `(theorem $fid :
              CExpr.compile $nmId $proj = $q := by
              simp only [$writesEqId:ident, CExpr.compile, $nmId:ident]
              all_goals (first | rfl | (simp; done) | (simp; rfl))))
            pure fid
          let a ← mk "wa" waIR (← `((CdoM.writes $deepId ⟨$(quote kk), by decide⟩).1))
          let d ← mk "wd" wdIR (← `((CdoM.writes $deepId ⟨$(quote kk), by decide⟩).2.1))
          let e ← mk "we" weIR (← `((CdoM.writes $deepId ⟨$(quote kk), by decide⟩).2.2))
          pure #[a, d, e]
      else pure #[]
    let fidOutId := mkI s!"{base}{suffix}_deep_fidelity_out"
    let outQ ← quoteIR (Tools.ConcatNorm.concatNorm 10000 outIR)
    if hasMem then
      elabSync (← `(theorem $fidOutId :
        CExpr.compile $nmId (CdoM.out $deepId) = $outQ := by
        simp only [$outEqId:ident, CExpr.compile, $nmId:ident]
        all_goals (first | rfl | (simp; done) | (simp; rfl))))
    else
      elabSync (← `(theorem $fidOutId :
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
    -- For a memory-bearing body the combinational seam facts are stated
    -- over the body WITHOUT its memory statements (`stripSyncMem`: a
    -- synchronous memory is a no-op for `evalAssigns`), which is
    -- memory-free and hence inside the seam theorems' premises; the
    -- state step (regstep/memstep) keeps the full body.
    let weMId := mkI s!"{base}_deep_weM"
    let bodyId := mkI s!"{base}_deep_body"
    let stopLId := mkI s!"{base}_deep_stopL"
    let stopAtMId := mkI s!"{base}_deep_stopAtM"
    let wtLId := mkI s!"{base}_deep_wtL"
    let wtMId := mkI s!"{base}_deep_wtM"
    let bodyCId := mkI s!"{base}_deep_bodyC"
    let bodyC : Term ← if hasCombo then `($bodyCId)
      else if hasMem then `(Tools.ConeFold.stripSyncMem $bodyId)
      else `($bodyId)
    -- with combinational reads: the body without ANY memory statement
    -- (`bodyC`), and for each combinational read, in body order, the
    -- prefix/suffix around its statement in the successively stripped
    -- body (`_deep_bodyP{c}` / `_deep_bodyQ{c}`)
    let topoBody := deepOrderBody m.body
    let comboSplits : List (List Sparkle.IR.AST.Stmt × List Sparkle.IR.AST.Stmt) := Id.run do
      let mut cur := Tools.ConeFold.stripSyncOnly topoBody
      let mut out := []
      for (_, rd, _, _, _) in combos do
        let idx := cur.findIdx fun st => match st with
          | .memory _ _ _ _ _ _ _ _ rd' _ _ _ => rd' == rd
          | _ => false
        let pre := cur.take idx
        let post := cur.drop (idx + 1)
        out := out ++ [(pre, post)]
        cur := pre ++ post
      return out
    let bodyCList : List Sparkle.IR.AST.Stmt :=
      (Tools.ConeFold.stripSyncMem topoBody).filter fun st => match st with
        | .memory .. => false
        | _ => true
    let addStmtList (id : Ident) (l : List Sparkle.IR.AST.Stmt) : CommandElabM Unit := do
      liftCoreM <| addAndCompile <| .defnDecl {
        name := id.getId, levelParams := []
        type := mkApp (mkConst ``List [levelZero]) (mkConst ``Sparkle.IR.AST.Stmt)
        value := toExpr l, hints := .abbrev, safety := .safe }
      liftCoreM <| Lean.enableRealizationsForConst id.getId
    let outT0 : Term ← if hasMem then `(CdoM.out $deepId) else `(Cdo.out $deepId)
    let addExprConst (id : Ident) (e : Sparkle.IR.AST.Expr) : CommandElabM Unit := do
      liftCoreM <| addAndCompile <| .defnDecl {
        name := id.getId, levelParams := []
        type := mkConst ``Sparkle.IR.AST.Expr
        value := toExpr e, hints := .abbrev, safety := .safe }
      liftCoreM <| Lean.enableRealizationsForConst id.getId
    -- one G1 lemma: `lhs` is the compiled reification (or its literal),
    -- `hnormTac` proves `lhs = concatNorm cone`, `eIn` the IR expression
    -- whose cone `coneRaw` is (the inlining hypothesis is recomputed)
    let mkG1 (g1Id : Ident) (lhs : Term) (hnormTac : Lean.TSyntax `tactic)
        (coneRawId coneId : Ident) (eIn : Term) : CommandElabM Unit := do
      elabSync (← `(theorem $g1Id (env : Sparkle.IR.Semantics.Env) :
          Sparkle.IR.Semantics.evalExpr
              (weOfC $nmId (fun j => ($ΓAllT).get j))
              env $lhs
            = Sparkle.IR.Semantics.evalExpr $weMId env $coneId := by
        have hnorm : $lhs = Tools.ConcatNorm.concatNorm 10000 $coneId := by
          $hnormTac:tactic
        have hinl : Tools.ConeFold.inlineConeT
            (Sparkle.IR.Optimize.buildDefMap $bodyC) $stopAtMId 10000
            $eIn = .ok $coneRawId := by native_decide
        have hres : $coneId
            = Tools.ConeFold.resolveSlicesT $wtMId 10000 $coneRawId := by
          native_decide
        have hag : ∀ n ∈ $stopLId,
            (weOfC $nmId (fun j => ($ΓAllT).get j)) n
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
          (Sparkle.IR.Optimize.buildDefMap $bodyC) $stopAtMId 10000
          $eIn $coneRawId hinl n
          (Tools.ConeFold.resolveSlicesT_refs $wtMId 10000 $coneRawId
            n h1)
        have hmem : n ∈ $stopLId := by
          rcases Tools.ConeFold.stopFold_mem $stopLId {} n href
            with h | h
          · exact h
          · simp at h
        exact hag n hmem))
    if k == 0 then
      let weBody ← do
        let mut acc ← `((0 : Nat))
        for (n, w) in wt.toList do
          acc ← `(if n == $(quote n) then $(quote w) else $acc)
        pure acc
      elabSync (← `(def $weMId : Sparkle.IR.Semantics.WEnv :=
        fun n => $weBody))
      liftCoreM <| addAndCompile <| .defnDecl {
        name := bodyId.getId, levelParams := []
        type := mkApp (mkConst ``List [levelZero])
          (mkConst ``Sparkle.IR.AST.Stmt)
        value := toExpr (deepOrderBody m.body),
        hints := .abbrev, safety := .safe }
      liftCoreM <| Lean.enableRealizationsForConst bodyId.getId
      if hasCombo then
        addStmtList bodyCId bodyCList
        for c in List.range nC do
          let (pre, post) := comboSplits[c]!
          addStmtList (mkI s!"{base}_deep_bodyP{c}") pre
          addStmtList (mkI s!"{base}_deep_bodyQ{c}") post
      let stopL : List String := (ins.map (·.1)) ++ (regs.map (·.1))
        ++ (combos.map (·.2.1))
      liftCoreM <| addAndCompile <| .defnDecl {
        name := stopLId.getId, levelParams := []
        type := mkApp (mkConst ``List [levelZero]) (mkConst ``String)
        value := toExpr stopL, hints := .abbrev, safety := .safe }
      liftCoreM <| Lean.enableRealizationsForConst stopLId.getId
      elabSync (← `(def $stopAtMId : Std.HashMap String Bool :=
        ($stopLId).foldl (fun h n => h.insert n true) {}))
      liftCoreM <| addAndCompile <| .defnDecl {
        name := wtLId.getId, levelParams := []
        type := mkApp (mkConst ``List [levelZero])
          (mkApp2 (mkConst ``Prod [levelZero, levelZero])
            (mkConst ``String) (mkConst ``Nat))
        value := toExpr wt.toList, hints := .abbrev, safety := .safe }
      liftCoreM <| Lean.enableRealizationsForConst wtLId.getId
      elabSync (← `(def $wtMId : Std.HashMap String Nat :=
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
        addExprConst coneRawId craw
        addExprConst coneId conesIR[i]!
        addExprConst regInId input
        let fidId := fidIds[i]!
        let g1Id := mkI s!"{base}_deep_coneEval_r{i}"
        if !hasMem then
          mkG1 g1Id (← `(CExpr.compile $nmId (Cdo.next $deepId ⟨$(quote i), by decide⟩)))
            (← `(tactic| (rw [$fidId:ident]; native_decide))) coneRawId coneId (← `($regInId))
        else if i < nReg then
          -- cone slot of a CdoM: fidelity is `compileCone … = some lit`,
          -- so G1 is stated over the literal itself
          let coneQ ← quoteIR (Tools.ConcatNorm.concatNorm 10000 conesIR[i]!)
          mkG1 g1Id coneQ (← `(tactic| native_decide)) coneRawId coneId (← `($regInId))
        else
          -- latch slot: over the compiled read address (ascribed as in
          -- its fidelity theorem)
          let compT ← `(@CExpr.compile $ΓAllT
            (($ΓmT : List MemSig).get ⟨$(quote syncIdx[i - nReg]!), by decide⟩).1
            $nmId $(cones[i]!))
          mkG1 g1Id compT
            (← `(tactic| (rw [$fidId:ident]; native_decide))) coneRawId coneId (← `($regInId))
      -- write ports: address / data / enable cones of every memory
      if hasMem then
        for kk in List.range nM do
          let (name, _, _, waIR, wdIR, weIR, _, _) := mems[kk]!
          let (waC, wdC, weC) := memConesIR[kk]!
          let portG1 (tag : String) (portIR coneIR : Sparkle.IR.AST.Expr) (proj : Term) :
              CommandElabM Unit := do
            let coneRawId := mkI s!"{base}_deep_coneRaw_m{kk}_{tag}"
            let coneId := mkI s!"{base}_deep_cone_m{kk}_{tag}"
            let portInId := mkI s!"{base}_deep_portIn_m{kk}_{tag}"
            let craw ← match Tools.ConeFold.inlineConeT dm stopAt 10000 portIR with
              | .ok c => pure c
              | .error e => throwError "#verify_elab_deep bridge: write port {tag} of memory {name}: {e}"
            addExprConst coneRawId craw
            addExprConst coneId coneIR
            addExprConst portInId portIR
            let fidId := mkI s!"{base}{suffix}_deep_fidelity_m{kk}_{tag}"
            let g1Id := mkI s!"{base}_deep_coneEval_m{kk}_{tag}"
            mkG1 g1Id (← `(CExpr.compile $nmId $proj))
              (← `(tactic| (rw [$fidId:ident]; native_decide))) coneRawId coneId (← `($portInId))
          portG1 "wa" waIR waC (← `((CdoM.writes $deepId ⟨$(quote kk), by decide⟩).1))
          portG1 "wd" wdIR wdC (← `((CdoM.writes $deepId ⟨$(quote kk), by decide⟩).2.1))
          portG1 "we" weIR weC (← `((CdoM.writes $deepId ⟨$(quote kk), by decide⟩).2.2))
        -- read addresses (combinational reads)
        for c in List.range nC do
          let (kk, rd, raIR, _, _) := combos[c]!
          let coneRawId := mkI s!"{base}_deep_coneRaw_c{c}"
          let coneId := mkI s!"{base}_deep_cone_c{c}"
          let portInId := mkI s!"{base}_deep_portIn_c{c}"
          let craw ← match Tools.ConeFold.inlineConeT dm stopAt 10000 raIR with
            | .ok cc => pure cc
            | .error e => throwError "#verify_elab_deep bridge: read address of {rd}: {e}"
          addExprConst coneRawId craw
          addExprConst coneId comboConesIR[c]!
          addExprConst portInId raIR
          let fidId := mkI s!"{base}{suffix}_deep_fidelity_c{c}"
          let g1Id := mkI s!"{base}_deep_coneEval_c{c}"
          let compT ← `(@CExpr.compile ($ΓrT ++ $ΓiT)
            (($ΓmT : List MemSig).get ⟨$(quote kk), by decide⟩).1
            $nm0Id $(comboCs[c]!))
          mkG1 g1Id compT (← `(tactic| (rw [$fidId:ident]; native_decide)))
            coneRawId coneId (← `($portInId))
    -- per-port: the output cone's G1
    let outConeRawId := mkI s!"{base}{suffix}_deep_coneRaw_out"
    let outConeId := mkI s!"{base}{suffix}_deep_cone_out"
    let outRawIR ← match Tools.ConeFold.inlineConeT dm stopAt 10000
        (.ref portName) with
      | .ok c => pure c
      | .error e => throwError "#verify_elab_deep bridge: out cone: {e}"
    addExprConst outConeRawId outRawIR
    addExprConst outConeId outIR
    let g1OutId := mkI s!"{base}{suffix}_deep_coneEval_out"
    mkG1 g1OutId (← `(CExpr.compile $nmId $outT0))
      (← `(tactic| (rw [$fidOutId:ident]; native_decide))) outConeRawId outConeId
      (← `(Sparkle.IR.AST.Expr.ref $(quote portName)))
    -- readers + Signal-side bridge + capstone, as its own compilation
    -- unit (see replayBlock below); it hands the replay the LHS signal
    let rec bridgeBlock : Unit → CommandElabM (Option Term) := fun _ => do
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
      -- (the memory contents readers' lemmas are appended below, once the
      -- readers exist; see `rdZeroAll` / `rdSuccAll`)
      let gIds : Array Ident := (List.range nR).toArray.map fun i =>
        mkI s!"g{i}"
      let addrId := mkI "addr"
      let mdIds : Array Ident := (List.range nM).toArray.map fun kk =>
        mkI s!"{base}{suffix}_deep_md{kk}"
      -- shallow terms over registers and inputs only (read addresses)
      let shallowAt0 (tv : Term) (e : Sparkle.IR.AST.Expr) :
          CommandElabM Term :=
        toShallow slotIdx nR nI
          (fun i => do let rdId : Ident := rdIds[i]!; `(($rdId $appArgs* $tv)))
          (fun j => inpValRhs[j]! tv)
          (fun c => throwError "#verify_elab_deep: read slot {c} inside a read address") e
      -- a read slot reads the contents at its address, same cycle
      let shallowAt (tv : Term) (e : Sparkle.IR.AST.Expr) :
          CommandElabM Term :=
        toShallow slotIdx nR nI
          (fun i => do let rdId : Ident := rdIds[i]!; `(($rdId $appArgs* $tv)))
          (fun j => inpValRhs[j]! tv)
          (fun c => do
            let (kk, _, _, _, _) := combos[c]!
            let mdId : Ident := mdIds[kk]!
            let a ← shallowAt0 tv comboConesIR[c]!
            `(($mdId $appArgs* $tv $a))) e
      -- all readers first: a register's step lemma mentions every
      -- register its cone reads
      for i in List.range nR do
        let w := regWs[i]!
        let rdId : Ident := rdIds[i]!
        if hasMem then
          elabSync (← `(def $rdId $paramBinders* ($sId : Nat) :
              BitVec $(quote w) :=
            (CdoM.stateAt $deepId (fun t j => (($inpS) j).val t) $sId).1
              ⟨$(quote i), by decide⟩))
        else
          elabSync (← `(def $rdId $paramBinders* ($sId : Nat) :
              BitVec $(quote w) :=
            Cdo.stateAt $deepId (fun t j => (($inpS) j).val t) $sId
              ⟨$(quote i), by decide⟩))
      -- memory contents readers: `md_k s : BitVec aw → BitVec dw`
      for kk in List.range nM do
        let (_, aw, dw, _, _, _, _, _) := mems[kk]!
        let mdId : Ident := mdIds[kk]!
        elabSync (← `(def $mdId $paramBinders* ($sId : Nat) :
            BitVec $(quote aw) → BitVec $(quote dw) :=
          (CdoM.stateAt $deepId (fun t j => (($inpS) j).val t) $sId).2
            ⟨$(quote kk), by decide⟩))
      for i in List.range nR do
        let (_, _, init) := regs[i]!
        let w := regWs[i]!
        let rdId : Ident := rdIds[i]!
        let rdZeroId : Ident := rdZeroIds[i]!
        let rdSuccId : Ident := rdSuccIds[i]!
        elabSync (← `(theorem $rdZeroId $paramBinders* :
          $rdId $appArgs* 0
            = BitVec.ofNat $(quote w) $(quote init.toNat) := rfl))
        let rhs ← if i < nReg then shallowAt (← `($sId)) conesIR[i]!
          else do
            -- latch: the contents at the previous cycle, at the read address
            let mdId : Ident := mdIds[syncIdx[i - nReg]!]!
            let addrS ← shallowAt (← `($sId)) conesIR[i]!
            `(($mdId $appArgs* $sId $addrS))
        elabSync (← `(theorem $rdSuccId $paramBinders* ($sId : Nat) :
          $rdId $appArgs* ($sId + 1) = $rhs := rfl))
      let mdZeroIds : Array Ident := (List.range nM).toArray.map fun kk =>
        mkI s!"{base}{suffix}_deep_md{kk}_zero"
      let mdSuccIds : Array Ident := (List.range nM).toArray.map fun kk =>
        mkI s!"{base}{suffix}_deep_md{kk}_succ"
      for kk in List.range nM do
        let mdId : Ident := mdIds[kk]!
        let (waIR, wdIR, weIR) := memConesIR[kk]!
        let waS ← shallowAt (← `($sId)) waIR
        let wdS ← shallowAt (← `($sId)) wdIR
        let weS ← shallowAt (← `($sId)) weIR
        let mz : Ident := mdZeroIds[kk]!
        let ms : Ident := mdSuccIds[kk]!
        elabSync (← `(theorem $mz $paramBinders* :
          $mdId $appArgs* 0 = fun _ => 0 := rfl))
        elabSync (← `(theorem $ms $paramBinders* ($sId : Nat) :
          $mdId $appArgs* ($sId + 1)
            = fun $addrId => if $weS = 1#1 ∧ $addrId = $waS then $wdS
                else $mdId $appArgs* $sId $addrId := rfl))
      let rdZeroAll : Array Ident := rdZeroIds ++ mdZeroIds
      let rdSuccAll : Array Ident := rdSuccIds ++ mdSuccIds
      let outSId := mkI s!"{base}{suffix}_deep_outS"
      let outRhs ← shallowAt (← `($sId)) outIR
      if hasMem then
        elabSync (← `(theorem $outSId $paramBinders* ($sId : Nat) :
            (CdoM.outSig $deepId $inpS).val $sId = $outRhs := by
          show CExpr.denote _ _ = _
          rw [CdoM.stateSig_eq]
          rfl))
      else
        elabSync (← `(theorem $outSId $paramBinders* ($sId : Nat) :
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
            elabSync (← `(theorem $dupId $paramBinders* : ∀ ($nId : Nat), $stmt := by
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
              elabSync (← `(theorem $dupRId $paramBinders* ($sId : Nat) :
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
          `(tactic| all_goals (try gen_occ $rdApp = $gId))
      -- (the memory contents readers `md_k` are NOT generalized: bv_decide
      -- treats `md_k … n addr` as an atom already, and `generalize` on the
      -- function-valued partial application left an unassigned
      -- metavariable in the proof term — kernel "declaration has
      -- metavariables")
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
        `(tactic| simp [loopFOf, packRegister, Signal.register, Signal.memStep, Circuit.next,
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
                  all_goals (try simp only [$[$rdZeroAll:ident],*])
                  $closers:tactic
                | succ $mId =>
                  $st1s:tactic
                  $appendFix:tactic
                  $deeper:tactic
                  all_goals (try simp only [$[$rdSuccAll:ident],*])
                  $dupSimp:tactic
                  ($[$genLines:tactic]*)
                  $closers:tactic)))
        -- memories (`memory_eq_loops`): the read latch is a one-slot loop
        -- with pack `rd_latch s`, the contents a loop with pack `md_k s`
        -- (function-valued: `funext` before the closers)
        let skip := ((← IO.getEnv "SPARKLE_DEEP_SKIP").getD "").splitOn ","
        for kk in (if skip.contains "memalts" then [] else List.range nM) do
          let mdId : Ident := mdIds[kk]!
          let pM ← `($mdId $appArgs* $sId)
          let pMI ← `($mdId $appArgs* $iId)
          -- a synchronous read adds the latch alternative; a combinational
          -- read has only the contents loop
          let latchAlt : List (Term × Term × Bool) ← match syncIdx.idxOf? kk with
            | some sp => do
              let rdL : Ident := rdIds[nReg + sp]!
              pure [(← `($rdL $appArgs* $sId), ← `($rdL $appArgs* $iId), false)]
            | none => pure []
          for (packS, packI, isContents) in latchAlt ++ [(pM, pMI, true)] do
            let st1z ← stage1 #[]
            let st1s ← stage1 #[← `($hqId $mId (Nat.lt_succ_self $mId)),
              ← `($hgId $mId (Nat.lt_succ_self $mId))]
            let deeper ← match depth with
              | 0 => `(tactic| skip)
              | d + 1 =>
                innerBlock (← `((($qId).val $iId = $packI) ∧ $gBody))
                  (← `((fun $iId $hiId => ⟨$hqId $iId (by omega), $hgId $iId (by omega)⟩))) d (lvl + 1)
            let fx ← if isContents && !skip.contains "funext" then
                `(tactic| all_goals (try funext $addrId:ident))
              else `(tactic| skip)
            alts := alts.push (← `(tactic| (
              rw [loop_trace_guardedP_at _ (fun $sId => $packS) (fun $iId => $gBody) ?$hsId _ $guard]
              case $hsId:ident =>
                intro $uId:ident $qId:ident $hqId:ident $hgId:ident
                cases $uId:ident with
                | zero =>
                  $st1z:tactic
                  $appendFix:tactic
                  all_goals (try simp only [$[$rdZeroAll:ident],*])
                  $fx:tactic
                  $closers:tactic
                | succ $mId =>
                  $st1s:tactic
                  $appendFix:tactic
                  $deeper:tactic
                  all_goals (try simp only [$[$rdSuccAll:ident],*])
                  $dupSimp:tactic
                  $fx:tactic
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
      -- memories become loops for the bridge (`Signal.memory_eq_loops`)
      let outUnfoldIds : Array Ident := if hasMem then
          outUnfoldIds.push (mkIdent ``Sparkle.Core.Signal.Signal.memory_eq_loops)
        else outUnfoldIds
      let outUnfoldIds : Array Ident := if hasCombo then
          outUnfoldIds.push (mkIdent ``Sparkle.Core.Signal.Signal.memoryComboRead_eq_loop)
        else outUnfoldIds
      -- The top loop, per candidate block: abstract the loop signal as
      -- `L`, prove its trace once (`hLt`, via loop_trace_at with the
      -- step recipe — nested loops inside the step are discharged with
      -- the `hpre` prefix as guard), then the output side against the
      -- shallow output equation, with `hLt` itself as the guard for the
      -- nested loops the output reads.
      let retTyStx : Term ← liftTermElabM do
        if retTy.hasFVar then
          throwError "#verify_elab_deep: return type mentions a local binder: {retTy}"
        Lean.PrettyPrinter.delab retTy
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
        -- term nesting needs at most two levels per nested circuit (its
        -- input carries the enclosing loop's term) and one below a memory
        -- latch (it reads the contents loop); the script has
        -- (#alternatives)^depth leaves, so also cap by size
        let nAlts := nAlts + 2 * nM
        let want := (if nestedNodes.isEmpty then 0 else 2 * nestedNodes.size + 1)
          + (if hasMem then 2 else 0) + (if hasCombo then 1 else 0)
        let depth := Id.run do
          let mut d := 0
          for k in [1:6] do
            if k ≤ want && nAlts ^ k ≤ 64 then d := k
          return max d (if hasMem then 1 else 0)
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
              all_goals (try simp only [$[$rdZeroAll:ident],*])
              $closers:tactic
            | succ $nId =>
              $st1s:tactic
              $appendFix:tactic
              $innerHpre:tactic
              -- stage 2: one step of the spec recurrence, as the shallow
              -- literal-width expressions over the readers at cycle n
              all_goals (try simp only [$[$rdSuccAll:ident],*])
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
      -- the IR seed of the capstone: CdoM's `irEnv` (registers, inputs,
      -- read slots) or Cdo's joined state/inputs
      let irEnvT : Term ← if hasMem then
          `(CdoM.irEnv $deepId (fun t j => (($inpS) j).val t) t)
        else `(natJoin (Cdo.irState $deepId $nmId (fun t j => (($inpS) j).val t) t)
          (fun j => ((($inpS) j).val t).toNat))
      let outT : Term ← if hasMem then `(CdoM.out $deepId) else `(Cdo.out $deepId)
      let elabGenRw : Lean.TSyntax `tactic ← if hasMem then
          `(tactic| rw [← CdoM.elab_general $deepId $nmId (by decide) $inpS t])
        else `(tactic| rw [← Cdo.elab_general $deepId $nmId (by decide) $inpS t])
      let thmCmd ← `(set_option maxRecDepth 65536 in
        set_option maxHeartbeats 1600000 in
        theorem $thId $paramBinders* (t : Nat) :
          (($lhsSig).val t).toNat
          = (Sparkle.IR.Semantics.evalExpr
              (weOfC $nmId (fun j => ($ΓAllT).get j))
              (envOfC $nmId $irEnvT)
              (CExpr.compile $nmId $outT)).getD 0 := by
        $elabGenRw:tactic
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
        return none
      elabSync thmCmd
      return some lhsSig
    let some lhsSig ← bridgeBlock () | continue
    -- The per-port replay is a separate compilation unit (`let rec`
    -- lambda-lifts it): the LCNF compiler's cost on one giant do-block
    -- was superlinear (16 min and a heartbeat timeout for the whole
    -- generator).
    let rec replayBlock : Unit → CommandElabM Unit := fun _ => do
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
      let inpFam : Term ← `((fun t j => (($inpS) j).val t))
      -- the IR state recurrence of a deep circuit (Cdo / CdoM) at cycle `tt`
      let irStateAt (d : Ident) (tt : Term) : CommandElabM Term :=
        if hasMem then `(CdoM.irState $d $inpFam $tt)
        else `(Cdo.irState $d $nmId $inpFam $tt)
      -- the IR seed (as a `Fin … → Nat` valuation) of recurrence `d` at `tt`
      let irEnvAt (d : Ident) (tt : Term) : CommandElabM Term :=
        if hasMem then `(CdoM.irEnv $d $inpFam $tt)
        else `(natJoin (Cdo.irState $d $nmId $inpFam $tt) (fun j => ((($inpS) j).val $tt).toNat))
      -- the IR memory contents at cycle `tt` (memory-free: the zero MEnv)
      let memAtId := mkI s!"{base}_deep_memAt"
      let memAtZeroId := mkI s!"{base}_deep_memAt_zero"
      let memsAt (tt : Term) : CommandElabM Term :=
        if hasMem then `($memAtId $appArgs* $tt) else `((fun _ _ => (0 : Nat)))
      let irET ← irEnvAt deepId (← `(t))
      elabSync (← `(theorem $sigMId $paramBinders* (t : Nat) :
          (($lhsSig).val t).toNat
          = (Sparkle.IR.Semantics.evalExpr $weMId
              (envOfC $nmId $irET)
              $outConeId).getD 0 := by
        rw [$thId $appArgs* t, $g1OutId _]))
      -- ===== DEEP-BRIDGE REPLAY =====
      -- The #verify_elab chain (step / regstep / state_trace /
      -- signal_fold / signal_run) replayed over the general-theorem
      -- route's recurrence `Cdo.irState` / `CdoM.irState`.  The seed the
      -- deep recurrence evaluates cones in is
      -- `envOfC nm (natJoin (irState t) inp)`; pointwise readers
      -- (register / input / other) identify it with a stepModule
      -- map-state seed, boundedness comes free from the BitVec state
      -- (irState = stateAt.toNat < 2^w), and the register phase's mask is
      -- killed the same way.  Hypotheses are discharged by native_decide
      -- on the emitted body/stop/width constants.  With memories the
      -- iteration is `stepIterM` (state × MEnv): the memory contents at
      -- cycle t are `memAt t` (the `CMem.natView` of the deep contents),
      -- a latch slot's next value comes from `syncReadLatches` on `memAt t`,
      -- and `memstep` shows `memNexts` lands on `memAt (t+1)`.
      let deepEnvAtId := mkI s!"{base}_deep_envAt"
      let irFunextId := mkI s!"{base}_deep_irState_funext"
      let seedBndId := mkI s!"{base}_deep_seed_bounded"
      let rdOtherId := mkI s!"{base}_deep_envAt_other"
      let dRegstepId := mkI s!"{base}_deep_regstep"
      let dMemstepId := mkI s!"{base}_deep_memstep"
      let dEnvStId := mkI s!"{base}_deep_envSt"
      let dSt0Id := mkI s!"{base}_deep_st0"
      let dEnvStBndId := mkI s!"{base}_deep_envSt_bounded"
      let dStateTraceId := mkI s!"{base}_deep_state_trace"
      let regRstsD : List String := m.body.filterMap fun st =>
        match st with
        | .register _ _ (rstName, _) _ _ => some rstName
        | _ => none
      -- every state slot's input (register input / latch read address) is
      -- a wire reference, so `hv` is `simp [evalExpr]`
      let refWiresD? : Option (List String) := regs.foldr
        (fun (r : String × Sparkle.IR.AST.Expr × Int) acc =>
          match r.2.1, acc with
          | .ref w, some l => some (w :: l)
          | _, _ => none) (some [])
      -- likewise the write ports (address, data, enable) of every memory
      let memPortWires? : Option (List (String × String × String)) := mems.foldr
        (fun (mm : String × Nat × Nat × Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr
            × Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr × String) acc =>
          match mm.2.2.2.1, mm.2.2.2.2.1, mm.2.2.2.2.2.1, acc with
          | .ref a, .ref d, .ref e, some l => some ((a, d, e) :: l)
          | _, _, _, _ => none) (some [])
      -- the register phase lists state updates in BODY order (a memory's
      -- latch comes where its `.memory` statement is)
      let regNames := regs.map (·.1)
      let stateOrder : List Nat := (deepOrderBody m.body).filterMap
        fun st => match st with
          | .register out _ _ _ _ => regNames.idxOf? out
          | .memory _ _ _ _ _ _ _ _ rd cr _ _ => if cr then none else regNames.idxOf? rd
          | _ => none
      -- nm order: registers 0..nR-1, then inputs nR..nR+nI-1, then the
      -- read slots
      let nmNames : List String :=
        (regs.map (·.1)) ++ (ins.map (·.1)) ++ (combos.map (·.2.1))
      let nAll := nR + nI + nC
      let hneIds : Array Ident :=
        (List.range nAll).toArray.map fun idx => mkI s!"hne_{idx}"
      let rdIds : Array Ident := (List.range nAll).toArray.map fun idx =>
        if idx < nR then mkI s!"{base}_deep_envAt_r{idx}"
        else if idx < nR + nI then mkI s!"{base}_deep_envAt_i{idx - nR}"
        else mkI s!"{base}_deep_envAt_c{idx - nR - nI}"
      -- the read addresses of the combinational reads are wire references
      let comboRaWires? : Option (List String) := combos.foldr
        (fun (cc : Nat × String × Sparkle.IR.AST.Expr × Nat × Nat) acc =>
          match cc.2.2.1, acc with
          | .ref w, some l => some (w :: l)
          | _, _ => none) (some [])
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
        for idx in List.range nAll do
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
      -- `irState t ⟨i⟩ < 2^w` for the recurrence `d`
      let mkHbnd (d : Ident) (hbndId : Ident) (i : Nat) : CommandElabM (Lean.TSyntax `tactic) := do
        let irTi ← irStateAt d (← `(t))
        if hasMem then
          `(tactic| have $hbndId:ident : $irTi ⟨$(quote i), by decide⟩ < 2 ^ $(quote regWs[i]!) := by
            simp only [CdoM.irState]
            exact BitVec.isLt _)
        else
          `(tactic| have $hbndId:ident : $irTi ⟨$(quote i), by decide⟩ < 2 ^ $(quote regWs[i]!) := by
            rw [Cdo.irState_eq _ _ (by decide)]
            exact BitVec.isLt _)
      let bridgeOk := nR > 0 && refWiresD?.isSome && regRstsD.length == nReg
        && memPortWires?.isSome && stateOrder.length == nR && comboRaWires?.isSome
      let mut bridgeAudit : Array Ident := #[]
      -- `hrunC : evalAssigns weM (memAt t) bodyC (envAt t) = some env1` from
      -- `hrun` over the full body: synchronous memories are no-ops for the
      -- fold (`evalAssigns_stripSyncMem`); each combinational read is
      -- dropped in body order by `evalAssigns_comboSeeded` — the seed
      -- carries its read value, and the read address's value after the
      -- (memory-free) prefix is the address cone at the seed (the seam on
      -- the prefix), which is what the deep read slot holds
      let mkHrunCTac : CommandElabM (Lean.TSyntax `tactic) := do
        let memsT ← memsAt (← `(t))
        if !hasMem then return ← `(tactic| exact hrun)
        if !hasCombo then
          return ← `(tactic| (rw [← Tools.ConeFold.evalAssigns_stripSyncMem $weMId _ $bodyId
              (Tools.ConeFold.syncMemOnlyCheck_sound _ (by decide))]; exact hrun))
        let comboRaWires := comboRaWires?.getD []
        let mut tacs : Array (Lean.TSyntax `tactic) := #[]
        tacs := tacs.push (← `(tactic| have hb : Sparkle.IR.Semantics.evalAssigns $weMId $memsT
            (Tools.ConeFold.stripSyncOnly $bodyId) ($deepEnvAtId $appArgs* t) = some env1 := by
          rw [← Tools.ConeFold.evalAssigns_stripSyncOnly $weMId _ $bodyId]
          exact hrun))
        let mut curT : Term ← `(Tools.ConeFold.stripSyncOnly $bodyId)
        for c in List.range nC do
          let (kk, rd, raIR, aw, dw) := combos[c]!
          let (name, _, _, waIR, wdIR, weIR, _, _) := mems[kk]!
          let clk := memClks[kk]!
          let raW := comboRaWires[c]!
          let bodyPId := mkI s!"{base}_deep_bodyP{c}"
          let bodyQId := mkI s!"{base}_deep_bodyQ{c}"
          let coneId := mkI s!"{base}_deep_cone_c{c}"
          let coneRawId := mkI s!"{base}_deep_coneRaw_c{c}"
          let portInId := mkI s!"{base}_deep_portIn_c{c}"
          let g1Id := mkI s!"{base}_deep_coneEval_c{c}"
          let rdC := rdIds[nR + nI + c]!
          let waQ ← quoteIR waIR
          let wdQ ← quoteIR wdIR
          let weQ ← quoteIR weIR
          let raQ ← quoteIR raIR
          let memStmt ← `(Sparkle.IR.AST.Stmt.memory $(quote name) $(quote aw) $(quote dw)
            $(quote clk) $waQ $wdQ $weQ $raQ $(quote rd) true [] [])
          let envPId := mkI s!"envP{c}"
          let hPId := mkI s!"hP{c}"
          let hsId := mkI s!"hs{c}"
          let hdenId := mkI s!"hdenC{c}"
          let hrdId := mkI s!"hrdC{c}"
          tacs := tacs.push (← `(tactic| rw [show $curT = $bodyPId ++ $memStmt :: $bodyQId by native_decide] at hb))
          tacs := tacs.push (← `(tactic| obtain ⟨$envPId:ident, $hPId:ident⟩ := Option.isSome_iff_exists.mp
            (Tools.ConeFold.evalAssigns_isSome $weMId $memsT $bodyPId (by native_decide)
              ($deepEnvAtId $appArgs* t))))
          tacs := tacs.push (← `(tactic| have $hsId:ident : Sparkle.IR.Semantics.evalExpr $weMId
              ($deepEnvAtId $appArgs* t) $coneId = some ($envPId $(quote raW)) := by
            have hres : $coneId
                = Tools.ConeFold.resolveSlicesT $wtMId 10000 $coneRawId := by
              native_decide
            rw [hres]
            exact Tools.ConeFold.cone_resolved_agrees_at_seed $weMId
              $memsT $stopAtMId $wtMId
              (Sparkle.IR.Reorder.woCheck_sound [] $bodyPId (by decide))
              (Tools.ConeFold.memFreeCheck_sound _ (by decide))
              (Tools.ConeFold.noSelfReadCheck_sound _ (by decide))
              $hPId
              (Tools.ConeFold.hwfCheck_sound $weMId $stopAtMId $bodyPId
                (by native_decide))
              (Tools.ConeFold.hwt_of_assoc $weMId $wtLId (by native_decide))
              ($seedBndId $appArgs* t)
              (Tools.ConeFold.stopAtFrozenCheck_sound $stopAtMId $bodyPId
                (by native_decide))
              (fuel := 10000) (e := $portInId)
              (hinl := by native_decide)
              10000 (by simp [$portInId:ident, Sparkle.IR.Semantics.evalExpr])))
          tacs := tacs.push (← `(tactic| have $hdenId:ident :
              (@CExpr.denote ($ΓrT ++ $ΓiT) (($ΓmT : List MemSig).get ⟨$(quote kk), by decide⟩).1
                (CEnv.join (CdoM.stateAt $deepId $inpFam t).1 ($inpFam t))
                $(comboCs[c]!)).toNat
                = $envPId $(quote raW) :=
            CdoM.toNat_denote0 $deepId $nmId (by decide) $nm0Id $nm0EqId $inpFam t _
              (by rw [$g1Id:ident]; exact $hsId:ident)))
          tacs := tacs.push (← `(tactic| have $hrdId:ident : $envPId $(quote rd)
              = Sparkle.IR.Semantics.mask $(quote dw) ($memsT $(quote name)
                  (Sparkle.IR.Semantics.mask $(quote aw) ($envPId $(quote raW)))) := by
            rw [Tools.ConeFold.evalAssigns_frame $weMId $memsT $bodyPId _ $envPId $hPId
              (Tools.ConeFold.memFreeCheck_sound _ (by decide)) $(quote rd)
              (by native_decide)]
            rw [$rdC $appArgs* t]
            have hm : ∀ x, $memAtId $appArgs* t $(quote name) x
                = CMem.natView (CdoM.stateAt $deepId $inpFam t).2
                    ⟨$(quote kk), by decide⟩ x := by
              intro x; simp [$memAtId:ident]
            rw [hm]
            exact (CdoM.irReads_eq $deepId $inpFam t ⟨$(quote c), by decide⟩ rfl rfl $hdenId).symm))
          tacs := tacs.push (← `(tactic| rw [Tools.ConeFold.evalAssigns_comboSeeded $weMId $memsT
            $bodyPId $bodyQId $(quote name) $(quote aw) $(quote dw) $(quote clk) $waQ $wdQ $weQ $raQ
            $(quote rd) [] _ $envPId _ $hPId (by simp [Sparkle.IR.Semantics.evalExpr]) $hrdId] at hb))
          curT ← `($bodyPId ++ $bodyQId)
        tacs := tacs.push (← `(tactic| rw [show $curT = $bodyCId by native_decide] at hb))
        tacs := tacs.push (← `(tactic| exact hb))
        `(tactic| ($[$tacs:tactic]*))
      if bridgeOk && k == 0 then
        let regWiresD := refWiresD?.getD []
        let memPortWires := memPortWires?.getD []
        let irTt ← irStateAt deepId (← `(t))
        let irTs ← irStateAt deepId (← `(t + 1))
        let irEt ← irEnvAt deepId (← `(t))
        let memsT ← memsAt (← `(t))
        elabSync (← `(def $deepEnvAtId $paramBinders* (t : Nat) :
            Sparkle.IR.Semantics.Env :=
          envOfC $nmId $irEt))
        if hasMem then
          elabSync (← `(theorem $seedBndId $paramBinders* (t : Nat) :
              ∀ n, $deepEnvAtId $appArgs* t n < 2 ^ $weMId n := by
            intro n
            unfold $deepEnvAtId
            apply envOfC_bounded
            intro i
            have hag : ∀ i : Fin ($ΓAllT).length,
                $weMId ($nmId i) = ($ΓAllT).get i := by
              native_decide
            rw [hag i, CdoM.irEnv_eq]
            exact BitVec.isLt _))
        else
          elabSync (← `(theorem $irFunextId $paramBinders* (t : Nat) :
              $irTt = fun i => (Cdo.stateAt $deepId $inpFam t i).toNat := by
            funext i
            exact Cdo.irState_eq _ _ (by decide) _ t i))
          elabSync (← `(theorem $seedBndId $paramBinders* (t : Nat) :
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
        for idx in List.range nAll do
          let nmS := nmNames[idx]!
          let rdId := rdIds[idx]!
          let rhs : Term ← if idx < nR then
              `($irTt ⟨$(quote idx), by decide⟩)
            else if idx < nR + nI then
              `(((($inpS) ⟨$(quote (idx - nR)), by decide⟩).val t).toNat)
            else
              `(CdoM.irReads $deepId $inpFam t ⟨$(quote (idx - nR - nI)), by decide⟩)
          elabSync (← `(theorem $rdId $paramBinders* (t : Nat) :
              $deepEnvAtId $appArgs* t $(quote nmS) = $rhs := by
            unfold $deepEnvAtId
            rw [show $(quote nmS) = $nmId ⟨$(quote idx), by decide⟩ from rfl,
              envOfC_names _ _ (by decide)]
            rfl))
        -- names outside the register/input family read 0
        let hneBinders ← (List.range nAll).toArray.mapM fun idx => do
          let h : Ident := hneIds[idx]!
          `(Lean.Parser.Term.bracketedBinderF| ($h:ident : n ≠ $(quote nmNames[idx]!)))
        let hneSymm : Array Term ← (List.range nAll).toArray.mapM
          fun idx => do
            let h : Ident := hneIds[idx]!
            `(Ne.symm $h:ident)
        elabSync (← `(theorem $rdOtherId $paramBinders* (t : Nat)
            (n : String) $hneBinders* :
            $deepEnvAtId $appArgs* t n = 0 := by
          simp [$deepEnvAtId:ident, envOfC, chainMap, List.finRange,
            $nmId:ident, $[$hneSymm:term],*]))
        -- the IR memory contents at cycle t: the natView of the deep contents
        if hasMem then
          let memAtBody ← do
            let mut acc ← `((0 : Nat))
            for kk in (List.range nM).reverse do
              let (name, _, _, _, _, _, _, _) := mems[kk]!
              acc ← `(if nm == $(quote name) then
                CMem.natView (CdoM.stateAt $deepId $inpFam t).2 ⟨$(quote kk), by decide⟩ i
                else $acc)
            pure acc
          elabSync (← `(def $memAtId $paramBinders* (t : Nat) :
              Sparkle.IR.Semantics.MEnv := fun nm i => $memAtBody))
          elabSync (← `(theorem $memAtZeroId $paramBinders* :
              $memAtId $appArgs* 0 = fun _ _ => 0 := by
            funext nm i
            simp [$memAtId:ident, CMem.natView, CdoM.stateAt, $minitsEqId:ident]))
          bridgeAudit := bridgeAudit.push memAtZeroId
        -- the stripped-body run, for the seam facts
        let hrunCTac ← mkHrunCTac
        -- one step lemma: the cone of `eIn` at the seed evaluates to what
        -- `eIn` evaluates to after the combinational fold
        let mkStep (stepId : Ident) (coneId coneRawId : Ident) (eIn : Term) :
            CommandElabM Unit := do
          elabSync (← `(theorem $stepId $paramBinders* (t : Nat)
              {env1 : Sparkle.IR.Semantics.Env} {v : Nat}
              (hrun : Sparkle.IR.Semantics.evalAssigns $weMId $memsT
                $bodyId ($deepEnvAtId $appArgs* t) = some env1)
              (hv : Sparkle.IR.Semantics.evalExpr $weMId env1 $eIn = some v) :
              Sparkle.IR.Semantics.evalExpr $weMId ($deepEnvAtId $appArgs* t)
                $coneId = some v := by
            have hres : $coneId
                = Tools.ConeFold.resolveSlicesT $wtMId 10000 $coneRawId := by
              native_decide
            rw [hres]
            have hrunC : Sparkle.IR.Semantics.evalAssigns $weMId $memsT
                $bodyC ($deepEnvAtId $appArgs* t) = some env1 := by
              $hrunCTac:tactic
            exact Tools.ConeFold.cone_resolved_agrees_at_seed $weMId
              $memsT $stopAtMId $wtMId
              (Sparkle.IR.Reorder.woCheck_sound [] $bodyC (by decide))
              (Tools.ConeFold.memFreeCheck_sound _ (by decide))
              (Tools.ConeFold.noSelfReadCheck_sound _ (by decide))
              hrunC
              (Tools.ConeFold.hwfCheck_sound $weMId $stopAtMId $bodyC
                (by native_decide))
              (Tools.ConeFold.hwt_of_assoc $weMId $wtLId (by native_decide))
              ($seedBndId $appArgs* t)
              (Tools.ConeFold.stopAtFrozenCheck_sound $stopAtMId $bodyC
                (by native_decide))
              (fuel := 10000) (e := $eIn)
              (hinl := by native_decide)
              10000 hv))
        -- per-slot step + the register phase
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
          mkStep stepId coneId coneRawId (← `($regInId))
        -- per-write-port step (memories)
        if hasMem then
          for kk in List.range nM do
            for tag in ["wa", "wd", "we"] do
              let stepId := mkI s!"{base}_deep_step_m{kk}_{tag}"
              bridgeAudit := bridgeAudit.push stepId
              mkStep stepId (mkI s!"{base}_deep_cone_m{kk}_{tag}")
                (mkI s!"{base}_deep_coneRaw_m{kk}_{tag}")
                (← `($(mkI s!"{base}_deep_portIn_m{kk}_{tag}")))
        -- regstep
        let mut nextsItems : Array Term := #[]
        let mut pre : Array (Lean.TSyntax `tactic) := #[]
        let mut finalArgs : Array Term := #[]
        let mut closers : Array (Lean.TSyntax `tactic) := #[]
        let mut slRws : Array Term := #[]
        if hasMem then
          pre := pre.push (← `(tactic| have hrunC : Sparkle.IR.Semantics.evalAssigns $weMId $memsT
              $bodyC ($deepEnvAtId $appArgs* t) = some env1 := by
            $hrunCTac:tactic))
        let hrunCRef : Term ← if hasMem then `(hrunC) else `(hrun)
        for i in stateOrder do
          let (rn, _, _) := regs[i]!
          nextsItems := nextsItems.push (← `(($(quote rn), $irTs ⟨$(quote i), by decide⟩)))
        for i in List.range nR do
          let (rn, _, _) := regs[i]!
          let sanit := Sparkle.Backend.Verilog.sanitizeName rn
          let coneId := mkI s!"{base}_deep_cone_{sanit}"
          let regInId := mkI s!"{base}_deep_regIn_{sanit}"
          let g1Id := mkI s!"{base}_deep_coneEval_r{i}"
          let w := regWiresD[i]!
          let hrstId := mkI s!"hrst{i}"
          let hstepId := mkI s!"hstep{i}"
          let hnextId := mkI s!"hnext{i}"
          let hbndId := mkI s!"hbnd{i}"
          pre := pre.push (← `(tactic| have $hstepId:ident :=
            $(stepIds[i]!) $appArgs* t hrun
              (show Sparkle.IR.Semantics.evalExpr $weMId env1 $regInId
                  = some (env1 $(quote w)) by
                simp [$regInId:ident, Sparkle.IR.Semantics.evalExpr])))
          if i < nReg then
            let rstName := regRstsD[i]!
            pre := pre.push (← `(tactic| have $hrstId:ident :
                env1 $(quote rstName) = 0 := by
              have hfr := Tools.ConeFold.evalAssigns_frame $weMId $memsT
                $bodyC _ env1 $hrunCRef
                (Tools.ConeFold.memFreeCheck_sound _ (by decide))
                $(quote rstName) (by native_decide)
              rw [hfr]
              simp [$deepEnvAtId:ident, envOfC, chainMap, List.finRange,
                $nmId:ident]))
            if hasMem then
              let fidId := fidIds[i]!
              pre := pre.push (← `(tactic| have $hnextId:ident :
                  $irTs ⟨$(quote i), by decide⟩ = env1 $(quote w) :=
                CdoM.irState_succ_cone $deepId $nmId (by decide) $inpFam t
                  ⟨$(quote i), by decide⟩ $fidId
                  (by rw [$g1Id:ident]; exact $hstepId:ident)))
              pre := pre.push (← `(tactic| have $hbndId:ident :
                  env1 $(quote w) < 2 ^ $(quote regWs[i]!) := by
                rw [← $hnextId:ident]
                simp only [CdoM.irState]
                exact BitVec.isLt _))
            else
              pre := pre.push (← `(tactic| have $hnextId:ident :
                  $irTs ⟨$(quote i), by decide⟩ = env1 $(quote w) := by
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
          else
            -- latch slot of memory kk: its next value is the contents at
            -- the read address; `syncReadLatches` on `memAt t` lands there
            let kk := i - nReg
            let (name, aw, dw, _, _, _, raIR, rd) := mems[kk]!
            let fidLId := mkI s!"{base}{suffix}_deep_fidelity_latch{i}"
            let hslId := mkI s!"hsl{i}"
            let raQ ← quoteIR raIR
            pre := pre.push (← `(tactic| have $hnextId:ident :
                $irTs ⟨$(quote i), by decide⟩
                  = ((CdoM.stateAt $deepId $inpFam t).2 ⟨$(quote kk), by decide⟩
                      (BitVec.ofNat $(quote aw) (env1 $(quote w)))).toNat :=
              CdoM.irState_succ_latch $deepId $nmId (by decide) $inpFam t
                ⟨$(quote i), by decide⟩ ⟨$(quote kk), by decide⟩ _ $fidLId
                (by rw [$g1Id:ident]; exact $hstepId:ident)))
            pre := pre.push (← `(tactic| have $hslId:ident :
                Sparkle.IR.Semantics.syncReadLatches $weMId $memsT $(quote name)
                  $(quote aw) $(quote dw) [($raQ, $(quote rd))] env1
                = some [($(quote rd), $irTs ⟨$(quote i), by decide⟩)] := by
              simp only [Sparkle.IR.Semantics.syncReadLatches,
                Sparkle.IR.Semantics.evalExpr, Option.bind_eq_bind, Option.bind_some]
              rw [$hnextId:ident]
              have hm : ∀ x, $memAtId $appArgs* t $(quote name) x
                  = CMem.natView (CdoM.stateAt $deepId $inpFam t).2
                      ⟨$(quote kk), by decide⟩ x := by
                intro x; simp [$memAtId:ident]
              rw [hm, CMem.natView_latch (CdoM.stateAt $deepId $inpFam t).2
                ⟨$(quote kk), by decide⟩ (aw := $(quote aw)) (dw := $(quote dw)) rfl rfl]
              rfl))
            slRws := slRws.push ⟨hslId.raw⟩
        elabSync (← `(theorem $dRegstepId $paramBinders* (t : Nat)
            {env1 : Sparkle.IR.Semantics.Env}
            (hrun : Sparkle.IR.Semantics.evalAssigns $weMId $memsT
              $bodyId ($deepEnvAtId $appArgs* t) = some env1) :
            Sparkle.IR.Semantics.regNexts $weMId $memsT $bodyId env1
              = some [$nextsItems,*] := by
          $[$pre:tactic]*
          simp only [$bodyId:ident, Sparkle.IR.Semantics.regNexts,
            Sparkle.IR.Semantics.evalExpr, Option.bind_eq_bind,
            Option.bind_some, Bool.false_eq_true, eq_self_iff_true, ↓reduceIte,
            List.cons_append, List.nil_append, $[$slRws:term],*]
          simp [Sparkle.IR.Semantics.mask, $weMId:ident, -Fin.zero_eta,
            -Fin.mk_zero, -Fin.mk_one, $[$finalArgs:term],*]
          repeat' (apply And.intro)
          $[$closers:tactic]*))
        -- memstep: the memory phase lands on the next cycle's contents
        if hasMem then
          let mut mpre : Array (Lean.TSyntax `tactic) := #[]
          let mut payRws : Array Term := #[]
          let mut viewRws : Array Term := #[]
          for kk in List.range nM do
            let (name, aw, dw, waIR, wdIR, weIR, _, _) := mems[kk]!
            let (waW, wdW, weW) := memPortWires[kk]!
            let ports : List (String × String × Sparkle.IR.AST.Expr × Term) :=
              [("wa", waW, waIR, ← `((CdoM.writes $deepId ⟨$(quote kk), by decide⟩).1)),
               ("wd", wdW, wdIR, ← `((CdoM.writes $deepId ⟨$(quote kk), by decide⟩).2.1)),
               ("we", weW, weIR, ← `((CdoM.writes $deepId ⟨$(quote kk), by decide⟩).2.2))]
            let mut hdenIds : Array Ident := #[]
            for (tag, w, portIR, proj) in ports do
              let stepId := mkI s!"{base}_deep_step_m{kk}_{tag}"
              let g1Id := mkI s!"{base}_deep_coneEval_m{kk}_{tag}"
              let portInId := mkI s!"{base}_deep_portIn_m{kk}_{tag}"
              let hstepId := mkI s!"hstep_m{kk}_{tag}"
              let hdenId := mkI s!"hden_m{kk}_{tag}"
              let hpayId := mkI s!"hpay_m{kk}_{tag}"
              let portQ ← quoteIR portIR
              hdenIds := hdenIds.push hdenId
              mpre := mpre.push (← `(tactic| have $hstepId:ident :=
                $stepId $appArgs* t hrun
                  (show Sparkle.IR.Semantics.evalExpr $weMId env1 $portInId
                      = some (env1 $(quote w)) by
                    simp [$portInId:ident, Sparkle.IR.Semantics.evalExpr])))
              mpre := mpre.push (← `(tactic| have $hdenId:ident :
                  (CExpr.denote (CdoM.fullEnv $deepId
                      (CEnv.join (CdoM.stateAt $deepId $inpFam t).1 ($inpFam t))
                      (CdoM.stateAt $deepId $inpFam t).2)
                    $proj).toNat = env1 $(quote w) :=
                CdoM.toNat_denote $deepId $nmId (by decide) $inpFam t _
                  (by rw [$g1Id:ident]; exact $hstepId:ident)))
              -- generic in the resolution state: `memNexts` threads the
              -- state updated by the EARLIER memories into a later
              -- memory's port evaluation (a payload in the total fragment
              -- never reads it)
              mpre := mpre.push (← `(tactic| have $hpayId:ident :
                  ∀ mems : Sparkle.IR.Semantics.MEnv,
                  Sparkle.IR.Semantics.evalPayload $weMId mems env1 $(quote name)
                    $(quote aw) $(quote dw) $portQ = some (env1 $(quote w)) := by
                intro mems
                rw [Tools.ConeFold.evalPayload_evalOk _ _ _ _ _ _ _ (by native_decide)]
                simp [Sparkle.IR.Semantics.evalExpr]))
              payRws := payRws.push ⟨hpayId.raw⟩
            viewRws := viewRws.push (← `(CdoM.memUpd_natView $deepId _ _
              ⟨$(quote kk), by decide⟩ $(hdenIds[0]!) $(hdenIds[1]!) $(hdenIds[2]!) i))
          elabSync (← `(theorem $dMemstepId $paramBinders* (t : Nat)
              {env1 : Sparkle.IR.Semantics.Env}
              (hrun : Sparkle.IR.Semantics.evalAssigns $weMId $memsT
                $bodyId ($deepEnvAtId $appArgs* t) = some env1) :
              Sparkle.IR.Semantics.memNexts $weMId $bodyId $memsT env1
                = some ($memAtId $appArgs* (t + 1)) := by
            $[$mpre:tactic]*
            simp only [$bodyId:ident, Sparkle.IR.Semantics.memNexts,
              Sparkle.IR.Semantics.memWritePorts, Option.bind_eq_bind,
              $[$payRws:term],* , Option.bind_some]
            congr 1
            funext nm i
            -- the IR's update is an `ite` at the function level
            have ite_app : ∀ {c : Prop} [Decidable c]
                (f g : Sparkle.IR.Semantics.MEnv) (nm : String) (i : Nat),
                (if c then f else g) nm i = if c then f nm i else g nm i := by
              intro c _ f g nm i
              split <;> rfl
            simp only [ite_app, $memAtId:ident, CdoM.stateAt_succ_mem, $[$viewRws:term],*]
            repeat' split
            all_goals simp_all))
          bridgeAudit := bridgeAudit.push dMemstepId
        -- map-state seed, initial state, boundedness
        let envStBody ← do
          let mut acc ← `((0 : Nat))
          -- read slots: the seed carries the deep read value (comboReads
          -- recomputes and overwrites it in the fold — this only lets the
          -- seeded-read seam lemma drop the statement)
          for c in (List.range nC).reverse do
            let (_, rd, _, _, _) := combos[c]!
            acc ← `(if n == $(quote rd) then
              CdoM.irReads $deepId $inpFam t ⟨$(quote c), by decide⟩ else $acc)
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
        elabSync (← `(def $dEnvStId $paramBinders* (t : Nat)
            (st : String → Nat) : Sparkle.IR.Semantics.Env :=
          fun n => $envStBody))
        let st0Body ← do
          let mut acc ← `((0 : Nat))
          for i in (List.range nR).reverse do
            let (rn, _, _) := regs[i]!
            let initT : Term ← if hasMem then `((CdoM.inits $deepId ⟨$(quote i), by decide⟩).toNat)
              else `((Cdo.inits $deepId ⟨$(quote i), by decide⟩).toNat)
            acc ← `(if n == $(quote rn) then $initT else $acc)
          pure acc
        elabSync (← `(def $dSt0Id : String → Nat := fun n => $st0Body))
        -- boundedness of the seed, by an EXPLICIT case cascade over the
        -- chain (registers, inputs, read slots — the seed's own order).
        -- `repeat' split` was used before; on a 7-register seed `split`'s
        -- internal simp exceeds its step limit, and `repeat'` swallows
        -- that failure and leaves the chain unsplit (the residual goal
        -- then went to `omega`, which cannot see through the `ite`).
        let chainEntries : List (String × Nat × Nat) :=
          (List.range nR).map (fun i => ((regs[i]!).1, regWs[i]!, (0 : Nat)))
          ++ (List.range nI).map (fun j => ((ins[j]!).1, inWs[j]!, (1 : Nat)))
          ++ (List.range nC).map (fun c => ((combos[c]!).2.1, comboWs[c]!, (2 : Nat)))
        -- built as a FLAT tactic array (the file's established shape for
        -- generated scripts): nesting `by_cases` with `case`/`·` blocks
        -- inside one `(tactic| ( … ))` quotation does not parse.
        -- `rotate_left` moves the remaining (negative) goal to the front,
        -- so the chain is walked without focusing syntax.
        let mut bndTacs : Array (Lean.TSyntax `tactic) := #[]
        for (e, idx) in chainEntries.toArray.zipIdx do
          let (name, w, kind) := e
          let hId := mkI s!"hc{idx}"
          let predT : Term ← `((n == $(quote name)) = true)
          let wRfl : Term ← `(show $weMId $(quote name) = $(quote w) from rfl)
          let closer : Lean.TSyntax `tactic ← match kind with
            | 0 => `(tactic| exact Nat.mod_lt _ (Nat.two_pow_pos _))
            | 1 => `(tactic| exact BitVec.isLt _)
            | _ => `(tactic| (simp only [CdoM.irReads]; exact BitVec.isLt _))
          bndTacs := bndTacs.push (← `(tactic| by_cases $hId:ident : $predT:term))
          bndTacs := bndTacs.push (← `(tactic| rotate_left))
          bndTacs := bndTacs.push (← `(tactic| rw [if_neg $hId:ident]))
          bndTacs := bndTacs.push (← `(tactic| rotate_left))
          bndTacs := bndTacs.push (← `(tactic| rw [if_pos $hId:ident, beq_iff_eq.mp $hId:ident, $wRfl:term]))
          bndTacs := bndTacs.push closer
        bndTacs := bndTacs.push (← `(tactic| exact Nat.two_pow_pos _))
        elabSync (← `(theorem $dEnvStBndId $paramBinders* (t : Nat)
            (st : String → Nat) :
            ∀ n, $dEnvStId $appArgs* t st n < 2 ^ $weMId n := by
          intro n
          simp only [$dEnvStId:ident]
          $[$bndTacs:tactic]*))
        -- state_trace
        let stateConj ← do
          let mut conjs : Array Term := #[]
          for i in List.range nR do
            let (rn, _, _) := regs[i]!
            conjs := conjs.push (← `(st $(quote rn) = $irTt ⟨$(quote i), by decide⟩))
          let mut acc : Term := conjs.back!
          for c in conjs.pop.reverse do
            acc ← `($c ∧ $acc)
          pure acc
        let hbndIds : Array Ident :=
          (List.range nR).toArray.map fun i => mkI s!"hbnd{i}"
        let mut hbndTacs : Array (Lean.TSyntax `tactic) := #[]
        for i in List.range nR do
          hbndTacs := hbndTacs.push (← mkHbnd deepId hbndIds[i]! i)
        let henvTacs ← mkHenv ihcId hbndIds
        let stateZeroSimp : Lean.TSyntax `tactic ← if hasMem then
            `(tactic| simp [$dSt0Id:ident, CdoM.irState, CdoM.stateAt])
          else `(tactic| simp [$dSt0Id:ident, Cdo.irState])
        if hasMem then
          -- the induction step, as its own quotation (one quotation for the
          -- whole theorem exceeds the elaborator's recursion depth)
          let succTac : Lean.TSyntax `tactic ← `(tactic| (
            intro st' ms' h
            simp only [Tools.ConeFold.stepIterM, Option.bind_eq_bind] at h
            cases hprev : Tools.ConeFold.stepIterM $weMId $bodyId
                ($dEnvStId $appArgs*) $dSt0Id ($memAtId $appArgs* 0) t with
            | none => rw [hprev] at h; simp at h
            | some p =>
              obtain ⟨st, ms⟩ := p
              rw [hprev] at h
              simp only [Option.bind_some] at h
              have $ihcId:ident := (ih hprev).1
              have hms := (ih hprev).2
              subst hms
              $[$hbndTacs:tactic]*
              have henv : $dEnvStId $appArgs* t st
                  = $deepEnvAtId $appArgs* t := by
                $[$henvTacs:tactic]*
              rw [henv] at h
              simp only [Sparkle.IR.Semantics.stepModule,
                Option.bind_eq_bind] at h
              cases hrun : Sparkle.IR.Semantics.evalAssigns $weMId
                  ($memAtId $appArgs* t) $bodyId ($deepEnvAtId $appArgs* t) with
              | none => rw [hrun] at h; simp at h
              | some env1 =>
                rw [hrun] at h
                simp only [Option.bind_some] at h
                rw [$dRegstepId $appArgs* t hrun, $dMemstepId $appArgs* t hrun] at h
                simp only [Option.bind_some, Option.some_inj, Prod.mk.injEq] at h
                obtain ⟨h1, h2⟩ := h
                subst h1
                subst h2
                refine ⟨?_, rfl⟩
                simp [Sparkle.IR.Semantics.applyNexts]))
          let zeroTac : Lean.TSyntax `tactic ← `(tactic| (
            intro st ms h
            simp only [Tools.ConeFold.stepIterM, Option.some_inj, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h
            subst h1
            subst h2
            refine ⟨?_, rfl⟩
            $stateZeroSimp:tactic))
          elabSync (← `(theorem $dStateTraceId $paramBinders* :
              ∀ (t : Nat) {st : String → Nat} {ms : Sparkle.IR.Semantics.MEnv},
              Tools.ConeFold.stepIterM $weMId $bodyId ($dEnvStId $appArgs*)
                $dSt0Id ($memAtId $appArgs* 0) t = some (st, ms)
                → ($stateConj) ∧ ms = $memAtId $appArgs* t := by
            intro t
            induction t with
            | zero => $zeroTac:tactic
            | succ t ih => $succTac:tactic))
        else
          elabSync (← `(theorem $dStateTraceId $paramBinders* :
              ∀ (t : Nat) {st : String → Nat},
              Tools.ConeFold.stepIter $weMId $bodyId ($dEnvStId $appArgs*)
                $dSt0Id t = some st → $stateConj := by
            intro t
            induction t with
            | zero =>
              intro st h
              simp only [Tools.ConeFold.stepIter, Option.some_inj] at h
              subst h
              $stateZeroSimp:tactic
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
                    (Tools.ConeFold.memFreeCheck_sound _ (by decide))]
                    at h
                  simp only [Option.bind_some, Option.some_inj] at h
                  subst h
                  simp [Sparkle.IR.Semantics.applyNexts]))
      if bridgeOk && k == 0 then
        bridgeAudit := bridgeAudit ++ #[seedBndId, rdOtherId, dRegstepId,
          dEnvStBndId, dStateTraceId]
        if !hasMem then bridgeAudit := bridgeAudit.push irFunextId
      -- per-port: the output cone at the seed, and the Signal-level chain
      if bridgeOk then
        let dStepOutId := mkI s!"{base}{suffix}_deep_step_out"
        let dSigFoldId := mkI s!"{base}{suffix}_deep_signal_fold"
        let dSigRunId := mkI s!"{base}{suffix}_deep_signal_run"
        let memsT ← memsAt (← `(t))
        let hrunCTac ← mkHrunCTac
        -- this port's Signal value over the SHARED recurrence (the first
        -- port's Cdo): irState only reads next/inits (and writes/minits),
        -- which every port's Cdo of a struct circuit shares syntactically
        let sigM0Id := mkI s!"{base}{suffix}_deep_signalM0"
        let irE0T ← irEnvAt deep0Id (← `(t))
        if k == 0 then
          elabSync (← `(theorem $sigM0Id $paramBinders* (t : Nat) :
              (($lhsSig).val t).toNat
              = (Sparkle.IR.Semantics.evalExpr $weMId
                  (envOfC $nmId $irE0T)
                  $outConeId).getD 0 := $sigMId $appArgs* t))
        else
          let congrRw : Lean.TSyntax `tactic ← if hasMem then
              `(tactic| rw [$sigMId $appArgs* t,
                CdoM.irEnv_congr $deepId $deep0Id $inpFam rfl rfl rfl rfl rfl])
            else
              `(tactic| rw [$sigMId $appArgs* t,
                Cdo.irState_congr $deepId $deep0Id $nmId $inpFam rfl rfl])
          elabSync (← `(theorem $sigM0Id $paramBinders* (t : Nat) :
              (($lhsSig).val t).toNat
              = (Sparkle.IR.Semantics.evalExpr $weMId
                  (envOfC $nmId $irE0T)
                  $outConeId).getD 0 := by
            $congrRw:tactic))
        elabSync (← `(theorem $dStepOutId $paramBinders* (t : Nat)
            {env1 : Sparkle.IR.Semantics.Env} {v : Nat}
            (hrun : Sparkle.IR.Semantics.evalAssigns $weMId $memsT
              $bodyId ($deepEnvAtId $appArgs* t) = some env1)
            (hv : Sparkle.IR.Semantics.evalExpr $weMId env1
              (.ref $(quote portName)) = some v) :
            Sparkle.IR.Semantics.evalExpr $weMId ($deepEnvAtId $appArgs* t)
              $outConeId = some v := by
          have hres : $outConeId
              = Tools.ConeFold.resolveSlicesT $wtMId 10000 $outConeRawId := by
            native_decide
          rw [hres]
          have hrunC : Sparkle.IR.Semantics.evalAssigns $weMId $memsT
              $bodyC ($deepEnvAtId $appArgs* t) = some env1 := by
            $hrunCTac:tactic
          exact Tools.ConeFold.cone_resolved_agrees_at_seed $weMId
            $memsT $stopAtMId $wtMId
            (Sparkle.IR.Reorder.woCheck_sound [] $bodyC (by decide))
            (Tools.ConeFold.memFreeCheck_sound _ (by decide))
            (Tools.ConeFold.noSelfReadCheck_sound _ (by decide))
            hrunC
            (Tools.ConeFold.hwfCheck_sound $weMId $stopAtMId $bodyC
              (by native_decide))
            (Tools.ConeFold.hwt_of_assoc $weMId $wtLId (by native_decide))
            ($seedBndId $appArgs* t)
            (Tools.ConeFold.stopAtFrozenCheck_sound $stopAtMId $bodyC
              (by native_decide))
            (fuel := 10000) (e := .ref $(quote portName))
            (hinl := by native_decide)
            10000 hv))
        let hbndIds : Array Ident :=
          (List.range nR).toArray.map fun i => mkI s!"hbnd{i}"
        let mut hbndTacs : Array (Lean.TSyntax `tactic) := #[]
        for i in List.range nR do
          hbndTacs := hbndTacs.push (← mkHbnd deep0Id hbndIds[i]! i)
        let henvTacs ← mkHenv ihcId hbndIds
        if hasMem then
          elabSync (← `(theorem $dSigFoldId $paramBinders* (t : Nat)
              {st : String → Nat} {ms : Sparkle.IR.Semantics.MEnv}
              {env1 : Sparkle.IR.Semantics.Env}
              (hstep : Tools.ConeFold.stepIterM $weMId $bodyId
                ($dEnvStId $appArgs*) $dSt0Id ($memAtId $appArgs* 0) t = some (st, ms))
              (hrun : Sparkle.IR.Semantics.evalAssigns $weMId ms
                $bodyId ($dEnvStId $appArgs* t st) = some env1) :
              (($lhsSig).val t).toNat = env1 $(quote portName) := by
            have $ihcId:ident := ($dStateTraceId $appArgs* t hstep).1
            have hms := ($dStateTraceId $appArgs* t hstep).2
            subst hms
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
          elabSync (← `(theorem $dSigRunId $paramBinders* (K : Nat) :
              ∃ envs, Sparkle.IR.Semantics.runModule $weMId $bodyId
                  (fun td s => $dEnvStId $appArgs* (K - 1 - td) s) K $dSt0Id
                  (fun _ _ => 0) = some envs
                ∧ ∀ t, t < K → ∃ env1, envs[t]? = some env1
                  ∧ (($lhsSig).val t).toNat = env1 $(quote portName) := by
            rw [← $memAtZeroId $appArgs*]
            obtain ⟨envs, henvs⟩ := Option.isSome_iff_exists.mp
              (Tools.ConeFold.runModule_isSomeM $weMId $bodyId (by decide)
                (fun td s => $dEnvStId $appArgs* (K - 1 - td) s) K $dSt0Id
                ($memAtId $appArgs* 0))
            refine ⟨envs, henvs, ?_⟩
            intro t ht
            have henvs' : Sparkle.IR.Semantics.runModule $weMId $bodyId
                (fun td s => $dEnvStId $appArgs* (0 + (K - 1 - td)) s) K $dSt0Id
                ($memAtId $appArgs* 0) = some envs := by
              rw [Tools.ConeFold.runModule_seed_congr $weMId $bodyId K
                (fun td s => $dEnvStId $appArgs* (0 + (K - 1 - td)) s)
                (fun td s => $dEnvStId $appArgs* (K - 1 - td) s)
                (fun td htd => by simp only [Nat.zero_add])]
              exact henvs
            obtain ⟨st', ms', env1, hsi, hev, hget⟩ :=
              Tools.ConeFold.runModule_stepIterM $weMId $bodyId
                ($dEnvStId $appArgs*) K 0 $dSt0Id ($memAtId $appArgs* 0) envs henvs' t ht
            refine ⟨env1, hget, ?_⟩
            have hsi' : Tools.ConeFold.stepIterM $weMId $bodyId
                ($dEnvStId $appArgs*) $dSt0Id ($memAtId $appArgs* 0) t = some (st', ms') := by
              rw [Tools.ConeFold.stepIterM_seed_congr $weMId $bodyId
                ($dEnvStId $appArgs*)
                (fun tt s => $dEnvStId $appArgs* (0 + tt) s) $dSt0Id
                ($memAtId $appArgs* 0) t
                (fun tt htt => by simp only [Nat.zero_add])]
              exact hsi
            have hev' : Sparkle.IR.Semantics.evalAssigns $weMId ms'
                $bodyId ($dEnvStId $appArgs* t st') = some env1 := by
              have h0 : (0 : Nat) + t = t := by omega
              rw [← h0]
              exact hev
            exact $dSigFoldId $appArgs* t hsi' hev'))
        else
          elabSync (← `(theorem $dSigFoldId $paramBinders* (t : Nat)
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
          elabSync (← `(theorem $dSigRunId $paramBinders* (K : Nat) :
              ∃ envs, Sparkle.IR.Semantics.runModule $weMId $bodyId
                  (fun td s => $dEnvStId $appArgs* (K - 1 - td) s) K $dSt0Id
                  (fun _ _ => 0) = some envs
                ∧ ∀ t, t < K → ∃ env1, envs[t]? = some env1
                  ∧ (($lhsSig).val t).toNat = env1 $(quote portName) := by
            obtain ⟨envs, henvs⟩ := Option.isSome_iff_exists.mp
              (Tools.ConeFold.runModule_isSome $weMId $bodyId
                (Tools.ConeFold.memFreeCheck_sound _ (by decide))
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
                (Tools.ConeFold.memFreeCheck_sound _ (by decide))
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
      else
        logInfo m!"#verify_elab_deep {declName}: IR replay skipped (a state or memory-port input is not a wire reference, or the register/reset bookkeeping is irregular); the certified statement is the capstone {thId.getId}"
      -- audit the capstone AND every fidelity theorem: elabCommand
      -- recovers failed tactic blocks as sorry, and a sorry'd fidelity
      -- proof would silently demote the result to the unverified twin.
      -- A kernel-rejected declaration ("has metavariables") is absent:
      -- getConstInfo throws, so it can never be reported PROVEN.  The
      -- generated names are SIMPLE and land in the current namespace —
      -- resolve them there (a bare-name lookup silently found nothing
      -- inside `namespace …`).
      for aud in #[thId] ++ fidIds ++ fidLIds ++ fidCIds ++ fidMemIds ++ #[fidOutId] ++ bridgeAudit do
        let full ← liftCoreM <| Lean.resolveGlobalConstNoOverload aud
        let ci ← liftCoreM <| Lean.getConstInfo full
        if ci.type.hasExprMVar || (ci.value?.map (·.hasExprMVar)).getD false then
          throwError "#verify_elab_deep {declName}: generated proof {aud.getId} FAILED (metavariables)"
        let axioms ← liftCoreM <| Lean.collectAxioms full
        if axioms.contains ``sorryAx then
          throwError "#verify_elab_deep {declName}: generated proof {aud.getId} FAILED (sorryAx) — see the errors above"
      let portTag := if structName?.isSome then s!".{portName}" else ""
      let replayTag := if bridgeOk then s!"; IR replay {base}{suffix}_deep_signal_run" else "; IR replay skipped"
      if hasMem then
        logInfo m!"#verify_elab_deep {declName}{portTag}: PROVEN via CdoM.elab_general — {thId.getId} ({nReg} registers, {nM} memories ({nC} combinational reads), {nI} inputs; axioms clean; fidelity: {fidIds.size} slot cones + {fidMemIds.size} write-port cones + {fidCIds.size} read addresses + out = the elaborated IR, by unfolding{replayTag})"
      else
        logInfo m!"#verify_elab_deep {declName}{portTag}: PROVEN via Cdo.elab_general — {thId.getId} ({nR} registers, {nI} inputs; axioms clean; fidelity: {fidIds.size} register cones + out = the elaborated IR, by unfolding{replayTag})"
    replayBlock ()

end Tools.DeepElab
