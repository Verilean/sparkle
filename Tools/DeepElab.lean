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

/-- Shallow denotation: BitVec values for the variables, BitVec out. -/
def CEnv (Γ : List Nat) := ∀ i : Fin Γ.length, BitVec (Γ.get i)

def CExpr.denote {Γ w} (ρ : CEnv Γ) : CExpr Γ w → BitVec w
  | .const _ v => BitVec.ofNat _ v
  | .var i => ρ i
  | .add a b => a.denote ρ + b.denote ρ
  | .sub a b => a.denote ρ - b.denote ρ
  | .mux c t e => if c.denote ρ = 1#1 then t.denote ρ else e.denote ρ
  | .eq a b => if a.denote ρ = b.denote ρ then 1#1 else 0#1

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
