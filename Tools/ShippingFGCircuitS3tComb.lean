import Sparkle.IR.Semantics
import Sparkle.IR.RegDedup
set_option autoImplicit false
-- FG circuit pilot S3t, step 2: a validator `checkComb` for ONE combinational child module (assign statements only) and its soundness `checkComb_sound`, for the operators the pilot children use: `ref`, `const`, `eq`, `mux`, `slice`, `concat` (two parts).  The source is given as `CTerm`s over source positions; the module is translated wire by wire into `CTerm`s (a wire is replaced by its definition when its DECLARED width is the definition's width), and every output's translation must EQUAL the source term.  The theorem is about the IR semantics of the module (`evalAssigns` at the declared widths) for ALL inputs; it says nothing about how the source terms relate to a declaration's `MachineData` (that is `Tools.ShippingFGCircuitS3tCombRun`).  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §69.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3tComb
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)

/-! ## Source terms and their denotation -/

/-- source terms: a source position with its width, a literal, equality, mux, part-select, two-part concatenation -/
inductive CTerm where
  | var (p w : Nat)
  | lit (w v : Nat)
  | eq (a b : CTerm)
  | mux (c a b : CTerm)
  | slice (a : CTerm) (hi lo : Nat)
  | cat (a b : CTerm)
  deriving DecidableEq, Repr, Inhabited

namespace CTerm

/-- the width of a term -/
def width : CTerm → Nat
  | .var _ w => w
  | .lit w _ => w
  | .eq _ _ => 1
  | .mux _ a _ => a.width
  | .slice _ hi lo => hi - lo + 1
  | .cat a b => a.width + b.width

/-- well-formedness: equal operand widths of `eq`, a one-bit `mux` condition and equal branch widths, a part-select inside its operand -/
def wf : CTerm → Bool
  | .var _ _ => true
  | .lit _ _ => true
  | .eq a b => a.wf && b.wf && (a.width == b.width)
  | .mux c a b => c.wf && a.wf && b.wf && (c.width == 1) && (a.width == b.width)
  | .slice a hi lo => a.wf && decide (lo ≤ hi) && decide (hi < a.width)
  | .cat a b => a.wf && b.wf

/-- the value of a term at a valuation `V` of the source positions (a position's value is read modulo its width) -/
def den (V : Nat → Nat) : CTerm → Nat
  | .var p w => V p % 2 ^ w
  | .lit w v => v % 2 ^ w
  | .eq a b => if a.den V = b.den V then 1 else 0
  | .mux c a b => if c.den V ≠ 0 then a.den V else b.den V
  | .slice a hi lo => (a.den V >>> lo) % 2 ^ (hi - lo + 1)
  | .cat a b => (a.den V <<< b.width) ||| b.den V

theorem or_shift_lt {x y m n : Nat} (hx : x < 2 ^ m) (hy : y < 2 ^ n) : (x <<< n) ||| y < 2 ^ (m + n) := by
  have h1 : x <<< n < 2 ^ (m + n) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos n)
  have h2 : y < 2 ^ (m + n) := Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega))
  exact Nat.or_lt_two_pow h1 h2

/-- a well-formed term's value fits its width -/
theorem den_lt (V : Nat → Nat) : ∀ c : CTerm, c.wf = true → c.den V < 2 ^ c.width
  | .var p w, _ => Nat.mod_lt _ (Nat.two_pow_pos w)
  | .lit w v, _ => Nat.mod_lt _ (Nat.two_pow_pos w)
  | .eq a b, _ => by
    simp only [den, width]
    split <;> omega
  | .mux c a b, h => by
    simp only [wf, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hc, ha⟩, hb⟩, _⟩, hw⟩ := h
    simp only [den, width]
    split
    · exact den_lt V a ha
    · rw [hw]; exact den_lt V b hb
  | .slice a hi lo, _ => Nat.mod_lt _ (Nat.two_pow_pos _)
  | .cat a b, h => by
    simp only [wf, Bool.and_eq_true] at h
    simp only [den, width]
    exact or_shift_lt (den_lt V a h.1) (den_lt V b h.2)

end CTerm

/-! ## Translating the module's expressions -/

/-- a part-select, with the two simplifications the compiler's emitted forms need: a whole-width select is the term, a select of a literal is a literal -/
def mkSlice (c : CTerm) (hi lo : Nat) : CTerm :=
  if lo = 0 ∧ hi + 1 = c.width then c
  else match c with
    | .lit w v => .lit (hi - lo + 1) (((v % 2 ^ w) >>> lo) % 2 ^ (hi - lo + 1))
    | _ => .slice c hi lo

/-- the name table: the first entry for a name is its definition -/
def look (T : List (String × CTerm)) (n : String) : Option CTerm := (T.find? (fun p => p.1 == n)).map (·.2)

/-- the operators of the pilot children: equality and mux, with their width conditions -/
def opC : Operator → List CTerm → Option CTerm
  | .eq, [a, b] => if a.width = b.width then some (.eq a b) else none
  | .mux, [c, t, f] => if c.width = 1 ∧ t.width = f.width then some (.mux c t f) else none
  | _, _ => none

mutual
/-- the translation of an expression: names are replaced by their (declared-width-consistent) definitions -/
def toC (m : Module) (T : List (String × CTerm)) : Expr → Option CTerm
  | .const v w => if 0 ≤ v then some (.lit w v.toNat) else none
  | .ref n => match look T n with
    | some c => if declWidth m n = c.width then some c else none
    | none => none
  | .op o args => match toCList m T args with
    | some cs => opC o cs
    | none => none
  | .concat args => match toCList m T args with
    | some [a, b] => some (.cat a b)
    | _ => none
  | .slice e hi lo => match toC m T e with
    | some c => if lo ≤ hi ∧ hi < c.width then some (mkSlice c hi lo) else none
    | none => none
  | .sliceDim _ _ _ => none
  | .index _ _ => none

def toCList (m : Module) (T : List (String × CTerm)) : List Expr → Option (List CTerm)
  | [] => some []
  | a :: rest => match toC m T a, toCList m T rest with
    | some c, some cs => some (c :: cs)
    | _, _ => none
end

/-! ## Soundness of the translation -/

theorem mkSlice_width (c : CTerm) (hi lo : Nat) (h : lo ≤ hi ∧ hi < c.width) : (mkSlice c hi lo).width = hi - lo + 1 := by
  unfold mkSlice
  split
  · rename_i h1; obtain ⟨h0, h2⟩ := h1; omega
  · cases c <;> simp [CTerm.width]

theorem mkSlice_wf (c : CTerm) (hc : c.wf = true) (hi lo : Nat) (h : lo ≤ hi ∧ hi < c.width) :
    (mkSlice c hi lo).wf = true := by
  unfold mkSlice
  split
  · exact hc
  · cases c <;> simp_all [CTerm.wf]

theorem mkSlice_den (V : Nat → Nat) (c : CTerm) (hc : c.wf = true) (hi lo : Nat) (h : lo ≤ hi ∧ hi < c.width) :
    (mkSlice c hi lo).den V = (c.den V >>> lo) % 2 ^ (hi - lo + 1) := by
  unfold mkSlice
  split
  · rename_i h1
    obtain ⟨h0, h2⟩ := h1
    subst h0
    have := CTerm.den_lt V c hc
    rw [← h2] at this
    simp only [Nat.shiftRight_zero, Nat.sub_zero]
    exact (Nat.mod_eq_of_lt this).symm
  · cases c with
    | lit w v => simp [CTerm.den]
    | var p w => rfl
    | eq a b => rfl
    | mux a b c => rfl
    | slice a b c => rfl
    | cat a b => rfl

/-- a non-negative constant, as the evaluator reads it -/
theorem const_eval (v : Int) (w : Nat) (hv : 0 ≤ v) :
    mask w (Int.toNat (((v % (2 ^ w : Nat)) + (2 ^ w : Nat)) % (2 ^ w : Nat))) = v.toNat % 2 ^ w := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hv
  have hM : (0 : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos w
  have h1 : (((n : Int) % ((2 ^ w : Nat) : Int)) + ((2 ^ w : Nat) : Int)) % ((2 ^ w : Nat) : Int) =
      (n : Int) % ((2 ^ w : Nat) : Int) := by
    rw [Int.add_emod_right, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  rw [h1]
  have h2 : Int.toNat ((n : Int) % ((2 ^ w : Nat) : Int)) = n % 2 ^ w := by
    rw [← Int.natCast_emod]; rfl
  rw [h2]
  simp only [mask, Int.toNat_natCast]
  exact Nat.mod_mod _ _

theorem opC_cases {o : Operator} {cs : List CTerm} {c : CTerm} (h : opC o cs = some c) :
    (o = .eq ∧ ∃ a b, cs = [a, b] ∧ a.width = b.width ∧ c = .eq a b) ∨
    (o = .mux ∧ ∃ x y z, cs = [x, y, z] ∧ x.width = 1 ∧ y.width = z.width ∧ c = .mux x y z) := by
  unfold opC at h
  split at h
  · rename_i a b
    split at h
    · rename_i hw
      cases h
      exact Or.inl ⟨rfl, a, b, rfl, hw, rfl⟩
    · cases h
  · rename_i x y z
    split at h
    · rename_i hw
      cases h
      exact Or.inr ⟨rfl, x, y, z, rfl, hw.1, hw.2, rfl⟩
    · cases h
  · cases h

mutual
theorem toC_sound (m : Module) (T : List (String × CTerm)) (env : Env) (V : Nat → Nat)
    (hT : ∀ n c, look T n = some c → env n = c.den V ∧ c.wf = true) :
    ∀ (e : Expr) (c : CTerm), toC m T e = some c →
      c.wf = true ∧ widthOf (declWidth m) e = c.width ∧ evalExpr (declWidth m) env e = some (c.den V)
  | .const v w, c, h => by
    simp only [toC] at h
    split at h
    · rename_i hv
      cases h
      refine ⟨rfl, rfl, ?_⟩
      simp only [evalExpr, CTerm.den, const_eval v w hv]
    · cases h
  | .ref n, c, h => by
    simp only [toC] at h
    split at h
    · rename_i c' hc'
      split at h
      · rename_i hw
        cases h
        have := hT n c hc'
        exact ⟨this.2, by simpa [widthOf] using hw, by simp [evalExpr, this.1]⟩
      · cases h
    · cases h
  | .op o args, c, h => by
    simp only [toC] at h
    split at h
    · rename_i cs hcs
      obtain ⟨hlen, hwfs, hws, hev⟩ := toCList_sound m T env V hT args cs hcs
      rcases opC_cases h with ⟨rfl, a, b, rfl, hw, rfl⟩ | ⟨rfl, x, y, z, rfl, h1, h2, rfl⟩
      · rcases args with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, rest⟩⟩⟩ <;> simp at hlen
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
        refine ⟨?_, ?_, ?_⟩
        · simp [CTerm.wf, hw, hwfs a (by simp), hwfs b (by simp)]
        · simp [widthOf, CTerm.width]
        · simp only [List.map_cons, List.map_nil] at hev
          simp [evalExpr, hev, evalOp, CTerm.den]
      · rcases args with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | ⟨e4, rest⟩⟩⟩⟩ <;> simp at hlen
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
        refine ⟨?_, ?_, ?_⟩
        · simp [CTerm.wf, h1, h2, hwfs x (by simp), hwfs y (by simp), hwfs z (by simp)]
        · simp [widthOf, CTerm.width, hws.2.1]
        · simp only [List.map_cons, List.map_nil] at hev
          simp [evalExpr, hev, evalOp, CTerm.den, widthOf]
    · cases h
  | .concat args, c, h => by
    simp only [toC] at h
    split at h
    · rename_i a b hcs
      cases h
      obtain ⟨hlen, hwfs, hws, hev⟩ := toCList_sound m T env V hT args [a, b] hcs
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, rest⟩⟩⟩ <;> simp at hlen
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
      have ha : a.wf = true := hwfs a (by simp)
      have hb : b.wf = true := hwfs b (by simp)
      refine ⟨by simp [CTerm.wf, ha, hb], ?_, ?_⟩
      · simp [widthOf, widthOf.go, CTerm.width, hws.1, hws.2]
      · simp only [List.map_cons, List.map_nil] at hev
        have la := CTerm.den_lt V a ha
        have lb := CTerm.den_lt V b hb
        simp only [evalExpr, hev]
        show some (evalExpr.go (declWidth m) _ [CTerm.den V a, CTerm.den V b]) = _
        simp only [evalExpr.go, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, hws.1, hws.2,
          mask, Nat.zero_add, Nat.shiftLeft_zero, Nat.or_zero, Nat.mod_eq_of_lt la, Nat.mod_eq_of_lt lb, CTerm.den]
    · cases h
  | .slice e hi lo, c, h => by
    simp only [toC] at h
    split at h
    · rename_i c1 h1
      split at h
      · rename_i hh
        cases h
        obtain ⟨hw1, hww1, hev1⟩ := toC_sound m T env V hT e c1 h1
        refine ⟨mkSlice_wf c1 hw1 hi lo hh, ?_, ?_⟩
        · rw [mkSlice_width c1 hi lo hh]; rfl
        · rw [mkSlice_den V c1 hw1 hi lo hh]; simp [evalExpr, hev1, mask]
      · cases h
    · cases h
  | .sliceDim _ _ _, c, h => by simp [toC] at h
  | .index _ _, c, h => by simp [toC] at h

theorem toCList_sound (m : Module) (T : List (String × CTerm)) (env : Env) (V : Nat → Nat)
    (hT : ∀ n c, look T n = some c → env n = c.den V ∧ c.wf = true) :
    ∀ (es : List Expr) (cs : List CTerm), toCList m T es = some cs →
      es.length = cs.length ∧ (∀ c ∈ cs, c.wf = true) ∧
      es.map (widthOf (declWidth m)) = cs.map CTerm.width ∧
      evalList (declWidth m) env es = some (cs.map (·.den V))
  | [], cs, h => by
    simp only [toCList] at h
    cases h
    simp [evalList]
  | a :: rest, cs, h => by
    simp only [toCList] at h
    split at h
    · rename_i c1 cs1 h1 h2
      cases h
      obtain ⟨hw1, hww1, hev1⟩ := toC_sound m T env V hT a c1 h1
      obtain ⟨hl2, hwf2, hww2, hev2⟩ := toCList_sound m T env V hT rest cs1 h2
      refine ⟨by simp [hl2], ?_, ?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hw1
        · exact hwf2 c hc
      · simp [hww1, hww2]
      · simp [evalList, hev1, hev2]
    · cases h
end

/-! ## The module: a body of assignments -/

/-- the width of a port's type (`bit` = 1, `bitVector n` = n; any other type 0) -/
def portW (p : Port) : Nat :=
  match p.ty with
  | .bit => 1
  | .bitVector n => n
  | _ => 0

/-- translate the statements in order, extending the table by each assignment: the assigned wire's DECLARED width must be the definition's width (or the wire is an output port, which no later statement may read with a width: its declared width is not recorded); a statement that is not an assignment makes the check fail -/
def stepT (m : Module) : List (String × CTerm) → List Stmt → Option (List (String × CTerm))
  | T, [] => some T
  | T, .assign l r :: rest =>
    match toC m T r with
    | some c => if declWidth m l = c.width ∨ m.outputs.any (fun p => p.name == l) = true then stepT m ((l, c) :: T) rest else none
    | none => none
  | _, _ :: _ => none

theorem stepT_sound (m : Module) (mems : MEnv) (V : Nat → Nat) :
    ∀ (body : List Stmt) (T T' : List (String × CTerm)) (env : Env),
      (∀ n c, look T n = some c → env n = c.den V ∧ c.wf = true) → stepT m T body = some T' →
      ∃ env', evalAssigns (declWidth m) mems body env = some env' ∧
        ∀ n c, look T' n = some c → env' n = c.den V ∧ c.wf = true
  | [], T, T', env, hT, h => by
    simp only [stepT] at h
    cases h
    exact ⟨env, rfl, hT⟩
  | .assign l r :: rest, T, T', env, hT, h => by
    simp only [stepT] at h
    split at h
    · rename_i c hc
      split at h
      · obtain ⟨hw, hww, hev⟩ := toC_sound m T env V hT r c hc
        obtain ⟨env', he, hT'⟩ := stepT_sound m mems V rest ((l, c) :: T) T' (fun n => if n = l then c.den V else env n) (by
          intro n c' hn
          by_cases hnl : n = l
          · subst hnl
            simp only [look, List.find?_cons, beq_self_eq_true, Option.map_some, Option.some.injEq] at hn
            subst hn
            exact ⟨by simp, hw⟩
          · have hb : ((l == n) = false) := by simpa using Ne.symm hnl
            simp only [look, List.find?_cons, hb] at hn
            have := hT n c' (by simpa [look] using hn)
            exact ⟨by simpa [hnl] using this.1, this.2⟩) h
        refine ⟨env', ?_, hT'⟩
        simp only [evalAssigns, hev]
        exact he
      · cases h
    · cases h
  | .register .. :: rest, T, T', env, hT, h => by simp [stepT] at h
  | .memory .. :: rest, T, T', env, hT, h => by simp [stepT] at h
  | .inst .. :: rest, T, T', env, hT, h => by simp [stepT] at h

/-- the source: the source position of each input port (in port order) and one term per output port (in port order) -/
structure CSrc where
  inPos : List Nat
  outs : List CTerm

/-- **the validator for a combinational child**: the inputs are distinct and as many as the source's positions, each declared at its port width; the body is assignments; the translation of the body goes through; each output port's translation EQUALS the source term and the port is declared at that term's width -/
def checkComb (s : CSrc) (m : Module) : Bool :=
  decide (m.inputs.map (·.name)).Nodup &&
  (m.inputs.length == s.inPos.length) && (m.outputs.length == s.outs.length) &&
  (m.inputs.all fun p => declWidth m p.name == portW p) &&
  (match stepT m ((m.inputs.zip s.inPos).map (fun (p, q) => (p.name, CTerm.var q (portW p)))) m.body with
   | some T => (m.outputs.zip s.outs).all (fun (p, c) => (look T p.name == some c) && (portW p == c.width))
   | none => false)

theorem look_inputs (m : Module) (s : CSrc) (n : String) (c : CTerm)
    (h : look ((m.inputs.zip s.inPos).map (fun (p, q) => (p.name, CTerm.var q (portW p)))) n = some c) :
    ∃ (i : Nat) (p : Port) (q : Nat), m.inputs[i]? = some p ∧ s.inPos[i]? = some q ∧ n = p.name ∧ c = CTerm.var q (portW p) := by
  generalize m.inputs = ps at *
  generalize s.inPos = qs at *
  induction ps generalizing qs with
  | nil => simp [look] at h
  | cons p ps ih =>
    cases qs with
    | nil => simp [look] at h
    | cons q qs =>
      simp only [List.zip_cons_cons, List.map_cons, look, List.find?_cons] at h
      by_cases hn : p.name = n
      · simp only [hn, beq_self_eq_true, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨0, p, q, rfl, rfl, hn.symm, rfl⟩
      · have hb : ((p.name == n) = false) := by simpa using hn
        simp only [hb] at h
        obtain ⟨i, p', q', h1, h2, h3, h4⟩ := ih qs (by simpa [look] using h)
        exact ⟨i + 1, p', q', by simpa using h1, by simpa using h2, h3, h4⟩

/-- **soundness of the validator**: if `checkComb s m` is true, then for EVERY valuation `V` of the source positions, every memory state and every environment whose input ports carry the source's inputs, the module's IR semantics (`evalAssigns` at the declared widths) succeeds, and every output port carries the value of the source's term for it -/
theorem checkComb_sound (s : CSrc) (m : Module) (h : checkComb s m = true) (V : Nat → Nat) (mems : MEnv) (env : Env)
    (hin : ∀ (i : Nat) (p : Port) (q : Nat), m.inputs[i]? = some p → s.inPos[i]? = some q → env p.name = V q % 2 ^ portW p) :
    ∃ env', evalAssigns (declWidth m) mems m.body env = some env' ∧
      ∀ (i : Nat) (p : Port) (c : CTerm), m.outputs[i]? = some p → s.outs[i]? = some c → env' p.name = c.den V := by
  unfold checkComb at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h⟩ := h
  split at h
  · rename_i T' hT'
    have hT0 : ∀ n c, look ((m.inputs.zip s.inPos).map (fun (p, q) => (p.name, CTerm.var q (portW p)))) n = some c →
        env n = c.den V ∧ c.wf = true := by
      intro n c hn
      obtain ⟨i, p, q, h1, h2, rfl, rfl⟩ := look_inputs m s n c hn
      exact ⟨by simpa [CTerm.den] using hin i p q h1 h2, rfl⟩
    obtain ⟨env', he, hT⟩ := stepT_sound m mems V m.body _ T' env hT0 hT'
    refine ⟨env', he, ?_⟩
    intro i p c hp hc
    have hz : (m.outputs.zip s.outs)[i]? = some (p, c) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hp, hc⟩
    have hmem := List.all_eq_true.mp h (p, c) (List.mem_of_getElem? hz)
    have hl : look T' p.name = some c := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hmem
      exact hmem.1
    exact (hT p.name c hl).1
  · cases h

end Tools.ShippingFGCircuitS3tComb
