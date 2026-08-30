/-
  M4, first fragment: DIRECT forward correctness of the emitter.

      evalSV wof env (widthOf we e) (emitAstExpr wof e) = evalExpr we env e

  — the IR value of a fragment expression equals the VERILOG value of
  its emission, evaluated by the SystemVerilog-subset semantics at the
  assignment context width (which the module fragment's width-agreement
  conditions pin to `widthOf we e`).  This is the statement that removes
  the PARSER from the trusted base for the emit direction.

  The v0 fragment deliberately requires WIDTH-UNIFORM operands on
  arithmetic (`widthOf a = widthOf b`) and mux arms: Verilog evaluates
  context-determined operands at the CONTEXT width, so a bare
  mixed-width nested addition keeps its inner carry where the IR
  semantics masks per node — the emitter does not (yet) pin binop
  operands, so mixed widths sit outside this fragment (recorded as the
  M4 opening investigation).
-/
import Tools.SVParser.EmitAst
import Tools.SVParser.SVSemantics

namespace Tools.SVParser.EmitSem

open Tools.SVParser.AST
open Tools.SVParser.SVSemantics
open Sparkle.IR.AST
open Sparkle.IR.Semantics

/-- IR shapes whose EMISSIONS are context-immune (see `immuneSV`):
    refs, fitting constants, compares, the pinned NOT (a size cast),
    and every slice (all three slice emission arms are idents, ident
    slices, or size casts). -/
def immuneE : Expr → Bool
  | .ref _ => true
  | .const v w => v < ((2 ^ w : Nat) : Int)
  | .op .not [_] => true
  | .op op [a, b] =>
    match op with
    | .eq | .lt_u | .le_u | .gt_u | .ge_u => true
    | .lt_s | .le_s | .gt_s | .ge_s => true
    -- bitwise ops are carry-free: immune operands make the node immune
    | .and | .or | .xor => immuneE a && immuneE b
    | _ => false
  | .slice _ _ _ => true
  -- concat elements are self-determined; the assembly fits its width
  | .concat _ => true
  | _ => false

/-- v0 forward fragment: refs, fitting constants, width-uniform
    unsigned arithmetic/bitwise, width-uniform mux, and the pinned
    NOT. -/
inductive SF4 (wof : String → Option Nat) (we : WEnv) : Expr → Prop
  | ref (n : String)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n)) : SF4 wof we (.ref n)
  | const (v : Int) (w : Nat) (hw : 0 < w) :
      SF4 wof we (.const v w)
  | binop (op : Operator)
      (hop : op = .and ∨ op = .or ∨ op = .xor ∨ op = .add
        ∨ op = .sub ∨ op = .mul)
      {a b : Expr}
      -- each operand either IS the max width (evaluating it at the
      -- node's context is exactly the IH) or has a context-immune
      -- emission (zero-extension changes nothing — a Nat value is its
      -- own zero-extension)
      (hA : Sparkle.IR.Semantics.widthOf we a
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE a = true)
      (hB : Sparkle.IR.Semantics.widthOf we b
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE b = true)
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])
  | mux {c t f : Expr}
      (hwf : Sparkle.IR.Semantics.widthOf we f
        = Sparkle.IR.Semantics.widthOf we t)
      (hc : SF4 wof we c) (ht : SF4 wof we t) (hf : SF4 wof we f) :
      SF4 wof we (.op .mux [c, t, f])
  | not {x : Expr} (w : Nat)
      (hwT : Tools.SVParser.EmitAst.exprWidthT wof x = some w)
      (hwS : Sparkle.IR.Semantics.widthOf we x = w)
      (hw0 : 0 < w)
      (hx : SF4 wof we x) : SF4 wof we (.op .not [x])
  | neg {x : Expr} (hx : SF4 wof we x) :
      SF4 wof we (.op .neg [x])
  | cmpU (op : Operator)
      (hop : op = .eq ∨ op = .lt_u ∨ op = .le_u ∨ op = .gt_u
        ∨ op = .ge_u)
      {a b : Expr}
      -- Verilog sizes comparison operands to their own max; each
      -- operand either IS the max width or is context-immune
      (hA : Sparkle.IR.Semantics.widthOf we a
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE a = true)
      (hB : Sparkle.IR.Semantics.widthOf we b
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE b = true)
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])
  | cmpS (op : Operator)
      (hop : op = .lt_s ∨ op = .le_s ∨ op = .gt_s ∨ op = .ge_s)
      {a b : Expr}
      -- the emitter's bias encoding `((x&m)^sb) OP ((y&m)^sb)` needs
      -- the emitter's width computation to agree with the IR's
      (hwTa : Tools.SVParser.EmitAst.exprWidthT wof a
        = some (Sparkle.IR.Semantics.widthOf we a))
      (hwTb : Tools.SVParser.EmitAst.exprWidthT wof b
        = some (Sparkle.IR.Semantics.widthOf we b))
      (hA : Sparkle.IR.Semantics.widthOf we a
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE a = true)
      (hB : Sparkle.IR.Semantics.widthOf we b
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE b = true)
      (hw0 : 0 < max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b))
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])
  | cmpS1 (op : Operator)
      (hop : op = .lt_s ∨ op = .le_s ∨ op = .gt_s ∨ op = .ge_s)
      {a b : Expr}
      -- the emitter cannot width the RIGHT operand (a mul/shift): it
      -- biases at the LEFT operand's width, which must therefore BE
      -- the comparison width
      (hwTa : Tools.SVParser.EmitAst.exprWidthT wof a
        = some (Sparkle.IR.Semantics.widthOf we a))
      (hwTb : Tools.SVParser.EmitAst.exprWidthT wof b = none)
      (hwba : Sparkle.IR.Semantics.widthOf we b
        ≤ Sparkle.IR.Semantics.widthOf we a)
      (hB : Sparkle.IR.Semantics.widthOf we b
          = Sparkle.IR.Semantics.widthOf we a
        ∨ immuneE b = true)
      (hw0 : 0 < Sparkle.IR.Semantics.widthOf we a)
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])
  | sliceRef (n : String) (hi lo : Nat)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n))
      (hlo : lo ≤ hi) (hhi : hi < we n)
      -- the exact full-width slice is the ELIDED emission — see
      -- `sliceRefFull`
      (hne : ¬(lo = 0 ∧ hi + 1 = we n)) :
      SF4 wof we (.slice (.ref n) hi lo)
  | sliceRefFull (n : String) (hi : Nat)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n))
      (hfull : hi + 1 = we n) :
      SF4 wof we (.slice (.ref n) hi 0)
  | concat {args : List Expr}
      (hall : ∀ e, e ∈ args → SF4 wof we e)
      -- op-typed elements get the emitter's width-pinning size cast;
      -- the pin is faithful when the emitter's width matches the IR's
      (hpin : ∀ e, e ∈ args → ∀ op as, e = .op op as →
        Tools.SVParser.EmitAst.exprWidthT wof e
          = some (Sparkle.IR.Semantics.widthOf we e)
        ∧ 0 < Sparkle.IR.Semantics.widthOf we e) :
      SF4 wof we (.concat args)
  | castEnc {x : Expr} (w : Nat) (hw0 : 0 < w)
      (hx : SF4 wof we x)
      -- Verilog evaluates a cast's argument at the CAST width: a
      -- DOWN-cast evaluates it at its own width (safe for any
      -- fragment shape); an UP-cast widens the context, which is only
      -- faithful for context-immune emissions.
      (hsafe : w ≤ Sparkle.IR.Semantics.widthOf we x
        ∨ immuneE x = true) :
      SF4 wof we (.slice (.concat [.const 0 w, x]) (w - 1) 0)
  | sliceGen {x : Expr} (hi lo : Nat)
      (hcomp : ∀ n, x ≠ .ref n)
      (hncast : ∀ w y, x = .concat [.const 0 w, y] →
        ¬(lo = 0 ∧ hi + 1 = w))
      (hlo : lo ≤ hi)
      (hlo32 : lo < 2 ^ 32)
      (hx : SF4 wof we x)
      -- the emitted `n'((E) >> lo)` puts E in an n-bit-or-wider
      -- context; safe when the select stays inside the value, or when
      -- the emission is context-immune
      (hsafe : hi + 1 - lo ≤ Sparkle.IR.Semantics.widthOf we x
        ∨ immuneE x = true) :
      SF4 wof we (.slice x hi lo)
  | shiftOp (op : Operator) (hop : op = .shl ∨ op = .shr)
      {a b : Expr}
      -- Verilog: shift result width = LEFT operand width; the IR takes
      -- the max of both.  They coincide when the amount is no wider
      -- than the value (the amount itself is self-determined, so its
      -- own evaluation always matches the IH).
      (hwb : Sparkle.IR.Semantics.widthOf we b
        ≤ Sparkle.IR.Semantics.widthOf we a)
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])

/-- Emission shapes whose value is CONTEXT-IMMUNE: evaluating at any
    width ≥ their own gives the same value.  These are exactly the
    shapes that carry their own mask (casts, slices, fitting literals,
    0/1-valued compares) or are bounded by declaration (idents under a
    width-respecting environment). -/
def immuneSV : SVExpr → Bool
  | .ident _ => true
  | .lit (.decimal (some w) v) => v < 2 ^ w
  | .lit (.hex (some w) v) => v < 2 ^ w
  | .sizeCast _ _ => true
  | .slice (.ident _) _ _ => true
  | .binary .eq _ _ | .binary .lt _ _ | .binary .le _ _
  | .binary .gt _ _ | .binary .ge _ _ => true
  -- a concat is immune outright: its elements are SELF-determined
  -- (evaluated at context 0 inside `goConcat`), and the assembled
  -- value fits the total width, so the outer context mask is inert
  | .concat _ => true
  -- bitwise ops are carry-free: with immune (hence width-bounded)
  -- operands, widening the context adds no bits
  | .binary .bitAnd a b => immuneSV a && immuneSV b
  | .binary .bitOr a b => immuneSV a && immuneSV b
  | .binary .bitXor a b => immuneSV a && immuneSV b
  | _ => false

/-- `goConcat`'s assembly fits the total width (each element is masked
    to its own width before shifting into place). -/
private theorem goConcat_lt {wof : String → Option Nat} {env : SEnv} :
    ∀ (svs : List SVExpr) (tw v : Nat),
      widthSV.go wof svs = some tw →
      goConcat wof env svs = some v → v < 2 ^ tw := by
  intro svs
  induction svs with
  | nil =>
    intro tw v hw hv
    simp only [widthSV.go, Option.some_inj] at hw
    simp only [goConcat, Option.some_inj] at hv
    subst hw; subst hv
    simp
  | cons a rest ih =>
    intro tw v hw hv
    simp only [widthSV.go, Option.bind_eq_bind] at hw
    obtain ⟨wa, hwa, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨wr, hwr, hw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [Option.some_inj] at hw
    subst hw
    simp only [goConcat, Option.bind_eq_bind] at hv
    obtain ⟨wa', hwa', hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, hva, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wr', hwr', hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vr, hvr, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    rw [hwa] at hwa'
    rw [hwr] at hwr'
    simp only [Option.some_inj] at hwa' hwr'
    subst hwa'; subst hwr'
    have h1 : mask wa va < 2 ^ wa := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : mask wa va <<< wr < 2 ^ (wa + wr) := by
      rw [Nat.shiftLeft_eq, Nat.pow_add]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
    have h3 : vr < 2 ^ (wa + wr) :=
      Nat.lt_of_lt_of_le (ih wr vr hwr hvr)
        (Nat.pow_le_pow_right (by omega) (by omega))
    exact Nat.or_lt_two_pow h2 h3

/-- Context-immunity, semantically: an immune emission evaluates the
    same at every width ≥ its own (and its value fits its width).
    This is what makes the self-determined boundaries (cast arguments,
    comparison operands) safe to UP-size — the extra context bits
    never materialize. -/
private theorem evalAt_immune_all {wof : String → Option Nat}
    {env : SEnv}
    (hb : ∀ n wn, wof n = some wn → env n < 2 ^ wn) :
    ∀ (sv : SVExpr) (w : Nat), immuneSV sv = true →
      widthSV wof sv = some w →
      (∀ v, evalAt wof env w sv = some v → v < 2 ^ w)
      ∧ (∀ W, w ≤ W → evalAt wof env W sv = evalAt wof env w sv)
  | .ident n, w, _, hw => by
    simp only [widthSV] at hw
    have hbn := hb n w hw
    constructor
    · intro v hv
      simp only [evalAt, hw, Option.bind_eq_bind, Option.bind_some,
        Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      have hpow : (2 : Nat) ^ w ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hW
      simp only [evalAt, hw, Option.bind_eq_bind, Option.bind_some]
      simp [mask, Nat.mod_eq_of_lt hbn,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hbn hpow)]
  | .lit (.decimal (some w') v), w, himm, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    simp only [immuneSV, decide_eq_true_eq] at himm
    constructor
    · intro u hu
      simp only [evalAt, litVal, Option.some_inj] at hu
      subst hu
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      have hpow : (2 : Nat) ^ w' ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hW
      simp [evalAt, litVal, mask, Nat.mod_eq_of_lt himm,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le himm hpow)]
  | .lit (.hex (some w') v), w, himm, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    simp only [immuneSV, decide_eq_true_eq] at himm
    constructor
    · intro u hu
      simp only [evalAt, litVal, Option.some_inj] at hu
      subst hu
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      have hpow : (2 : Nat) ^ w' ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hW
      simp [evalAt, litVal, mask, Nat.mod_eq_of_lt himm,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le himm hpow)]
  | .sizeCast w' a, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨u, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      have hpow : (2 : Nat) ^ w' ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hW
      simp only [evalAt]
      cases hv : evalSV wof env w' a with
      | none => simp [hv]
      | some v =>
        have hlt : v % 2 ^ w' < 2 ^ w' := Nat.mod_lt _ (Nat.two_pow_pos _)
        simp [hv, mask, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow),
          Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), Nat.mod_eq_of_lt hlt]
  | .slice (.ident n) hi lo, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨wn, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      by_cases hc : lo ≤ hi ∧ hi < wn
      · simp only [if_pos hc, Option.some_inj] at hv
        subst hv
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · simp [if_neg hc] at hv
    · intro W hW
      have hpow : (2 : Nat) ^ (hi - lo + 1) ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by omega) hW
      simp only [evalAt]
      cases hwn : wof n with
      | none => simp [hwn]
      | some wn =>
        by_cases hc : lo ≤ hi ∧ hi < wn
        · have hlt : (env n >>> lo) % 2 ^ (hi - lo + 1)
              < 2 ^ (hi - lo + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
          simp [hwn, hc, mask,
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow),
            Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), Nat.mod_eq_of_lt hlt]
        · simp [hwn, hc]
  | .binary .eq a b, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    refine ⟨?_, fun W _ => by simp only [evalAt]⟩
    intro v hv
    simp only [evalAt] at hv
    obtain ⟨wa, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    split <;> omega
  | .binary .lt a b, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    refine ⟨?_, fun W _ => by simp only [evalAt]⟩
    intro v hv
    simp only [evalAt] at hv
    obtain ⟨wa, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    split <;> omega
  | .binary .le a b, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    refine ⟨?_, fun W _ => by simp only [evalAt]⟩
    intro v hv
    simp only [evalAt] at hv
    obtain ⟨wa, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    split <;> omega
  | .binary .gt a b, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    refine ⟨?_, fun W _ => by simp only [evalAt]⟩
    intro v hv
    simp only [evalAt] at hv
    obtain ⟨wa, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    split <;> omega
  | .binary .ge a b, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    refine ⟨?_, fun W _ => by simp only [evalAt]⟩
    intro v hv
    simp only [evalAt] at hv
    obtain ⟨wa, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    split <;> omega
  | .concat svs, w, _, hw => by
    simp only [widthSV] at hw
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨u, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      have hpow : (2 : Nat) ^ w ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hW
      simp only [evalAt]
      cases hv : goConcat wof env svs with
      | none => simp [hv]
      | some v =>
        have hlt := goConcat_lt svs w v hw hv
        simp [hv, mask, Nat.mod_eq_of_lt hlt,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow)]
  | .binary .bitAnd a b, w, himm, hw => by
    simp only [immuneSV, Bool.and_eq_true] at himm
    obtain ⟨himmA, himmB⟩ := himm
    simp only [widthSV, Option.bind_eq_bind] at hw
    obtain ⟨sa, hsa, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨sb, hsb, hw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [Option.some_inj] at hw
    subst hw
    obtain ⟨bndA, stbA⟩ := evalAt_immune_all hb a sa himmA hsa
    obtain ⟨bndB, stbB⟩ := evalAt_immune_all hb b sb himmB hsb
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      simp only [evalAt]
      rw [stbA W (Nat.le_trans (Nat.le_max_left _ _) hW),
          stbB W (Nat.le_trans (Nat.le_max_right _ _) hW),
          stbA (max sa sb) (Nat.le_max_left _ _),
          stbB (max sa sb) (Nat.le_max_right _ _)]
      cases hva : evalAt wof env sa a with
      | none => simp [hva]
      | some va =>
      cases hvb : evalAt wof env sb b with
      | none => simp [hva, hvb]
      | some vb =>
      have hlt : va &&& vb < 2 ^ max sa sb :=
        Nat.lt_of_le_of_lt Nat.and_le_left
          (Nat.lt_of_lt_of_le (bndA va hva)
            (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)))
      have hpow : (2 : Nat) ^ max sa sb ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by omega) hW
      simp [hva, hvb, mask, Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow)]
  | .binary .bitOr a b, w, himm, hw => by
    simp only [immuneSV, Bool.and_eq_true] at himm
    obtain ⟨himmA, himmB⟩ := himm
    simp only [widthSV, Option.bind_eq_bind] at hw
    obtain ⟨sa, hsa, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨sb, hsb, hw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [Option.some_inj] at hw
    subst hw
    obtain ⟨bndA, stbA⟩ := evalAt_immune_all hb a sa himmA hsa
    obtain ⟨bndB, stbB⟩ := evalAt_immune_all hb b sb himmB hsb
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      simp only [evalAt]
      rw [stbA W (Nat.le_trans (Nat.le_max_left _ _) hW),
          stbB W (Nat.le_trans (Nat.le_max_right _ _) hW),
          stbA (max sa sb) (Nat.le_max_left _ _),
          stbB (max sa sb) (Nat.le_max_right _ _)]
      cases hva : evalAt wof env sa a with
      | none => simp [hva]
      | some va =>
      cases hvb : evalAt wof env sb b with
      | none => simp [hva, hvb]
      | some vb =>
      have hlt : va ||| vb < 2 ^ max sa sb :=
        Nat.or_lt_two_pow
          (Nat.lt_of_lt_of_le (bndA va hva)
            (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)))
          (Nat.lt_of_lt_of_le (bndB vb hvb)
            (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)))
      have hpow : (2 : Nat) ^ max sa sb ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by omega) hW
      simp [hva, hvb, mask, Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow)]
  | .binary .bitXor a b, w, himm, hw => by
    simp only [immuneSV, Bool.and_eq_true] at himm
    obtain ⟨himmA, himmB⟩ := himm
    simp only [widthSV, Option.bind_eq_bind] at hw
    obtain ⟨sa, hsa, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨sb, hsb, hw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [Option.some_inj] at hw
    subst hw
    obtain ⟨bndA, stbA⟩ := evalAt_immune_all hb a sa himmA hsa
    obtain ⟨bndB, stbB⟩ := evalAt_immune_all hb b sb himmB hsb
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      simp only [evalAt]
      rw [stbA W (Nat.le_trans (Nat.le_max_left _ _) hW),
          stbB W (Nat.le_trans (Nat.le_max_right _ _) hW),
          stbA (max sa sb) (Nat.le_max_left _ _),
          stbB (max sa sb) (Nat.le_max_right _ _)]
      cases hva : evalAt wof env sa a with
      | none => simp [hva]
      | some va =>
      cases hvb : evalAt wof env sb b with
      | none => simp [hva, hvb]
      | some vb =>
      have hlt : va ^^^ vb < 2 ^ max sa sb :=
        Nat.xor_lt_two_pow
          (Nat.lt_of_lt_of_le (bndA va hva)
            (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)))
          (Nat.lt_of_lt_of_le (bndB vb hvb)
            (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)))
      have hpow : (2 : Nat) ^ max sa sb ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by omega) hW
      simp [hva, hvb, mask, Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow)]

/-- The stability face of `evalAt_immune_all` (the shape the fragment
    proofs consume). -/
private theorem evalAt_immune {wof : String → Option Nat} {env : SEnv}
    {sv : SVExpr} {w : Nat}
    (himm : immuneSV sv = true)
    (hw : widthSV wof sv = some w)
    (hb : ∀ n wn, wof n = some wn → env n < 2 ^ wn) :
    ∀ W, w ≤ W → evalAt wof env W sv = evalAt wof env w sv :=
  (evalAt_immune_all hb sv w himm hw).2

/-- v0 fragment expressions always evaluate (their shapes are total in
    `evalExpr`). -/
theorem sf4_eval_isSome {wof : String → Option Nat} {we : WEnv}
    {e : Expr} (h : SF4 wof we e) :
    ∀ env, (evalExpr we env e).isSome := by
  induction h with
  | ref n hs hw => intro env; simp [evalExpr]
  | const v w hw => intro env; simp [evalExpr]
  | binop op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h | h | h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]
  | mux hwf hc ht hf ihc iht ihf =>
    rename_i c t f
    intro env
    obtain ⟨vc, hvc⟩ := Option.isSome_iff_exists.mp (ihc env)
    obtain ⟨vt, hvt⟩ := Option.isSome_iff_exists.mp (iht env)
    obtain ⟨vf, hvf⟩ := Option.isSome_iff_exists.mp (ihf env)
    simp [evalExpr, evalList, hvc, hvt, hvf, evalOp]
  | not w hwT hwS hw0 hx ihx =>
    rename_i x
    intro env
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp (ihx env)
    simp [evalExpr, evalList, hvx, evalOp]
  | neg hx ihx =>
    rename_i x
    intro env
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp (ihx env)
    simp [evalExpr, evalList, hvx, evalOp]
  | cmpU op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h | h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]
  | cmpS op hop hwTa hwTb hA hB hw0 ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]
  | cmpS1 op hop hwTa hwTb hwba hB hw0 ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]
  | sliceRef n hi lo hs hw hlo hhi hne =>
    intro env; simp [evalExpr]
  | sliceRefFull n hi hs hw hfull =>
    intro env; simp [evalExpr]
  | concat hall hpin ihall =>
    rename_i args
    intro env
    have : ∀ (as : List Expr), (∀ e, e ∈ as → (evalExpr we env e).isSome)
        → (evalList we env as).isSome := by
      intro as
      induction as with
      | nil => intro _; simp [evalList]
      | cons a rest ih =>
        intro hmem
        obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp
          (hmem a (List.mem_cons_self ..))
        obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp
          (ih fun e he => hmem e (List.mem_cons_of_mem _ he))
        simp [evalList, hva, hvs]
    obtain ⟨vals, hvals⟩ := Option.isSome_iff_exists.mp
      (this args fun e he => ihall e he env)
    simp [evalExpr, hvals]
  | castEnc w hw0 hx hsafe ihx =>
    rename_i x
    intro env
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp (ihx env)
    simp [evalExpr, evalList, hvx]
  | sliceGen hi lo hcomp hncast hlo hlo32 hx hsafe ihx =>
    rename_i x
    intro env
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp (ihx env)
    simp [evalExpr, hvx]
  | shiftOp op hop hwb ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]

private theorem evalList_length {we : WEnv} {env : Env} :
    ∀ (as : List Expr) (vs : List Nat),
      evalList we env as = some vs → vs.length = as.length := by
  intro as
  induction as with
  | nil => intro vs h; simp [evalList] at h; simp [← h]
  | cons a rest ih =>
    intro vs h
    simp only [evalList, Option.bind_eq_bind] at h
    obtain ⟨va, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vr, hvr, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some_inj] at h
    subst h
    simp [ih vr hvr]

private theorem zip_foldl_width {we : WEnv} :
    ∀ (as : List Expr) (vs : List Nat) (acc : Nat),
      as.length = vs.length →
      (as.zip vs).foldl (fun acc (p : Expr × Nat) =>
        acc + Sparkle.IR.Semantics.widthOf we p.1) acc
      = acc + Sparkle.IR.Semantics.widthOf.go we as := by
  intro as
  induction as with
  | nil =>
    intro vs acc _
    simp [Sparkle.IR.Semantics.widthOf.go]
  | cons a rest ih =>
    intro vs acc hlen
    cases vs with
    | nil => simp at hlen
    | cons v vrest =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih vrest _ (by simpa using hlen),
        Sparkle.IR.Semantics.widthOf.go]
      omega

private theorem evalOp_mask_bound {we : WEnv} {op : Operator}
    {args : List Expr} {vals : List Nat} {w v : Nat}
    (hop : op = .and ∨ op = .or ∨ op = .xor ∨ op = .add
      ∨ op = .sub ∨ op = .mul)
    (h : evalOp we op args vals w = some v) : v < 2 ^ w := by
  rcases hop with h' | h' | h' | h' | h' | h' <;> subst h' <;>
  · match vals, h with
    | [a, b], h =>
      simp only [evalOp, Option.some_inj] at h
      subst h
      exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The IR's MSB-first assembly fits the total width (no boundedness
    of the values needed — `go` masks each element itself). -/
private theorem evalExpr_go_lt {we : WEnv} :
    ∀ (args : List Expr) (vals : List Nat),
      args.length = vals.length →
      Sparkle.IR.Semantics.evalExpr.go we args vals
        < 2 ^ Sparkle.IR.Semantics.widthOf.go we args := by
  intro args
  induction args with
  | nil =>
    intro vals _
    simp [Sparkle.IR.Semantics.evalExpr.go,
      Sparkle.IR.Semantics.widthOf.go]
  | cons a rest ih =>
    intro vals hlen
    cases vals with
    | nil => simp at hlen
    | cons v vrest =>
      simp only [Sparkle.IR.Semantics.evalExpr.go,
        Sparkle.IR.Semantics.widthOf.go]
      rw [zip_foldl_width rest vrest 0 (by simpa using hlen)]
      simp only [Nat.zero_add]
      have h1 : mask (Sparkle.IR.Semantics.widthOf we a) v
          < 2 ^ Sparkle.IR.Semantics.widthOf we a :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have h2 : mask (Sparkle.IR.Semantics.widthOf we a) v
            <<< Sparkle.IR.Semantics.widthOf.go we rest
          < 2 ^ (Sparkle.IR.Semantics.widthOf we a
              + Sparkle.IR.Semantics.widthOf.go we rest) := by
        rw [Nat.shiftLeft_eq, Nat.pow_add]
        exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
      have h3 : Sparkle.IR.Semantics.evalExpr.go we rest vrest
          < 2 ^ (Sparkle.IR.Semantics.widthOf we a
              + Sparkle.IR.Semantics.widthOf.go we rest) :=
        Nat.lt_of_lt_of_le (ih vrest (by simpa using hlen))
          (Nat.pow_le_pow_right (by omega) (by omega))
      exact Nat.or_lt_two_pow h2 h3

/-- Element-wise alignment of the emitter's concat with the IR's:
    same total width, same MSB-first assembly, and the assembled value
    fits its total width (so the context mask at the top is inert). -/
private theorem concat_elems_sem {wof : String → Option Nat} {we : WEnv}
    {env : Env} :
    ∀ (args : List Expr) (svs : List SVExpr),
      (∀ e, e ∈ args → (evalExpr we env e).isSome) →
      (∀ e, e ∈ args → ∀ sv,
        Tools.SVParser.EmitAst.emitAstExpr wof e = some sv →
          widthSV wof sv = some (Sparkle.IR.Semantics.widthOf we e)
          ∧ evalAt wof env (Sparkle.IR.Semantics.widthOf we e) sv
              = evalExpr we env e) →
      (∀ e, e ∈ args → ∀ op as, e = .op op as →
        Tools.SVParser.EmitAst.exprWidthT wof e
          = some (Sparkle.IR.Semantics.widthOf we e)
        ∧ 0 < Sparkle.IR.Semantics.widthOf we e) →
      Tools.SVParser.EmitAst.emitConcatElems wof args = some svs →
      widthSV.go wof svs
          = some (Sparkle.IR.Semantics.widthOf.go we args)
      ∧ ∃ vals, evalList we env args = some vals
        ∧ goConcat wof env svs
            = some (Sparkle.IR.Semantics.evalExpr.go we args vals)
        ∧ Sparkle.IR.Semantics.evalExpr.go we args vals
            < 2 ^ Sparkle.IR.Semantics.widthOf.go we args := by
  intro args
  induction args with
  | nil =>
    intro svs _ _ _ hemit
    simp only [Tools.SVParser.EmitAst.emitConcatElems,
      Option.some_inj] at hemit
    subst hemit
    exact ⟨by simp [widthSV.go, Sparkle.IR.Semantics.widthOf.go],
      [], by simp [evalList],
      by simp [goConcat, Sparkle.IR.Semantics.evalExpr.go],
      by simp [Sparkle.IR.Semantics.evalExpr.go,
        Sparkle.IR.Semantics.widthOf.go, Nat.zero_lt_one]⟩
  | cons a rest ih =>
    intro svs hsome hsem hpin hemit
    obtain ⟨vA, hvA⟩ := Option.isSome_iff_exists.mp
      (hsome a (List.mem_cons_self ..))
    -- the assembly, abstracted over the (possibly cast-pinned) head:
    -- any head emission with the right width whose value agrees with
    -- the IR element up to its own mask assembles correctly
    have finish : ∀ (ca : SVExpr) (es : List SVExpr),
        Tools.SVParser.EmitAst.emitConcatElems wof rest = some es →
        widthSV wof ca = some (Sparkle.IR.Semantics.widthOf we a) →
        (∃ va, evalSV wof env 0 ca = some va
          ∧ mask (Sparkle.IR.Semantics.widthOf we a) va
            = mask (Sparkle.IR.Semantics.widthOf we a) vA) →
        widthSV.go wof (ca :: es)
            = some (Sparkle.IR.Semantics.widthOf.go we (a :: rest))
        ∧ ∃ vals, evalList we env (a :: rest) = some vals
          ∧ goConcat wof env (ca :: es)
              = some (Sparkle.IR.Semantics.evalExpr.go we (a :: rest) vals)
          ∧ Sparkle.IR.Semantics.evalExpr.go we (a :: rest) vals
              < 2 ^ Sparkle.IR.Semantics.widthOf.go we (a :: rest) := by
      rintro ca es hes htw ⟨va, hva, hmva⟩
      obtain ⟨hwgo, vals, hvals, hgo, hbnd⟩ := ih es
        (fun e he => hsome e (List.mem_cons_of_mem _ he))
        (fun e he => hsem e (List.mem_cons_of_mem _ he))
        (fun e he => hpin e (List.mem_cons_of_mem _ he))
        hes
      have hlen := evalList_length rest vals hvals
      refine ⟨?_, vA :: vals, ?_, ?_, ?_⟩
      · simp only [widthSV.go, htw, hwgo, Option.bind_eq_bind,
          Option.bind_some, Sparkle.IR.Semantics.widthOf.go]
      · simp [evalList, hvA, hvals]
      · simp only [goConcat, htw, hva, hwgo, hgo, Option.bind_eq_bind,
          Option.bind_some, Option.some_inj,
          Sparkle.IR.Semantics.evalExpr.go]
        rw [zip_foldl_width rest vals 0 hlen.symm, hmva]
        simp
      · simp only [Sparkle.IR.Semantics.evalExpr.go,
          Sparkle.IR.Semantics.widthOf.go]
        rw [zip_foldl_width rest vals 0 hlen.symm]
        simp only [Nat.zero_add]
        have h1 : mask (Sparkle.IR.Semantics.widthOf we a) vA
            < 2 ^ Sparkle.IR.Semantics.widthOf we a :=
          Nat.mod_lt _ (Nat.two_pow_pos _)
        have h2 : mask (Sparkle.IR.Semantics.widthOf we a) vA
              <<< Sparkle.IR.Semantics.widthOf.go we rest
            < 2 ^ (Sparkle.IR.Semantics.widthOf we a
                + Sparkle.IR.Semantics.widthOf.go we rest) := by
          rw [Nat.shiftLeft_eq, Nat.pow_add]
          exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
        have h3 : Sparkle.IR.Semantics.evalExpr.go we rest vals
            < 2 ^ (Sparkle.IR.Semantics.widthOf we a
                + Sparkle.IR.Semantics.widthOf.go we rest) :=
          Nat.lt_of_lt_of_le hbnd
            (Nat.pow_le_pow_right (by omega) (by omega))
        exact Nat.or_lt_two_pow h2 h3
    cases a
    case op op' as' =>
      obtain ⟨hpT, hp0⟩ := hpin _ (List.mem_cons_self ..) op' as' rfl
      simp only [Tools.SVParser.EmitAst.emitConcatElems, hpT,
        Option.bind_eq_bind] at hemit
      obtain ⟨ea, hea, hemit⟩ := Option.bind_eq_some_iff.mp hemit
      obtain ⟨es, hes, hemit⟩ := Option.bind_eq_some_iff.mp hemit
      simp only [Option.some_inj] at hemit
      rw [if_pos hp0] at hemit
      subst hemit
      obtain ⟨hwea, hvea⟩ := hsem _ (List.mem_cons_self ..) ea hea
      refine finish _ es hes (by simp [widthSV]) ?_
      refine ⟨mask (Sparkle.IR.Semantics.widthOf we (.op op' as'))
        (mask (Sparkle.IR.Semantics.widthOf we (.op op' as')) vA),
        ?_, by simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]⟩
      unfold evalSV
      simp only [widthSV, Option.bind_eq_bind, Option.bind_some,
        Nat.max_eq_right (Nat.zero_le _), evalAt]
      unfold evalSV
      simp [hwea, hvea, hvA]
    all_goals
      (simp only [Tools.SVParser.EmitAst.emitConcatElems,
         Option.bind_eq_bind] at hemit;
       obtain ⟨ea, hea, hemit⟩ := Option.bind_eq_some_iff.mp hemit;
       obtain ⟨es, hes, hemit⟩ := Option.bind_eq_some_iff.mp hemit;
       simp only [Option.some_inj] at hemit;
       subst hemit;
       obtain ⟨hwea, hvea⟩ := hsem _ (List.mem_cons_self ..) ea hea;
       refine finish ea es hes hwea ⟨vA, ?_, rfl⟩;
       unfold evalSV;
       simp [hwea, hvea, hvA])

/-- XORing the top bit of a `w`-bit value adds the bias when the bit
    is clear and removes it when set — the classic biased encoding. -/
private theorem xor_top_bit {w v : Nat} (hw : 0 < w) (hv : v < 2 ^ w) :
    v ^^^ 2 ^ (w - 1)
      = if v < 2 ^ (w - 1) then v + 2 ^ (w - 1) else v - 2 ^ (w - 1) := by
  have h2 : (2 : Nat) ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hpos : 0 < (2 : Nat) ^ (w - 1) := Nat.two_pow_pos _
  have hdiv : (v ^^^ 2 ^ (w - 1)) / 2 ^ (w - 1)
      = v / 2 ^ (w - 1) ^^^ 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self hpos]
  have hmod : (v ^^^ 2 ^ (w - 1)) % 2 ^ (w - 1) = v % 2 ^ (w - 1) := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  have hda := Nat.div_add_mod (v ^^^ 2 ^ (w - 1)) (2 ^ (w - 1))
  have hdv := Nat.div_add_mod v (2 ^ (w - 1))
  rw [hdiv, hmod] at hda
  have hmv : v % 2 ^ (w - 1) < 2 ^ (w - 1) := Nat.mod_lt _ hpos
  have hxlt : v ^^^ 2 ^ (w - 1) < 2 ^ w :=
    Nat.xor_lt_two_pow hv (by omega)
  by_cases hcase : v < 2 ^ (w - 1)
  · have hd0 : v / 2 ^ (w - 1) = 0 := Nat.div_eq_of_lt hcase
    rw [hd0] at hda
    have hx1 : (0 : Nat) ^^^ 1 = 1 := rfl
    rw [hx1] at hda
    have hm0 : v % 2 ^ (w - 1) = v := Nat.mod_eq_of_lt hcase
    rw [hm0] at hda
    rw [if_pos hcase]
    omega
  · have hd1 : v / 2 ^ (w - 1) = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · omega
    rw [hd1] at hda
    have hx0 : (1 : Nat) ^^^ 1 = 0 := rfl
    rw [hx0] at hda
    rw [hd1] at hdv
    rw [if_neg hcase]
    omega

/-- Unsigned comparison of biased values IS signed comparison. -/
private theorem biased_lt {w a b : Nat} (hw : 0 < w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    ((a ^^^ 2 ^ (w - 1)) < (b ^^^ 2 ^ (w - 1)))
      ↔ toSigned w a < toSigned w b := by
  rw [xor_top_bit hw ha, xor_top_bit hw hb]
  have h2 : (2 : Nat) ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  unfold toSigned
  by_cases hA : a < 2 ^ (w - 1) <;> by_cases hB : b < 2 ^ (w - 1) <;>
    simp only [if_pos, if_neg, hA, hB, if_true, if_false] <;>
    omega

private theorem biased_le {w a b : Nat} (hw : 0 < w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    ((a ^^^ 2 ^ (w - 1)) ≤ (b ^^^ 2 ^ (w - 1)))
      ↔ toSigned w a ≤ toSigned w b := by
  rw [xor_top_bit hw ha, xor_top_bit hw hb]
  have h2 : (2 : Nat) ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  unfold toSigned
  by_cases hA : a < 2 ^ (w - 1) <;> by_cases hB : b < 2 ^ (w - 1) <;>
    simp only [if_pos, if_neg, hA, hB, if_true, if_false] <;>
    omega

/-- Fragment values are width-bounded: under a bounded environment,
    every fragment expression evaluates below 2^its-width.  (The one
    rule that does not mask its own result is `mux` — its arms carry
    the bound.) -/
theorem sf4_bounded {wof : String → Option Nat} {we : WEnv} {e : Expr}
    (h : SF4 wof we e) {env : Env} (hbe : Bounded we env) :
    ∀ v, evalExpr we env e = some v
      → v < 2 ^ Sparkle.IR.Semantics.widthOf we e := by
  induction h with
  | ref n hs hw =>
    intro v hv
    simp only [evalExpr, Option.some_inj] at hv
    subst hv
    simpa [Sparkle.IR.Semantics.widthOf] using hbe n
  | const v' w hw =>
    intro v hv
    simp only [evalExpr, Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | binop op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vals, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    exact evalOp_mask_bound hop hv
  | mux hwf hc ht hf ihc iht ihf =>
    rename_i c t f
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vals, hvals, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [evalList, Option.bind_eq_bind] at hvals
    obtain ⟨vc, hvc, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    obtain ⟨vrest, hvrest, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    obtain ⟨vt, hvt, hvrest⟩ := Option.bind_eq_some_iff.mp hvrest
    obtain ⟨vrest2, hvrest2, hvrest⟩ := Option.bind_eq_some_iff.mp hvrest
    obtain ⟨vf, hvf, hvrest2⟩ := Option.bind_eq_some_iff.mp hvrest2
    obtain ⟨vnil, hvnil, hvrest2⟩ := Option.bind_eq_some_iff.mp hvrest2
    simp only [evalList, Option.some_inj] at hvnil
    subst hvnil
    simp only [Option.some_inj] at hvrest2 hvrest hvals
    subst hvrest2; subst hvrest; subst hvals
    simp only [evalOp, Option.some_inj] at hv
    have hWt : Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f])
        = Sparkle.IR.Semantics.widthOf we t := by
      simp [Sparkle.IR.Semantics.widthOf]
    rw [hWt]
    subst hv
    by_cases h0 : vc ≠ 0
    · rw [if_pos h0]; exact iht vt hvt
    · rw [if_neg h0]; exact hwf ▸ ihf vf hvf
  | not w hwT hwS hw0 hx ihx =>
    rename_i x
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vals, hvals, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [evalList, Option.bind_eq_bind] at hvals
    obtain ⟨vx, hvx, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    obtain ⟨vnil, hvnil, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    simp only [evalList, Option.some_inj] at hvnil
    subst hvnil
    simp only [Option.some_inj] at hvals
    subst hvals
    simp only [evalOp, Option.some_inj] at hv
    subst hv
    have : Sparkle.IR.Semantics.widthOf we (.op .not [x])
        = Sparkle.IR.Semantics.widthOf we x := by
      simp [Sparkle.IR.Semantics.widthOf]
    rw [this]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | neg hx ihx =>
    rename_i x
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vals, hvals, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [evalList, Option.bind_eq_bind] at hvals
    obtain ⟨vx, hvx, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    obtain ⟨vnil, hvnil, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    simp only [evalList, Option.some_inj] at hvnil
    subst hvnil
    simp only [Option.some_inj] at hvals
    subst hvals
    simp only [evalOp, Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | cmpU op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro v hv
    rcases hop with h' | h' | h' | h' | h' <;> subst h' <;>
    · simp only [evalExpr, Option.bind_eq_bind] at hv
      obtain ⟨vals, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      match vals, hv with
      | [x, y], hv =>
        simp only [evalOp, Option.some_inj] at hv
        subst hv
        simp only [Sparkle.IR.Semantics.widthOf]
        split <;> omega
  | cmpS op hop hwTa hwTb hA hB hw0 ha hb iha ihb =>
    rename_i a b
    intro v hv
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [evalExpr, Option.bind_eq_bind] at hv
      obtain ⟨vals, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      match vals, hv with
      | [x, y], hv =>
        simp only [evalOp, Option.some_inj] at hv
        subst hv
        simp only [Sparkle.IR.Semantics.widthOf]
        split <;> omega
  | cmpS1 op hop hwTa hwTb hwba hB hw0 ha hb iha ihb =>
    rename_i a b
    intro v hv
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [evalExpr, Option.bind_eq_bind] at hv
      obtain ⟨vals, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      match vals, hv with
      | [x, y], hv =>
        simp only [evalOp, Option.some_inj] at hv
        subst hv
        simp only [Sparkle.IR.Semantics.widthOf]
        split <;> omega
  | sliceRef n hi lo hs hw hlo hhi hne =>
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind, Option.bind_some,
      Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | sliceRefFull n hi hs hw hfull =>
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind, Option.bind_some,
      Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | concat hall hpin ihall =>
    rename_i args
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vals, hvals, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    have := evalExpr_go_lt (we := we) args vals
      (evalList_length args vals hvals).symm
    simpa [Sparkle.IR.Semantics.widthOf] using this
  | castEnc w hw0 hx hsafe ihx =>
    rename_i x
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vin, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | sliceGen hi lo hcomp hncast hlo hlo32 hx hsafe ihx =>
    rename_i x
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vin, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | shiftOp op hop hwb ha hb iha ihb =>
    rename_i a b
    intro v hv
    rcases hop with h' | h' <;> subst h' <;>
    · simp only [evalExpr, Option.bind_eq_bind] at hv
      obtain ⟨vals, hvals, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [evalList, Option.bind_eq_bind] at hvals
      obtain ⟨va, hva, hvals⟩ := Option.bind_eq_some_iff.mp hvals
      obtain ⟨vrest, hvrest, hvals⟩ := Option.bind_eq_some_iff.mp hvals
      obtain ⟨vb, hvb, hvrest⟩ := Option.bind_eq_some_iff.mp hvrest
      obtain ⟨vnil, hvnil, hvrest⟩ := Option.bind_eq_some_iff.mp hvrest
      simp only [evalList, Option.some_inj] at hvnil
      subst hvnil
      simp only [Option.some_inj] at hvrest hvals
      subst hvrest; subst hvals
      simp only [evalOp, Option.some_inj] at hv
      subst hv
      first
      | exact Nat.mod_lt _ (Nat.two_pow_pos _)
      | · -- shr: the result only loses bits
          have hba := iha va hva
          calc va >>> vb ≤ va := Nat.shiftRight_le va vb
            _ < 2 ^ Sparkle.IR.Semantics.widthOf we a := hba
            _ ≤ 2 ^ Sparkle.IR.Semantics.widthOf we (.op .shr [a, b]) := by
                simp only [Sparkle.IR.Semantics.widthOf]
                exact Nat.pow_le_pow_right (by omega)
                  (Nat.le_max_left _ _)

/-- Emissions of `immuneE` fragment shapes are context-immune
    (`immuneSV`) — the bridge from the IR-level side condition to the
    semantic stability lemma. -/
private theorem emit_immune {wof : String → Option Nat} {we : WEnv}
    {e : Expr} (h : SF4 wof we e) :
    immuneE e = true →
    ∀ sv, Tools.SVParser.EmitAst.emitAstExpr wof e = some sv →
      immuneSV sv = true := by
  induction h with
  | ref n hs hw =>
    intro himm sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs,
      Option.some_inj] at hsv
    subst hsv; rfl
  | const v w hw =>
    intro himm sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [immuneE, decide_eq_true_eq] at himm
    have h2 : (0 : Int) < ((2 ^ w : Nat) : Int) :=
      Int.natCast_pos.mpr (Nat.two_pow_pos w)
    by_cases hneg : v < 0
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
        if_pos hneg, Option.some_inj] at hsv
      subst hsv
      simp only [immuneSV, decide_eq_true_eq,
        Tools.SVParser.EmitAst.encodeConst]
      have hlt := Int.emod_lt_of_pos
        (b := ((2 ^ w : Nat) : Int))
        ((v % ((2 ^ w : Nat) : Int)) + ((2 ^ w : Nat) : Int)) h2
      have hge := Int.emod_nonneg
        (b := ((2 ^ w : Nat) : Int))
        ((v % ((2 ^ w : Nat) : Int)) + ((2 ^ w : Nat) : Int))
        (Int.ne_of_gt h2)
      have hcast : ((((v % ((2 ^ w : Nat) : Int))
            + ((2 ^ w : Nat) : Int)) % ((2 ^ w : Nat) : Int)).toNat
            : Int) < ((2 ^ w : Nat) : Int) := by
        rw [Int.toNat_of_nonneg hge]; exact hlt
      exact Int.ofNat_lt.mp hcast
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
        if_neg hneg, Option.some_inj] at hsv
      subst hsv
      simp only [immuneSV, decide_eq_true_eq]
      have hcast : ((v.toNat : Int)) < ((2 ^ w : Nat) : Int) := by
        rw [Int.toNat_of_nonneg (Int.not_lt.mp hneg)]; exact himm
      exact Int.ofNat_lt.mp hcast
  | binop op hop hA hB ha hb iha ihb =>
    intro himm sv hsv
    rcases hop with h' | h' | h' | h' | h' | h' <;> subst h' <;>
    first
    | (exfalso; simp [immuneE] at himm; done)
    | (simp only [immuneE, Bool.and_eq_true] at himm
       obtain ⟨himmA, himmB⟩ := himm
       simp only [Tools.SVParser.EmitAst.emitAstExpr,
         Option.bind_eq_bind] at hsv
       obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
       obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
       simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
         Option.some_inj] at hsv
       subst hsv
       simp only [immuneSV, Bool.and_eq_true]
       exact ⟨iha himmA sva hsa, ihb himmB svb hsb⟩)
  | mux hwf hc ht hf ihc iht ihf =>
    intro himm sv hsv
    exfalso
    simp [immuneE] at himm
  | not w hwT hwS hw0 hx ihx =>
    intro himm sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hwT, hne,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [hne, Bool.false_eq_true, if_false,
      Option.some_inj] at hsv
    subst hsv; rfl
  | neg hx ihx =>
    intro himm sv hsv
    exfalso
    simp [immuneE] at himm
  | cmpU op hop hA hB ha hb iha ihb =>
    intro himm sv hsv
    rcases hop with h' | h' | h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨sva, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv; rfl
  | cmpS op hop hwTa hwTb hA hB hw0 ha hb iha ihb =>
    intro himm sv hsv
    rename_i a b
    have hne : (max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b) == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hwTa, hwTb, hne,
        Bool.false_eq_true, if_false, Option.bind_eq_bind] at hsv
      obtain ⟨sva, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Option.some_inj] at hsv
      subst hsv
      rfl
  | cmpS1 op hop hwTa hwTb hwba hB hw0 ha hb iha ihb =>
    intro himm sv hsv
    rename_i a b
    have hne : (Sparkle.IR.Semantics.widthOf we a == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hwTa, hwTb, hne,
        Bool.false_eq_true, if_false, Option.bind_eq_bind] at hsv
      obtain ⟨sva, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Option.some_inj] at hsv
      subst hsv
      rfl
  | sliceRef n hi lo hs hw hlo hhi hne' =>
    intro himm sv hsv
    have helide : (lo == 0 && hi + 1 == we n) = false := by
      rcases Nat.eq_zero_or_pos lo with h0 | h0
      · subst h0
        have : hi + 1 ≠ we n := fun hc => hne' ⟨rfl, hc⟩
        simp [this]
      · simp [Nat.pos_iff_ne_zero.mp h0]
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide,
      Bool.false_eq_true, if_false, if_pos hhi,
      Option.some_inj] at hsv
    subst hsv; rfl
  | sliceRefFull n hi hs hw hfull =>
    intro himm sv hsv
    have helide : (0 == 0 && hi + 1 == we n) = true := by simp [hfull]
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide,
      if_true, Option.some_inj] at hsv
    subst hsv; rfl
  | concat hall hpin ihall =>
    intro himm sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svs, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv; rfl
  | castEnc w hw0 hx hsafe ihx =>
    intro himm sv hsv
    have hsucc : w - 1 + 1 = w := Nat.sub_add_cancel hw0
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hsucc,
      beq_self_eq_true, Bool.and_self, if_true,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv; rfl
  | sliceGen hi lo hcomp hncast hlo hlo32 hx hsafe ihx =>
    intro himm sv hsv
    rw [Tools.SVParser.EmitAst.emitAst_slice_general hi lo hcomp
      hncast] at hsv
    obtain ⟨inner, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    by_cases h0 : lo == 0 <;> simp only [h0, if_true, if_false,
      Bool.false_eq_true, Option.some_inj] at hsv <;> subst hsv <;> rfl
  | shiftOp op hop hwb ha hb iha ihb =>
    intro himm sv hsv
    exfalso
    rcases hop with h' | h' <;> subst h' <;> simp [immuneE] at himm

/-- The bias-encoded operand `((x & m) ^ sb)` at context `W` reads
    exactly `vx ^^^ 2^(W-1)`, where `vx` is the operand's IR value. -/
private theorem biased_operand_sem {wof : String → Option Nat}
    {we : WEnv} {env : Env} {x : Expr} {sve : SVExpr} {vx : Nat}
    (W : Nat)
    (hbe : Bounded we env)
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn)
    (hx : SF4 wof we x)
    (hsx : Tools.SVParser.EmitAst.emitAstExpr wof x = some sve)
    (hwx : widthSV wof sve = some (Sparkle.IR.Semantics.widthOf we x))
    (hvxAt : evalAt wof env (Sparkle.IR.Semantics.widthOf we x) sve
      = evalExpr we env x)
    (hcond : Sparkle.IR.Semantics.widthOf we x = W ∨ immuneE x = true)
    (hWx : Sparkle.IR.Semantics.widthOf we x ≤ W)
    (hW0 : 0 < W)
    (hvx : evalExpr we env x = some vx) :
    widthSV wof (SVExpr.binary .bitXor
        (.binary .bitAnd sve (.lit (.hex (some W) (2 ^ W - 1))))
        (.lit (.hex (some W) (2 ^ (W - 1)))))
      = some W
    ∧ evalAt wof env W (SVExpr.binary .bitXor
        (.binary .bitAnd sve (.lit (.hex (some W) (2 ^ W - 1))))
        (.lit (.hex (some W) (2 ^ (W - 1)))))
      = some (vx ^^^ 2 ^ (W - 1))
    ∧ vx < 2 ^ W := by
  have hvW : vx < 2 ^ W :=
    Nat.lt_of_lt_of_le (sf4_bounded hx hbe vx hvx)
      (Nat.pow_le_pow_right (by omega) hWx)
  have hval : evalAt wof env W sve = some vx := by
    rcases hcond with hEq | himm
    · rw [← hEq, hvxAt]; exact hvx
    · rw [evalAt_immune (emit_immune hx himm sve hsx) hwx hbw W hWx,
        hvxAt]
      exact hvx
  refine ⟨?_, ?_, hvW⟩
  · simp [widthSV, hwx, Nat.max_eq_right hWx]
  · have hm1 : (2 : Nat) ^ W - 1 < 2 ^ W := by
      have := Nat.two_pow_pos W
      omega
    have hsb : (2 : Nat) ^ (W - 1) < 2 ^ W :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have hand : vx &&& 2 ^ W - 1 = vx :=
      Nat.and_two_pow_sub_one_of_lt_two_pow hvW
    have hxor : vx ^^^ 2 ^ (W - 1) < 2 ^ W :=
      Nat.xor_lt_two_pow hvW hsb
    simp only [evalAt, litVal, hval, Option.bind_eq_bind,
      Option.bind_some, Option.some_inj]
    simp [mask, Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hsb,
      Nat.mod_eq_of_lt hvW, Nat.mod_eq_of_lt hxor, hand]

/-- **Forward correctness, v0**: the emitted form has the same
    self-determined width AND, evaluated at the IR width as context,
    the same value as the IR expression. -/
theorem emit_sem {wof : String → Option Nat} {we : WEnv} {env : Env}
    {e : Expr} (h : SF4 wof we e) (hbe : Bounded we env)
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn) :
    ∀ sv, Tools.SVParser.EmitAst.emitAstExpr wof e = some sv →
      widthSV wof sv = some (Sparkle.IR.Semantics.widthOf we e)
      ∧ evalAt wof env (Sparkle.IR.Semantics.widthOf we e) sv
          = evalExpr we env e := by
  induction h with
  | ref n hs hw =>
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs,
      Option.some_inj] at hsv
    subst hsv
    refine ⟨by simp [widthSV, hw, Sparkle.IR.Semantics.widthOf], ?_⟩
    simp only [evalAt, hw, Option.bind_eq_bind, Option.bind_some,
      evalExpr, Sparkle.IR.Semantics.widthOf]
    have := hbe n
    simp [mask, Nat.mod_eq_of_lt this]
  | const v w hw =>
    intro sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    by_cases hneg : v < 0
    · -- negative: sized-hex two's complement — the emission carries the
      -- IR encode LITERALLY (`encodeConst` is the same formula), so the
      -- two masked values coincide definitionally.
      simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
        if_pos hneg, Option.some_inj] at hsv
      subst hsv
      refine ⟨by simp [widthSV, Sparkle.IR.Semantics.widthOf], ?_⟩
      simp [evalAt, litVal, evalExpr, Sparkle.IR.Semantics.widthOf,
        Tools.SVParser.EmitAst.encodeConst]
    · -- nonnegative (fitting or not): both sides reduce `v` mod 2^w —
      -- the SV side by the context mask on the raw decimal, the IR side
      -- inside its two's-complement encode.
      simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
        if_neg hneg, Option.some_inj] at hsv
      subst hsv
      refine ⟨by simp [widthSV, hne, Sparkle.IR.Semantics.widthOf], ?_⟩
      simp only [evalAt, litVal, evalExpr, Sparkle.IR.Semantics.widthOf]
      congr 1
      rcases Int.eq_ofNat_of_zero_le (Int.not_lt.mp hneg) with ⟨n, rfl⟩
      have h2 : (0 : Int) < ((2 ^ w : Nat) : Int) :=
        Int.natCast_pos.mpr (Nat.two_pow_pos w)
      rw [Int.add_emod_right]
      have hmm : ∀ m : Nat, (m : Int) % ((2 ^ w : Nat) : Int)
          = ((m % 2 ^ w : Nat) : Int) := fun m => by omega
      rw [hmm n, hmm (n % 2 ^ w), Int.toNat_natCast, Int.toNat_natCast]
      simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  | binop op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    rcases hop with h | h | h | h | h | h <;> subst h <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb, hvb⟩ := ihb svb hsb
      -- each operand at the node's context (the max) reads its IR
      -- value: the max-width side by the IH directly, an immune side
      -- by stability
      have hA' : evalAt wof env
            (max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)) sva
          = evalExpr we env a := by
        rcases hA with hw' | himm
        · rw [← hw']; exact hva
        · rw [evalAt_immune (emit_immune ha himm sva hsa) hwa hbw _
            (Nat.le_max_left _ _)]
          exact hva
      have hB' : evalAt wof env
            (max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)) svb
          = evalExpr we env b := by
        rcases hB with hw' | himm
        · rw [← hw']; exact hvb
        · rw [evalAt_immune (emit_immune hb himm svb hsb) hwb hbw _
            (Nat.le_max_right _ _)]
          exact hvb
      constructor
      · simp only [widthSV, hwa, hwb, Option.bind_eq_bind,
          Option.bind_some, Sparkle.IR.Semantics.widthOf]
      · rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        cases hAv : evalExpr we env a with
        | none =>
          exact absurd hAv (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome ha env))
        | some va =>
        cases hBv : evalExpr we env b with
        | none =>
          exact absurd hBv (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome hb env))
        | some vb =>
        rw [hAv] at hA'
        rw [hBv] at hB'
        simp only [Sparkle.IR.Semantics.widthOf, evalAt,
          Option.bind_eq_bind, hA', hB', Option.bind_some, evalList,
          hAv, hBv, evalOp, Option.some_inj]
  | mux hwf hc ht hf ihc iht ihf =>
    rename_i c t f
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svc, hsc, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨svt, hst, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨svf, hsf, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    obtain ⟨hwc, hvc⟩ := ihc svc hsc
    obtain ⟨hwt, hvt⟩ := iht svt hst
    obtain ⟨hwff, hvf⟩ := ihf svf hsf
    constructor
    · simp [widthSV, hwt, hwff, Sparkle.IR.Semantics.widthOf, hwf,
        Nat.max_self]
    · -- condition is self-determined; arms inherit the context width
      have hW : Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f])
          = Sparkle.IR.Semantics.widthOf we t := by
        simp [Sparkle.IR.Semantics.widthOf]
      rw [hW]
      simp only [evalAt, evalSV, Option.bind_eq_bind, hwc,
        Option.bind_some, Nat.max_eq_right (Nat.zero_le _), hvc]
      rw [show evalExpr we env (.op .mux [c, t, f])
            = ((evalList we env [c, t, f]).bind fun vals =>
                evalOp we .mux [c, t, f] vals
                  (Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f])))
          from rfl]
      cases hC : evalExpr we env c with
      | none => simp [evalList, hC]
      | some vc =>
      cases hT : evalExpr we env t with
      | none =>
        exact absurd hT (Option.isSome_iff_ne_none.mp
          (sf4_eval_isSome ht env))
      | some vt =>
      cases hF : evalExpr we env f with
      | none =>
        exact absurd hF (Option.isSome_iff_ne_none.mp
          (sf4_eval_isSome hf env))
      | some vf =>
      simp only [evalList, hC, hT, hF, Option.bind_some,
        Option.bind_eq_bind, evalOp, Option.some_inj]
      have hvf' : evalAt wof env (Sparkle.IR.Semantics.widthOf we t) svf
          = evalExpr we env f := hwf ▸ hvf
      by_cases hvc0 : vc ≠ 0
      · rw [if_pos hvc0, if_pos hvc0, hvt, hT]
      · rw [if_neg hvc0, if_neg hvc0, hvf', hF]
  | not w hwT hwS hw0 hx ihx =>
    rename_i x
    intro sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hwT, hne,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, hsx, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [hne, Bool.false_eq_true, if_false,
      Option.some_inj] at hsv
    subst hsv
    obtain ⟨hwx, hvx⟩ := ihx svx hsx
    have hW : Sparkle.IR.Semantics.widthOf we (.op .not [x]) = w := by
      simp [Sparkle.IR.Semantics.widthOf, hwS]
    constructor
    · simp [widthSV, hW]
    · rw [hW]
      -- the emitted `w'(x ^ w'dM)`: cast boundary puts the xor in a
      -- w-bit context, and everything is width w
      simp only [evalAt, evalSV, Option.bind_eq_bind, widthSV, hwx,
        hwS, Option.bind_some, Nat.max_self,
        Nat.max_eq_right (Nat.le_refl w)]
      rw [show evalExpr we env (.op .not [x])
            = ((evalList we env [x]).bind fun vals =>
                evalOp we .not [x] vals
                  (Sparkle.IR.Semantics.widthOf we (.op .not [x])))
          from rfl]
      cases hX : evalExpr we env x with
      | none => simp [evalList, hX, hvx, hwS ▸ hvx]
      | some vx =>
      simp only [evalList, hX, Option.bind_some, Option.bind_eq_bind,
        evalOp, Option.some_inj, litVal]
      rw [hwS] at hvx
      simp only [hvx, hX, Option.bind_some]
      -- mask w (mask w (vx ^^^ mask w (2^w-1))) = mask w (vx ^^^ (2^w-1))
      have hm : mask w ((2 : Nat) ^ w - 1) = 2 ^ w - 1 := by
        have := Nat.two_pow_pos w
        simp [mask, Nat.mod_eq_of_lt (by omega)]
      simp [mask, hm, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), hwS]
  | neg hx ihx =>
    rename_i x
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, hsx, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    obtain ⟨hwx, hvx⟩ := ihx svx hsx
    have hW : Sparkle.IR.Semantics.widthOf we (.op .neg [x])
        = Sparkle.IR.Semantics.widthOf we x := by
      simp [Sparkle.IR.Semantics.widthOf]
    constructor
    · simp [widthSV, hwx, hW]
    · rw [hW]
      -- both sides: mask w (2^w - mask w v) at w = widthOf x
      rw [show evalExpr we env (.op .neg [x])
            = ((evalList we env [x]).bind fun vals =>
                evalOp we .neg [x] vals
                  (Sparkle.IR.Semantics.widthOf we (.op .neg [x])))
          from rfl]
      cases hX : evalExpr we env x with
      | none =>
        exact absurd hX (Option.isSome_iff_ne_none.mp
          (sf4_eval_isSome hx env))
      | some vx =>
      rw [hX] at hvx
      simp only [evalAt, hvx, Option.bind_eq_bind, Option.bind_some,
        evalList, hX, evalOp, Sparkle.IR.Semantics.widthOf,
        Option.some_inj]
  | cmpU op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    rcases hop with h | h | h | h | h <;> subst h <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb, hvb⟩ := ihb svb hsb
      -- comparison operands are SELF-determined: they size to their
      -- own max.  Width agreement pins that to the IH's width; when
      -- instead both emissions are context-immune, up-sizing to the
      -- max is inert (evalAt_immune).
      have hA' : evalAt wof env
            (max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)) sva
          = evalExpr we env a := by
        rcases hA with hw' | himm
        · rw [← hw']; exact hva
        · rw [evalAt_immune (emit_immune ha himm sva hsa) hwa hbw _
            (Nat.le_max_left _ _)]
          exact hva
      have hB' : evalAt wof env
            (max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)) svb
          = evalExpr we env b := by
        rcases hB with hw' | himm
        · rw [← hw']; exact hvb
        · rw [evalAt_immune (emit_immune hb himm svb hsb) hwb hbw _
            (Nat.le_max_right _ _)]
          exact hvb
      constructor
      · simp [widthSV, Sparkle.IR.Semantics.widthOf]
      · rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        cases hA : evalExpr we env a with
        | none =>
          exact absurd hA (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome ha env))
        | some va =>
        cases hB : evalExpr we env b with
        | none =>
          exact absurd hB (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome hb env))
        | some vb =>
        simp only [evalAt, hwa, hwb, Option.bind_eq_bind,
          Option.bind_some, hA', hB', hA, hB,
          evalList, evalOp, Option.some_inj]
  | cmpS op hop hwTa hwTb hA hB hw0 ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    have hne : (max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b) == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hwTa, hwTb, hne,
        Bool.false_eq_true, if_false, Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb, hvb⟩ := ihb svb hsb
      obtain ⟨vA, hvA⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome ha env)
      obtain ⟨vB, hvB⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome hb env)
      obtain ⟨hWa, hVa, hbndA⟩ := biased_operand_sem
        (max (Sparkle.IR.Semantics.widthOf we a)
          (Sparkle.IR.Semantics.widthOf we b))
        hbe hbw ha hsa hwa hva hA (Nat.le_max_left _ _) hw0 hvA
      obtain ⟨hWb, hVb, hbndB⟩ := biased_operand_sem
        (max (Sparkle.IR.Semantics.widthOf we a)
          (Sparkle.IR.Semantics.widthOf we b))
        hbe hbw hb hsb hwb hvb hB (Nat.le_max_right _ _) hw0 hvB
      constructor
      · simp [widthSV, Sparkle.IR.Semantics.widthOf]
      · rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        simp only [evalList, hvA, hvB, Option.bind_eq_bind,
          Option.bind_some, evalOp]
        -- make the biased operands opaque so unfolding `evalAt` stops
        -- at the comparison arm
        obtain ⟨A, hAdef⟩ : ∃ A, SVExpr.binary .bitXor
            (.binary .bitAnd sva (.lit (.hex
              (some (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b)))
              (2 ^ max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b) - 1))))
            (.lit (.hex
              (some (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b)))
              (2 ^ (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b) - 1)))) = A :=
          ⟨_, rfl⟩
        obtain ⟨B, hBdef⟩ : ∃ B, SVExpr.binary .bitXor
            (.binary .bitAnd svb (.lit (.hex
              (some (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b)))
              (2 ^ max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b) - 1))))
            (.lit (.hex
              (some (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b)))
              (2 ^ (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b) - 1)))) = B :=
          ⟨_, rfl⟩
        rw [hAdef] at hWa hVa
        rw [hBdef] at hWb hVb
        rw [hAdef, hBdef]
        simp only [evalAt, hWa, hWb, Option.bind_eq_bind,
          Option.bind_some, Nat.max_self, hVa, hVb, Option.some_inj]
        first
        | (simp only [biased_lt hw0 hbndA hbndB])
        | (simp only [biased_le hw0 hbndA hbndB])
        | (simp only [biased_lt hw0 hbndB hbndA])
        | (simp only [biased_le hw0 hbndB hbndA])
  | cmpS1 op hop hwTa hwTb hwba hB hw0 ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    have hne : (Sparkle.IR.Semantics.widthOf we a == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    have hmaxw : max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b)
        = Sparkle.IR.Semantics.widthOf we a := Nat.max_eq_left hwba
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hwTa, hwTb, hne,
        Bool.false_eq_true, if_false, Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb, hvb⟩ := ihb svb hsb
      obtain ⟨vA, hvA⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome ha env)
      obtain ⟨vB, hvB⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome hb env)
      obtain ⟨hWa, hVa, hbndA⟩ := biased_operand_sem
        (Sparkle.IR.Semantics.widthOf we a)
        hbe hbw ha hsa hwa hva (Or.inl rfl) (Nat.le_refl _) hw0 hvA
      obtain ⟨hWb, hVb, hbndB⟩ := biased_operand_sem
        (Sparkle.IR.Semantics.widthOf we a)
        hbe hbw hb hsb hwb hvb hB hwba hw0 hvB
      constructor
      · simp [widthSV, Sparkle.IR.Semantics.widthOf]
      · rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        simp only [evalList, hvA, hvB, Option.bind_eq_bind,
          Option.bind_some, evalOp, hmaxw]
        obtain ⟨A, hAdef⟩ : ∃ A, SVExpr.binary .bitXor
            (.binary .bitAnd sva (.lit (.hex
              (some (Sparkle.IR.Semantics.widthOf we a))
              (2 ^ Sparkle.IR.Semantics.widthOf we a - 1))))
            (.lit (.hex
              (some (Sparkle.IR.Semantics.widthOf we a))
              (2 ^ (Sparkle.IR.Semantics.widthOf we a - 1)))) = A :=
          ⟨_, rfl⟩
        obtain ⟨B, hBdef⟩ : ∃ B, SVExpr.binary .bitXor
            (.binary .bitAnd svb (.lit (.hex
              (some (Sparkle.IR.Semantics.widthOf we a))
              (2 ^ Sparkle.IR.Semantics.widthOf we a - 1))))
            (.lit (.hex
              (some (Sparkle.IR.Semantics.widthOf we a))
              (2 ^ (Sparkle.IR.Semantics.widthOf we a - 1)))) = B :=
          ⟨_, rfl⟩
        rw [hAdef] at hWa hVa
        rw [hBdef] at hWb hVb
        rw [hAdef, hBdef]
        simp only [evalAt, hWa, hWb, Option.bind_eq_bind,
          Option.bind_some, Nat.max_self, hVa, hVb, Option.some_inj]
        first
        | (simp only [biased_lt hw0 hbndA hbndB])
        | (simp only [biased_le hw0 hbndA hbndB])
        | (simp only [biased_lt hw0 hbndB hbndA])
        | (simp only [biased_le hw0 hbndB hbndA])
  | sliceRef n hi lo hs hw hlo hhi hne =>
    intro sv hsv
    -- unfold the emitter on the non-castEnc, non-elided, in-range slice
    have helide : (lo == 0 && hi + 1 == we n) = false := by
      rcases Nat.eq_zero_or_pos lo with h0 | h0
      · subst h0
        have : hi + 1 ≠ we n := fun hc => hne ⟨rfl, hc⟩
        simp [this]
      · simp [Nat.pos_iff_ne_zero.mp h0]
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide,
      Bool.false_eq_true, if_false, if_pos hhi,
      Option.some_inj] at hsv
    subst hsv
    constructor
    · simp [widthSV, Sparkle.IR.Semantics.widthOf]
    · simp only [Sparkle.IR.Semantics.widthOf, evalAt, hw,
        Option.bind_eq_bind, Option.bind_some, evalExpr,
        if_pos (And.intro hlo hhi)]
      simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  | concat hall hpin ihall =>
    rename_i args
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svs, hsvs, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    have hsome : ∀ e, e ∈ args → (evalExpr we env e).isSome :=
      fun e he => sf4_eval_isSome (hall e he) env
    obtain ⟨hwgo, vals, hvals, hgo, hbnd⟩ :=
      concat_elems_sem args svs hsome (fun e he => ihall e he) hpin hsvs
    constructor
    · simpa [widthSV, Sparkle.IR.Semantics.widthOf] using hwgo
    · simp only [evalAt, Option.bind_eq_bind, hgo, Option.bind_some,
        evalExpr, hvals, Sparkle.IR.Semantics.widthOf,
        Option.some_inj]
      simp [mask, Nat.mod_eq_of_lt hbnd]
  | castEnc w hw0 hx hsafe ihx =>
    rename_i x
    intro sv hsv
    have hsucc : w - 1 + 1 = w := Nat.sub_add_cancel hw0
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hsucc,
      beq_self_eq_true, Bool.and_self, if_true,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, hsx, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    obtain ⟨hwx, hvx⟩ := ihx svx hsx
    obtain ⟨vx, hvxv⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hx env)
    have hW : Sparkle.IR.Semantics.widthOf we
        (.slice (.concat [.const 0 w, x]) (w - 1) 0) = w := by
      simp [Sparkle.IR.Semantics.widthOf, hsucc]
    constructor
    · simp [widthSV, hW]
    · rw [hW]
      -- SV side: the cast's argument sees a w-bit context
      have hstab : evalAt wof env
            (max w (Sparkle.IR.Semantics.widthOf we x)) svx
          = some vx := by
        rcases hsafe with hle | himm
        · rw [Nat.max_eq_right hle, hvx]; exact hvxv
        · rw [evalAt_immune (emit_immune hx himm svx hsx) hwx hbw _
            (Nat.le_max_right _ _), hvx]
          exact hvxv
      have hSV : evalAt wof env w (.sizeCast w svx)
          = some (mask w (mask w vx)) := by
        simp only [evalAt]
        unfold evalSV
        simp [hwx, hstab]
      rw [hSV]
      -- IR side: slice of the zero-extension concat
      have hc0 : evalExpr we env (.const 0 w) = some 0 := by
        simp only [evalExpr, Option.some_inj]
        simp [Int.zero_emod, Int.zero_add, Int.emod_self, mask]
      have hIR : evalExpr we env
          (.slice (.concat [.const 0 w, x]) (w - 1) 0)
          = some (mask w (mask (Sparkle.IR.Semantics.widthOf we x) vx)) := by
        simp only [evalExpr, evalList, hc0, hvxv, Option.bind_eq_bind,
          Option.bind_some, Option.some_inj,
          Sparkle.IR.Semantics.evalExpr.go]
        simp [mask, Nat.shiftRight_zero, Nat.shiftLeft_eq, hsucc,
          Nat.zero_mod, Nat.sub_zero]
      rw [hIR, Option.some_inj]
      -- mask w (mask w vx) = mask w (mask wx vx)
      rcases hsafe with hle | himm
      · -- down/equal cast: both collapse to mask w vx
        simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _),
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hle)]
      · -- up-cast of an immune shape: the value already fits its width
        have hb := sf4_bounded hx hbe vx hvxv
        simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _),
          Nat.mod_eq_of_lt hb]
  | sliceGen hi lo hcomp hncast hlo hlo32 hx hsafe ihx =>
    rename_i x
    intro sv hsv
    rw [Tools.SVParser.EmitAst.emitAst_slice_general hi lo hcomp
      hncast] at hsv
    obtain ⟨inner, hsx, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨hwx, hvx⟩ := ihx inner hsx
    obtain ⟨vx, hvxv⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hx env)
    have hn : hi + 1 - lo = hi - lo + 1 := by omega
    have hW : Sparkle.IR.Semantics.widthOf we (.slice x hi lo)
        = hi - lo + 1 := by simp [Sparkle.IR.Semantics.widthOf]
    -- the cast's argument (the value, possibly shifted) sees a context
    -- of max(cast width, its own); both hsafe branches pin the value
    have hstab : ∀ W', Sparkle.IR.Semantics.widthOf we x ≤ W' →
        (W' = max (hi + 1 - lo) (Sparkle.IR.Semantics.widthOf we x)) →
        evalAt wof env W' inner = some vx := by
      intro W' _ hmax
      rcases hsafe with hle | himm
      · rw [hmax, Nat.max_eq_right hle, hvx]; exact hvxv
      · rw [hmax, evalAt_immune (emit_immune hx himm inner hsx) hwx
          hbw _ (Nat.le_max_right _ _), hvx]
        exact hvxv
    have hIR : evalExpr we env (.slice x hi lo)
        = some (mask (hi - lo + 1) (vx >>> lo)) := by
      simp [evalExpr, hvxv]
    by_cases h0 : lo = 0
    · subst h0
      simp only [if_pos rfl, beq_self_eq_true, if_true,
        Option.some_inj] at hsv
      subst hsv
      constructor
      · simp [widthSV, hW, Nat.sub_zero]
      · rw [hW]
        simp only [Nat.sub_zero, evalAt]
        unfold evalSV
        simp only [hwx, Option.bind_eq_bind, Option.bind_some]
        rw [hstab _ (Nat.le_max_right _ _) (by simp)]
        rw [hIR, Option.bind_some, Option.some_inj]
        simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _),
          Nat.shiftRight_zero, Nat.sub_zero]
    · have h0' : (lo == 0) = false := by simp [h0]
      simp only [h0', Bool.false_eq_true, if_false,
        Option.some_inj] at hsv
      subst hsv
      constructor
      · simp [widthSV, hW, hn]
      · rw [hW]
        simp only [evalAt]
        unfold evalSV
        simp only [widthSV, hwx, Option.bind_eq_bind, Option.bind_some]
        -- expose the shift arm, then pin the shifted value:
        -- E at max(n, wx), then >>> lo
        simp only [evalAt, Option.bind_eq_bind]
        rw [hstab _ (Nat.le_max_right _ _) rfl]
        have hamt : evalSV wof env 0 (.lit (.decimal none lo))
            = some lo := by
          unfold evalSV
          simp [widthSV, evalAt, litVal, mask, Nat.mod_eq_of_lt hlo32]
        rw [hamt, hIR]
        simp [hn, mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  | shiftOp op hop hwb ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    have hmax : max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b)
        = Sparkle.IR.Semantics.widthOf we a := Nat.max_eq_left hwb
    rcases hop with h | h <;> subst h <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb', hvb⟩ := ihb svb hsb
      -- the amount is self-determined at its own width — exactly the
      -- IH's evaluation
      have hamt : evalSV wof env 0 svb = evalExpr we env b := by
        unfold evalSV
        simp [hwb', hvb]
      constructor
      · simp only [widthSV, hwa, Sparkle.IR.Semantics.widthOf, hmax]
      · rw [show Sparkle.IR.Semantics.widthOf we (.op _ [a, b])
            = Sparkle.IR.Semantics.widthOf we a by
          simp [Sparkle.IR.Semantics.widthOf, hmax]]
        rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        cases hA : evalExpr we env a with
        | none =>
          exact absurd hA (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome ha env))
        | some va =>
        cases hB : evalExpr we env b with
        | none =>
          exact absurd hB (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome hb env))
        | some vb =>
        rw [hA] at hva
        rw [hB] at hamt
        simp only [evalAt, hva, hamt, Option.bind_eq_bind,
          Option.bind_some, evalList, hA, hB, evalOp,
          Sparkle.IR.Semantics.widthOf, hmax, Option.some_inj]
  | sliceRefFull n hi hs hw hfull =>
    intro sv hsv
    have helide : (0 == 0 && hi + 1 == we n) = true := by simp [hfull]
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide,
      if_true, Option.some_inj] at hsv
    subst hsv
    constructor
    · simp [widthSV, hw, Sparkle.IR.Semantics.widthOf, hfull]
    · simp only [Sparkle.IR.Semantics.widthOf, evalAt, hw,
        Option.bind_eq_bind, Option.bind_some, evalExpr,
        Nat.sub_zero, Option.some_inj]
      simp [Nat.shiftRight_zero]

/-- Decidable mirror of `SF4` — the per-expression forward-fragment
    membership test the census and gate run.  Soundness below ties a
    `true` verdict to the `emit_sem` theorem. -/
def sf4Check (wof : String → Option Nat) (we : WEnv) :
    Expr → Bool
  | .ref n =>
    (Sparkle.Backend.Verilog.sanitizeName n == n)
      && (wof n == some (we n))
  | .const _ w => 0 < w
  | .op .neg [x] => sf4Check wof we x
  | .op .not [x] =>
    (Tools.SVParser.EmitAst.exprWidthT wof x
        == some (Sparkle.IR.Semantics.widthOf we x))
      && (0 < Sparkle.IR.Semantics.widthOf we x)
      && sf4Check wof we x
  | .op .mux [c, t, f] =>
    (Sparkle.IR.Semantics.widthOf we f
        == Sparkle.IR.Semantics.widthOf we t)
      && sf4Check wof we c && sf4Check wof we t && sf4Check wof we f
  | .op op [a, b] =>
    let wa := Sparkle.IR.Semantics.widthOf we a
    let wb := Sparkle.IR.Semantics.widthOf we b
    let perOp := ((wa == max wa wb) || immuneE a)
      && ((wb == max wa wb) || immuneE b)
      && sf4Check wof we a && sf4Check wof we b
    match op with
    | .and | .or | .xor | .add | .sub | .mul => perOp
    | .eq | .lt_u | .le_u | .gt_u | .ge_u => perOp
    | .shl | .shr =>
      (wb ≤ wa) && sf4Check wof we a && sf4Check wof we b
    | .lt_s | .le_s | .gt_s | .ge_s =>
      ((Tools.SVParser.EmitAst.exprWidthT wof a == some wa)
        && (Tools.SVParser.EmitAst.exprWidthT wof b == some wb)
        && (0 < max wa wb) && perOp) ||
      ((Tools.SVParser.EmitAst.exprWidthT wof a == some wa)
        && (Tools.SVParser.EmitAst.exprWidthT wof b == none)
        && (wb ≤ wa) && ((wb == wa) || immuneE b) && (0 < wa)
        && sf4Check wof we a && sf4Check wof we b)
    | _ => false
  | .concat args =>
    args.attach.all fun ⟨e, _⟩ =>
      sf4Check wof we e &&
      (match e with
       | .op _ _ =>
         (Tools.SVParser.EmitAst.exprWidthT wof e
             == some (Sparkle.IR.Semantics.widthOf we e))
           && (0 < Sparkle.IR.Semantics.widthOf we e)
       | _ => true)
  | .slice (.concat [.const 0 w, x]) hi lo =>
    -- canonical cast encode, or the general-slice route over the concat
    ((lo == 0) && (hi + 1 == w) && (0 < w) && sf4Check wof we x
      && ((w ≤ Sparkle.IR.Semantics.widthOf we x) || immuneE x)) ||
    (!(lo == 0 && hi + 1 == w) && (lo ≤ hi) && (lo < 2 ^ 32)
      && sf4Check wof we (.concat [.const 0 w, x])
      && ((hi + 1 - lo
            ≤ Sparkle.IR.Semantics.widthOf we (.concat [.const 0 w, x]))
        || immuneE (.concat [.const 0 w, x])))
  | .slice (.ref n) hi lo =>
    ((Sparkle.Backend.Verilog.sanitizeName n == n)
      && (wof n == some (we n))
      && (lo ≤ hi) && (hi < we n) && !(lo == 0 && hi + 1 == we n)) ||
    ((Sparkle.Backend.Verilog.sanitizeName n == n)
      && (wof n == some (we n)) && (lo == 0) && (hi + 1 == we n))
  | .slice x hi lo =>
    (lo ≤ hi) && (lo < 2 ^ 32) && sf4Check wof we x
      && ((hi + 1 - lo ≤ Sparkle.IR.Semantics.widthOf we x)
        || immuneE x)
  | _ => false
decreasing_by all_goals
  first
  | (simp_wf
     have := List.sizeOf_lt_of_mem ‹_ ∈ _›
     omega)
  | (simp_wf; omega)

set_option maxHeartbeats 1600000 in
/-- Soundness of the mirror: a `true` verdict puts the expression in
    the proven forward fragment, so `emit_sem` applies to it. -/
theorem sf4Check_sound {wof : String → Option Nat} {we : WEnv} :
    ∀ {e : Expr}, sf4Check wof we e = true → SF4 wof we e := by
  intro e h
  induction e using sf4Check.induct wof we
  case case1 n =>
    simp only [sf4Check, Bool.and_eq_true, beq_iff_eq] at h
    exact SF4.ref n h.1 h.2
  case case2 v w =>
    simp only [sf4Check, decide_eq_true_eq] at h
    exact SF4.const v w h
  case case3 x ih =>
    simp only [sf4Check] at h
    exact SF4.neg (ih h)
  case case4 x ih =>
    simp only [sf4Check, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    exact SF4.not _ h.1.1 rfl h.1.2 (ih h.2)
  case case5 c t f ihc iht ihf =>
    simp only [sf4Check, Bool.and_eq_true, beq_iff_eq] at h
    exact SF4.mux h.1.1.1 (ihc h.1.1.2) (iht h.1.2) (ihf h.2)
  case case6 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.binop _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case7 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.binop _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case8 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.binop _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case9 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.binop _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case10 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.binop _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case11 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.binop _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case12 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.cmpU _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case13 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.cmpU _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case14 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.cmpU _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case15 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.cmpU _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case16 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    exact SF4.cmpU _ (by simp) h.1.1.1 h.1.1.2 (iha h.1.2) (ihb h.2)
  case case17 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, decide_eq_true_eq] at h
    exact SF4.shiftOp _ (Or.inl rfl) h.1.1 (iha h.1.2) (ihb h.2)
  case case18 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true, decide_eq_true_eq] at h
    exact SF4.shiftOp _ (Or.inr rfl) h.1.1 (iha h.1.2) (ihb h.2)
  case case19 a b iha ihb =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at h
    rcases h with
      ⟨⟨⟨hwTa, hwTb⟩, hmax0⟩, ⟨⟨hpA, hpB⟩, hchka⟩, hchkb⟩ |
      ⟨⟨⟨⟨⟨⟨hwTa, hwTbn⟩, hba⟩, hBor⟩, h0⟩, hchka⟩, hchkb⟩
    · exact SF4.cmpS _ (by simp) hwTa hwTb hpA hpB hmax0
        (iha hchka) (ihb hchkb)
    · exact SF4.cmpS1 _ (by simp) hwTa hwTbn hba hBor h0
        (iha hchka) (ihb hchkb)
  case case20 a b iha ihb =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at h
    rcases h with
      ⟨⟨⟨hwTa, hwTb⟩, hmax0⟩, ⟨⟨hpA, hpB⟩, hchka⟩, hchkb⟩ |
      ⟨⟨⟨⟨⟨⟨hwTa, hwTbn⟩, hba⟩, hBor⟩, h0⟩, hchka⟩, hchkb⟩
    · exact SF4.cmpS _ (by simp) hwTa hwTb hpA hpB hmax0
        (iha hchka) (ihb hchkb)
    · exact SF4.cmpS1 _ (by simp) hwTa hwTbn hba hBor h0
        (iha hchka) (ihb hchkb)
  case case21 a b iha ihb =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at h
    rcases h with
      ⟨⟨⟨hwTa, hwTb⟩, hmax0⟩, ⟨⟨hpA, hpB⟩, hchka⟩, hchkb⟩ |
      ⟨⟨⟨⟨⟨⟨hwTa, hwTbn⟩, hba⟩, hBor⟩, h0⟩, hchka⟩, hchkb⟩
    · exact SF4.cmpS _ (by simp) hwTa hwTb hpA hpB hmax0
        (iha hchka) (ihb hchkb)
    · exact SF4.cmpS1 _ (by simp) hwTa hwTbn hba hBor h0
        (iha hchka) (ihb hchkb)
  case case22 a b iha ihb =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at h
    rcases h with
      ⟨⟨⟨hwTa, hwTb⟩, hmax0⟩, ⟨⟨hpA, hpB⟩, hchka⟩, hchkb⟩ |
      ⟨⟨⟨⟨⟨⟨hwTa, hwTbn⟩, hba⟩, hBor⟩, h0⟩, hchka⟩, hchkb⟩
    · exact SF4.cmpS _ (by simp) hwTa hwTb hpA hpB hmax0
        (iha hchka) (ihb hchkb)
    · exact SF4.cmpS1 _ (by simp) hwTa hwTbn hba hBor h0
        (iha hchka) (ihb hchkb)
  case case23 =>
    exfalso
    rw [sf4Check.eq_def] at h
    split at h <;>
      first
      | (simp_all; done)
      | grind
      | (simp_all; grind)
  case case24 args ih =>
    simp only [sf4Check, List.all_eq_true, List.mem_attach,
      true_implies, Subtype.forall, Bool.and_eq_true] at h
    refine SF4.concat (fun e he => ih e he (h e he).1) ?_
    intro e he op as heq
    obtain ⟨-, hpin⟩ := h e he
    subst heq
    simpa [beq_iff_eq, decide_eq_true_eq] using hpin
  case case25 w x hi lo ih2 ih1 =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    rcases h with h | h
    · obtain ⟨⟨⟨⟨hlo, hhi⟩, hw0⟩, hchk⟩, hsafe⟩ := h
      subst hlo
      have : hi = w - 1 := by omega
      subst this
      exact SF4.castEnc w hw0 (ih2 hchk) (by
        rcases hsafe with hle | himm
        · exact Or.inl hle
        · exact Or.inr himm)
    · obtain ⟨⟨⟨⟨hne, hlohi⟩, hlo32⟩, hchk⟩, hsafe⟩ := h
      refine SF4.sliceGen hi lo (fun n hn => by simp at hn)
        (fun w' y heq => ?_) hlohi hlo32 (ih1 (by simp only [sf4Check]; exact hchk)) (by
          rcases hsafe with hle | himm
          · exact Or.inl hle
          · exact Or.inr himm)
      -- the non-canonical guard survives the concat injectivity
      obtain ⟨he1, he2⟩ := by
        simpa using heq
      subst he1
      intro ⟨hl0, hh1⟩
      subst hl0
      simp_all
  case case26 n hi lo =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    rcases h with h | h
    · obtain ⟨⟨⟨⟨hs, hw⟩, hlo⟩, hhi⟩, hne⟩ := h
      refine SF4.sliceRef n hi lo hs hw hlo hhi ?_
      intro ⟨hl0, hh1⟩
      subst hl0
      simp [hh1] at hne
    · obtain ⟨⟨⟨hs, hw⟩, hlo⟩, hhi⟩ := h
      subst hlo
      exact SF4.sliceRefFull n hi hs hw hhi
  case case27 x hi lo hncast hcomp ih =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨hlohi, hlo32⟩, hchk⟩, hsafe⟩ := h
    exact SF4.sliceGen hi lo (fun n hn => absurd hn (by
        intro hc; exact hcomp n hc))
      (fun w' y heq => absurd heq (by
        intro hc; exact hncast w' y hc))
      hlohi hlo32 (ih hchk) (by
        rcases hsafe with hle | himm
        · exact Or.inl hle
        · exact Or.inr himm)
  case case28 =>
    exfalso
    rw [sf4Check.eq_def] at h
    split at h <;>
      first
      | (simp_all; done)
      | grind
      | (simp_all; grind)

/-- The headline form: at the assignment context width (which the
    module fragment's width-agreement conditions supply), the emitted
    Verilog computes the IR value. -/
theorem emit_sem_evalSV {wof : String → Option Nat} {we : WEnv}
    {env : Env} {e : Expr} (h : SF4 wof we e) (hbe : Bounded we env)
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn)
    {sv : SVExpr}
    (hsv : Tools.SVParser.EmitAst.emitAstExpr wof e = some sv) :
    evalSV wof env (Sparkle.IR.Semantics.widthOf we e) sv
      = evalExpr we env e := by
  obtain ⟨hw, hv⟩ := emit_sem h hbe hbw sv hsv
  unfold evalSV
  simp [hw, Nat.max_self, hv]

end Tools.SVParser.EmitSem
