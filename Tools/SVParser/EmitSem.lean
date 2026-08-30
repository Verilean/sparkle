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
  | .op .mux [_, t, f] => immuneE t && immuneE f
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
      -- SHR's width IS its value operand's (the formal rule matches
      -- Verilog's self-determined one), so it enters unconditionally;
      -- SHL still takes the generic max, so its amount must be no
      -- wider than the value for the two width rules to coincide.
      (hwb : op = .shr ∨ Sparkle.IR.Semantics.widthOf we b
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
  -- a ternary just selects one of its (context-determined) arms; if
  -- both are immune, so is the selection
  | .ternary _ t f => immuneSV t && immuneSV f
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
  | .ternary c t f, w, himm, hw => by
    simp only [immuneSV, Bool.and_eq_true] at himm
    obtain ⟨himmT, himmF⟩ := himm
    simp only [widthSV, Option.bind_eq_bind] at hw
    obtain ⟨wt, hwt, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨wf, hwf, hw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [Option.some_inj] at hw
    subst hw
    obtain ⟨bndT, stbT⟩ := evalAt_immune_all hb t wt himmT hwt
    obtain ⟨bndF, stbF⟩ := evalAt_immune_all hb f wf himmF hwf
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨vc, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      by_cases hc : vc ≠ 0
      · rw [if_pos hc, stbT (max wt wf) (Nat.le_max_left _ _)] at hv
        exact Nat.lt_of_lt_of_le (bndT v hv)
          (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
      · rw [if_neg hc, stbF (max wt wf) (Nat.le_max_right _ _)] at hv
        exact Nat.lt_of_lt_of_le (bndF v hv)
          (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    · intro W hW
      simp only [evalAt]
      rw [stbT W (Nat.le_trans (Nat.le_max_left _ _) hW),
          stbF W (Nat.le_trans (Nat.le_max_right _ _) hW),
          stbT (max wt wf) (Nat.le_max_left _ _),
          stbF (max wt wf) (Nat.le_max_right _ _)]
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
                simp [Sparkle.IR.Semantics.widthOf]

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
    simp only [immuneE, Bool.and_eq_true] at himm
    obtain ⟨himmT, himmF⟩ := himm
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svc, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨svt, hst, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨svf, hsf, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    simp only [immuneSV, Bool.and_eq_true]
    exact ⟨iht himmT svt hst, ihf himmF svf hsf⟩
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
    have hmax : op = .shl →
        max (Sparkle.IR.Semantics.widthOf we a)
          (Sparkle.IR.Semantics.widthOf we b)
        = Sparkle.IR.Semantics.widthOf we a := by
      intro hshl
      rcases hwb with hs | hle
      · rw [hshl] at hs; exact absurd hs (by simp)
      · exact Nat.max_eq_left hle
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
      · first
        | simp only [widthSV, hwa, Sparkle.IR.Semantics.widthOf,
            hmax rfl]
        | simp only [widthSV, hwa, Sparkle.IR.Semantics.widthOf]
      · rw [show Sparkle.IR.Semantics.widthOf we (.op _ [a, b])
            = Sparkle.IR.Semantics.widthOf we a from by
          first
          | simp [Sparkle.IR.Semantics.widthOf, hmax rfl]
          | simp [Sparkle.IR.Semantics.widthOf]]
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
        first
        | simp only [evalAt, hva, hamt, Option.bind_eq_bind,
            Option.bind_some, evalList, hA, hB, evalOp,
            Sparkle.IR.Semantics.widthOf, hmax rfl, Option.some_inj]
        | simp only [evalAt, hva, hamt, Option.bind_eq_bind,
            Option.bind_some, evalList, hA, hB, evalOp,
            Sparkle.IR.Semantics.widthOf, Option.some_inj]
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

private theorem emitConcatElems_isSome {wof : String → Option Nat} :
    ∀ (args : List Expr),
      (∀ e, e ∈ args → (Tools.SVParser.EmitAst.emitAstExpr wof e).isSome) →
      (Tools.SVParser.EmitAst.emitConcatElems wof args).isSome := by
  intro args
  induction args with
  | nil => intro _; simp [Tools.SVParser.EmitAst.emitConcatElems]
  | cons a rest ih =>
    intro hall
    obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp
      (hall a (List.mem_cons_self ..))
    obtain ⟨es, hes⟩ := Option.isSome_iff_exists.mp
      (ih fun e he => hall e (List.mem_cons_of_mem _ he))
    simp [Tools.SVParser.EmitAst.emitConcatElems, hea, hes]

/-- Fragment expressions always EMIT: the emitter is total on `SF4`.
    (Together with `emit_sem` this upgrades the per-expression theorem
    from "if it emits, it is right" to "it emits, and is right".) -/
theorem sf4_emit_isSome {wof : String → Option Nat} {we : WEnv}
    {e : Expr} (h : SF4 wof we e) :
    (Tools.SVParser.EmitAst.emitAstExpr wof e).isSome := by
  induction h with
  | ref n hs hw => simp [Tools.SVParser.EmitAst.emitAstExpr, hs]
  | const v w hw =>
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    by_cases hneg : v < 0 <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hne, hneg]
  | binop op hop hA hB ha hb iha ihb =>
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svb, hsb⟩ := Option.isSome_iff_exists.mp ihb
    rcases hop with h' | h' | h' | h' | h' | h' <;> subst h' <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsb,
        Tools.SVParser.EmitAst.binOpOf]
  | mux hwf hc ht hf ihc iht ihf =>
    obtain ⟨svc, hsc⟩ := Option.isSome_iff_exists.mp ihc
    obtain ⟨svt, hst⟩ := Option.isSome_iff_exists.mp iht
    obtain ⟨svf, hsf⟩ := Option.isSome_iff_exists.mp ihf
    simp [Tools.SVParser.EmitAst.emitAstExpr, hsc, hst, hsf]
  | not w hwT hwS hw0 hx ihx =>
    obtain ⟨svx, hsx⟩ := Option.isSome_iff_exists.mp ihx
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp [Tools.SVParser.EmitAst.emitAstExpr, hsx, hwT, hne]
  | neg hx ihx =>
    obtain ⟨svx, hsx⟩ := Option.isSome_iff_exists.mp ihx
    simp [Tools.SVParser.EmitAst.emitAstExpr, hsx]
  | cmpU op hop hA hB ha hb iha ihb =>
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svb, hsb⟩ := Option.isSome_iff_exists.mp ihb
    rcases hop with h' | h' | h' | h' | h' <;> subst h' <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsb,
        Tools.SVParser.EmitAst.binOpOf]
  | cmpS op hop hwTa hwTb hA hB hw0 ha hb iha ihb =>
    rename_i a b
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svb, hsb⟩ := Option.isSome_iff_exists.mp ihb
    have hne : (max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b) == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsb, hwTa, hwTb,
        hne]
  | cmpS1 op hop hwTa hwTb hwba hB hw0 ha hb iha ihb =>
    rename_i a b
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svb, hsb⟩ := Option.isSome_iff_exists.mp ihb
    have hne : (Sparkle.IR.Semantics.widthOf we a == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsb, hwTa, hwTb,
        hne]
  | sliceRef n hi lo hs hw hlo hhi hne =>
    have helide : (lo == 0 && hi + 1 == we n) = false := by
      rcases Nat.eq_zero_or_pos lo with h0 | h0
      · subst h0
        have : hi + 1 ≠ we n := fun hc => hne ⟨rfl, hc⟩
        simp [this]
      · simp [Nat.pos_iff_ne_zero.mp h0]
    simp [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide, hhi]
  | sliceRefFull n hi hs hw hfull =>
    have helide : (0 == 0 && hi + 1 == we n) = true := by simp [hfull]
    simp [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide, hfull]
  | concat hall hpin ihall =>
    rename_i args
    obtain ⟨svs, hsvs⟩ := Option.isSome_iff_exists.mp
      (emitConcatElems_isSome args fun e he => ihall e he)
    simp [Tools.SVParser.EmitAst.emitAstExpr, hsvs]
  | castEnc w hw0 hx hsafe ihx =>
    obtain ⟨svx, hsx⟩ := Option.isSome_iff_exists.mp ihx
    have hsucc : w - 1 + 1 = w := Nat.sub_add_cancel hw0
    simp [Tools.SVParser.EmitAst.emitAstExpr, hsucc, hsx]
  | sliceGen hi lo hcomp hncast hlo hlo32 hx hsafe ihx =>
    obtain ⟨svx, hsx⟩ := Option.isSome_iff_exists.mp ihx
    rw [Tools.SVParser.EmitAst.emitAst_slice_general hi lo hcomp
      hncast]
    by_cases h0 : lo == 0 <;> simp [hsx, h0]
  | shiftOp op hop hwb ha hb iha ihb =>
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svb, hsb⟩ := Option.isSome_iff_exists.mp ihb
    rcases hop with h' | h' <;> subst h' <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsb,
        Tools.SVParser.EmitAst.binOpOf]

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
    -- SHR's width is its value operand's, so no width condition;
    -- SHL still takes the generic max
    | .shl => (wb ≤ wa) && sf4Check wof we a && sf4Check wof we b
    | .shr => sf4Check wof we a && sf4Check wof we b
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
    exact SF4.shiftOp _ (Or.inl rfl) (Or.inr h.1.1)
      (iha h.1.2) (ihb h.2)
  case case18 a b iha ihb =>
    simp only [sf4Check, Bool.and_eq_true] at h
    exact SF4.shiftOp _ (Or.inr rfl) (Or.inl rfl) (iha h.1) (ihb h.2)
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

/- ------------------------------------------------------------------ -/
/- The memory layer: combinational read ports and write ports.          -/

mutual
/-- No array-read (`.index`) nodes anywhere.  For a memory port
    expression this rules out reads of the memory being written, which
    is what makes `evalPayload` collapse to plain `evalExpr` (the
    read-modify-write splice has nothing to splice). -/
def idxFree : Expr → Bool
  | .index _ _ => false
  | .op _ args => idxFreeL args
  | .concat args => idxFreeL args
  | .slice x _ _ => idxFree x
  | .sliceDim x _ _ => idxFree x
  | _ => true

/-- List lift of `idxFree`. -/
def idxFreeL : List Expr → Bool
  | [] => true
  | a :: rest => idxFree a && idxFreeL rest
end

/-- On index-free expressions the RMW read extraction is the identity,
    so `evalPayload` is just `evalExpr`. -/
theorem evalPayload_of_idxFree {we : WEnv} {mems : Sparkle.IR.Semantics.MEnv}
    {env : Env} {arr : String} {aw dw : Nat} {e : Expr}
    (h : idxFree e = true) :
    Sparkle.IR.Semantics.evalPayload we mems env arr aw dw e
      = evalExpr we env e := by
  have hid : ∀ (x : Expr), idxFree x = true →
      ∀ a k, Sparkle.IR.Semantics.extractReads a x k = (x, [], k) := by
    intro x
    induction x using idxFree.induct (motive_2 := fun l =>
        idxFreeL l = true →
        ∀ a k, Sparkle.IR.Semantics.extractReadsList a l k = (l, [], k)) with
    | case1 a i => intro h; cases h
    | case2 o args ih =>
      intro h a k
      simp only [idxFree] at h
      simp [Sparkle.IR.Semantics.extractReads, ih h a k]
    | case3 args ih =>
      intro h a k
      simp only [idxFree] at h
      simp [Sparkle.IR.Semantics.extractReads, ih h a k]
    | case4 x hi lo ih =>
      intro h a k
      simp only [idxFree] at h
      simp [Sparkle.IR.Semantics.extractReads, ih h a k]
    | case5 x hi lo ih =>
      intro h a k
      simp [Sparkle.IR.Semantics.extractReads]
    | case6 x h1 h2 h3 h4 h5 =>
      intro _ a k
      cases x with
      | ref n => rfl
      | const v w => rfl
      | op o args => exact absurd rfl (h2 o args)
      | concat args => exact absurd rfl (h3 args)
      | slice y hi lo => exact absurd rfl (h4 y hi lo)
      | sliceDim y d i => exact absurd rfl (h5 y d i)
      | index y i => exact absurd rfl (h1 y i)
    | case7 =>
      rename_i _ ar k
      rfl
    | case8 a rest ih1 ih2 =>
      rename_i h ar k
      simp only [idxFreeL, Bool.and_eq_true] at h
      simp [Sparkle.IR.Semantics.extractReadsList, ih1 h.1 ar k,
        ih2 h.2 ar k]
  simp [Sparkle.IR.Semantics.evalPayload, hid e h,
    Sparkle.IR.Semantics.spliceReads]

/-- Verilog's combinational read port: `assign rd = Mem[addr];` — the
    address is evaluated self-determined (it indexes an array), the
    fetched word truncated into the read target's width. -/
def comboReadsSV (wof : String → Option Nat) (mems : Sparkle.IR.Semantics.MEnv)
    (name : String) (aw dw : Nat) :
    List (SVExpr × String) → SEnv → Option SEnv
  | [], env => some env
  | (a, rd) :: rest, env => do
    let av ← evalSV wof env aw a
    comboReadsSV wof mems name aw dw rest
      (fun n => if n = rd then mask dw (mems name (mask aw av)) else env n)

/-- Verilog's write port inside `always_ff`: `if (en) Mem[a] <= d;` —
    a later port overwrites an earlier one at the same address. -/
def memWritePortsSV (wof : String → Option Nat) (env : SEnv)
    (name : String) (aw dw : Nat) :
    List (SVExpr × SVExpr × SVExpr) → Sparkle.IR.Semantics.MEnv →
    Option Sparkle.IR.Semantics.MEnv
  | [], m => some m
  | (a, d, en) :: rest, m => do
    let ev ← evalSV wof env 1 en
    let av ← evalSV wof env aw a
    let dv ← evalSV wof env dw d
    memWritePortsSV wof env name aw dw rest
      (if ev ≠ 0 then
        (fun nm i => if nm = name ∧ i = mask aw av then mask dw dv
                     else m nm i)
       else m)

/-- Port-list check: each port expression is in the fragment, is
    index-free (no read of the memory being written — that is the RMW
    layer), and its IR width matches the port's declared width. -/
def portCheck (wof : String → Option Nat) (we : WEnv) (w : Nat)
    (e : Expr) : Bool :=
  idxFree e && (Sparkle.IR.Semantics.widthOf we e == w) && sf4Check wof we e

/-- Every read port of one memory is checkable and its target is a
    declared name wide enough for the fetched word. -/
def readPortsCheck (wof : String → Option Nat) (we : WEnv)
    (aw dw : Nat) (ports : List (Expr × String)) : Bool :=
  ports.all fun p => portCheck wof we aw p.1 && (wof p.2 == some (we p.2))
    && (decide (dw ≤ we p.2))

/-- The emitter's read-port list for one memory. -/
def emitReadPorts (wof : String → Option Nat) :
    List (Expr × String) → Option (List (SVExpr × String))
  | [] => some []
  | (a, rd) :: rest => do
    let sa ← Tools.SVParser.EmitAst.emitAstExpr wof a
    let others ← emitReadPorts wof rest
    some ((sa, rd) :: others)

/-- The emitter's write-port list for one memory. -/
def emitWritePorts (wof : String → Option Nat) :
    List (Expr × Expr × Expr) → Option (List (SVExpr × SVExpr × SVExpr))
  | [] => some []
  | (a, d, en) :: rest => do
    let sa ← Tools.SVParser.EmitAst.emitAstExpr wof a
    let sd ← Tools.SVParser.EmitAst.emitAstExpr wof d
    let sen ← Tools.SVParser.EmitAst.emitAstExpr wof en
    let others ← emitWritePorts wof rest
    some ((sa, sd, sen) :: others)

set_option maxHeartbeats 800000 in
/-- **Forward correctness, combinational read ports**: the emitted
    `assign rd = Mem[addr];` chain lands in the same environment as the
    IR's `comboReads`, and preserves the width invariants. -/
theorem emit_sem_comboReads {wof : String → Option Nat} {we : WEnv}
    (mems : Sparkle.IR.Semantics.MEnv) (name : String) (aw dw : Nat) :
    ∀ (ports : List (Expr × String)) (env : Env),
      readPortsCheck wof we aw dw ports = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ svports env',
        emitReadPorts wof ports = some svports
        ∧ Sparkle.IR.Semantics.comboReads we mems name aw dw ports env
            = some env'
        ∧ comboReadsSV wof mems name aw dw svports env = some env'
        ∧ Bounded we env'
        ∧ (∀ n wn, wof n = some wn → env' n < 2 ^ wn) := by
  intro ports
  induction ports with
  | nil => intro env _ hbe hbw; exact ⟨[], env, rfl, rfl, rfl, hbe, hbw⟩
  | cons p rest ih =>
    obtain ⟨a, rd⟩ := p
    intro env hchk hbe hbw
    simp only [readPortsCheck, List.all_cons, Bool.and_eq_true,
      portCheck, beq_iff_eq, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨hidx, hwa⟩, hfr⟩, hwrd⟩, hdwrd⟩ := hchk.1
    have hSF := sf4Check_sound hfr
    obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hSF env)
    obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.mp (sf4_emit_isSome hSF)
    -- the fetched word fits `dw`, hence the read target's width
    have hfit : mask dw (mems name (mask aw av)) < 2 ^ dw :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hbe' : Bounded we
        (fun n => if n = rd then mask dw (mems name (mask aw av))
                  else env n) := by
      intro n
      by_cases hn : n = rd <;> simp [hn]
      · exact Nat.lt_of_lt_of_le hfit
          (Nat.pow_le_pow_right (by omega) (hn ▸ hdwrd))
      · exact hbe n
    have hbw' : ∀ n wn, wof n = some wn →
        (fun n => if n = rd then mask dw (mems name (mask aw av))
                  else env n) n < 2 ^ wn := by
      intro n wn hn
      by_cases hnr : n = rd <;> simp [hnr]
      · subst hnr
        rw [hn] at hwrd
        simp only [Option.some_inj] at hwrd
        exact Nat.lt_of_lt_of_le hfit
          (Nat.pow_le_pow_right (by omega) (hwrd ▸ hdwrd))
      · exact hbw n wn hn
    have htail : readPortsCheck wof we aw dw rest = true := by
      simp only [readPortsCheck, List.all_eq_true]
      intro x hx
      have h2 := hchk.2
      simp only [List.all_eq_true] at h2
      exact h2 x hx
    obtain ⟨svrest, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
      ih _ htail hbe' hbw'
    refine ⟨(sa, rd) :: svrest, env', ?_, ?_, ?_, hbe'', hbw''⟩
    · simp [emitReadPorts, hsa, hemit]
    · simp [Sparkle.IR.Semantics.comboReads, hav, hIR]
    · have hval : evalSV wof env aw sa = some av := by
        rw [← hwa, emit_sem_evalSV hSF hbe hbw hsa]
        exact hav
      simp only [comboReadsSV, hval, Option.bind_eq_bind,
        Option.bind_some]
      exact hSV

set_option maxHeartbeats 800000 in
/-- **Forward correctness, write ports**: the emitted `always_ff`
    guarded stores produce the same memory state as the IR's
    `memWritePorts` (index-free ports, so the RMW splice is inert). -/
theorem emit_sem_writePorts {wof : String → Option Nat} {we : WEnv}
    (mems0 : Sparkle.IR.Semantics.MEnv) (name : String) (aw dw : Nat) :
    ∀ (ports : List (Expr × Expr × Expr)) (env : Env)
      (m : Sparkle.IR.Semantics.MEnv),
      (ports.all fun p => portCheck wof we aw p.1
        && portCheck wof we dw p.2.1
        && portCheck wof we 1 p.2.2) = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ svports m',
        emitWritePorts wof ports = some svports
        ∧ Sparkle.IR.Semantics.memWritePorts we mems0 env name aw dw
            ports m = some m'
        ∧ memWritePortsSV wof env name aw dw svports m = some m' := by
  intro ports
  induction ports with
  | nil => intro env m _ _ _; exact ⟨[], m, rfl, rfl, rfl⟩
  | cons p rest ih =>
    obtain ⟨a, d, en⟩ := p
    intro env m hchk hbe hbw
    simp only [List.all_cons, Bool.and_eq_true, portCheck,
      beq_iff_eq] at hchk
    obtain ⟨⟨⟨⟨hidxA, hwa⟩, hfrA⟩, ⟨⟨hidxD, hwd⟩, hfrD⟩⟩,
      ⟨⟨hidxE, hwe⟩, hfrE⟩⟩ := hchk.1
    have hSFa := sf4Check_sound hfrA
    have hSFd := sf4Check_sound hfrD
    have hSFe := sf4Check_sound hfrE
    obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hSFa env)
    obtain ⟨dv, hdv⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hSFd env)
    obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hSFe env)
    obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.mp (sf4_emit_isSome hSFa)
    obtain ⟨sd, hsd⟩ := Option.isSome_iff_exists.mp (sf4_emit_isSome hSFd)
    obtain ⟨sen, hsen⟩ := Option.isSome_iff_exists.mp (sf4_emit_isSome hSFe)
    obtain ⟨svrest, m', hemit, hIR, hSV⟩ := ih env _ hchk.2 hbe hbw
    refine ⟨(sa, sd, sen) :: svrest, m', ?_, ?_, ?_⟩
    · simp [emitWritePorts, hsa, hsd, hsen, hemit]
    · simp only [Sparkle.IR.Semantics.memWritePorts,
        evalPayload_of_idxFree hidxE, evalPayload_of_idxFree hidxA,
        evalPayload_of_idxFree hidxD, hev, hav, hdv,
        Option.bind_eq_bind, Option.bind_some]
      exact hIR
    · have hvA : evalSV wof env aw sa = some av := by
        rw [← hwa, emit_sem_evalSV hSFa hbe hbw hsa]; exact hav
      have hvD : evalSV wof env dw sd = some dv := by
        rw [← hwd, emit_sem_evalSV hSFd hbe hbw hsd]; exact hdv
      have hvE : evalSV wof env 1 sen = some ev := by
        rw [← hwe, emit_sem_evalSV hSFe hbe hbw hsen]; exact hev
      simp only [memWritePortsSV, hvA, hvD, hvE, Option.bind_eq_bind,
        Option.bind_some]
      exact hSV

/- ------------------------------------------------------------------ -/
/- The statement layer: the combinational phase of a module.           -/

/-- One step of the emitted combinational program: a continuous
    assignment, or one memory's combinational read ports. -/
inductive CombStep where
  | assign (lhs : String) (rhs : SVExpr)
  | reads (name : String) (aw dw : Nat) (ports : List (SVExpr × String))

/-- The combinational program the emitter prints: `assign l = E;` for
    each assign, and `assign rd = Mem[addr];` for each
    combinationally-read memory.  Registers, instances and sync-read
    memories contribute nothing to this phase. -/
def emitAssigns (wof : String → Option Nat) :
    List Stmt → Option (List CombStep)
  | [] => some []
  | .assign l r :: rest => do
    let sv ← Tools.SVParser.EmitAst.emitAstExpr wof r
    let others ← emitAssigns wof rest
    some (.assign l sv :: others)
  | .register _ _ _ _ _ :: rest => emitAssigns wof rest
  | .memory name aw dw _ _ _ _ ra rd cr _ er :: rest =>
    if cr then do
      let ports ← emitReadPorts wof ((ra, rd) :: er)
      let others ← emitAssigns wof rest
      some (.reads name aw dw ports :: others)
    else emitAssigns wof rest
  | .inst _ _ _ :: rest => emitAssigns wof rest

/-- Verilog's combinational fold: each continuous assignment evaluates
    its RHS at its LHS's declared width (the assignment context) and
    truncates into the target; each read port fetches its word. -/
def evalAssignsSV (wof : String → Option Nat)
    (mems : Sparkle.IR.Semantics.MEnv) :
    List CombStep → SEnv → Option SEnv
  | [], env => some env
  | .assign n sv :: rest, env => do
    let w ← wof n
    let v ← evalSV wof env w sv
    evalAssignsSV wof mems rest
      (fun m => if m = n then mask w v else env m)
  | .reads name aw dw ports :: rest, env => do
    let env' ← comboReadsSV wof mems name aw dw ports env
    evalAssignsSV wof mems rest env'

/-- Per-body forward-fragment check: every assign's RHS is in the
    fragment, agrees in width with its LHS, and the LHS is a declared,
    sanitize-fixed name; a combinationally-read memory's read ports are
    checkable (index-free addresses at the address width, targets wide
    enough); registers, instances and sync-read memories are
    combinationally inert. -/
def assignsCheck (wof : String → Option Nat) (we : WEnv) :
    List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    (Sparkle.Backend.Verilog.sanitizeName l == l)
      && (wof l == some (we l))
      && (Sparkle.IR.Semantics.widthOf we r == we l)
      && sf4Check wof we r
      && assignsCheck wof we rest
  | .register _ _ _ _ _ :: rest => assignsCheck wof we rest
  | .memory _ aw dw _ _ _ _ ra rd cr _ er :: rest =>
    (!cr || readPortsCheck wof we aw dw ((ra, rd) :: er))
      && assignsCheck wof we rest
  | .inst _ _ _ :: rest => assignsCheck wof we rest

set_option maxHeartbeats 800000 in
/-- **Forward correctness, statement layer**: on a checked body, the
    emitter's assign list EXISTS and Verilog's in-order assignment fold
    computes exactly the IR's `evalAssigns` — the whole combinational
    phase of the module agrees, and the result environment stays
    width-bounded on both counts. -/
theorem emit_sem_assigns {wof : String → Option Nat} {we : WEnv}
    (mems : Sparkle.IR.Semantics.MEnv) :
    ∀ (body : List Stmt) (env : Env),
      assignsCheck wof we body = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ pairs env',
        emitAssigns wof body = some pairs
        ∧ Sparkle.IR.Semantics.evalAssigns we mems body env = some env'
        ∧ evalAssignsSV wof mems pairs env = some env'
        ∧ Bounded we env'
        ∧ (∀ n wn, wof n = some wn → env' n < 2 ^ wn) := by
  intro body
  induction body with
  | nil =>
    intro env _ hbe hbw
    exact ⟨[], env, rfl, rfl, rfl, hbe, hbw⟩
  | cons st rest ih =>
    intro env hchk hbe hbw
    cases st with
    | assign l r =>
      simp only [assignsCheck, Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨⟨⟨hs, hwl⟩, hwr⟩, hfr⟩, hrest⟩ := hchk
      have hSF := sf4Check_sound hfr
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome hSF env)
      obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
        (sf4_emit_isSome hSF)
      have hvlt : v < 2 ^ we l :=
        hwr ▸ sf4_bounded hSF hbe v hv
      -- the two updated environments are the SAME function
      have henv : (fun m => if m = l then mask (we l) v else env m)
          = (fun m => if m = l then v else env m) := by
        funext m
        by_cases hm : m = l <;>
          simp [hm, mask, Nat.mod_eq_of_lt hvlt]
      have hbe' : Bounded we (fun m => if m = l then v else env m) := by
        intro m
        by_cases hm : m = l <;> simp [hm]
        · exact hvlt
        · exact hbe m
      have hbw' : ∀ n wn, wof n = some wn →
          (fun m => if m = l then v else env m) n < 2 ^ wn := by
        intro n wn hn
        by_cases hm : n = l <;> simp [hm]
        · subst hm
          rw [hn] at hwl
          simp only [Option.some_inj] at hwl
          exact hwl ▸ hvlt
        · exact hbw n wn hn
      obtain ⟨pairs, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
        ih _ hrest hbe' hbw'
      refine ⟨.assign l sv :: pairs, env', ?_, ?_, ?_, hbe'', hbw''⟩
      · simp [emitAssigns, hsv, hemit]
      · simp [Sparkle.IR.Semantics.evalAssigns, hv, hIR]
      · -- SV: the LHS width is declared; the RHS at that width is the
        -- IR value (width agreement rewrites the context)
        have hval : evalSV wof env (we l) sv = some v := by
          rw [← hwr]
          rw [emit_sem_evalSV hSF hbe hbw hsv]
          exact hv
        simp only [evalAssignsSV, hwl, hval, Option.bind_eq_bind,
          Option.bind_some]
        rw [henv]
        exact hSV
    | register n w clk x init =>
      simp only [assignsCheck] at hchk
      obtain ⟨pairs, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
        ih env hchk hbe hbw
      exact ⟨pairs, env', by simpa [emitAssigns] using hemit,
        by simpa [Sparkle.IR.Semantics.evalAssigns] using hIR,
        hSV, hbe'', hbw''⟩
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [assignsCheck, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true] at hchk
      obtain ⟨hmem, hrest⟩ := hchk
      by_cases hcr : cr
      · -- combinational read ports: they ARE part of this phase
        subst hcr
        have hports : readPortsCheck wof we aw dw ((ra, rd) :: er) = true := by
          rcases hmem with h | h
          · exact absurd h (by simp)
          · exact h
        obtain ⟨svports, envR, hemitR, hIRR, hSVR, hbeR, hbwR⟩ :=
          emit_sem_comboReads mems nm aw dw ((ra, rd) :: er) env hports
            hbe hbw
        obtain ⟨pairs, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
          ih envR hrest hbeR hbwR
        refine ⟨.reads nm aw dw svports :: pairs, env', ?_, ?_, ?_,
          hbe'', hbw''⟩
        · simp [emitAssigns, hemitR, hemit]
        · simp [Sparkle.IR.Semantics.evalAssigns, hIRR, hIR]
        · simp [evalAssignsSV, hSVR, hSV]
      · simp only [hcr] at hmem
        obtain ⟨pairs, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
          ih env hrest hbe hbw
        exact ⟨pairs, env', by simpa [emitAssigns, hcr] using hemit,
          by simpa [Sparkle.IR.Semantics.evalAssigns, hcr] using hIR,
          hSV, hbe'', hbw''⟩
    | inst nm md conns =>
      simp only [assignsCheck] at hchk
      obtain ⟨pairs, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
        ih env hchk hbe hbw
      exact ⟨pairs, env', by simpa [emitAssigns] using hemit,
        by simpa [Sparkle.IR.Semantics.evalAssigns] using hIR,
        hSV, hbe'', hbw''⟩

/- ------------------------------------------------------------------ -/
/- The sequential layer and the cycle-trace capstone.                   -/

/-- The register tuples the emitter prints as always-blocks:
    (target, reset name, next-value emission, reset value). -/
def emitRegs (wof : String → Option Nat) :
    List Stmt → Option (List (String × String × SVExpr × Int))
  | [] => some []
  | .register out _ (rstName, _) input init :: rest => do
    let sv ← Tools.SVParser.EmitAst.emitAstExpr wof input
    let others ← emitRegs wof rest
    some ((out, rstName, sv, init) :: others)
  | .assign _ _ :: rest => emitRegs wof rest
  | .memory _ _ _ _ _ _ _ _ _ _ _ _ :: rest => emitRegs wof rest
  | .inst _ _ _ :: rest => emitRegs wof rest

/-- Verilog's register phase: each always-block reads the SETTLED
    combinational environment, applies its reset mux, and truncates
    the next value into the register's declared width. -/
def regNextsSV (wof : String → Option Nat) :
    List (String × String × SVExpr × Int) → SEnv →
    Option (List (String × Nat))
  | [], _ => some []
  | (out, rst, svin, init) :: rest, env => do
    let w ← wof out
    let v ← evalSV wof env w svin
    let nexts ← regNextsSV wof rest env
    some ((out, if env rst ≠ 0
      then Sparkle.IR.Semantics.encodeInit init w
      else mask w v) :: nexts)

/-- The sequential fragment check: the combinational conditions, plus
    every register's next value in the fragment at the register's
    width under a declared name — and NO memories (their ports are the
    next layer). -/
def seqCheck (wof : String → Option Nat) (we : WEnv) :
    List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    (Sparkle.Backend.Verilog.sanitizeName l == l)
      && (wof l == some (we l))
      && (Sparkle.IR.Semantics.widthOf we r == we l)
      && sf4Check wof we r
      && seqCheck wof we rest
  | .register out _ _ input _ :: rest =>
    (wof out == some (we out))
      && (Sparkle.IR.Semantics.widthOf we input == we out)
      && sf4Check wof we input
      && seqCheck wof we rest
  -- a combinationally-read memory: read ports feed the combinational
  -- phase, write ports the sequential one (sync-read memories latch
  -- into register-like state, which is the next layer)
  | .memory _ aw dw _ wa wd wen ra rd cr ew er :: rest =>
    cr && readPortsCheck wof we aw dw ((ra, rd) :: er)
      && (((wa, wd, wen) :: ew).all fun p =>
            portCheck wof we aw p.1 && portCheck wof we dw p.2.1
              && portCheck wof we 1 p.2.2)
      && seqCheck wof we rest
  | .inst _ _ _ :: rest => seqCheck wof we rest

/-- `seqCheck` implies the combinational-phase check. -/
theorem seqCheck_assigns {wof : String → Option Nat} {we : WEnv} :
    ∀ {body : List Stmt}, seqCheck wof we body = true →
      assignsCheck wof we body = true := by
  intro body
  induction body with
  | nil => intro _; rfl
  | cons st rest ih =>
    intro h
    cases st with
    | assign l r =>
      simp only [seqCheck, Bool.and_eq_true] at h
      simp only [assignsCheck, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
    | register _ _ _ _ _ =>
      simp only [seqCheck, Bool.and_eq_true] at h
      simpa [assignsCheck] using ih h.2
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [seqCheck, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hcr, hrd⟩, _⟩, hrest⟩ := h
      simp only [assignsCheck, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨Or.inr hrd, ih hrest⟩
    | inst _ _ _ =>
      simp only [seqCheck] at h
      simpa [assignsCheck] using ih h

/-- The emitter's memory-write program: one entry per memory. -/
def emitMemWrites (wof : String → Option Nat) :
    List Stmt → Option (List (String × Nat × Nat ×
      List (SVExpr × SVExpr × SVExpr)))
  | [] => some []
  | .memory name aw dw _ wa wd wen _ _ _ ew _ :: rest => do
    let ports ← emitWritePorts wof ((wa, wd, wen) :: ew)
    let others ← emitMemWrites wof rest
    some ((name, aw, dw, ports) :: others)
  | .assign _ _ :: rest => emitMemWrites wof rest
  | .register _ _ _ _ _ :: rest => emitMemWrites wof rest
  | .inst _ _ _ :: rest => emitMemWrites wof rest

/-- Verilog's memory-update phase: run each memory's write ports in the
    settled environment. -/
def memNextsSV (wof : String → Option Nat) :
    List (String × Nat × Nat × List (SVExpr × SVExpr × SVExpr)) →
    Sparkle.IR.Semantics.MEnv → SEnv → Option Sparkle.IR.Semantics.MEnv
  | [], mems, _ => some mems
  | (name, aw, dw, ports) :: rest, mems, env => do
    let mems' ← memWritePortsSV wof env name aw dw ports mems
    memNextsSV wof rest mems' env

set_option maxHeartbeats 800000 in
/-- **Forward correctness, memory phase**: the emitted `always_ff`
    stores produce the same memory state as the IR's `memNexts`. -/
theorem emit_sem_memNexts {wof : String → Option Nat} {we : WEnv} :
    ∀ (body : List Stmt) (mems : Sparkle.IR.Semantics.MEnv) (env : Env),
      seqCheck wof we body = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ prog mems',
        emitMemWrites wof body = some prog
        ∧ Sparkle.IR.Semantics.memNexts we body mems env = some mems'
        ∧ memNextsSV wof prog mems env = some mems' := by
  intro body
  induction body with
  | nil => intro mems env _ _ _; exact ⟨[], mems, rfl, rfl, rfl⟩
  | cons st rest ih =>
    intro mems env hchk hbe hbw
    cases st with
    | assign l r =>
      simp only [seqCheck, Bool.and_eq_true] at hchk
      obtain ⟨prog, mems', hemit, hIR, hSV⟩ := ih mems env hchk.2 hbe hbw
      exact ⟨prog, mems', by simpa [emitMemWrites] using hemit,
        by simpa [Sparkle.IR.Semantics.memNexts] using hIR, hSV⟩
    | register _ _ _ _ _ =>
      simp only [seqCheck, Bool.and_eq_true] at hchk
      obtain ⟨prog, mems', hemit, hIR, hSV⟩ := ih mems env hchk.2 hbe hbw
      exact ⟨prog, mems', by simpa [emitMemWrites] using hemit,
        by simpa [Sparkle.IR.Semantics.memNexts] using hIR, hSV⟩
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [seqCheck, Bool.and_eq_true] at hchk
      obtain ⟨⟨⟨_, _⟩, hwp⟩, hrest⟩ := hchk
      obtain ⟨svports, m1, hemitW, hIRW, hSVW⟩ :=
        emit_sem_writePorts mems nm aw dw ((wa, wd, wen) :: ew) env mems
          hwp hbe hbw
      obtain ⟨prog, mems', hemit, hIR, hSV⟩ := ih m1 env hrest hbe hbw
      refine ⟨(nm, aw, dw, svports) :: prog, mems', ?_, ?_, ?_⟩
      · simp [emitMemWrites, hemitW, hemit]
      · simp [Sparkle.IR.Semantics.memNexts, hIRW, hIR]
      · simp [memNextsSV, hSVW, hSV]
    | inst _ _ _ =>
      simp only [seqCheck] at hchk
      obtain ⟨prog, mems', hemit, hIR, hSV⟩ := ih mems env hchk hbe hbw
      exact ⟨prog, mems', by simpa [emitMemWrites] using hemit,
        by simpa [Sparkle.IR.Semantics.memNexts] using hIR, hSV⟩

/-- **Forward correctness, register phase**: on a checked body, the
    emitter's register list exists and Verilog's always-block fold in
    the settled environment computes exactly the IR's `regNexts`. -/
theorem emit_sem_regs {wof : String → Option Nat} {we : WEnv}
    (mems : Sparkle.IR.Semantics.MEnv) :
    ∀ (body : List Stmt) (env : Env),
      seqCheck wof we body = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ regs nexts,
        emitRegs wof body = some regs
        ∧ Sparkle.IR.Semantics.regNexts we mems body env = some nexts
        ∧ regNextsSV wof regs env = some nexts := by
  intro body
  induction body with
  | nil => intro env _ _ _; exact ⟨[], [], rfl, rfl, rfl⟩
  | cons st rest ih =>
    intro env hchk hbe hbw
    cases st with
    | assign l r =>
      simp only [seqCheck, Bool.and_eq_true] at hchk
      obtain ⟨regs, nexts, hemit, hIR, hSV⟩ := ih env hchk.2 hbe hbw
      exact ⟨regs, nexts, by simpa [emitRegs] using hemit,
        by simpa [Sparkle.IR.Semantics.regNexts] using hIR, hSV⟩
    | register out clk rstK input init =>
      obtain ⟨rstName, kind⟩ := rstK
      simp only [seqCheck, Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨⟨hwo, hwi⟩, hfr⟩, hrest⟩ := hchk
      have hSF := sf4Check_sound hfr
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome hSF env)
      obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
        (sf4_emit_isSome hSF)
      obtain ⟨regs, nexts, hemit, hIR, hSV⟩ := ih env hrest hbe hbw
      have hval : evalSV wof env (we out) sv = some v := by
        rw [← hwi, emit_sem_evalSV hSF hbe hbw hsv]
        exact hv
      refine ⟨(out, rstName, sv, init) :: regs,
        (out, if env rstName ≠ 0
          then Sparkle.IR.Semantics.encodeInit init (we out)
          else mask (we out) v) :: nexts, ?_, ?_, ?_⟩
      · simp [emitRegs, hsv, hemit]
      · simp [Sparkle.IR.Semantics.regNexts, hv, hIR]
      · simp [regNextsSV, hwo, hval, hSV]
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [seqCheck, Bool.and_eq_true] at hchk
      obtain ⟨⟨⟨hcr, _⟩, _⟩, hrest⟩ := hchk
      obtain ⟨regs, nexts, hemit, hIR, hSV⟩ := ih env hrest hbe hbw
      -- a COMBINATIONALLY-read memory contributes no register updates
      refine ⟨regs, nexts, by simpa [emitRegs] using hemit, ?_, hSV⟩
      simpa [Sparkle.IR.Semantics.regNexts, hcr] using hIR
    | inst _ _ _ =>
      simp only [seqCheck] at hchk
      obtain ⟨regs, nexts, hemit, hIR, hSV⟩ := ih env hchk hbe hbw
      exact ⟨regs, nexts, by simpa [emitRegs] using hemit,
        by simpa [Sparkle.IR.Semantics.regNexts] using hIR, hSV⟩

/-- The Verilog trace: elaborate the assigns, step the registers,
    recurse — the mirror of `runModule` for a memory-free module. -/
def runModuleSV (wof : String → Option Nat)
    (pairs : List CombStep)
    (regs : List (String × String × SVExpr × Int))
    (mprog : List (String × Nat × Nat × List (SVExpr × SVExpr × SVExpr)))
    (seed : Nat → (String → Nat) → SEnv) :
    Nat → (String → Nat) → Sparkle.IR.Semantics.MEnv → Option (List SEnv)
  | 0, _, _ => some []
  | k + 1, st, mems => do
    let envF ← evalAssignsSV wof mems pairs (seed k st)
    let nexts ← regNextsSV wof regs envF
    let mems' ← memNextsSV wof mprog mems envF
    let rest ← runModuleSV wof pairs regs mprog seed k
      (Sparkle.IR.Semantics.applyNexts st nexts) mems'
    some (envF :: rest)

set_option maxHeartbeats 800000 in
/-- **The M4 capstone — the forward trace theorem.**  For a module
    body in the sequential fragment, and ANY seeding discipline that
    respects the declared widths, the emitted Verilog — under the
    SystemVerilog-subset semantics — produces the SAME cycle-by-cycle
    trace as the IR, for every cycle count.  On these modules the
    emitter is out of the trusted base in the forward direction. -/
theorem certified_forward_trace {wof : String → Option Nat} {we : WEnv}
    {body : List Stmt}
    (hchk : seqCheck wof we body = true)
    (seed : Nat → (String → Nat) → Env)
    (hseed : ∀ t st, Bounded we (seed t st)
      ∧ ∀ n wn, wof n = some wn → seed t st n < 2 ^ wn) :
    ∃ pairs regs mprog,
      emitAssigns wof body = some pairs
      ∧ emitRegs wof body = some regs
      ∧ emitMemWrites wof body = some mprog
      ∧ ∀ (k : Nat) (st : String → Nat)
          (mems : Sparkle.IR.Semantics.MEnv),
          Sparkle.IR.Semantics.runModule we body seed k st mems
            = runModuleSV wof pairs regs mprog seed k st mems := by
  -- the emissions exist (any bounded env will do to instantiate the
  -- phase theorems; take the seed at 0)
  obtain ⟨pairs0, env0', hemitA, _, _, _, _⟩ :=
    emit_sem_assigns (fun _ _ => 0) body (seed 0 fun _ => 0)
      (seqCheck_assigns hchk) (hseed 0 _).1 (hseed 0 _).2
  obtain ⟨regs0, _, hemitR, _, _⟩ :=
    emit_sem_regs (fun _ _ => 0) body (seed 0 fun _ => 0) hchk
      (hseed 0 _).1 (hseed 0 _).2
  obtain ⟨mprog0, _, hemitM, _, _⟩ :=
    emit_sem_memNexts body (fun _ _ => 0) (seed 0 fun _ => 0) hchk
      (hseed 0 _).1 (hseed 0 _).2
  refine ⟨pairs0, regs0, mprog0, hemitA, hemitR, hemitM, ?_⟩
  intro k
  induction k with
  | zero =>
    intro st mems
    rfl
  | succ k ihk =>
    intro st mems
    obtain ⟨pairs, envF, hemitA', hIRA, hSVA, hbeF, hbwF⟩ :=
      emit_sem_assigns mems body (seed k st)
        (seqCheck_assigns hchk) (hseed k st).1 (hseed k st).2
    rw [hemitA] at hemitA'
    simp only [Option.some_inj] at hemitA'
    subst hemitA'
    obtain ⟨regs, nexts, hemitR', hIRR, hSVR⟩ :=
      emit_sem_regs mems body envF hchk hbeF hbwF
    rw [hemitR] at hemitR'
    simp only [Option.some_inj] at hemitR'
    subst hemitR'
    obtain ⟨mprog, mems', hemitM', hIRM, hSVM⟩ :=
      emit_sem_memNexts body mems envF hchk hbeF hbwF
    rw [hemitM] at hemitM'
    simp only [Option.some_inj] at hemitM'
    subst hemitM'
    simp only [Sparkle.IR.Semantics.runModule,
      Sparkle.IR.Semantics.stepModule, runModuleSV, hIRA, hSVA, hIRR,
      hSVR, hIRM, hSVM, Option.bind_eq_bind, Option.bind_some]
    rw [ihk (Sparkle.IR.Semantics.applyNexts st nexts) mems']

end Tools.SVParser.EmitSem
