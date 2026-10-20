import Tools.ShippingTypedExprSoundness

/-! Local simulation of the mux result emitter used by the shipping handler.
Operand translation and result-type inference remain separate obligations;
this file proves the actual allocation/emission step, not the whole partial
handler or the synthesis entry. -/
namespace Tools.ShippingMuxLoweringSoundness
open Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics Sparkle.IR.Type
open Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingAllocationSoundness Tools.ShippingTranslateSoundness
open Tools.ShippingTypedExprSoundness

/-- The one-bit encoding shared by the source Bool and the IR condition. -/
def encodeBool (b : Bool) : Nat := if b then 1 else 0

theorem encodeBool_lt (b : Bool) : encodeBool b < 2 ^ 1 := by cases b <;> decide

/-- The source meaning is the actual library mux, at any observation time. -/
theorem library_mux {dom : DomainConfig} {n : Nat}
    (c : Signal dom Bool) (a b : Signal dom (BitVec n)) (t : Nat) :
    (Signal.mux c a b).val t = if c.val t then a.val t else b.val t := rfl

theorem mux_rhs_correct {dom : DomainConfig} {n : Nat}
    (c : Signal dom Bool) (a b : Signal dom (BitVec n)) (t : Nat)
    (we : WEnv) (env : Env) (cw aw bw : String)
    (hc : env cw = encodeBool (c.val t))
    (ha : env aw = (a.val t).toNat) (hb : env bw = (b.val t).toNat) :
    evalExpr we env (.op .mux [.ref cw, .ref aw, .ref bw]) =
      some ((Signal.mux c a b).val t).toNat := by
  rw [library_mux]
  cases h : c.val t <;>
    simp [evalExpr, evalList, evalOp, hc, ha, hb, h, encodeBool]

/-- Exact state transition of the non-recursive helper that the real mux
handler calls. It includes the compiler width-cache update via makeWire_returns. -/
theorem emitMuxResult_returns {ctx : CompilerState} {s s' : CircuitState}
    {cw aw bw hint : String} {named : Bool} {ty : HWType} {w : String}
    (h : Returns (emitMuxResult cw aw bw hint named ty) ctx s w s') :
    w = (CircuitM.makeWire hint ty named s).1 ∧
    s' = (CircuitM.emitAssign w (.op .mux [.ref cw, .ref aw, .ref bw])
      (CircuitM.makeWire hint ty named s).2).2 := by
  unfold emitMuxResult at h
  obtain ⟨r, sa, hm, k⟩ := Returns.bind h
  obtain ⟨hr, hs⟩ := makeWire_returns hm
  obtain ⟨u, sb, he, k⟩ := Returns.bind k
  obtain ⟨hw, hs'⟩ := Returns.pure k
  have hem := emitAssign_returns he
  subst w s'
  exact ⟨hr, by rw [hem, hs]⟩

/-- A successful shipping mux emission preserves the source value and every
other wire. Freshness is supplied by the allocator, not by the caller.
The declaration/width assumptions describe the already translated operands
and the selected result type; they do not assume evaluation of this mux. -/
theorem emitMuxResult_correct {Key : Type} {dom : DomainConfig} {n : Nat}
    (c : Signal dom Bool) (a b : Signal dom (BitVec n)) (t : Nat)
    {ctx : CompilerState} {s s' : CircuitState} {cw aw bw hint w : String} {named : Bool}
    (hrun : Returns (emitMuxResult cw aw bw hint named (.bitVector n)) ctx s w s')
    (we : WEnv) (mems : MEnv) (initial prior : Env)
    (lookup : Key → Option String) (values : Key → Nat)
    (hprefix : Runs we mems initial s prior)
    (hc : prior cw = encodeBool (c.val t))
    (ha : prior aw = (a.val t).toNat) (hb : prior bw = (b.val t).toNat)
    (hn : 0 < n) (hwc : we cw = 1) (hwa : we aw = n) (hwb : we bw = n)
    (hw : WidthsAgree we s')
    (bindings : BindingsAgree lookup values prior) (reserved : Reserved lookup s.usedNames) :
    s.usedNames.contains w = false ∧
    TypedExpr we (.op .mux [.ref cw, .ref aw, .ref bw]) n ∧
    we w = n ∧
    ∃ result, Runs we mems initial s' result ∧
      result w = ((Signal.mux c a b).val t).toNat ∧
      (∀ x, x ≠ w → result x = prior x) ∧
      BindingsAgree lookup values result ∧ Reserved lookup s'.usedNames := by
  obtain ⟨hr, hs⟩ := emitMuxResult_returns hrun
  have hm := CircuitM.makeWire_spec hint (.bitVector n) named s
  have hdecl : ({ name := w, ty := .bitVector n } : Port) ∈ s'.module.wires := by
    rw [hs, emitAssign_wires, hm.2.2.2, hr]
    simp
  have hww := hw _ hdecl n rfl
  have htyped : TypedExpr we (.op .mux [.ref cw, .ref aw, .ref bw]) n := by
    exact .mux (hwc ▸ TypedExpr.ref cw (by omega))
      (hwa ▸ TypedExpr.ref aw (by omega)) (hwb ▸ TypedExpr.ref bw (by omega))
  refine ⟨by rw [hr]; exact hm.1, htyped, hww, ?_⟩
  have hp : Runs we mems initial (CircuitM.makeWire hint (.bitVector n) named s).2 prior :=
    runs_of_body_eq hm.2.2.1 hprefix
  let value := ((Signal.mux c a b).val t).toNat
  refine ⟨write prior w value, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]
    exact emitAssign_sound _ we mems initial prior w _ value hp
      (mux_rhs_correct c a b t we prior cw aw bw hc ha hb)
  · simp [write, value]
  · intro x hx; simp [write, hx]
  · exact bindings.write_fresh w value (by
      rw [hr]; exact makeWire_not_live lookup s reserved hint (.bitVector n) named)
  · rw [hs, emitAssign_usedNames]
    exact makeWire_reserved lookup s reserved hint (.bitVector n) named

/-- The mux step extends a width-indexed assignment body, so its result can
feed the backend body checker without falling back to uniform-width `SizedBody`. -/
theorem emitMuxResult_typedBody {ctx : CompilerState} {s s' : CircuitState}
    {cw aw bw hint w : String} {named : Bool} {n : Nat} {we : WEnv}
    (hrun : Returns (emitMuxResult cw aw bw hint named (.bitVector n)) ctx s w s')
    (hw : WidthsAgree we s')
    (hmux : TypedExpr we (.op .mux [.ref cw, .ref aw, .ref bw]) n)
    (hbody : ∀ st ∈ s.module.body, ∃ l r, st = .assign l r ∧ TypedExpr we r (we l)) :
    ∀ st ∈ s'.module.body, ∃ l r, st = .assign l r ∧ TypedExpr we r (we l) := by
  obtain ⟨hr, hs⟩ := emitMuxResult_returns hrun
  have hm := CircuitM.makeWire_spec hint (.bitVector n) named s
  have hdecl : ({ name := w, ty := .bitVector n } : Port) ∈ s'.module.wires := by
    rw [hs, emitAssign_wires, hm.2.2.2, hr]
    simp
  have hww : we w = n := hw _ hdecl n rfl
  rw [hs, emitAssign_body_cons, hm.2.2.1]
  intro st hst
  rcases List.mem_cons.mp hst with he | he
  · subst st
    exact ⟨w, _, rfl, hww.symm ▸ hmux⟩
  · exact hbody st he

/-- For the same Bool/BitVec source values, actual expression text has the
certified syntax and evaluates to the library mux result. Width/identifier
checks are derived from the three translated operand wires. -/
theorem mux_printed {dom : DomainConfig} {n : Nat}
    (c : Signal dom Bool) (a b : Signal dom (BitVec n)) (t : Nat)
    (we : WEnv) (env : Env) (wof : String → Option Nat) (cw aw bw : String)
    (hc : env cw = encodeBool (c.val t))
    (ha : env aw = (a.val t).toNat) (hb : env bw = (b.val t).toNat)
    (hn : 0 < n) (hwc : we cw = 1) (hwa : we aw = n) (hwb : we bw = n)
    (hnames : ∀ x ∈ [cw, aw, bw], Sparkle.Backend.Verilog.sanitizeName x = x ∧
      wof x = some (we x) ∧ Tools.SVParser.ConcreteSyntax.Identifier x)
    (hbounded : Bounded we env)
    (hprint : ∀ x w, wof x = some w → env x < 2 ^ w) :
    ∃ sv, Tools.SVParser.EmitAst.emitAstExpr wof (.op .mux [.ref cw, .ref aw, .ref bw]) = some sv ∧
      Tools.SVParser.ConcreteSyntax.Expression sv
        (Sparkle.Backend.Verilog.emitExpr wof (.op .mux [.ref cw, .ref aw, .ref bw])) ∧
      Tools.SVParser.SVSemantics.evalSV wof env n sv = some ((Signal.mux c a b).val t).toNat := by
  have ht : TypedExpr we (.op .mux [.ref cw, .ref aw, .ref bw]) n :=
    .mux (hwc ▸ TypedExpr.ref cw (by omega))
      (hwa ▸ TypedExpr.ref aw (by omega)) (hwb ▸ TypedExpr.ref bw (by omega))
  obtain ⟨sv, he, hs, hv⟩ := typedExpr_printed ht (wof := wof) (by
    intro x hx
    exact hnames x (by simpa [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList] using hx))
  exact ⟨sv, he, hs, (hv env hbounded hprint).trans (mux_rhs_correct c a b t we env cw aw bw hc ha hb)⟩

end Tools.ShippingMuxLoweringSoundness
