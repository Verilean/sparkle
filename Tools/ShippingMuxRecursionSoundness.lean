import Tools.ShippingMuxLoweringSoundness

/-! Compositional simulation of the actual recursive mux sequence. The child
contracts include preservation of reserved wires, not just the returned value:
otherwise translating the else branch could invalidate the condition or then
branch. Discharging these contracts for the full recursive DSL, and proving
the MetaM result-type query, remain front-end obligations. -/
namespace Tools.ShippingMuxRecursionSoundness
open Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics Sparkle.IR.Type
open Sparkle.Compiler.Elab Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingScalarSoundness Tools.ShippingAllocationSoundness
open Tools.ShippingTranslateSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingMuxLoweringSoundness

def TypedBody (we : WEnv) (s : CircuitState) : Prop :=
  ∀ st ∈ s.module.body, ∃ l r, st = .assign l r ∧ TypedExpr we r (we l)

/-- An induction hypothesis for one child, valid at any intermediate state
satisfying the front-end invariant `good`. Cache hits may return an existing
reserved wire; freshness is deliberately not required of child results. -/
def ChildSpec (rec : TranslateFn) (ctx : CompilerState) (we : WEnv)
    (mems : MEnv) (initial : Env) (good : CircuitState → Env → Prop)
    (e : Lean.Expr) (hint : String) (width value : Nat) : Prop :=
  ∀ s s' w prior, good s prior → Runs we mems initial s prior →
    Returns (rec e hint false false) ctx s w s' →
    ∃ result, good s' result ∧ Runs we mems initial s' result ∧
      s'.usedNames.contains w = true ∧ we w = width ∧ result w = value ∧
      (∀ x, s.usedNames.contains x = true → s'.usedNames.contains x = true) ∧
      (∀ x, s.usedNames.contains x = true → result x = prior x)

/-- Exact successful execution of the shipping sequence, including child order
and the state at which the type query is executed. -/
theorem translateMuxWith_returns {rec : TranslateFn} {query : CompilerM HWType}
    {c a b : Lean.Expr} {hint w : String} {named : Bool}
    {ctx : CompilerState} {s s' : CircuitState}
    (h : Returns (translateMuxWith rec query c a b hint named) ctx s w s') :
    ∃ cw aw bw sc sa sb sq ty,
      Returns (rec c "mux_cond" false false) ctx s cw sc ∧
      Returns (rec a "mux_then" false false) ctx sc aw sa ∧
      Returns (rec b "mux_else" false false) ctx sa bw sb ∧
      Returns query ctx sb ty sq ∧
      Returns (emitMuxResult cw aw bw hint named ty) ctx sq w s' := by
  unfold translateMuxWith at h
  obtain ⟨cw, sc, hc, h⟩ := Returns.bind h
  obtain ⟨aw, sa, ha, h⟩ := Returns.bind h
  obtain ⟨bw, sb, hb, h⟩ := Returns.bind h
  obtain ⟨ty, sq, hq, he⟩ := Returns.bind h
  exact ⟨cw, aw, bw, sc, sa, sb, sq, ty, hc, ha, hb, hq, he⟩

/-- Compose three recursive simulations with real allocation/emission. Source
values come from the actual library mux. The conclusion preserves every wire
reserved at entry, so outer recursive nodes can retain earlier child values.
The result-type query's value and lack of circuit-state effects are explicit
premises, not an assumed proof of the MetaM oracle. -/
theorem translateMuxWith_correct {dom : DomainConfig} {n : Nat}
    (c : Signal dom Bool) (a b : Signal dom (BitVec n)) (t : Nat)
    {rec : TranslateFn} {query : CompilerM HWType} {ce ae be : Lean.Expr}
    {hint w : String} {named : Bool} {ctx : CompilerState} {s s' : CircuitState}
    (we : WEnv) (mems : MEnv) (initial prior : Env)
    (good : CircuitState → Env → Prop)
    (hc : ChildSpec rec ctx we mems initial good ce "mux_cond" 1 (encodeBool (c.val t)))
    (ha : ChildSpec rec ctx we mems initial good ae "mux_then" n (a.val t).toNat)
    (hb : ChildSpec rec ctx we mems initial good be "mux_else" n (b.val t).toNat)
    (hq : ∀ sb sq ty, Returns query ctx sb ty sq → ty = .bitVector n ∧ sq = sb)
    (hbody : ∀ sb result, good sb result → TypedBody we sb)
    (hgood : good s prior) (hprefix : Runs we mems initial s prior)
    (hn : 0 < n) (hw : WidthsAgree we s')
    (hrun : Returns (translateMuxWith rec query ce ae be hint named) ctx s w s') :
    s.usedNames.contains w = false ∧ we w = n ∧ TypedBody we s' ∧
    s'.usedNames.contains w = true ∧
    (∀ x, s.usedNames.contains x = true → s'.usedNames.contains x = true) ∧
    ∃ result, Runs we mems initial s' result ∧
      result w = ((Signal.mux c a b).val t).toNat ∧
      (∀ x, s.usedNames.contains x = true → result x = prior x) := by
  obtain ⟨cw, aw, bw, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ :=
    translateMuxWith_returns hrun
  obtain ⟨hty, hsq⟩ := hq sb sq ty rq
  subst ty sq
  obtain ⟨vc, gc, ec, uc, wc, vcw, mc, fc⟩ := hc s sc cw prior hgood hprefix rc
  obtain ⟨va, ga, ea, ua, wa, vaw, ma, fa⟩ := ha sc sa aw vc gc ec ra
  obtain ⟨vb, gb, eb, ub, wb, vbw, mb, fb⟩ := hb sa sb bw va ga ea rb
  have vbc : vb cw = encodeBool (c.val t) := (fb cw (ma cw uc)).trans ((fa cw uc).trans vcw)
  have vba : vb aw = (a.val t).toNat := (fb aw ua).trans vaw
  -- Track all pre-existing reserved wires as bindings, including prior child
  -- results. This makes freshness protection independent of source variables.
  let lookup : String → Option String := fun x => if sb.usedNames.contains x then some x else none
  have bindings : BindingsAgree lookup vb vb := by
    intro x y hxy
    simp only [lookup] at hxy
    split at hxy
    · cases hxy; rfl
    · cases hxy
  have reserved : Reserved lookup sb.usedNames := by
    intro x y hxy
    simp only [lookup] at hxy
    split at hxy
    · next h => cases hxy; exact h
    · cases hxy
  obtain ⟨fresh, typed, ww, result, er, vr, frame, _, _⟩ :=
    emitMuxResult_correct c a b t re we mems initial vb lookup vb eb
      vbc vba vbw hn wc wa wb hw bindings reserved
  have mono : ∀ x, s.usedNames.contains x = true → sb.usedNames.contains x = true :=
    fun x hx => mb x (ma x (mc x hx))
  have fresh0 : s.usedNames.contains w = false := by
    cases hu : s.usedNames.contains w
    · rfl
    · have := mono w hu; simp [fresh] at this
  obtain ⟨hr, hs⟩ := emitMuxResult_returns re
  have used : s'.usedNames = sb.usedNames.insert w := by
    rw [hs, emitAssign_usedNames, (CircuitM.makeWire_spec hint (.bitVector n) named sb).2.1, ← hr]
  refine ⟨fresh0, ww, emitMuxResult_typedBody re hw typed (hbody sb vb gb),
    ?_, ?_, result, er, vr, ?_⟩
  · simp [used]
  · intro x hx
    simp [used, Std.HashSet.contains_insert, mono x hx]
  · intro x hx
    have xne : x ≠ w := by
      intro he; subst x; simp [fresh0] at hx
    exact (frame x xne).trans ((fb x (ma x (mc x hx))).trans
      ((fa x (mc x hx)).trans (fc x hx)))

end Tools.ShippingMuxRecursionSoundness
