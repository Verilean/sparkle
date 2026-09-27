import Tools.ShippingBoolSourceSoundness

/-! Shipping unsigned/signed comparison lowering. The comparison node itself is
proved, including allocation, typing, execution and Bool-record preservation.
Recursive operand contracts and the joint entry invariant remain explicit. -/
namespace Tools.ShippingCompareLoweringSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Type
open Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingBuilderSoundness Tools.ShippingScalarSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMuxRecursionSoundness Tools.ShippingEntrySoundness

/-- Unlike the old BitVec-only width agreement, this includes scalar Bool wires. -/
def ScalarWidthsAgree (we : WEnv) (s : CircuitState) : Prop :=
  ∀ p ∈ s.module.wires, we p.name = p.ty.bitWidth

/-- The IR signed interpretation agrees with the source bit vector, including
width one. Width agreement is essential: the sign bit is width dependent. -/
theorem signed_toInt {n : Nat} (x : BitVec n) : toSigned n x.toNat = x.toInt := by
  unfold toSigned
  rw [BitVec.toInt_eq_toNat_cond]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    have hx : x.toNat = 0 := by have := x.isLt; omega
    simp [hx]
  · have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
      have hp := Nat.pow_succ 2 (n - 1)
      rwa [show (n - 1).succ = n from Nat.succ_pred_eq_of_pos h] at hp
    have hx := x.isLt
    split <;> split <;> omega

theorem typed_compare_refs (op : SignalCompareKind) {we : WEnv} {a b : String} {n : Nat}
    (hn : 0 < n) (wa : we a = n) (wb : we b = n) :
    TypedExpr we (.op (signalCompareOp op) [.ref a, .ref b]) 1 := by
  exact TypedExpr.compareRefs (by cases op <;> rfl) hn wa wb

theorem compare_rhs_correct {n : Nat} (le : SignalCompareKind) (x y : BitVec n)
    (we : WEnv) (env : Env) (a b : String)
    (ha : env a = x.toNat) (hb : env b = y.toNat)
    (wa : we a = n) (wb : we b = n) :
    evalExpr we env (.op (signalCompareOp le) [.ref a, .ref b]) =
      some (encodeBool (compareValue le x y)) := by
  cases le <;> simp [signalCompareOp, compareValue, evalExpr, evalList, evalOp,
    ha, hb, wa, wb, widthOf, signed_toInt, encodeBool, BitVec.ult_eq_decide, BitVec.ule_eq_decide,
    BitVec.slt, BitVec.sle]

theorem emitBoolResult_returns {rhs : Sparkle.IR.AST.Expr} {hint w : String} {named : Bool}
    {ctx : CompilerState} {s s' : CircuitState}
    (h : Returns (emitBoolResult rhs hint named) ctx s w s') :
    w = (CircuitM.makeWire hint .bit named s).1 ∧
    s' = (CircuitM.emitAssign w rhs
      (CircuitM.makeWire hint .bit named s).2).2 := by
  unfold emitBoolResult at h
  obtain ⟨r, sm, hm, h⟩ := Returns.bind h
  obtain ⟨hr, hs⟩ := makeWire_returns hm
  obtain ⟨u, se, he, h⟩ := Returns.bind h
  obtain ⟨hw, hs'⟩ := Returns.pure h
  have hem := emitAssign_returns he
  subst w s'
  exact ⟨hr, by rw [hem, hs]⟩

theorem emitCompareResult_returns {le : SignalCompareKind} {a b hint w : String} {named : Bool}
    {ctx : CompilerState} {s s' : CircuitState}
    (h : Returns (emitCompareResult le a b hint named) ctx s w s') :
    w = (CircuitM.makeWire hint .bit named s).1 ∧
    s' = (CircuitM.emitAssign w (.op (signalCompareOp le) [.ref a, .ref b])
      (CircuitM.makeWire hint .bit named s).2).2 := emitBoolResult_returns h

/-- Facts needed by parent control nodes and by the validated cache wrapper. -/
structure BoolStep (ρ : BoolValuation) (β : Valuation) (we : WEnv) (mems : MEnv)
    (initial prior : Env) (s s' : CircuitState) (w : String) (value : Bool) : Prop where
  fresh : s.usedNames.contains w = false
  width : we w = 1
  typed : TypedBody we s'
  used : s'.usedNames.contains w = true
  grows : ∀ x, s.usedNames.contains x = true → s'.usedNames.contains x = true
  execution : ∃ result, Runs we mems initial s' result ∧ BoolRecordOk ρ β we s' result ∧
    result w = encodeBool value ∧
    (∀ x, s.usedNames.contains x = true → result x = prior x)

theorem emitBoolResult_correct {ρ β we mems initial prior s s' ctx}
    {rhs : Sparkle.IR.AST.Expr} {hint w : String} {named value : Bool}
    (hr : Returns (emitBoolResult rhs hint named) ctx s w s')
    (hp : Runs we mems initial s prior) (hrec : BoolRecordOk ρ β we s prior)
    (hbody : TypedBody we s) (typed : TypedExpr we rhs 1)
    (heval : evalExpr we prior rhs = some (encodeBool value))
    (hwidth : ScalarWidthsAgree we s') :
    BoolStep ρ β we mems initial prior s s' w value := by
  obtain ⟨hrw, hs⟩ := emitBoolResult_returns hr
  have hm := CircuitM.makeWire_spec hint .bit named s
  have fresh : s.usedNames.contains w = false := by rw [hrw]; exact hm.1
  have used : s'.usedNames = s.usedNames.insert w := by
    rw [hs, emitAssign_usedNames, hm.2.1, ← hrw]
  have decl : ({name := w, ty := .bit} : Port) ∈ s'.module.wires := by
    rw [hs, emitAssign_wires, hm.2.2.2, hrw]; simp
  have ww : we w = 1 := hwidth _ decl
  have grows : ∀ z, s.usedNames.contains z = true → s'.usedNames.contains z = true := by
    intro z hz; simp [used, Std.HashSet.contains_insert, hz]
  let result := write prior w (encodeBool value)
  have frame : ∀ z, s.usedNames.contains z = true → result z = prior z := by
    intro z hz
    have hne : z ≠ w := by intro he; subst z; simp [fresh] at hz
    simp [result, write, hne]
  refine ⟨fresh, ww, ?_, by simp [used], grows, result, ?_, ?_, ?_, frame⟩
  · unfold TypedBody
    rw [hs, emitAssign_body_cons, hm.2.2.1]
    intro st hst
    rcases List.mem_cons.mp hst with hst | hst
    · subst st; exact ⟨w, _, rfl, ww.symm ▸ typed⟩
    · exact hbody st hst
  · rw [hs]
    exact emitAssign_sound _ we mems initial prior w _ _ (runs_of_body_eq hm.2.2.1 hp)
      heval
  · apply hrec.transfer ?_ grows frame
    rw [hs, emitAssign_translateRecord, CircuitM.makeWire_translateRecord]
  · simp [result, write]

theorem emitCompareResult_correct {ρ β we mems initial prior s s' ctx}
    {a b hint w : String} {named : Bool} {le : SignalCompareKind} {n : Nat} (x y : BitVec n)
    (hr : Returns (emitCompareResult le a b hint named) ctx s w s')
    (hp : Runs we mems initial s prior) (hrec : BoolRecordOk ρ β we s prior)
    (hbody : TypedBody we s) (hn : 0 < n)
    (ha : prior a = x.toNat) (hb : prior b = y.toNat)
    (wa : we a = n) (wb : we b = n) (hwidth : ScalarWidthsAgree we s') :
    BoolStep ρ β we mems initial prior s s' w (compareValue le x y) :=
  emitBoolResult_correct hr hp hrec hbody
    (typed_compare_refs le hn wa wb)
    (compare_rhs_correct le x y we prior a b ha hb wa wb) hwidth

/-- Both recursive operand calls are visible in the successful run. -/
theorem translateSignalCompare_returns {rec : TranslateFn} {le : SignalCompareKind} {a b : Lean.Expr}
    {hint w : String} {named : Bool} {ctx : CompilerState} {s s' : CircuitState}
    (h : Returns (translateSignalCompare rec le a b hint named) ctx s w s') :
    ∃ aw bw sa sb, Returns (rec a "a" false false) ctx s aw sa ∧
      Returns (rec b "b" false false) ctx sa bw sb ∧
      Returns (emitCompareResult le aw bw hint named) ctx sb w s' := by
  unfold translateSignalCompare at h
  obtain ⟨aw, sa, ha, h⟩ := Returns.bind h
  obtain ⟨bw, sb, hb, he⟩ := Returns.bind h
  exact ⟨aw, bw, sa, sb, ha, hb, he⟩

/-- Complete simulation of a comparison node, given recursive child contracts.
No result-type query or uncached comparison-handler correctness is assumed. -/
theorem translateSignalCompare_correct {ρ β we mems initial prior s s' ctx}
    {rec : TranslateFn} {ae be : Lean.Expr} {hint w : String} {named : Bool} {le : SignalCompareKind} {n : Nat}
    (x y : BitVec n) (good : CircuitState → Env → Prop)
    (ha : ChildSpec rec ctx we mems initial good ae "a" n x.toNat)
    (hb : ChildSpec rec ctx we mems initial good be "b" n y.toNat)
    (hg : good s prior) (hp : Runs we mems initial s prior) (hn : 0 < n)
    (ht : ∀ st env, good st env → TypedBody we st)
    (hc : ∀ st env, good st env → BoolRecordOk ρ β we st env)
    (hw : ScalarWidthsAgree we s')
    (hr : Returns (translateSignalCompare rec le ae be hint named) ctx s w s') :
    BoolStep ρ β we mems initial prior s s' w (compareValue le x y) := by
  obtain ⟨aw, bw, sa, sb, ra, rb, re⟩ := translateSignalCompare_returns hr
  obtain ⟨va, ga, ea, ua, wa, xa, ma, fa⟩ := ha s sa aw prior hg hp ra
  obtain ⟨vb, gb, eb, ub, wb, yb, mb, fb⟩ := hb sa sb bw va ga ea rb
  have xb : vb aw = x.toNat := (fb aw ua).trans xa
  have step := emitCompareResult_correct x y re eb (hc sb vb gb) (ht sb vb gb) hn xb yb wa wb hw
  have mono : ∀ z, s.usedNames.contains z = true → sb.usedNames.contains z = true :=
    fun z hz => mb z (ma z hz)
  have fresh : s.usedNames.contains w = false := by
    cases hu : s.usedNames.contains w
    · rfl
    · have := mono w hu; simp [step.fresh] at this
  obtain ⟨result, er, cr, vr, fr⟩ := step.execution
  exact ⟨fresh, step.width, step.typed, step.used,
    fun z hz => step.grows z (mono z hz), result, er, cr, vr,
    fun z hz => (fr z (mono z hz)).trans ((fb z (ma z hz)).trans (fa z hz))⟩

/-- The canonical source quotation selects this exact lowering, independent
of the legacy handler supplied by the shipping fallback. -/
theorem translateBoolUncachedWith_compare (rec legacy : TranslateFn) (dom ae be : Lean.Expr)
    (n : Nat) (le : SignalCompareKind) (hint : String) (top named : Bool) :
    translateBoolUncachedWith rec legacy
      (mkApp4 (.const (compareName le) []) dom (natE n) ae be) hint top named =
      translateSignalCompare rec le ae be hint named := by cases le <;> rfl

/-- Shipping comparison fallback, through BOTH validated cache branches.
The only translation assumptions are about the two children; the comparison
handler and its record insertion are discharged by the preceding theorems. -/
theorem translateFallback_compare_correct {ρ β we mems initial prior s s' ctx}
    {rec : TranslateFn} {dom ae be : Lean.Expr} {hint w : String} {top named : Bool} {le : SignalCompareKind} {n : Nat}
    (x y : BitVec n) (good : CircuitState → Env → Prop)
    (da : Denotes β ae n x) (db : Denotes β be n y)
    (ha : ChildSpec rec ctx we mems initial good ae "a" n x.toNat)
    (hb : ChildSpec rec ctx we mems initial good be "b" n y.toNat)
    (hg : good s prior) (hp : Runs we mems initial s prior) (hn : 0 < n)
    (ht : ∀ st env, good st env → TypedBody we st)
    (hc : ∀ st env, good st env → BoolRecordOk ρ β we st env)
    (hw : ScalarWidthsAgree we s')
    (hr : Returns (translateFallback rec
      (mkApp4 (.const (compareName le) []) dom (natE n) ae be) hint top named) ctx s w s') :
    ∃ result, Runs we mems initial s' result ∧ BoolRecordOk ρ β we s' result ∧
      s'.usedNames.contains w = true ∧ we w = 1 ∧
      result w = encodeBool (compareValue le x y) := by
  have hd := BoolDenotes.quoteCompare (ρ := ρ) dom ae be le da db
  rw [translateFallback_bool rec _ hint top named (by cases le <;> rfl)] at hr
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · obtain ⟨hs, hu, hv, hw'⟩ := validatedBoolHit_correct (hc s prior hg) hd hit
    subst s'
    exact ⟨prior, hp, hc s prior hg, hu, hw', hv⟩
  · rw [translateBoolUncachedWith_compare] at miss
    have hs := recordTranslation_returns record
    have wm : ScalarWidthsAgree we sm := by
      intro p hp
      apply hw p
      rw [hs]
      exact hp
    have step := translateSignalCompare_correct x y good ha hb hg hp hn ht hc wm miss
    obtain ⟨result, er, cr, vr, fr⟩ := step.execution
    refine ⟨result, ?_, recordTranslation_bool cr hd step.used vr step.width record,
      ?_, step.width, vr⟩
    · rw [hs]; exact er
    · rw [hs]; exact step.used

end Tools.ShippingCompareLoweringSoundness
