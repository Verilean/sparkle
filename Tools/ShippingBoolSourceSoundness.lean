import Tools.ShippingMuxTypeSoundness

/-! Bool source meanings and the shipping validated cache. Comparison operands
use the existing BitVec source relation. This is the Bool component of the
front-end invariant, not a proof of all partial handlers or mixed-type source
induction. No lawfulness assumption about ExprStructMap is needed for hits. -/
namespace Tools.ShippingBoolSourceSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingTranslateSoundness Tools.ShippingMuxLoweringSoundness

abbrev BoolValuation := FVarId → Option Bool

def compareName : SignalCompareKind → Name
  | .ult => ``Signal.ult
  | .ule => ``Signal.ule
  | .slt => ``Signal.slt
  | .sle => ``Signal.sle
  | .eq => ``Signal.beq

/-- Equality has a type/instance argument telescope, unlike the four ordered
comparisons. Quote the actual standard BitVec BEq instance explicitly. -/
def compareE (kind : SignalCompareKind) (dom : Lean.Expr) (n : Nat) (a b : Lean.Expr) : Lean.Expr :=
  let w := Tools.ShippingEntrySoundness.natE n
  let ty := mkApp (.const ``BitVec []) w
  let head := match kind with
    | .eq => mkApp3 (.const ``Signal.beq []) ty dom
        (mkApp2 (.const ``instBEqOfDecidableEq [.zero]) ty (mkApp (.const ``instDecidableEqBitVec []) w))
    | _ => mkApp2 (.const (compareName kind) []) dom w
  mkApp2 head a b
def compareValue {n : Nat} : SignalCompareKind → BitVec n → BitVec n → Bool
  | .ult => BitVec.ult
  | .ule => BitVec.ule
  | .slt => BitVec.slt
  | .sle => BitVec.sle
  | .eq => fun a b => a == b
def boolName (b : Bool) : Name := if b then ``Bool.true else ``Bool.false

/-- Source semantics on the actual input Expr. Width-changing comparisons
produce Bool while their operands retain the existing BitVec interpretation. -/
inductive BoolDenotes (ρ : BoolValuation) (β : Valuation) : Lean.Expr → Bool → Prop
  | fvar {id : FVarId} {b : Bool} : ρ id = some b → BoolDenotes ρ β (.fvar id) b
  | pureLit {e : Lean.Expr} {us : List Level} {b : Bool} :
      e.getAppFn = .const ``Signal.pure us →
      e.getAppArgs.back? = some (.const (boolName b) []) → BoolDenotes ρ β e b
  | compare {e : Lean.Expr} {us : List Level} {n : Nat} {a b : BitVec n} (le : SignalCompareKind) :
      e.getAppFn = .const (compareName le) us →
      Denotes β e.getAppArgs[e.getAppArgs.size - 2]! n a →
      Denotes β e.getAppArgs[e.getAppArgs.size - 1]! n b →
      BoolDenotes ρ β e (compareValue le a b)
  | mux {e : Lean.Expr} {us : List Level} {c a b : Bool} :
      e.getAppFn = .const ``Signal.mux us →
      BoolDenotes ρ β e.getAppArgs[e.getAppArgs.size - 3]! c →
      BoolDenotes ρ β e.getAppArgs[e.getAppArgs.size - 2]! a →
      BoolDenotes ρ β e.getAppArgs[e.getAppArgs.size - 1]! b →
      BoolDenotes ρ β e (if c then a else b)

theorem library_bool_pure {dom : DomainConfig} (b : Bool) (t : Nat) :
    (Signal.pure b : Signal dom Bool).val t = b := rfl
theorem library_ult {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (Signal.ult a b).val t = compareValue false (a.val t) (b.val t) := rfl
theorem library_ule {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (Signal.ule a b).val t = compareValue true (a.val t) (b.val t) := rfl
theorem library_slt {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (Signal.slt a b).val t = compareValue .slt (a.val t) (b.val t) := rfl
theorem library_sle {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (Signal.sle a b).val t = compareValue .sle (a.val t) (b.val t) := rfl
theorem library_beq {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (Signal.beq a b).val t = compareValue .eq (a.val t) (b.val t) := rfl
theorem library_bool_mux {dom : DomainConfig} (c a b : Signal dom Bool) (t : Nat) :
    (Signal.mux c a b).val t = if c.val t then a.val t else b.val t := rfl

theorem compareName_inj {a b : SignalCompareKind} (h : compareName a = compareName b) : a = b := by
  cases a <;> cases b <;> simp_all [compareName]
theorem boolName_inj {a b : Bool} (h : boolName a = boolName b) : a = b := by
  cases a <;> cases b <;> simp_all [boolName]

/-- Recording a Bool expression has a unique value, including nested Bool muxes
and comparisons whose operands have any width admitted by `Denotes`. -/
theorem BoolDenotes.det {ρ β e a b} (h : BoolDenotes ρ β e a)
    (h' : BoolDenotes ρ β e b) : a = b := by
  induction h generalizing b with
  | fvar hv =>
    cases h' with
    | fvar hv' => rw [hv] at hv'; exact Option.some.inj hv'
    | pureLit hf _ | compare _ hf _ _ | mux hf _ _ _ =>
      simp [Lean.Expr.getAppFn] at hf
  | pureLit hf hv =>
    cases h' with
    | fvar _ => simp [Lean.Expr.getAppFn] at hf
    | pureLit hf' hv' =>
      rw [hv] at hv'
      exact boolName_inj (Lean.Expr.const.inj (Option.some.inj hv')).1
    | compare le hf' _ _ => cases le <;> simp_all [compareName]
    | mux hf' _ _ _ => simp_all
  | @compare e us n x y le hf hx hy =>
    cases h' with
    | fvar _ => simp [Lean.Expr.getAppFn] at hf
    | pureLit hf' _ => cases le <;> simp_all [compareName]
    | @compare _ us' n' x' y' le' hf' hx' hy' =>
      have he : le = le' := compareName_inj (Lean.Expr.const.inj (hf.symm.trans hf')).1
      subst le'
      obtain ⟨hn, hxn⟩ := Denotes.det hx hx'
      subst n'
      have hxx := BitVec.eq_of_toNat_eq hxn
      have hyy := BitVec.eq_of_toNat_eq (Denotes.det hy hy').2
      subst x' y'
      rfl
    | mux hf' _ _ _ => cases le <;> simp_all [compareName]
  | mux hf _ _ _ ihc iha ihb =>
    cases h' with
    | fvar _ => simp [Lean.Expr.getAppFn] at hf
    | pureLit hf' _ => simp_all
    | compare le hf' _ _ => cases le <;> simp_all [compareName]
    | mux _ hc ha hb => rw [ihc hc, iha ha, ihb hb]

open Tools.ShippingEntrySoundness Tools.ShippingMuxTypeSoundness

/-- Bool syntax with the existing arithmetic fragment as comparison operands. -/
inductive BExpr where
  | inp (j : Nat)
  | lit (b : Bool)
  | compare (le : SignalCompareKind) (a b : FExpr)
  | mux (c a b : BExpr)

def BExpr.WF (kb kv n : Nat) : BExpr → Prop
  | .inp j => j < kb
  | .lit _ => True
  | .compare _ a b => a.WF kv n ∧ b.WF kv n
  | .mux c a b => c.WF kb kv n ∧ a.WF kb kv n ∧ b.WF kb kv n

def evalB (n : Nat) (bools : Nat → Bool) (bits : Nat → BitVec n) : BExpr → Bool
  | .inp j => bools j
  | .lit b => b
  | .compare le a b => compareValue le (evalFE n bits a) (evalFE n bits b)
  | .mux c a b => if evalB n bools bits c then evalB n bools bits a else evalB n bools bits b

def denoteB {dom : DomainConfig} (n : Nat) (bools : Nat → Signal dom Bool)
    (bits : Nat → Signal dom (BitVec n)) : BExpr → Signal dom Bool
  | .inp j => bools j
  | .lit b => Signal.pure b
  | .compare le a b => match le with
      | .ult => Signal.ult (denoteFE n bits a) (denoteFE n bits b)
      | .ule => Signal.ule (denoteFE n bits a) (denoteFE n bits b)
      | .slt => Signal.slt (denoteFE n bits a) (denoteFE n bits b)
      | .sle => Signal.sle (denoteFE n bits a) (denoteFE n bits b)
      | .eq => Signal.beq (denoteFE n bits a) (denoteFE n bits b)
  | .mux c a b => Signal.mux (denoteB n bools bits c) (denoteB n bools bits a) (denoteB n bools bits b)

theorem denoteB_val {dom : DomainConfig} (n : Nat) (bools : Nat → Signal dom Bool)
    (bits : Nat → Signal dom (BitVec n)) (t : Nat) : ∀ e,
    (denoteB n bools bits e).val t = evalB n (fun j => (bools j).val t) (fun j => (bits j).val t) e
  | .inp _ => rfl
  | .lit _ => rfl
  | .compare le a b => by
      cases le <;> simp [denoteB, evalB, library_ult, library_ule, library_slt, library_sle, library_beq, denoteFE_val]
  | .mux c a b => by
      simp only [denoteB, evalB, library_bool_mux, denoteB_val n bools bits t c,
        denoteB_val n bools bits t a, denoteB_val n bools bits t b]

def quoteB (dom : Lean.Expr) (n : Nat) (bools bits : Nat → Lean.Expr) : BExpr → Lean.Expr
  | .inp j => bools j
  | .lit b => mkApp3 (.const ``Signal.pure [.zero]) dom (.const ``Bool []) (.const (boolName b) [])
  | .compare le a b => compareE le dom n
      (quoteF dom n bits a) (quoteF dom n bits b)
  | .mux c a b => muxE dom (.const ``Bool [])
      (quoteB dom n bools bits c) (quoteB dom n bools bits a) (quoteB dom n bools bits b)

theorem quotedBool_control (dom : Lean.Expr) (n : Nat) (bools bits : Nat → Lean.Expr)
    (e : BExpr) (he : ∀ j, e ≠ .inp j) : isBoolControl (quoteB dom n bools bits e) = true := by
  cases e with
  | inp j => exact False.elim (he j rfl)
  | lit b => rfl
  | compare le a b => cases le <;> rfl
  | mux c a b => rfl

/-- The real fallback routes these source expressions through the proved
wrapper, using the uncached partial handler only on a miss. -/
theorem translateFallback_bool (rec : TranslateFn) (e : Lean.Expr) (hint : String)
    (top named : Bool) (he : isBoolControl e = true) :
    translateFallback rec e hint top named = translateControlCachedWith
      (translateBoolUncachedWith rec
        (fun e h t n => Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e h t n))
      e hint top named := by simp [translateFallback, he]

/-- The old arithmetic quotation theorem without its uniform entry telescope,
so it can be used under mixed Bool/BitVec input binders. -/
theorem denotesF_inputs {β : Valuation} {dom : Lean.Expr} {n k : Nat}
    {inp : Nat → Lean.Expr} {vals : Nat → BitVec n}
    (hi : ∀ j, j < k → Denotes β (inp j) n (vals j)) :
    ∀ e, e.WF k n → Denotes β (quoteF dom n inp e) n (evalFE n vals e)
  | .inp j, hj => hi j hj
  | .lit v, hv => .pureLit (us := [.zero])
      (c := mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) rfl rfl (litValue_natE n v hv)
  | .bin op a b, ⟨ha, hb⟩ => by
      have ck := op_checks op dom (quoteF dom n inp a) (quoteF dom n inp b) n
      have da := denotesF_inputs (dom := dom) hi a ha
      have db := denotesF_inputs (dom := dom) hi b hb
      rw [← ck.2.2.2.2.1] at da
      rw [← ck.2.2.2.2.2.1] at db
      exact .binary (bop := op) ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 da db

theorem BoolDenotes.quotePure {ρ β} (dom : Lean.Expr) (b : Bool) :
    BoolDenotes ρ β (mkApp3 (.const ``Signal.pure [.zero]) dom (.const ``Bool [])
      (.const (boolName b) [])) b :=
  .pureLit (us := [.zero]) rfl rfl

theorem BoolDenotes.quoteCompare {ρ β n} (dom ae be : Lean.Expr) (le : SignalCompareKind)
    {a b : BitVec n} (ha : Denotes β ae n a) (hb : Denotes β be n b) :
    BoolDenotes ρ β (compareE le dom n ae be)
      (compareValue le a b) := by
  refine @BoolDenotes.compare ρ β (compareE le dom n ae be)
    [] n a b le (by cases le <;> rfl) ?_ ?_
  all_goals
    have args : (compareE le dom n ae be).getAppArgs =
        (match le with
        | .eq => #[mkApp (.const ``BitVec []) (natE n), dom,
            mkApp2 (.const ``instBEqOfDecidableEq [.zero]) (mkApp (.const ``BitVec []) (natE n))
              (mkApp (.const ``instDecidableEqBitVec []) (natE n)), ae, be]
        | _ => #[dom, natE n, ae, be]) := by cases le <;> rfl
    rw [args]
    cases le <;> assumption

theorem BoolDenotes.quoteMux {ρ β} (dom ce ae be : Lean.Expr)
    {c a b : Bool} (hc : BoolDenotes ρ β ce c) (ha : BoolDenotes ρ β ae a)
    (hb : BoolDenotes ρ β be b) :
    BoolDenotes ρ β (muxE dom (.const ``Bool []) ce ae be) (if c then a else b) := by
  have args : (muxE dom (.const ``Bool []) ce ae be).getAppArgs =
      #[dom, .const ``Bool [], ce, ae, be] := rfl
  refine @BoolDenotes.mux ρ β (muxE dom (.const ``Bool []) ce ae be) [.zero] c a b rfl ?_ ?_ ?_
  · rw [args]; exact hc
  · rw [args]; exact ha
  · rw [args]; exact hb

/-- Every well-formed quoted Bool term has the library meaning, recursively.
The two input premises can be instantiated from mixed source valuations. -/
theorem denotesB_quote {ρ : BoolValuation} {β : Valuation} {dom : Lean.Expr} {n kb kv : Nat}
    {binp vinp : Nat → Lean.Expr} {bools : Nat → Bool} {bits : Nat → BitVec n}
    (hb : ∀ j, j < kb → BoolDenotes ρ β (binp j) (bools j))
    (hv : ∀ j, j < kv → Denotes β (vinp j) n (bits j)) :
    ∀ e, e.WF kb kv n → BoolDenotes ρ β (quoteB dom n binp vinp e) (evalB n bools bits e)
  | .inp j, hj => hb j hj
  | .lit b, _ => BoolDenotes.quotePure dom b
  | .compare le a b, ⟨ha, hb'⟩ => BoolDenotes.quoteCompare dom _ _ le
      (denotesF_inputs (dom := dom) hv a ha) (denotesF_inputs (dom := dom) hv b hb')
  | .mux c a b, ⟨hc, ha, hb'⟩ =>
      BoolDenotes.quoteMux dom _ _ _ (denotesB_quote (dom := dom) hb hv c hc)
        (denotesB_quote (dom := dom) hb hv a ha) (denotesB_quote (dom := dom) hb hv b hb')

/-- Bool half of the translation-record invariant. It covers only expressions
with a Bool meaning; a joint Bool/BitVec invariant is still needed at entry. -/
def BoolRecordOk (ρ : BoolValuation) (β : Valuation) (we : WEnv)
    (s : CircuitState) (env : Env) : Prop :=
  ∀ w e, s.translateRecord.get? w = some e → ∀ b, BoolDenotes ρ β e b →
    s.usedNames.contains w = true ∧ env w = encodeBool b ∧ we w = 1

theorem BoolRecordOk.insert {ρ β we s env} (h : BoolRecordOk ρ β we s env)
    {e : Lean.Expr} {w : String} {b : Bool} (hd : BoolDenotes ρ β e b)
    (hu : s.usedNames.contains w = true) (hv : env w = encodeBool b) (hw : we w = 1) :
    BoolRecordOk ρ β we {s with translateRecord := s.translateRecord.insert w e} env := by
  intro w' e' he b' hd'
  simp only [Std.HashMap.get?_insert] at he
  split at he
  · next hww =>
      have : w = w' := by simpa using hww
      subst w'
      cases he
      rw [← hd.det hd']
      exact ⟨hu, hv, hw⟩
  · exact h w' e' he b' hd'

theorem BoolRecordOk.transfer {ρ β we s s' env env'} (h : BoolRecordOk ρ β we s env)
    (hr : s'.translateRecord = s.translateRecord)
    (hu : ∀ w, s.usedNames.contains w = true → s'.usedNames.contains w = true)
    (hv : ∀ w, s.usedNames.contains w = true → env' w = env w) :
    BoolRecordOk ρ β we s' env' := by
  intro w e he b hd
  rw [hr] at he
  obtain ⟨used, value, width⟩ := h w e he b hd
  exact ⟨hu w used, (hv w used).trans value, width⟩

/-- The real record-writing action maintains the Bool invariant, whether or
not the mutable cache is enabled. -/
theorem recordTranslation_bool {ρ β we s s' env ctx e w b cacheable u}
    (h : BoolRecordOk ρ β we s env) (hd : BoolDenotes ρ β e b)
    (hu : s.usedNames.contains w = true) (hv : env w = encodeBool b) (hw : we w = 1)
    (hr : Returns (recordTranslation e w cacheable) ctx s u s') :
    BoolRecordOk ρ β we s' env := by
  rw [recordTranslation_returns hr]
  exact h.insert hd hu hv hw

/-- A real validated cache hit returns the source Bool value at width one.
The raw mutable cache may be arbitrary: the proved structural validator and
the circuit's translation record suffice. -/
theorem validatedBoolHit_correct {ρ β we s s' env ctx e w b}
    (h : BoolRecordOk ρ β we s env) (hd : BoolDenotes ρ β e b)
    (hr : Returns (cacheLookupValidated e) ctx s (some w) s') :
    s' = s ∧ s.usedNames.contains w = true ∧ env w = encodeBool b ∧ we w = 1 := by
  obtain ⟨hs, he⟩ := cacheLookupValidated_returns hr
  exact ⟨hs, h w e (he w rfl) b hd⟩

/-- A cached quoted Bool expression carries the actual library value at any
source observation time, rather than an unrelated abstract Boolean function. -/
theorem validatedQuotedBoolHit {ρ β we s s' env ctx domE n kb kv binp vinp e w}
    {dom : DomainConfig} (bools : Nat → Signal dom Bool)
    (bits : Nat → Signal dom (BitVec n)) (t : Nat)
    (hb : ∀ j, j < kb → BoolDenotes ρ β (binp j) ((bools j).val t))
    (hv : ∀ j, j < kv → Denotes β (vinp j) n ((bits j).val t))
    (he : e.WF kb kv n) (h : BoolRecordOk ρ β we s env)
    (hr : Returns (cacheLookupValidated (quoteB domE n binp vinp e)) ctx s (some w) s') :
    s' = s ∧ s.usedNames.contains w = true ∧
      env w = encodeBool ((denoteB n bools bits e).val t) ∧ we w = 1 := by
  rw [denoteB_val]
  exact validatedBoolHit_correct h (denotesB_quote hb hv e he) hr

/-- Exact alternatives of the wrapper used by the shipping Bool fallback. -/
theorem translateControlCachedWith_returns {lower : TranslateFn}
    {e : Lean.Expr} {hint w : String} {top named : Bool} {ctx : CompilerState}
    {s s' : CircuitState}
    (h : Returns (translateControlCachedWith lower e hint top named) ctx s w s') :
    Returns (cacheLookupValidated e) ctx s (some w) s' ∨
      ∃ sm, Returns (lower e hint top named) ctx s w sm ∧
        Returns (recordTranslation e w (!named && !e.isFVar && !top)) ctx sm () s' := by
  unfold translateControlCachedWith at h
  dsimp only at h
  split at h
  · obtain ⟨hit, sh, hc, h⟩ := Returns.bind h
    have hs := (cacheLookupValidated_returns hc).1
    subst sh
    split at h
    · obtain ⟨hw, hs⟩ := Returns.pure h
      subst w s'
      exact Or.inl hc
    · obtain ⟨r, sm, hl, h⟩ := Returns.bind h
      obtain ⟨u, sr, hr, h⟩ := Returns.bind h
      obtain ⟨hw, hs⟩ := Returns.pure h
      subst w s'
      cases u
      exact Or.inr ⟨sm, hl, hr⟩
  · obtain ⟨r, sm, hl, h⟩ := Returns.bind h
    obtain ⟨u, sr, hr, h⟩ := Returns.bind h
    obtain ⟨hw, hs⟩ := Returns.pure h
    subst w s'
    cases u
    exact Or.inr ⟨sm, hl, hr⟩

/-- The wrapper is sound if a cache miss's uncached translation is sound. The
hit branch requires no property of the mutable cache's contents or key hashes.
The miss hypothesis is the remaining recursive translation obligation. -/
theorem translateControlCachedWith_correct {ρ β we s s' env ctx e w b lower hint top named}
    (mems : MEnv) (initial : Env) (hprefix : Runs we mems initial s env)
    (h : BoolRecordOk ρ β we s env) (hd : BoolDenotes ρ β e b)
    (hl : ∀ sm r, Returns (lower e hint top named) ctx s r sm →
      ∃ result, Runs we mems initial sm result ∧ BoolRecordOk ρ β we sm result ∧ sm.usedNames.contains r = true ∧
        result r = encodeBool b ∧ we r = 1)
    (hr : Returns (translateControlCachedWith lower e hint top named) ctx s w s') :
    ∃ result, Runs we mems initial s' result ∧ BoolRecordOk ρ β we s' result ∧ s'.usedNames.contains w = true ∧
      result w = encodeBool b ∧ we w = 1 := by
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · obtain ⟨hs, hu, hv, hw⟩ := validatedBoolHit_correct h hd hit
    subst s'
    exact ⟨env, hprefix, h, hu, hv, hw⟩
  · obtain ⟨result, hrun, hok, hu, hv, hw⟩ := hl sm w miss
    refine ⟨result, ?_, recordTranslation_bool hok hd hu hv hw record, ?_, hv, hw⟩
    · rw [recordTranslation_returns record]
      exact hrun
    · rw [recordTranslation_returns record]
      exact hu

end Tools.ShippingBoolSourceSoundness
