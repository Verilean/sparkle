import Tools.ShippingMuxRecursionSoundness

/-! Eliminate the result-type oracle from canonical library mux applications.
The syntax below is checked against elaborated library applications in the
regression tests. Recursive child contracts and the source/cache invariant
remain separate obligations; this does not prove the partial name dispatcher. -/
namespace Tools.ShippingMuxTypeSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Sparkle.IR.Semantics Sparkle.IR.Type Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingTranslateSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingMuxRecursionSoundness

/-- The actual library application with its domain and result-type arguments. -/
def muxE (dom ty c a b : Lean.Expr) : Lean.Expr :=
  mkApp5 (.const ``Signal.mux [.zero]) dom ty c a b

def bitVecE (n : Nat) : Lean.Expr := mkApp (.const ``BitVec []) (natE n)

theorem library_nat_literal (n : Nat) :
    @OfNat.ofNat Nat n (instOfNatNat n) = n := rfl

theorem canonicalNatLitValue?_natE (n : Nat) : canonicalNatLitValue? (natE n) = some n := by
  change (if n == n then some n else none) = some n
  simp

theorem canonicalMuxType?_bitVec (dom c a b : Lean.Expr) (n : Nat) :
    canonicalMuxType? (muxE dom (bitVecE n) c a b) = some (.bitVector n) := by
  change (canonicalNatLitValue? (natE n)).map HWType.bitVector = some (.bitVector n)
  rw [canonicalNatLitValue?_natE]
  rfl

theorem canonicalMuxType?_bool (dom c a b : Lean.Expr) :
    canonicalMuxType? (muxE dom (.const ``Bool []) c a b) = some .bit := rfl

/-- The selected type and absence of circuit-state effects follow from the
shipping action itself, for every compiler context and successful run. -/
theorem muxResultType_returns {e : Lean.Expr} {ty result : HWType}
    {ctx : CompilerState} {s s' : CircuitState}
    (he : canonicalMuxType? e = some ty)
    (hr : Returns (muxResultType e) ctx s result s') : result = ty ∧ s' = s := by
  simp only [muxResultType, he] at hr
  exact Returns.pure hr

/-- The recursive mux theorem without a type-inference hypothesis: the
literal-width type argument in the source expression determines the width.
Child simulations and final declaration agreement remain explicit. -/
theorem translateQuotedMux_correct {dom : DomainConfig} {n : Nat}
    (c : Signal dom Bool) (a b : Signal dom (BitVec n)) (t : Nat)
    {rec : TranslateFn} {domE ce ae be : Lean.Expr}
    {hint w : String} {named : Bool} {ctx : CompilerState} {s s' : CircuitState}
    (we : WEnv) (mems : MEnv) (initial prior : Env)
    (good : CircuitState → Env → Prop)
    (hc : ChildSpec rec ctx we mems initial good ce "mux_cond" 1 (encodeBool (c.val t)))
    (ha : ChildSpec rec ctx we mems initial good ae "mux_then" n (a.val t).toNat)
    (hb : ChildSpec rec ctx we mems initial good be "mux_else" n (b.val t).toNat)
    (hbody : ∀ sb result, good sb result → TypedBody we sb)
    (hgood : good s prior) (hprefix : Runs we mems initial s prior)
    (hn : 0 < n) (hw : WidthsAgree we s')
    (hrun : Returns (translateMuxWith rec
      (muxResultType (muxE domE (bitVecE n) ce ae be)) ce ae be hint named) ctx s w s') :
    s.usedNames.contains w = false ∧ we w = n ∧ TypedBody we s' ∧
    s'.usedNames.contains w = true ∧
    (∀ x, s.usedNames.contains x = true → s'.usedNames.contains x = true) ∧
    ∃ result, Runs we mems initial s' result ∧
      result w = ((Signal.mux c a b).val t).toNat ∧
      (∀ x, s.usedNames.contains x = true → result x = prior x) := by
  exact translateMuxWith_correct c a b t we mems initial prior good hc ha hb
    (fun _ _ _ hr => muxResultType_returns (canonicalMuxType?_bitVec domE ce ae be n) hr)
    hbody hgood hprefix hn hw hrun

end Tools.ShippingMuxTypeSoundness
