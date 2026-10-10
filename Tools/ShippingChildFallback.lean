import Tools.ShippingChildTranslate

/-! # The fallback's arms keep the child invariant

`translateFallback rec` dispatches on `fallbackKind`: fourteen certified arms
(ordinary definitions) and, for everything else, the instance arm
`translateInstanceOrFallback`, which either lowers a `@[hardware_module]` call
— synthesising the child through `childSynthEntry` — or hands over to the
legacy translator (`Rec.translateExprToWireCached` / `Rec.translateExprToWireImpl`).

Every arm is walked here (`vc`), on every outcome, given that the recursive
translator `rec`, the memoised child entry and the two legacy entry points
keep the invariant. So `FallbackRel` — and with it `TranslateRel` — follows
from the same statement about the legacy translator alone (`LegacyRel`). -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
variable (L : RefLaws mref cref) (D : Nat)

/-- **A child's synthesis from inside the translator** keeps the invariant,
given the memoised child entry does: the synthesis ref's read returns
`synthesizeChild` in an invariant world. -/
@[keeps] theorem childSynthEntry_keeps (hC : ChildKeeps L D) (c : Name) :
    Keeps mctx mref cctx cref (J L D) (childSynthEntry c) := by
  rw [keeps_iff]
  unfold childSynthEntry
  refine Triple.bindQ (Triple.synthRead L D) ?_
  intro s hs
  subst hs
  exact keeps_iff.mp (hC mctx cctx c)

/-! ## The certified arms -/

section Arms
variable (rec : TranslateFn)
  (hrec : ∀ e hint top named, KeepsC mctx mref cctx cref (J L D) (rec e hint top named))
include hrec

@[keeps] theorem translateBoolUncachedWith_keepsC (legacy : TranslateFn)
    (hleg : ∀ e hint top named, KeepsC mctx mref cctx cref (J L D) (legacy e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateBoolUncachedWith rec legacy e hint top named) := by
  vc

@[keeps] theorem translateVectorMuxUncachedWith_keepsC (n : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateVectorMuxUncachedWith rec n e hint top named) := by
  vc

@[keeps] theorem translateSetWidthUncachedWith_keepsC (ws wt : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateSetWidthUncachedWith rec ws wt e hint top named) := by
  vc

@[keeps] theorem translateRegisterUncachedWith_keepsC (w v : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateRegisterUncachedWith rec w v e hint top named) := by
  vc

@[keeps] theorem translateRegisterEnableUncachedWith_keepsC (w v : Nat) (e : Lean.Expr)
    (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D)
      (translateRegisterEnableUncachedWith rec w v e hint top named) := by
  vc

@[keeps] theorem translateLoopRegisterUncachedWith_keepsC (w v : Nat) (e : Lean.Expr)
    (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D)
      (translateLoopRegisterUncachedWith rec w v e hint top named) := by
  vc

@[keeps] theorem translateCircuitDoUncachedWith_keepsC (w v : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateCircuitDoUncachedWith rec w v e hint top named) := by
  vc

@[keeps] theorem translateCircuitDo2UncachedWith_keepsC (w v0 v1 ret : Nat) (e : Lean.Expr)
    (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D)
      (translateCircuitDo2UncachedWith rec w v0 v1 ret e hint top named) := by
  vc

@[keeps] theorem translateMemoryUncachedWith_keepsC (aw dw : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateMemoryUncachedWith rec aw dw e hint top named) := by
  vc

@[keeps] theorem translateSliceUncachedWith_keepsC (start len : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateSliceUncachedWith rec start len e hint top named) := by
  vc

@[keeps] theorem translateConcatUncachedWith_keepsC (m n : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateConcatUncachedWith rec m n e hint top named) := by
  vc

@[keeps] theorem translateConcatLitUncachedWith_keepsC (hi : Bool) (k v w : Nat) (e : Lean.Expr)
    (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D)
      (translateConcatLitUncachedWith rec hi k v w e hint top named) := by
  vc

@[keeps] theorem translateSliceFUncachedWith_keepsC (start len : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateSliceFUncachedWith rec start len e hint top named) := by
  vc

/-- The instance arms' argument walk: one recursive translation per operand. -/
@[keeps] theorem instArgs_keepsC :
    ∀ (rest : List (Sparkle.IR.AST.Port × Lean.Expr)) (acc : List (String × Sparkle.IR.AST.Expr))
      (i : Nat), KeepsC mctx mref cctx cref (J L D) (instArgs rec acc rest i)
  | [], acc, i => by unfold instArgs; vc
  | (p, a) :: rest, acc, i => by
    have ih := fun acc i => instArgs_keepsC rest acc i
    unfold instArgs
    vc

end Arms

/-- The shared validated-cache wrapper around an arm. -/
@[keeps] theorem translateControlCachedWith_keepsC (lower : TranslateFn)
    (hlow : ∀ e hint top named, KeepsC mctx mref cctx cref (J L D) (lower e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateControlCachedWith lower e hint top named) := by
  vc

@[keeps] theorem instAddModules_keepsC (existing : List String) :
    ∀ ms : List Sparkle.IR.AST.Module,
      KeepsC mctx mref cctx cref (J L D) (instAddModules existing ms)
  | [] => by unfold instAddModules; vc
  | m :: ms => by
    have ih := instAddModules_keepsC existing ms
    unfold instAddModules
    vc

@[keeps] theorem instClkRst_keepsC :
    ∀ (ps : List Sparkle.IR.AST.Port) (acc : List (String × Sparkle.IR.AST.Expr)),
      KeepsC mctx mref cctx cref (J L D) (instClkRst acc ps)
  | [], acc => by unfold instClkRst; vc
  | p :: ps, acc => by
    have ih := fun acc => instClkRst_keepsC ps acc
    unfold instClkRst
    vc

/-- One wire per output port of a multi-output child, recorded in the port map. -/
@[keeps] theorem instOutWires_keepsC (callKey : UInt64) (hint : String) :
    ∀ (ps : List Sparkle.IR.AST.Port) (conns : List (String × Sparkle.IR.AST.Expr))
      (ws : List (String × String)),
      KeepsC mctx mref cctx cref (J L D) (instOutWires callKey hint ps conns ws)
  | [], conns, ws => by unfold instOutWires; vc
  | outP :: rest, conns, ws => by
    have ih := fun conns ws => instOutWires_keepsC callKey hint rest conns ws
    unfold instOutWires
    vc

/-! ## The instance arm and the dispatch -/

section Dispatch
variable (rec : TranslateFn)
  (hrec : ∀ e hint top named, KeepsC mctx mref cctx cref (J L D) (rec e hint top named))
  (hC : ChildKeeps L D)
  (hlegC : ∀ e hint top named, KeepsC mctx mref cctx cref (J L D)
    (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named))
  (hlegI : ∀ e hint top named, KeepsC mctx mref cctx cref (J L D)
    (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named))
  (hkey : ∀ e, KeepsC mctx mref cctx cref (J L D) (canonHardwareKey e))
include hrec hC hlegC hkey

/-- **The instance arm**: the environment read, the child's synthesis
(`childSynthEntry`), the single-output and the projection lowerings under the
validated cache wrapper, or the legacy translator. -/
@[keeps] theorem translateInstanceOrFallback_keepsC (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateInstanceOrFallback rec e hint top named) := by
  vc

include hlegI

/-- **The fallback**: one arm per `fallbackKind`. -/
theorem translateFallback_keepsC (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateFallback rec e hint top named) := by
  vc

end Dispatch

/-- **`FallbackRel` from `LegacyRel`.** -/
theorem fallbackRel_of_legacy (hLg : LegacyRel L) : FallbackRel L := by
  intro D hC mctx cctx rec hrec e hint top named
  obtain ⟨h1, h2, h3⟩ := hLg D hC mctx cctx rec hrec
  exact translateFallback_keepsC L D rec hrec hC h1 h2 h3 e hint top named

/-- **`TranslateRel` from `LegacyRel`**: the fuel induction, the step's own
code and every ordinary arm are proved; what is left is the legacy translator. -/
theorem translateRel_of_legacy (hLg : LegacyRel L) : TranslateRel L :=
  translateRel_of_fallback L (fallbackRel_of_legacy L hLg)

end Tools.ShippingChildInv
