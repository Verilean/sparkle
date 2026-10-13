import Tools.ShippingLegacySemChain
import Tools.ShippingLegacySemWalk4
import Tools.ShippingLegacySemUnfoldWalk

variable {tenv : Lean.Environment}

/-! # The body stage of a plain call, assembled

`bodyOutcome_plain`: for an application whose head is the constant `name`,
with

* `PlainHead name` — not tagged, not a structure projection, in the
  environment the run reads;
* `GlueName name`, `PlainName name`, `NotBitVecOp name`, `PlainName2 name` —
  `name` fails every name test of `Rec.translateExprToWireApp`'s inline guards
  and of the nine handlers before `Rec.handleDefinitionUnfold` (decidable
  facts of the name, apart from the `toString` suffix tests, which are stated
  as they are computed);

a successful run of the legacy body `Rec.translateExprToWireImpl` on the
expression has an `UnfoldOutcome` — the inline attempt's wire, or the
sub-module path after an attempt that returned none — GIVEN `hpre`: the
body's run on `e` is a run of `Rec.translateExprToWireApp` on `e`.

`hpre` is the one program of the body stage not walked: the body's prefix
(trace, call counter, limit, profile tick), its inline arms on the head's
name, and the `hasMappedFvar` / `whnf` step.

Nothing here is new mathematics: the file only puts the walks together. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- **The body stage of a plain call**, from the body's prefix alone. -/
theorem bodyOutcome_plain {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {name : Name} {us : List Level} (hfn : e.getAppFn = .const name us)
    (hplain : PlainHead tenv name) (g : GlueName name) (hn : PlainName name)
    (hb : NotBitVecOp name) (hm : PlainName2 name)
    (hpre : ∀ (hint : String) (top named : Bool) (s t : CircuitState) (w : String),
      Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)
        ctx s w t →
      Returns (Rec.translateExprToWireApp (fun e h t n => rec e h t n) e hint named) ctx s w t) :
    BodyOutcome rec ctx e :=
  bodyOutcome_of_pre hfn g (plainChain_of_names hn hb hm) (unfoldSpec_plain hplain) hpre

end Tools.ShippingLegacySem
