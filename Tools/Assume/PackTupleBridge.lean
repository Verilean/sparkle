import Tools.ShippingGen5ReaderTrace
set_option autoImplicit false
-- NOT BUILT yet (registration of Tools.Assume.PackTupleBridge; build SHA is recorded in a later comment-only commit). Assumption module (statements only; no theorems).

/-! # Assumption: N2-b `PackTupleInputsBridge` (with the twin model `lamDepth` / `packTupleInputsF`)

**This file holds ONLY assumption statements** — `Prop` definitions that proofs take as hypotheses. They are not
`axiom`s and not theorems. A change here is a change of what is assumed and needs reviewer approval; proof files must
not redefine them.

Design: `scripts/gen5/RT_U2_FREEZE.md` §1 (reviewer-approved design, conditional). The statements are moved verbatim from
`Tools/ShippingGen5ReaderTraceDirect.lean` (same namespaces, names, types).

* What is assumed: on `NoPh ∧ BvarLt 0` input the production `packTupleInputs` (a `partial def`) equals the total model
  `packTupleInputsF (lamDepth e) e`. `lamDepth` / `packTupleInputsF` are the definitions needed to read the statement.
* Why not proved: the body of a `partial def` is opaque to the logic. This investigation found no route; not a claim that it is underivable.
* Ledger: FG +1 (see freeze §5; counted only when the U2 composition is accepted).
-/

namespace Tools.ShippingGen5ReaderTracePack
open Lean Sparkle.Compiler.MachTupleIn Tools.ShippingGen5ReaderTrace
def lamDepth : Lean.Expr → Nat
  | .lam _ _ b _ => lamDepth b + 1
  | _ => 0
def packTupleInputsF : Nat → Lean.Expr → Lean.Expr
  | k + 1, .lam nm ty b bi =>
    match tupleInput? ty with
    | some (dom, ws) =>
      let n := ws.foldl (· + ·) 0
      let ty' := mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom (mkApp (.const ``BitVec []) (natE n))
      let b' := (b.liftLooseBVars 1 1).instantiate1 (unpackE (dom.liftLooseBVars 0 1) ws (.bvar 0))
      .lam nm ty' (packTupleInputsF k b') bi
    | none => .lam nm ty (packTupleInputsF k b) bi
  | _, e => e
end Tools.ShippingGen5ReaderTracePack

namespace Tools.Assume.PackTupleBridge
open Lean Tools.ShippingGen5ReaderTrace
def PackTupleInputsBridge : Prop :=
  ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true →
    Sparkle.Compiler.MachTupleIn.packTupleInputs e = Tools.ShippingGen5ReaderTracePack.packTupleInputsF (Tools.ShippingGen5ReaderTracePack.lamDepth e) e
end Tools.Assume.PackTupleBridge
