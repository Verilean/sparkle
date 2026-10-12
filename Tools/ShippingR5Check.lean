import Tools.ShippingShapeDecomp
import Tools.ShippingMachineAuto

/-! # R5 as a per-declaration data condition (NOT a general theorem)

R5 (`docs/parallel/B-readerinv.md` §7): for a returned shape with the
decomposition `ShapeDecomp … sp bs … names kinds inits letB`,

    (names.zip kinds).length = sp.layout.slots.length

The general statement would follow from the reader-state invariant
`MachRead.LenOk` (`Tools/ShippingReaderLenOk.lean`) of the state the
`partial` readers return — not derivable in the kernel. What CAN be done
without it: check R5 on the returned shape, per declaration.

**Not from the shape alone.** `sp.binders.length = bs.length +
sp.insts.length + (names.zip kinds).length + sp.layout.lets`, and the shape
does not record `bs.length` (how many of its binders are the
declaration's). One `MachineShape` can have two decompositions, one with R5
and one without: binders `[(a, k), (r0, k), (r1, k)]`, two slots of kind
`k`, no call, no `let` — it is `bs = [(a, k)]`, `names = [r0, r1]` (R5
holds), and also `bs = [(a, k), (r0, k)]`, `names = [r1]`, `kinds = [k, k]`,
`inits` of length 2 (one slot binder, two slots: R5 fails). So a check of R5
needs the number of declaration binders:

* `shapeR5Ok sp nB` — the binder count with `nB` declaration binders;
  `r5_of_count`: with `nB = bs.length` it gives R5;
* `MachineData.r5Ok d` — the same with `nB + insts.length = d.nIn`. The
  generator stores `nIn := nDecl + shape.insts.length`, `nDecl :=
  bsIn.length` for the peel of the entry constant's value, and already
  REFUSES a declaration for which this count fails
  (`Tools/ShippingMachineCommand.lean` 437–442, "binder count") — at the
  meta level. `r5_of_r5Ok` needs that relation as the explicit hypothesis
  `hnIn : d.nIn = bs.length + d.shape.insts.length`: it is the generator's
  knowledge, not a theorem (the peel is of the entry constant's value,
  through `packTupleInputs`, a `partial def`, and for an unfolded entry
  constant through `userInliner`).

So R5 stays a decidable per-declaration condition (`decide` on the
reflected data, like the other data conditions) PLUS the link `hnIn`.

Depends on `Tools/ShippingShapeDecomp.lean` (written, not built).
UNVERIFIED: written, not built. -/
namespace Tools.ShippingR5Check
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingMachineAuto
open Tools.ShippingMachineShapeUnfold Tools.ShippingShapeDecomp

/-- The binder count of a shape with `nB` declaration binders: one binder
per call entry, per layout slot and per `let` besides them. -/
def shapeR5Ok (sp : MachineShape) (nB : Nat) : Bool :=
  decide (sp.binders.length = nB + sp.insts.length + sp.layout.slots.length + sp.layout.lets)

/-- **R5 as a data condition** on a reflected declaration: the binder count
at the data's `nIn` (declaration binders plus call entries). -/
def _root_.Tools.ShippingMachineAuto.MachineData.r5Ok (md : MachineData) : Bool :=
  decide (md.shape.binders.length = md.nIn + md.shape.layout.slots.length + md.shape.layout.lets)

variable {d : DefinitionVal} {senv : StructEnv} {sp : MachineShape}
  {bs : List (Name × MixedGateBinder)} {e : Lean.Expr} {ctor? : Option Name}
  {outs : List (String × MixedGateBinder)} {names : List Name}
  {kinds : List MixedGateBinder} {inits : List Nat} {letB : List (Name × MixedGateBinder)}

/-- The binder count of a decomposed shape (pure). -/
theorem binders_length (D : ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB) :
    sp.binders.length =
      bs.length + sp.insts.length + (names.zip kinds).length + sp.layout.lets := by
  have hi : (instBinders sp.insts).length = sp.insts.length := instBinders_length _
  have hl : sp.layout.lets = letB.length := D.lets
  have hb : sp.binders.length =
      bs.length + (instBinders sp.insts).length + (names.zip kinds).length + letB.length := by
    rw [D.binders, List.length_append, List.length_append, List.length_append]
  omega

/-- **R5 from the count** at the decomposition's own number of declaration
binders. -/
theorem r5_of_count (D : ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB)
    (h : shapeR5Ok sp bs.length = true) :
    (names.zip kinds).length = sp.layout.slots.length := by
  have hc : sp.binders.length =
      bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets :=
    of_decide_eq_true h
  have hb := binders_length D
  omega

/-- R5 gives the count back: at `bs.length` the check is EQUIVALENT to R5
(so it is not a weaker or a stronger condition). -/
theorem count_of_r5 (D : ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB)
    (R5 : (names.zip kinds).length = sp.layout.slots.length) :
    shapeR5Ok sp bs.length = true := by
  have hb := binders_length D
  exact decide_eq_true (by omega)

/-- **R5 from the reflected data's check**, given that the data's `nIn`
counts the declaration binders of THIS decomposition and the call entries
(`hnIn`: the generator's relation, an explicit hypothesis). -/
theorem r5_of_r5Ok {md : MachineData}
    (D : ShapeDecomp d senv md.shape bs e ctor? outs names kinds inits letB)
    (hnIn : md.nIn = bs.length + md.shape.insts.length)
    (h : md.r5Ok = true) :
    (names.zip kinds).length = md.shape.layout.slots.length := by
  have hc : md.shape.binders.length =
      md.nIn + md.shape.layout.slots.length + md.shape.layout.lets :=
    of_decide_eq_true h
  have hb := binders_length D
  omega

end Tools.ShippingR5Check
