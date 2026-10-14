import Tools.ShippingReaderProjChainFold

/-! # The general lemmas, about the compiler's `projChain` ITSELF

WRITTEN, NOT BUILT (branch `fix/projchain-total`; record:
`docs/parallel/L-projchain-switch.md`). No `sorry`, no axiom, no
`native_decide`.

Before the switch-over `Sparkle.Compiler.MachRawSurface.projChain` was a
`partial def`: an opaque constant, about which the kernel can prove nothing.
Every lemma of `Tools/ShippingReaderProjChain.lean` and
`Tools/ShippingReaderProjChainFold.lean` was therefore about a COPY
(`projChainW`, `projChainP`) or about the structural form (`projChainT`).

After the switch the compiler's function is a plain `def` (its `do` text
over `Sparkle.Compiler.MachProjChain.tailAt`). Every statement in this file
has `Sparkle.Compiler.MachRawSurface.projChain` — the constant `rawNode`
calls — on its left-hand side:

* `projChain_text`     — it is its source text with `tail := tailAt tys`
                         (`projChainP`, the text with `tail` a parameter);
* `projChain_form`     — it is the range loop followed by the last step;
* `projChain_eq_projChainT`, `projChain_eq` — THE EQUATION: it is the
                         structural definition;
* `projChain_zero_last`, `projChain_zero_notLast_nil`,
  `projChain_zero_notLast_cons`, `projChain_succ_nil`, `projChain_succ_cons`
                       — its recursion equations, in terms of ITSELF;
* `projChain_some`     — a result on the whole range `Accepts`;
* `projChain_callSite`, `projChain_callSiteK` — a result at EVERY call
                         `rawNode` makes (`j < tys.length`, `last = (j + 1 ==
                         tys.length)`).

The exact results and the converse of `projChain_some`:
`Tools/ShippingReaderProjChainResult.lean`. One step up (`rawNode`'s
pair-matcher arm): `Tools/ShippingReaderProjChainArm.lean`.

What none of this says: anything about the OLD compiled `partial` function.
The switch replaced it; that the replacement returns what it returned is
MEASURED (`Tools/ShippingReaderProjChainShadow.lean`, `projChainOld`) and
corresponds to its source equation by `tailAt_eq` / `tail_unique` — see the
record.

PREDICTED axioms: those of `projChainW_eq_projChainT` (BUILT: `propext`,
`Classical.choice`, `Quot.sound`). -/
namespace Tools.ShippingReaderProjChainReal
open Lean
open Tools.ShippingReaderProjChain
open Sparkle.Compiler.MachRawSurface (projChain)

/-- The name `projChainW` IS the compiler's function (an abbreviation). -/
theorem projChainW_is_projChain (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) :
    projChainW regs tys j last = projChain regs tys j last := rfl

/-- The compiler's function is its source text, the `do` block with `tail`
a parameter (`projChainP`), at the total `tail`. -/
theorem projChain_text (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) :
    projChain regs tys j last = projChainP (tailAt tys) regs tys j last :=
  (projChainP_tailAt regs tys j last).symm

/-- The compiler's function is the range loop followed by the last step. -/
theorem projChain_form (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) :
    projChain regs tys j last =
      (forIn [0:j] regs (loopBody tys) : Option Expr).bind (finStep tys last j) :=
  projChainW_form regs tys j last

/-- **THE EQUATION of the compiler's function**: it is the structural
definition. -/
theorem projChain_eq_projChainT (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) :
    projChain regs tys j last = projChainT regs tys j last :=
  projChainW_eq_projChainT regs tys j last

/-- The same, as an equation of functions. -/
theorem projChain_eq : projChain = projChainT :=
  funext fun regs => funext fun tys => funext fun j => funext fun last =>
    projChain_eq_projChainT regs tys j last

/-! ## The recursion equations of the compiler's function -/

/-- No projection at all: `regs` itself. -/
theorem projChain_zero_last (regs : Expr) (tys : List Expr) :
    projChain regs tys 0 true = some regs :=
  (projChain_eq_projChainT regs tys 0 true).trans (chainGo_zero_true regs tys)

theorem projChain_zero_notLast_nil (regs : Expr) :
    projChain regs [] 0 false = none :=
  (projChain_eq_projChainT regs [] 0 false).trans (chainGo_zero_false_nil regs)

/-- The first component: one `fst`, typed by the head and the pair type of
the rest. -/
theorem projChain_zero_notLast_cons (regs a : Expr) (rest : List Expr) :
    projChain regs (a :: rest) 0 false = (tailTy rest).map fun b => fstE a b regs :=
  (projChain_eq_projChainT regs (a :: rest) 0 false).trans
    (chainGo_zero_false_cons regs a rest)

theorem projChain_succ_nil (regs : Expr) (k : Nat) (last : Bool) :
    projChain regs [] (k + 1) last = none :=
  (projChain_eq_projChainT regs [] (k + 1) last).trans (chainGo_succ_nil last regs k)

/-- One `snd`, then the compiler's function again on the remaining
components. -/
theorem projChain_succ_cons (regs a : Expr) (rest : List Expr) (k : Nat) (last : Bool) :
    projChain regs (a :: rest) (k + 1) last =
      (tailTy rest).bind fun b => projChain (sndE a b regs) rest k last := by
  first
    | (rw [projChain_eq]
       exact chainGo_succ_cons last regs a rest k)
    | (simp only [projChain_eq_projChainT]
       exact chainGo_succ_cons last regs a rest k)
    | exact (projChain_eq_projChainT regs (a :: rest) (k + 1) last).trans
        ((chainGo_succ_cons last regs a rest k).trans
          (congrArg (fun F : Expr → Option Expr => (tailTy rest).bind F)
            (funext fun b => (projChain_eq_projChainT (sndE a b regs) rest k last).symm)))

/-! ## Successful inputs -/

/-- The compiler's function returns a result on the whole range `Accepts`. -/
theorem projChain_some (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool)
    (h : Accepts last tys.length j) : ∃ r, projChain regs tys j last = some r :=
  match projChainT_some regs tys j last h with
  | ⟨r, hr⟩ => ⟨r, (projChain_eq_projChainT regs tys j last).trans hr⟩

/-- **At every call the reader makes** (`rawNode`: component `j` of the
`k = tys.length` a pair matcher binds, `last` for the final one) the
compiler's function returns a result. No premise about the source. -/
theorem projChain_callSite (regs : Expr) (tys : List Expr) (j : Nat) (hj : j < tys.length) :
    ∃ r, projChain regs tys j (j + 1 == tys.length) = some r :=
  match projChainT_callSite regs tys j hj with
  | ⟨r, hr⟩ => ⟨r, (projChain_eq_projChainT regs tys j (j + 1 == tys.length)).trans hr⟩

/-- The same with the count as `rawNode` has it: a separate `k` equal to the
number of component types. -/
theorem projChain_callSiteK (regs : Expr) (tys : List Expr) (j k : Nat)
    (hk : tys.length = k) (hj : j < k) :
    ∃ r, projChain regs tys j (j + 1 == k) = some r := by
  subst hk
  exact projChain_callSite regs tys j hj

end Tools.ShippingReaderProjChainReal
