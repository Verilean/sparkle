import Tools.ShippingReaderInputs
import Tools.ShippingMachineAuto

/-! # The machine endpoint's body equation, from the reader (G3)

The machine endpoints (`Tools.ShippingMachineAuto.machine_trace_of_data`, …)
ask two facts about the transition's body that are per-declaration kernel
evaluations today: the equation `hbody` (`f.machine_body`, an `Eq.refl`
between the body and the quotation of the packed term) and the conjunct
`d.packed.WF d.kb d.kv d.vw` of `MachineData.ok`.

Here both follow from ONE fact, for every `MachineData`: the reader returns
the packed term on the body.

* `machine_body_of_read`: `hbody`, from the reading.
* `machine_wf_of_read`: the well-formedness conjunct, from the reading.

What is NOT proved here
* The reading itself (`readTerm … d.shape.body = some ⟨_, d.packed⟩`) is
  still an evaluation per declaration: nothing in the compiler runs
  `readTerm`, and `machineShape?` is not reasoned about. It becomes a fact
  of every run only when the acceptance test of the machine route includes
  the reader (docs/parallel/G3-reader.md, §5).
* `d.packed` is given, not computed from the reading: the split of the term
  read into `let` fields, results and next values (`splitLets`,
  `splitFields`, `unField` of the generator) has no theorem.
* The three list equations (`bposL`, `vposL`, `vwL` are the positions and
  widths of the binders) are premises; they are evaluations on the binder
  kinds, independent of the body.
* The node kinds the reader does not read yet (ShippingReaderTerm). -/
namespace Tools.ShippingReaderMachine
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingReaderTerm Tools.ShippingReaderInputs
open Tools.ShippingMachineAuto
open Tools.ShippingMixedSourceBridge (inputExpr)

/-- The binder kinds of a machine's transition. -/
def kindsOf (d : MachineData) : List MixedGateBinder := d.shape.binders.map fun b => b.2

theorem kindsOf_length (d : MachineData) : (kindsOf d).length = d.shape.binders.length :=
  List.length_map ..

/-- **The body equation from the reading.** For every machine data: if the
reader returns the packed term on the transition's body, the body is the
quotation the endpoints ask for. -/
theorem machine_body_of_read (d : MachineData) (isDom : Lean.Expr → Bool)
    (hdom : ∀ x, isDom x = true → x = d.dom)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hread : readTerm (kindsCfg d.dom isDom (kindsOf d)) d.shape.body =
      some (⟨_, d.packed⟩ : AnyTerm)) :
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed := by
  have h := (readTerm_kinds_sound d.dom isDom hdom (kindsOf d) d.shape.body _ hread).1
  rw [kindsOf_length, ← hb, ← hv] at h
  exact h.symm

/-- **Well-formedness from the reading.** The conjunct of `MachineData.ok`
about the packed term. -/
theorem machine_wf_of_read (d : MachineData) (isDom : Lean.Expr → Bool)
    (hdom : ∀ x, isDom x = true → x = d.dom)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hread : readTerm (kindsCfg d.dom isDom (kindsOf d)) d.shape.body =
      some (⟨_, d.packed⟩ : AnyTerm)) :
    d.packed.WF d.kb d.kv d.vw := by
  have h := (readTerm_kinds_sound d.dom isDom hdom (kindsOf d) d.shape.body _ hread).2
  rw [← hb, ← hv, ← hw] at h
  exact h

end Tools.ShippingReaderMachine
