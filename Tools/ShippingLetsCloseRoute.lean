import Tools.ShippingMachineClosesData

/-! # Unit LC: what the machine route gives for `LetsClose`

BUILT: lc1 exit 0 (Tools.ShippingLetsCloseRoute); audit lc2 (ChildVertAuditTest) see REPORT-LC.md.

Question: does the COMPILER guarantee the shape data of `letsClose_of_data`
(`d.ok`, the body equation `d.shape.body = quote …`, `d.letsAliasOk`) for every
shape it puts on the machine route? Findings (details: docs/parallel/main-theorem-connection.md, L6c):

* The runtime checks of `Sparkle.Compiler.Elab.machineShape?` are `mixedGatePeel`, `machOuts?`/`outNameOk`/`Nodup`
  of the output names, the readers `machRoot`/`machConv`/…, `machDom?`/`machField`, and the Bool
  `unifiedGateRoot binders body`. None of them builds a typed `Term`, `MachineData`, `LetsScoped`,
  `LetsTyped` or `aliasOk`: `ok`, the body equation and `letsAliasOk` are conditions of the PROOF-GENERATION
  side (`Tools.ShippingMachineCommand.readMachine`, kernel `decide`), NOT checked by the compiler.
* The readers behind `machineShape?` are `partial` (opaque to the kernel): they cannot be unfolded, so no
  property of their output is derivable by `rfl`/`simp` from `machineShape? … = some shape`.
* `unifiedGateRoot` does not pin every position `quote` writes (`Tools/ShippingReaderTerm.lean`, "NOT proved"),
  so "accepted ⟹ the body is a quotation" is not available for it.
* The compiler's only run-time check of `LetsClose`'s conclusion is `closeLets` itself, on the module of THE run:
  a returning machine route with a `some` result gives `closeLets … = some` for THAT run
  (`closeLets_some_of_machine_some`); it does not give `LetsClose` (∀ tenv, logProf, w, over all harness runs).
  A `none` is the fallback case (MO2's `closeLets` pure `none` arm); it is exactly a refutation of `LetsClose`
  (`not_letsClose_of_refusal`).

PROVED here: `letsClose_of_noLets` (the shape class with `layout.lets = 0`: no data, unconditional),
`closeLets_some_of_machine_some` (run-local), `not_letsClose_of_refusal`, `letsClose_iff_no_refusal`.
OPEN: for shapes with `lets ≠ 0`, `LetsClose` from `machineShape? … = some shape` (needs the three data
conditions linked to the `partial` readers). No counterexample is known: the only real fall-through in the
census (`pCount`) falls at the calls' closing, not at `closeLets`; a refusing `closeLets` is only exhibited on
hand-built modules (`Tests/Compiler/ShippingReflectCtxTest.lean`), reachability from a source is NOT shown. -/
namespace Tools.ShippingLetsCloseRoute
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingClosesSplit

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A shape without `let`s: `closeLets` returns the module as it is, so `LetsClose` holds with no data
condition and no run fact. -/
theorem letsClose_of_noLets {declName : Name} {shape : MachineShape}
    (h : shape.layout.lets = 0) : LetsClose mctx mref cctx cref declName shape := by
  intro tenv logProf w t d w' _
  simp [closeLets, h]

/-- **Run-local.** A returning run of the machine synthesis whose result is `some` contains a harness run
whose module `closeLets` accepts. This is about THAT run: it is not `LetsClose`. -/
theorem closeLets_some_of_machine_some {tenv : Lean.Environment} {logProf : String → IO Unit}
    {declName : Name} {shape : MachineShape} {w : _} {res w' : _}
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName shape)
      mctx mref cctx cref w (some res) w') :
    ∃ t d w1 t',
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named)
        logProf declName shape.binders shape.body) mctx mref cctx cref w (t, d) w1 ∧
      closeLets shape.layout.lets t = some t' := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d⟩, w1, h1, hr⟩ := RunsTo.bind hr
  dsimp only at hr
  cases hcl : closeLets shape.layout.lets t with
  | some t' => exact ⟨t, d, w1, t', h1, hcl⟩
  | none =>
    rw [hcl] at hr
    dsimp only at hr
    have := RunsTo.pure_eq hr
    exact absurd this (by simp)

/-- A harness run whose module `closeLets` refuses refutes `LetsClose` (the fallback case of the route). -/
theorem not_letsClose_of_refusal {declName : Name} {shape : MachineShape} {tenv : Lean.Environment}
    {logProf : String → IO Unit} {w : _} {t d w' : _}
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      logProf declName shape.binders shape.body) mctx mref cctx cref w (t, d) w')
    (hn : closeLets shape.layout.lets t = none) :
    ¬ LetsClose mctx mref cctx cref declName shape := by
  intro h
  have := h logProf w t d w' hr
  rw [hn] at this
  simp at this

/-- `LetsClose` is exactly "no harness run is refused by `closeLets`". -/
theorem letsClose_iff_no_refusal {declName : Name} {shape : MachineShape} :
    LetsClose mctx mref cctx cref declName shape ↔
      ∀ {tenv : Lean.Environment} (logProf : String → IO Unit) w t d w',
        RunsTo (synthesizeMixedCertified
          (fun e hint top named => translateExprToWire tenv e hint top named)
          logProf declName shape.binders shape.body) mctx mref cctx cref w (t, d) w' →
        closeLets shape.layout.lets t ≠ none := by
  constructor
  · intro h tenv logProf w t d w' hr hn
    exact not_letsClose_of_refusal hr hn h
  · intro h tenv logProf w t d w' hr
    exact Option.isSome_iff_ne_none.mpr (h logProf w t d w' hr)

end Tools.ShippingLetsCloseRoute
