import Tools.ShippingPostSoundness
import Tools.ShippingOptSoundness
import Tools.ShippingPrintEntrySoundness

/-! The synthesis-entry theorems on REAL declarations: the quotation matches what
Lean elaborates, the user's definition is `denoteFE` by `rfl`, the certified
front end agrees with the legacy one, the IR computes the source values, and
the axiom audit. -/

namespace Sparkle.Tests.Compiler.ShippingEntrySoundnessTest

open Lean Elab Command Meta Tools.ShippingEntrySoundness Tools.ShippingScalarSoundness
open Tools.ShippingPostSoundness
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Compiler.Elab

def fragA {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  ((a + b) ^^^ (Signal.pure (BitVec.ofNat 8 3) : Signal dom (BitVec 8))) - a * b

def feA : FExpr :=
  .bin .sub (.bin .xor (.bin .add (.inp 0) (.inp 1)) (.lit 3)) (.bin .mul (.inp 0) (.inp 1))

def fragB {dom : DomainConfig} (a b c : Signal dom (BitVec 4)) : Signal dom (BitVec 4) :=
  (a + b) + (a + b) * c

def feB : FExpr :=
  .bin .add (.bin .add (.inp 0) (.inp 1)) (.bin .mul (.bin .add (.inp 0) (.inp 1)) (.inp 2))

def fragC {dom : DomainConfig} (x : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  x &&& (x ||| (Signal.pure 0x00f5#16 : Signal dom (BitVec 16)))

def feC : FExpr := .bin .and (.inp 0) (.bin .or (.inp 0) (.lit 0x00f5))

def fragD {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a

def feD : FExpr := .inp 0

/-- Shifts are on the certified front end but not in `Denotes`: checked here
only for front-end agreement and against the Lean value. -/
def fragS {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (a <<< b) + (a >>> b)

/-- Two spellings of the literal 5 elaborate to different `Expr`s, so the
translator emits two `const 5 8` wires and two adders; `mergeDuplicates` merges
them, and the checker must ACCEPT that merge. -/
def dupLit {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (a + (Signal.pure (5 : BitVec 8) : Signal dom (BitVec 8))) ^^^
    (a + (Signal.pure (BitVec.ofNat 8 5) : Signal dom (BitVec 8)))

/-- Outside the certified shape (a width-changing concatenation): the legacy
front end handles it. -/
def notCertified {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 16) :=
  a ++ a

def sigsOf {dom : DomainConfig} {n : Nat} (l : List (Signal dom (BitVec n))) (j : Nat) :
    Signal dom (BitVec n) :=
  l.getD j (Signal.pure 0)

/-! The user's definitions ARE `denoteFE` of their `FExpr`, by `rfl`. -/
example {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    fragA a b = denoteFE 8 (sigsOf [a, b]) feA := rfl
example {dom : DomainConfig} (a b c : Signal dom (BitVec 4)) :
    fragB a b c = denoteFE 4 (sigsOf [a, b, c]) feB := rfl
example {dom : DomainConfig} (x : Signal dom (BitVec 16)) :
    fragC x = denoteFE 16 (sigsOf [x]) feC := rfl
example {dom : DomainConfig} (a : Signal dom (BitVec 8)) :
    fragD a = denoteFE 8 (sigsOf [a]) feD := rfl

/-! ## The general theorem applied to the REAL `fragA`

`fragAValue` is `fragA`'s value as Lean elaborated it (read from the
environment by `#def_decl_value`), and it IS the quotation, by `rfl`. The
corollary then follows from `fragmentDecl_of_env` for any run of the real
entry on `fragA` whose environment defines `fragA` that way. -/

#def_decl_value fragAValue of fragA

theorem fragAValue_eq : fragAValue = quoteDecl `dom [`a, `b] 8 feA := rfl

/-- The general byte-rendering theorem applies to the same real declaration
and synthesis run, without separate metadata or body-shape hypotheses. -/
theorem fragA_text_render {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational ``fragA) mctx mref cctx cref w (M, D) w')
    (henv : EnvDefines mctx mref cctx cref ``fragA fragAValue) :
    let o := Sparkle.IR.OptCheck.checkedOptimize M
    ∃ sv, Tools.SVParser.EmitAst.emitAstModule o = some sv ∧
      Tools.ShippingModulePrintSoundness.renderModule o.name
        (o.wires.filter fun p => !((o.inputs ++ o.outputs).map (·.name)).contains p.name).length sv
        = some (Sparkle.Backend.Verilog.toVerilog o) := by
  rw [fragAValue_eq] at henv
  exact Tools.ShippingPrintEntrySoundness.printedModule_render h henv
    (by simp [feA, FExpr.WF]) (by decide)

theorem feA_wf : feA.WF 2 8 := by simp [feA, FExpr.WF]

/-- A real declaration uses the general core theorem; no per-circuit SAT
certificate or caller-supplied assignment order is involved. -/
theorem fragA_core_settled {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinationalCore ``fragA [] false) mctx mref cctx cref w (M, D) w')
    (henv : EnvDefines mctx mref cctx cref ``fragA fragAValue) :
    ∃ port : Nat → Option String,
      ∀ {dom : DomainConfig} (a b : Signal dom (BitVec 8)) (t : Nat)
        (initial : Sparkle.IR.Semantics.Env),
        (∀ j wire, j < 2 → port j = some wire →
          initial wire = ((sigsOf [a, b] j).val t).toNat) →
        Tools.ShippingSettledSoundness.Acyclic M.body ∧
        ∃ env, Tools.ShippingSettledSoundness.IREquations
            (Tools.ShippingEntrySoundness.weOf M) M.body env ∧
          Tools.ShippingSettledSoundness.ExternalValues M.body initial env ∧
          env "out" = ((fragA a b).val t).toNat ∧
          ∀ other, Tools.ShippingSettledSoundness.IREquations
              (Tools.ShippingEntrySoundness.weOf M) M.body other →
            Tools.ShippingSettledSoundness.ExternalValues M.body initial other → other = env := by
  rw [fragAValue_eq] at henv
  obtain ⟨port, _, _, hs⟩ := fragmentDecl_core_settled h henv feA_wf
  exact ⟨port, fun a b t initial hi => hs (sigsOf [a, b]) t initial hi⟩

/-- **`fragA` and its IR agree on every input, after post-processing.** For any
successful run of `synthesizeCombinational ``fragA` (the entry, then
`dropZeroWidthModule`, then `mergeDuplicates` unless `SPARKLE_NO_REGDEDUP` is
set — what `#synthesizeVerilog` compiles), in an environment that defines
`fragA` as elaborated here: the RETURNED module has two distinct input ports
`pa`, `pb`, and for every domain, all signals `a b` and every cycle `t`, driving
`pa`, `pb` with `a`, `b` at `t` makes `out` equal `(fragA a b).val t`. -/
theorem fragA_ir_correct {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational ``fragA) mctx mref cctx cref w (M, D) w')
    (henv : EnvDefines mctx mref cctx cref ``fragA fragAValue) :
    ∃ pa pb : String, pa ≠ pb ∧
      ∀ {dom : DomainConfig} (a b : Signal dom (BitVec 8)) (t : Nat)
        (mems : Sparkle.IR.Semantics.MEnv) (initial : Sparkle.IR.Semantics.Env),
        initial pa = (a.val t).toNat → initial pb = (b.val t).toNat →
        ∃ env, Sparkle.IR.Semantics.evalAssigns (weOf M) mems M.body initial = some env ∧
          env "out" = ((fragA a b).val t).toNat := by
  rw [fragAValue_eq] at henv
  obtain ⟨port, hdist, hex, hsem⟩ :=
    synthesizeCombinational_fragment (names := [`a, `b]) h henv feA_wf (by decide)
  obtain ⟨pa, hpa⟩ := hex 0 (by decide)
  obtain ⟨pb, hpb⟩ := hex 1 (by decide)
  refine ⟨pa, pb, fun he => by subst he; exact absurd (hdist 0 1 pa hpa hpb) (by decide), ?_⟩
  intro dom a b t mems initial ha hb
  have hinit : ∀ j w, j < [`a, `b].length → port j = some w →
      initial w = ((sigsOf [a, b] j).val t).toNat := by
    intro j w hj hw
    match j, hj with
    | 0, _ => rw [hpa] at hw; cases hw; exact ha
    | 1, _ => rw [hpb] at hw; cases hw; exact hb
  obtain ⟨env, hev, hout⟩ := hsem (sigsOf [a, b]) t mems initial hinit
  exact ⟨env, hev, hout⟩

/-- **`fragA` and the module `#synthesizeVerilog` prints agree on every
input.** `verilogOf M = toVerilog (checkedOptimize M)`; for any successful run
of `synthesizeCombinational ``fragA` under `EnvDefines`, the printed module has
input ports `pa ≠ pb` and drives `out` with `(fragA a b).val t`. -/
theorem fragA_printed_correct {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational ``fragA) mctx mref cctx cref w (M, D) w')
    (henv : EnvDefines mctx mref cctx cref ``fragA fragAValue) :
    verilogOf M = Sparkle.Backend.Verilog.toVerilog (Sparkle.IR.OptCheck.checkedOptimize M) ∧
    ∃ pa pb : String, pa ≠ pb ∧
      pa ∈ (Sparkle.IR.OptCheck.checkedOptimize M).inputs.map (·.name) ∧
      pb ∈ (Sparkle.IR.OptCheck.checkedOptimize M).inputs.map (·.name) ∧
      ∀ {dom : DomainConfig} (a b : Signal dom (BitVec 8)) (t : Nat)
        (mems : Sparkle.IR.Semantics.MEnv) (initial : Sparkle.IR.Semantics.Env),
        initial pa = (a.val t).toNat → initial pb = (b.val t).toNat →
        ∃ env, Sparkle.IR.Semantics.evalAssigns
            (Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize M)) mems
            (Sparkle.IR.OptCheck.checkedOptimize M).body initial = some env ∧
          env "out" = ((fragA a b).val t).toNat := by
  refine ⟨rfl, ?_⟩
  rw [fragAValue_eq] at henv
  obtain ⟨port, hdist, hex, hsem⟩ :=
    printedModule_fragment (names := [`a, `b]) h henv feA_wf (by decide)
  obtain ⟨pa, hpa, hpaIn⟩ := hex 0 (by decide)
  obtain ⟨pb, hpb, hpbIn⟩ := hex 1 (by decide)
  refine ⟨pa, pb, fun he => by subst he; exact absurd (hdist 0 1 pa hpa hpb) (by decide),
    hpaIn, hpbIn, ?_⟩
  intro dom a b t mems initial ha hb
  have hinit : ∀ j w, j < [`a, `b].length → port j = some w →
      initial w = ((sigsOf [a, b] j).val t).toNat := by
    intro j w hj hw
    match j, hj with
    | 0, _ => rw [hpa] at hw; cases hw; exact ha
    | 1, _ => rw [hpb] at hw; cases hw; exact hb
  obtain ⟨env, hev, hout⟩ := hsem (sigsOf [a, b]) t mems initial hinit
  exact ⟨env, hev, hout⟩

/-- Evaluate a synthesized combinational module on input values, under the
widths the module itself declares (`weOf`, as in the theorems). -/
def evalOut (m : Sparkle.IR.AST.Module) (inputs : List (String × Nat)) : Option Nat :=
  let initial : Sparkle.IR.Semantics.Env := fun s => (inputs.lookup s).getD 0
  (Sparkle.IR.Semantics.evalAssigns (weOf m) (fun _ _ => 0) m.body initial).map (· "out")

def cases : List (Name × Name × List Name × Nat × FExpr) :=
  [ (``fragA, `dom, [`a, `b], 8, feA), (``fragB, `dom, [`a, `b, `c], 4, feB),
    (``fragC, `dom, [`x], 16, feC), (``fragD, `dom, [`a], 8, feD) ]

run_cmd liftTermElabM do
  let tr : TranslateFn := fun e h t n => translateExprToWire e h t n
  for (decl, dn, names, n, fe) in cases do
    let ci ← getConstInfo decl
    -- (1) the value IS the quotation, by the Lean-level decidable equality
    let v := ci.value!
    unless @decide (v = quoteDecl dn names n fe) (Sparkle.Compiler.ExprDecEq.exprDecEq _ _) do
      throwError "{decl}: value is not quoteDecl of its FExpr"
    -- (2) the gate accepts it
    unless (certifiedShape? false [] ci).isSome do
      throwError "{decl}: certified front end did not accept it"
    -- (3) certified front end = legacy front end, as IR and as Verilog
    let (m1, _) ← synthesizeCombinationalCoreWith tr decl [] false true
    let (m2, _) ← synthesizeCombinationalCoreWith tr decl [] false false
    unless toString (repr m1) == toString (repr m2) do
      throwError "{decl}: certified and legacy front ends disagree"
    unless Sparkle.Backend.Verilog.toVerilog m1 == Sparkle.Backend.Verilog.toVerilog m2 do
      throwError "{decl}: Verilog differs between front ends"
    -- (4) the IR computes evalFE (the Lean meaning) on sample inputs
    let ports := m1.inputs.map (·.name)
    unless ports.length == names.length do throwError "{decl}: inputs {ports}"
    for seed in [0, 1, 7, 100, 12345] do
      let vals : Nat → BitVec n := fun j => BitVec.ofNat n (seed * 31 + j * 97 + 5)
      let inputs := (List.range names.length).map fun j => (ports[j]!, (vals j).toNat)
      let got := evalOut m1 inputs
      let want := (evalFE n vals fe).toNat
      unless got == some want do
        throwError "{decl}: IR gives {got}, source gives {want} (seed {seed})"
  -- (5) shifts: certified front end, same IR as legacy, IR = Lean value
  let ciS ← getConstInfo ``fragS
  unless (certifiedShape? false [] ciS).isSome do throwError "fragS: not certified"
  let (s1, _) ← synthesizeCombinationalCoreWith tr ``fragS [] false true
  let (s2, _) ← synthesizeCombinationalCoreWith tr ``fragS [] false false
  unless toString (repr s1) == toString (repr s2) do throwError "fragS: front ends disagree"
  let sp := s1.inputs.map (·.name)
  for (x, y) in [(3, 1), (200, 3), (255, 7), (17, 9), (128, 0)] do
    let want := ((fragS (dom := defaultDomain) (Signal.pure (BitVec.ofNat 8 x))
      (Signal.pure (BitVec.ofNat 8 y))).val 0).toNat
    let got := evalOut s1 [(sp[0]!, x), (sp[1]!, y)]
    unless got == some want do throwError "fragS: IR gives {got}, source gives {want}"
  -- (6) a real merge on a certified-shape module, accepted by the checker
  let (d0, _) ← synthesizeCombinationalCoreWith tr ``dupLit [] false true
  let dz := Sparkle.IR.ZeroWidth.dropZeroWidthModule d0
  let raw := Sparkle.IR.RegDedup.mergeDuplicatesRaw dz
  unless toString (repr raw.body) != toString (repr dz.body) do
    throwError "dupLit: expected mergeDuplicates to merge something"
  unless toString (repr (Sparkle.IR.RegDedup.mergeDuplicates dz).body) == toString (repr raw.body) do
    throwError "dupLit: the merge checker rejected a merge"
  let (dm, _) ← synthesizeCombinational ``dupLit
  let dp := dm.inputs.map (·.name)
  for x in [0, 1, 7, 200, 255] do
    let want := ((dupLit (dom := defaultDomain) (Signal.pure (BitVec.ofNat 8 x))).val 0).toNat
    let got := evalOut dm [(dp[0]!, x)]
    unless got == some want do throwError "dupLit: IR gives {got}, source gives {want}"
  -- (7) outside the shape: not certified, still synthesized by the legacy front end
  let ci ← getConstInfo ``notCertified
  unless (certifiedShape? false [] ci).isNone do
    throwError "notCertified: gate accepted a concatenation"
  let _ ← synthesizeCombinationalCoreWith tr ``notCertified [] false true


/-! ## The merge checker REJECTS a width-changing merge

Two wires with the same right-hand side but different declared widths (8 and
16 bits) feed a concatenation. The merge's signature ignores declared widths,
so the proposal merges them, which changes the concatenation's value. The
checker must reject it, and the shipped `mergeDuplicates` must return the
module unchanged. -/

open Sparkle.IR.AST in
def widthMismatch : Sparkle.IR.AST.Module :=
  { name := "widthMismatch"
    inputs := [{ name := "x", ty := .bitVector 8 }]
    outputs := [{ name := "out", ty := .bitVector 24 }]
    wires := [{ name := "_tmp_a", ty := .bitVector 8 }, { name := "_tmp_b", ty := .bitVector 16 }]
    body := [.assign "_tmp_a" (.ref "x"), .assign "_tmp_b" (.ref "x"),
      .assign "out" (.concat [.ref "_tmp_a", .ref "_tmp_b"])] }

def evalMod (m : Sparkle.IR.AST.Module) (x : Nat) : Option Nat :=
  (Sparkle.IR.Semantics.evalAssigns (weOf m) (fun _ _ => 0) m.body
    (fun s => if s = "x" then x else 0)).map (· "out")

run_cmd liftTermElabM do
  let m := widthMismatch
  let raw := Sparkle.IR.RegDedup.mergeDuplicatesRaw m
  unless toString (repr raw.body) != toString (repr m.body) do
    throwError "widthMismatch: expected the merge proposal to merge the two wires"
  -- the proposal is WRONG: it changes the value
  unless evalMod raw 1 != evalMod m 1 do
    throwError "widthMismatch: expected the unchecked merge to change the value"
  unless !(Sparkle.IR.RegDedup.validateMerge (Sparkle.IR.RegDedup.declWidth m) m.body raw.body) do
    throwError "widthMismatch: the checker accepted a width-changing merge"
  -- the shipped pass returns the module unchanged
  unless (Sparkle.IR.RegDedup.mergeDuplicates m) == m do
    throwError "widthMismatch: mergeDuplicates did not fall back to the original module"
  unless evalMod (Sparkle.IR.RegDedup.mergeDuplicates m) 1 == some 65537 do
    throwError "widthMismatch: wrong value after mergeDuplicates"

/-! ## The optimizer checker rejects a wrong "optimization"

A hand-built module claiming to optimise `fragA`'s module but computing
`a + b` instead: `optCheck` must reject it (so `checkedOptimize` would keep the
unoptimised module). And on the real module the real optimizer's result is
accepted. -/
run_cmd liftTermElabM do
  let (m, _) ← synthesizeCombinational ``fragA
  let o := Sparkle.IR.Optimize.optimizeModule m
  unless Sparkle.IR.OptCheck.optCheck m o do
    throwError "optCheck rejected the real optimizer's result on fragA"
  unless Sparkle.IR.OptCheck.checkedOptimize m == o do
    throwError "checkedOptimize did not keep the accepted optimisation"
  for bad in [{o with isPrimitive := true},
      {o with wires := o.wires ++ [{name := "unused_zero", ty := .bitVector 0}]}] do
    unless Sparkle.IR.OptCheck.optCheckCore m bad do
      throwError "metadata negative control must pass the old semantic checker"
    unless !(Sparkle.IR.OptCheck.optCheck m bad) do
      throwError "optCheck accepted a proposal with unsupported printed declarations"
  -- Integration check for the general module-rendering theorem: compare the
  -- SAME optimized module the shipping command hands to toVerilog. This is
  -- a byte regression, not a new per-circuit semantic certificate.
  let some sv := Tools.SVParser.EmitAst.emitAstModule o
    | throwError "fragA: optimized module has no SV AST"
  let wireCount := (o.wires.filter fun p => !((o.inputs ++ o.outputs).map (·.name)).contains p.name).length
  unless Tools.ShippingModulePrintSoundness.renderModule o.name wireCount sv ==
      some (Sparkle.Backend.Verilog.toVerilog o) do
    throwError "fragA: shipping module text differs from SV AST rendering"
  let ins := m.inputs.map (·.name)
  let bogus : Sparkle.IR.AST.Module :=
    { o with body := [.assign "out" (.op .add [.ref ins[0]!, .ref ins[1]!])] }
  unless !(Sparkle.IR.OptCheck.optCheck m bogus) do
    throwError "optCheck accepted a module computing a different output"

run_cmd do
  if (← get).messages.hasErrors then throwError "entry regression failed"
  for name in [``fragA_core_settled, ``fragmentDecl_core_settled, ``dropZeroWidth_entry_order,
      ``fragA_text_render, ``fragA_printed_correct, ``printedModule_fragment,
      ``Tools.ShippingPrintEntrySoundness.printedModule_render,
      ``Tools.ShippingPrintEntrySoundness.compiledFragment_artifact,
      ``Tools.ShippingPrintEntrySoundness.synthesized_printFacts,
      ``Tools.ShippingPrintEntrySoundness.checkedOptimize_printDecls,
      ``Tools.ShippingOptSoundness.optCheck_sound,
      ``Tools.ShippingOptSoundness.checkedOptimize_sound, ``postprocess_facts,
      ``fragA_ir_correct, ``fragAValue_eq, ``fragmentDecl_of_env,
      ``synthesizeCombinational_fragment, ``synthesizeCombinational_reads, ``postprocess_sound,
      ``dropZeroWidth_entry, ``mergeDuplicates_sound, ``validateMerge_sound,
      ``validateStep_sound, ``renameE_sound, ``weOf_dropWires,
      ``synthesizeCombinationalCore_reads, ``synthesizeFromConst_sound, ``outcome_quote,
      ``RunsTo.bind, ``RunsTo.ite, ``RunsTo.try_finally, ``RunsTo.mreturns,
      ``MReturns.bind, ``MReturns.pure, ``MReturns.throw, ``MReturns.run,
      ``MReturns.try_finally, ``MReturns.ite, ``addInput_returns, ``addOutput_returns,
      ``withVarMapping_returns, ``bindInputPort_returns, ``bindCertifiedInputs_returns,
      ``emitLeaves_single, ``finishSynth_returns, ``addClockReset_facts,
      ``widthsAgree_weOf, ``rhoOf_some, ``translateExprToWire_grows,
      ``synthesizeCertified_sound, ``synthesizeCombinationalCore_sound,
      ``denoteFE_val, ``op_checks, ``instFVars_quoteBody, ``certifiedShape_quote,
      ``rhoOf_at, ``denotes_quote, ``fragmentDecl_sound, ``fragmentDecl_sound_signal,
      ``Tools.ShippingTranslateSoundness.translateExprToWire_sound] do
    for a in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "unexpected entry axiom: {name}: {a}"
  logInfo "SHIPPING ENTRY OK: fragA_ir_correct — any run of synthesizeCombinational ``fragA (entry + dropZeroWidth + mergeDuplicates) whose environment defines fragA as elaborated yields IR equal to fragA on every input (constant read in the SAME run); standard axioms only"

end Sparkle.Tests.Compiler.ShippingEntrySoundnessTest
