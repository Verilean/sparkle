import Tools.ShippingSeqParentLemmas
import Tools.ShippingChecksMaskedLeafA
import Tools.ShippingKidsSelfA
import Tools.ShippingCallsMemPinned
import Tools.ShippingParentRunFactsA
import Tools.ShippingParentDesignFA
import Tools.ShippingParentSeqComposedA
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit SR3j): audit hardening (fr == #[closes], aligned arguments logged and asserted == [mctx, mref, cctx, cref, w, w', b, design, hr, entry] (integrator, by review; built in int-r26c at 758c4c71: Tests.Compiler.SeqParentGenTest exit 0 for parent and chained), no unresolved mvars): `qbuild build Tests.Compiler.SeqParentGenTest` j1 exit 1 (fr was [closes], not empty), j2 exit 0.
-- BUILT (unit SR3i): `qbuild build Tools.ShippingSeqParentGen` exit 0 (g1-g7 `lean` runs exit 1 until fixed: API names, compiler panic of evalTerm replaced by reduction, hent origins, sync elaboration); used by Tests.Compiler.SeqParentGenTest (final qbuild exit 0).
/-! # `#machine_seq_parent_endpoint f`: the new-boundary design endpoint of a sequential-call parent, GENERATED

Generalises, from the hand wiring of units SR3c-SR3h on the single declaration `Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent`
(`Tests/Compiler/{KidsMaskedParentA,ParentEndpointFactsA,ParentDesignCheckFA,ParentHoutTy,ParentSeqComposedA}Test.lean`), to every
declaration `f` of the following class (EXACT, checked by the command / by `decide` inside the generated proofs; a declaration
outside the class makes the command fail, it is never silently narrowed):

* `f` is a top-level (non-polymorphic) `circuit do` machine whose old endpoint `#machine_design_svNR f 1` was generated
  (`f.machine_composedNR1`, `f.machineData`, `f.machine_ok`, `f.machine_body`, `f.machine_ext_causal`, ...);
* `f` has NO memory (all data conditions the closing / the facts need are decided: `slotBs`/`letBs`, `instOrigins`, ...), and
  `instFields ≠ []` (it reads fields of at least one call);
* every call instance of `f` (`f.machineData.shape.insts`) calls ONE declaration `c` (the same child, any number of calls,
  calls whose arguments are other calls' fields included) — a *sequential leaf register machine* with `c.machineData`,
  `c.machine_closes`, `c.machine_leafKid`-level facts (`c` itself has no instances);
* the design depth is `n = 1` and `kD` = the number of the parent's own input ports, `kD = bsIn.length - insts.length`.

What is GENERATED (names `f.epA_*`, all by `Lean.Elab.Command.elabCommand` of template text, then kernel-checked):
`Bnd` (the boundary: `O`, `T : RefLawsATele`, `AdmCtx`, `MachineDefines c`, a `JQ` start world), `closes` (`MachineClosesAtA`),
`kidsMasked`, `runFacts`, `outsCheck`, `designCheck`, `houtTy`, `traceX`/`soundLA`/`composedA` and the endpoint
`epA_endpoint`.  In-command AUDITS (an error otherwise): standard axioms; the outer `Prop` premises are exactly `hr`, `entry`,
`closes : True`; the dependency closure contains the new-boundary lemmas and none of `RefLaws`/`ChildBnd`/`StartV`; `Bnd` stays in
the conclusion; and, when `f.machine_design_noShipsNoMaskedNR1` exists, the conclusion is `isDefEq` to its (post-processing, rest of
the run implication) with ALL shared binders as fvars (`alignInst`), only the boundary and the `designCheck` antecedent differing.

The pieces of the OLD generated `f.machine_composedNR1` that are REUSED (they mention neither `O` nor the boundary) are extracted by the
BINDER NAMES of the consumer head (`hcalls`) or its instance-implicit binder (the `Inhabited (HList …)` instance), NOT by position, into
declarations with an explicit STATED type: `f.epA_inhab : Inhabited (HList (tys f.machineData.ss))` and
`f.epA_hcalls : ∀ m design, HCallsOf 1 f.machineData design m …` (`HCallsOf` of `Tools/ShippingSeqParentLemmas.lean`).  The
causality fact is not extracted: it is the generated `f.machine_ext_causal` (`HCausalOf` states it).  If the old generator changes shape,
the extraction or the type ascription fails (loudly); it can never silently pick a different term.

No axiom, no new law / field of `RefLawsAOps`, no input guard, no refusal.  `T : RefLawsATele` is the ADDED boundary of the earlier
units; `RealChildA` is a history of past synthesis results.  This is NOT an unconditional semantic-equivalence theorem; not runtime fit. -/
namespace Tools.ShippingSeqParentGen
open Lean Elab Command Meta Term

/-- Replace the placeholders `@F@`, `@C@`, `@KD@` of a template. -/
def subst (s : String) (f c : Name) (kD : Nat) : String :=
  ((s.replace "@F@" f.toString).replace "@C@" c.toString).replace "@KD@" (toString kD)

/-- Parse and elaborate the commands of `src` one after the other, in the current scope. -/
def runCmds (src : String) : CommandElabM Unit := do
  let inputCtx := Parser.mkInputContext src "<seq-parent-gen>"
  let mut pstate : Parser.ModuleParserState := {}
  let mut msgs : MessageLog := {}
  repeat
    let scope ← getScope
    let pmctx : Parser.ParserModuleContext :=
      { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps', msgs') := Parser.parseCommand inputCtx pmctx pstate msgs
    pstate := ps'; msgs := msgs'
    if Parser.isTerminalCommand cmd then break
    if msgs.hasErrors then
      throwError "#machine_seq_parent_endpoint: template parse error: {← msgs.toList.mapM (·.toString)}"
    let msgs0 := (← get).messages
    modify fun s => { s with messages := {} }
    elabCommand cmd
    let ms := (← get).messages
    modify fun s => { s with messages := msgs0 ++ ms }
    if ms.hasErrors then
      let txt := match cmd.getPos?, cmd.getTailPos? with
        | some a, some b => (Substring.Raw.toString ⟨src, a, b⟩).take 400 |>.toString
        | _, _ => ""
      throwError "#machine_seq_parent_endpoint: the generated command failed: {txt}"

/-- Elaborate a closed term given as text. -/
def elabText (stx : String) : TermElabM Expr := do
  let some t := (Parser.runParserCategory (← getEnv) `term stx).toOption | throwError "elabText: parse error in {stx}"
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Read a `Name` back from a (reducible-to-constructors) expression. -/
partial def readName (e : Expr) : MetaM Name := do
  let e ← withDefault (whnf e)
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Lean.Name.anonymous, _ => return .anonymous
  | some ``Lean.Name.str, #[p, s] =>
    let s ← withDefault (whnf s)
    let .lit (.strVal str) := s | throwError "readName: not a string literal {s}"
    return .str (← readName p) str
  | some ``Lean.Name.num, #[p, n] =>
    let some k := (← withDefault (whnf n)).rawNatLit? | throwError "readName: not a numeral"
    return .num (← readName p) k
  | _, _ => throwError "readName: cannot read a Name from {e}"

/-- Read a `List Name` back from an expression by head reduction. -/
partial def readNames (e : Expr) : MetaM (List Name) := do
  let e ← withDefault (whnf e)
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``List.nil, _ => return []
  | some ``List.cons, #[_, h, t] => return (← readName h) :: (← readNames t)
  | _, _ => throwError "readNames: cannot read a list from {e}"

/-- Evaluate a closed `Nat` term by reduction. -/
def reduceNat (e : Expr) : MetaM Nat := do
  let r ← withDefault (reduce e)
  match r.rawNatLit? with
  | some n => return n
  | none =>
    match ← evalNat r with
    | some n => return n
    | none => throwError "reduceNat: not a numeral: {r}"

/-! ## the reused pieces of the old generated `f.machine_composedNR1`, extracted by binder NAME -/

/-- The first (outermost) application of the constant `head` in `e`. -/
def findHeadApp? (e : Expr) (head : Name) : Option Expr :=
  e.find? fun x => x.isApp && x.getAppFn.isConstOf head

/-- The arguments of `app` paired with the binder names / binder infos of the head constant's type. -/
def namedArgs (app : Expr) : MetaM (Array (Name × BinderInfo × Expr)) := do
  let .const nm us := app.getAppFn | throwError "namedArgs: not a constant application"
  let ci ← getConstInfo nm
  let ty := ci.type.instantiateLevelParams ci.levelParams us
  forallTelescope ty fun xs _ => do
    let args := app.getAppArgs
    let mut r := #[]
    for i in [0:min xs.size args.size] do
      let d ← xs[i]!.fvarId!.getDecl
      r := r.push (d.userName, d.binderInfo, args[i]!)
    return r

/-- Run `k` on the lambda-telescope of the value of the old theorem `f.machine_composedNR1`. -/
def withOldValue {α : Type} (f : Name) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let old := f ++ `machine_composedNR1
  let some (.thmInfo ti) := (← getEnv).find? old
    | throwError "#machine_seq_parent_endpoint: {old} not found: run `#machine_design_svNR {f} 1` first"
  lambdaTelescope ti.value k

/-- The consumer head of the old composed theorem (the sequential-call composed head) and its binder-name table. -/
def oldHeadArgs (f : Name) (k : Array Expr → Array (Name × BinderInfo × Expr) → MetaM α) : MetaM α :=
  withOldValue f fun ys body => do
    let some app := findHeadApp? body ``Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN
      | throwError "#machine_seq_parent_endpoint: the old composed theorem of {f} does not end in machine_linkedT_callsRN (outside the class)"
    k ys (← namedArgs app)

/-- Make the first `k` lambda binders explicit. -/
def explicitLams : Nat → Expr → Expr
  | 0, e => e
  | k+1, .lam n t b _ => .lam n t (explicitLams k b) .default
  | _, e => e

/-- Abstract the old binders named in `names` out of `e`; any other free variable is an error. -/
def closeOver (ys : Array Expr) (names : List Name) (e : Expr) (what : String) : MetaM Expr := do
  let mut keep : Array Expr := #[]
  for nm in names do
    for y in ys do
      if (← y.fvarId!.getUserName) == nm then keep := keep.push y
  let r ← mkLambdaFVars keep e
  let r := (List.range keep.size).foldl (fun r _ => r) r
  let r := explicitLams keep.size r
  if r.hasFVar then
    let fv := (Lean.collectFVars {} r).fvarIds
    let nms ← fv.mapM fun x => do return (← x.getUserName).toString
    throwError "#machine_seq_parent_endpoint: the reused piece `{what}` of the old theorem mentions the binders {nms} (outside the class)"
  return r

/-- `old_seqparent% hcalls f` / `old_seqparent% inhab f`: the reused piece, closed over the old binders `m`, `design`. -/
elab "old_seqparent% " kind:ident f:ident : term => do
  let fn := f.getId
  match kind.getId.toString with
  | "hcalls" =>
    oldHeadArgs fn fun ys tbl => do
      let some (_, _, a) := tbl.find? (·.1 == `hcalls) | throwError "no binder `hcalls` in the old head"
      closeOver ys [`m, `design] a "hcalls"
  | "inhab" =>
    oldHeadArgs fn fun ys tbl => do
      let some (_, _, h) := tbl.find? (·.1 == `h) | throwError "no binder `h` in the old head"
      let some tr := findHeadApp? h ``Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA
        | throwError "the old trace is not machine_traceL_of_data_causalRA (outside the class)"
      let inst := (← namedArgs tr).filter (·.2.1 == BinderInfo.instImplicit)
      unless inst.size == 1 do throwError "expected exactly one instance-implicit argument, found {inst.size}"
      closeOver ys [] inst[0]!.2.2 "Inhabited instance"
  | k => throwError "old_seqparent%: unknown kind {k}"

/-! ## the templates -/

def openBlock : String := r#"
section
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingSeqParentLemmas
set_option Elab.async false
set_option maxHeartbeats 4000000
"#

/-- Child-level data (generated once per child). -/
def childTemplate : String := r#"
theorem _root_.@C@.epA_outs_clean :
    ∀ o ∈ @C@.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel
noncomputable def _root_.@C@.epA_nk : Nat :=
  ((@C@.machineData.shape.binders.take (@C@.machineData.shape.binders.length -
    @C@.machineData.shape.layout.slots.length - @C@.machineData.shape.layout.lets)).filter
      fun x => x.2 != .domain).length
"#

def boundaryTemplate : String := r#"
def _root_.@F@.epA_Bnd : CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape ∧
    ∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))

theorem _root_.@F@.epA_insts : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length),
    (@F@.machineData.shape.insts[k]).1 = ``@C@ := by first | decide | decide +kernel

theorem _root_.@F@.epA_outs_clean :
    ∀ o ∈ @F@.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem _root_.@F@.epA_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk @F@.machineData @KD@
      (fun _ => Tools.ShippingPortWidthsPure.declWidths @C@.machineData) = true := by
  first | decide | decide +kernel

theorem _root_.@F@.epA_houtTy : ∀ o ∈ @F@.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem _root_.@F@.epA_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``@F@ @F@.machineData.shape := by
  have hent : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length),
      (@F@.machineData.shape.insts[k]).1 = ``@C@ ∧ ∃ j, j < @F@.machineData.shape.instFields.length ∧ Tools.ShippingInstTagged.originAt @F@.machineData.shape k = .field j := by
    first | decide | decide +kernel
  have hkid : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt @F@.machineData.shape k)
        (@F@.machineData.shape.insts[k]).1 y →
      Tools.ShippingMemCloses.ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``@C@) @C@.epA_nk
        (@C@.machineData.shape.layout.outs.map (·.name)) [] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, j, -, ho⟩ := hent k hk
    rw [ho] at hy
    rcases hy with hy | ⟨-, hre⟩
    · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · rw [hn] at hre
      have hG := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O @C@.machineData @C@.machine_ok
        @C@.machine_body (by decide) (by decide) hR0 (fun mc cc => @C@.machine_closes mc _ cc _) hre
      exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG)
        (fun hx => nomatch hx)
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := @KD@) O T hA @F@.machineData
    @F@.machine_ok @F@.machine_body (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun _ => Sparkle.IR.ModuleName.ofDecl ``@C@) (fun _ => @C@.epA_nk)
    (fun _ => @C@.machineData.shape.layout.outs.map (·.name)) (fun _ => [])
    hkid (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun k hk k' hk' _ => by
      obtain ⟨h1, j, -, h2⟩ := hent k hk
      obtain ⟨h1', j', -, h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (by decide : ``@C@ ≠ ``@F@))
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ @F@.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => nomatch hx)
    (fun k hk k' hk' hne => (hne (by
      obtain ⟨h1, j, -, h2⟩ := hent k hk
      obtain ⟨h1', j', -, h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)).elim)

theorem _root_.@F@.epA_kidsMasked {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``@F@ [] false)
      mctx mref cctx cref w (raw, D) w1)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@F@ @F@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true := by
  have hkidM : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (@F@.machineData.shape.insts[k]).1 y →
      Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true := by
    intro k hk y hy
    rw [@F@.epA_insts k hk] at hy
    exact Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA (nDecl := @C@.machineData.nIn) O @C@.machineData
      @C@.machine_ok @C@.machine_body (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hR0 (fun mc cc => @C@.machine_closes mc _ cc _) hy
  exact Tools.ShippingKidsSelfA.core_kidsMaskedN_topA O hA T @F@.machineData @F@.machine_ok
    @F@.machine_body (nDecl := @KD@) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) hkidM
    hcore entry (@F@.epA_closes O T hA hR0) hw hc hpost

theorem _root_.@F@.epA_runFacts {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``@F@ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``@F@ @F@.machineData.shape)
    (hBnd : @F@.epA_Bnd mctx mref cctx cref w raw D) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b := by
  obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
  have ran := Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (@F@.epA_closes O T hA hR0) hw hc
  have hkidP : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (@F@.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ Tools.ShippingInstStmtG.inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst" := by
    intro k hk y hy
    rw [@F@.epA_insts k hk] at hy
    exact (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O @C@.machineData @C@.machine_ok @C@.machine_body
      (by decide) (by decide) hR0 (fun mc cc => @C@.machine_closes mc _ cc _) hy).outsIn
  have hkidT : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (@F@.machineData.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys @C@.machineData.shape.layout.outs y.1 := by
    intro k hk y hy
    rw [@F@.epA_insts k hk] at hy
    exact Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA (O := O) @C@.machineData @C@.machine_ok @C@.machine_body
      (by decide) (by decide) (by decide) (by decide) hR0
      (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => @C@.machine_closes mctx' _ cctx' _ (Tools.ShippingChildInv.profLogIO b) w r w' hr) hy
  exact Tools.ShippingParentRunFactsA.core_runFacts_ranA (nDecl := @KD@) O @F@.machineData @F@.machine_ok @F@.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) hkidP
    (Tools.ShippingParentRunFactsA.hkidW_of_dataA O
      (kidOuts := fun _ => @C@.machineData.shape.layout.outs)
      (by first | decide | decide +kernel) hkidT)
    hpost ran

theorem _root_.@F@.epA_outsCheck {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design} (n : Nat)
    (hcore : RunsTo (synthesizeCombinationalCore ``@F@ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``@F@ @F@.machineData.shape)
    (hg : hierGate b = true) (hBnd : @F@.epA_Bnd mctx mref cctx cref w raw D) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true := by
  obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
  have ran := Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (@F@.epA_closes O T hA hR0) hw hc
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``@C@ @C@.machineData.shape :=
    fun mc cc => @C@.machine_closes mc _ cc _
  exact Tools.ShippingParentPortsA.core_outsCheck_all_gate_ranA (nDecl := @KD@) O @F@.machineData @F@.machine_ok
    @F@.machine_body (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun k hk y hy => by
      rw [@F@.epA_insts k hk] at hy
      exact Tools.ShippingParentRunFactsA.leaf_real_kidAA O @C@.machineData @C@.machine_ok @C@.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0 hcl hy)
    (fun k hk y hy => by
      rw [@F@.epA_insts k hk] at hy
      exact Tools.ShippingParentRunFactsA.leaf_real_kidRA O @C@.machineData @C@.machine_ok @C@.machine_body
        (by decide) (by decide) hR0 hcl hy)
    hpost ran hg n

theorem _root_.@F@.epA_designCheck {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design} (n : Nat)
    (hcore : RunsTo (synthesizeCombinationalCore ``@F@ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``@F@ @F@.machineData.shape)
    (hBnd : @F@.epA_Bnd mctx mref cctx cref w raw D) :
    designCheck (childMap D.modules) n (checkedOptimize b) = true := by
  obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
  have ran := Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (@F@.epA_closes O T hA hR0) hw hc
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``@C@ @C@.machineData.shape :=
    fun mc cc => @C@.machine_closes mc _ cc _
  have hon : ∀ o ∈ @C@.machineData.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
    fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (@C@.epA_outs_clean o ho)
  have hkidP : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (@F@.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ Tools.ShippingInstStmtG.inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst" := by
    intro k hk y hy
    rw [@F@.epA_insts k hk] at hy
    exact (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O @C@.machineData @C@.machine_ok @C@.machine_body
      (by decide) (by decide) hR0 (fun mc cc => @C@.machine_closes mc _ cc _) hy).outsIn
  have hkidT : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (@F@.machineData.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys @C@.machineData.shape.layout.outs y.1 := by
    intro k hk y hy
    rw [@F@.epA_insts k hk] at hy
    exact Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA (O := O) @C@.machineData @C@.machine_ok @C@.machine_body
      (by decide) (by decide) (by decide) (by decide) hR0
      (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => @C@.machine_closes mctx' _ cctx' _ (Tools.ShippingChildInv.profLogIO b) w r w' hr) hy
  exact Tools.ShippingParentDesignFA.core_designCheck_ranFA (nDecl := @KD@) O @F@.machineData @F@.machine_ok
    @F@.machine_body (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) hkidP
    (Tools.ShippingParentRunFactsA.hkidW_of_dataA O
      (kidOuts := fun _ => @C@.machineData.shape.layout.outs)
      (by first | decide | decide +kernel) hkidT)
    (fun k hk y hy => by
      rw [@F@.epA_insts k hk] at hy
      exact Tools.ShippingParentDesignFA.leaf_real_portsInA O @C@.machineData @C@.machine_ok @C@.machine_body
        (nDecl := @C@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hon (by decide) hy)
    (kidIns := fun _ => Tools.ShippingPortWidthsPure.declWidths @C@.machineData) @F@.epA_callArgs
    (fun k hk y hy j q hq => by
      rw [@F@.epA_insts k hk] at hy
      exact Tools.ShippingParentDesignFA.leaf_real_inWidthsA O @C@.machineData @C@.machine_ok
        @C@.machine_body (nDecl := @C@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy j q hq)
    (fun k hk y hy => by
      rw [@F@.epA_insts k hk] at hy
      exact Tools.ShippingParentDesignFA.leaf_real_clkA O @C@.machineData @C@.machine_ok @C@.machine_body
        (nDecl := @C@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy)
    (fun k hk y hy => by
      rw [@F@.epA_insts k hk] at hy
      exact Tools.ShippingParentDesignFA.leaf_real_kidK_regA O @C@.machineData @C@.machine_ok @C@.machine_body
        (nDecl := @C@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) (by decide) hR0 hcl hon (by decide) hy)
    hpost ran
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (@F@.epA_outs_clean o ho))
    (by decide) n
"#

/-- The reused old pieces and the new-boundary trace / `soundL` / `composed` (depth 1). -/
def composedTemplate : String := r#"
instance _root_.@F@.epA_inhab : Inhabited (HList (Tools.ShippingMachineDenote.tys @F@.machineData.ss)) :=
  old_seqparent% inhab @F@

theorem _root_.@F@.epA_hcausal : HCausalOf @F@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
    @F@.machineExt @F@.machineExtB := fun i bools bits S S' t h =>
  @F@.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
    (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)

theorem _root_.@F@.epA_hcalls (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 @F@.machineData design m (dom := fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      (Tools.ShippingMachineCausal.letObsB @F@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @F@.machineInits
        @F@.machineBody @F@.machineExt @F@.machineExtB)
      (fun i bools bits => @F@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @F@.machineInits (@F@.machineBody i bools bits)))
      (fun i bools bits => @F@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @F@.machineInits (@F@.machineBody i bools bits)))
      @KD@
      (fun n => if n = ``@C@ then @C@.machineData.bsIn else [])
      (fun n => if n = ``@C@ then @C@.machineData.shape.layout.outs else [])
      (fun i n => if n = ``@C@ then fun vals =>
          @C@.machineSource Sparkle.Core.Domain.defaultDomain
            (Tools.ShippingMachineChild.boolsOf @C@.machineData.bsIn vals)
            (Tools.ShippingMachineChild.bitsOf @C@.machineData.bsIn vals)
        else fun vals => [])
      (fun n => if n = ``@C@ then fun mc => Tools.ShippingGateChild.MachineRun ``@C@ @C@.machineData.shape mc
        else fun mc => Tools.ShippingGateChild.MachineRun ``@C@ @C@.machineData.shape mc) :=
  (old_seqparent% hcalls @F@) m design

theorem _root_.@F@.epA_traceX {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``@F@ [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``@F@ @F@.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (Tools.ShippingServedRealA.ServedRealA O ``@F@ @F@.machineData.shape m design)
      ``@F@ @F@.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @F@.machineSource
      (fun i bools bits => @F@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @F@.machineInits (@F@.machineBody i bools bits)))
      (fun i bools bits => @F@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @F@.machineInits (@F@.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB @F@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @F@.machineInits
        @F@.machineBody @F@.machineExt @F@.machineExtB) :=
  Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA @F@.machineData
    (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @F@.machineInits @F@.machineBody @F@.machineResult
    @F@.machineExt @F@.machineExtB @F@.machineSource @F@.machine_ok @F@.machine_body @F@.machine_inits
    @F@.machine_writes @F@.machine_result @F@.machine_source @F@.epA_hcausal
    O (Tools.ShippingChildComposeC.bodyStepC_of_tele O T) hA (n := D₀ + 1)
    (Tools.ShippingChildRunAMain.htr_of_tele O hA T D₀) (m := m) (design := design)
    (Tools.ShippingServedRealA.machineRunJQC_of_closesA O hA hcore entry (@F@.epA_closes O T hA hR0) hw hc)

theorem _root_.@F@.epA_soundLA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``@F@ [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``@F@ @F@.machineData.shape)
    (hBnd : @F@.epA_Bnd mctx mref cctx cref w m design) :
    MachineTraceLB ``@F@ @F@.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      @F@.machineSource
      (fun i bools bits => @F@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @F@.machineInits (@F@.machineBody i bools bits)))
      (fun i bools bits => @F@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @F@.machineInits (@F@.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB @F@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @F@.machineInits
        @F@.machineBody @F@.machineExt @F@.machineExtB) := by
  obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, -, tr⟩ :=
    @F@.epA_traceX O T hA hR0 hw hc hcore entry
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

theorem _root_.@F@.epA_composedA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``@F@ [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``@F@ @F@.machineData.shape)
    (hBnd : @F@.epA_Bnd mctx mref cctx cref w m design) :
    ComposedG (fun D => KSn (childMap D.modules) 1) (ResetNk 1) ``@F@ @F@.machineData @KD@ m design
      (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @F@.machineSource
      (fun i bools bits => @F@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @F@.machineInits (@F@.machineBody i bools bits)))
      (fun i bools bits => @F@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @F@.machineInits (@F@.machineBody i bools bits))) := by
  obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
  have h := @F@.epA_traceX O T hA hR0 hw hc hcore entry
  refine Tools.ShippingMachineShipsDepth.composedG_of_NW ?_
  exact Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA 1 O h (by decide) @KD@ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun n => if n = ``@C@ then @C@.machineData.bsIn else [])
    (fun n => if n = ``@C@ then @C@.machineData.shape.layout.outs else [])
    (fun i n => if n = ``@C@ then fun vals =>
        @C@.machineSource Sparkle.Core.Domain.defaultDomain
          (Tools.ShippingMachineChild.boolsOf @C@.machineData.bsIn vals)
          (Tools.ShippingMachineChild.bitsOf @C@.machineData.bsIn vals)
      else fun vals => [])
    (fun n => if n = ``@C@ then fun mc => Tools.ShippingGateChild.MachineRun ``@C@ @C@.machineData.shape mc
      else fun mc => Tools.ShippingGateChild.MachineRun ``@C@ @C@.machineData.shape mc)
    (@F@.epA_hcalls m design)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < @F@.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``@C@ := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact @F@.epA_insts k hk
      subst hck
      have hmr : Tools.ShippingGateChild.MachineRun ``@C@ @C@.machineData.shape mc :=
        ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR0,
          @C@.machine_closes mctx' _ cctx' _⟩
      split <;> exact hmr)
"#

/-- The term of the endpoint: `machine_design_noShips_noBd_dc` at `n := 1`, `C := True`, applied to the generated pieces. -/
def endpointTerm : String := r#"(@Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc 1 @F@.epA_Bnd (fun _ _ _ _ => True) _
    @F@.machineData @KD@ Unit (fun _ => Sparkle.Core.Domain.defaultDomain) _ _ _ _ _ _ _
    (fun hcore entry _ hBnd => @F@.epA_soundLA hcore entry hBnd)
    (fun hcore entry _ hBnd _ => @F@.epA_composedA hcore entry hBnd)
    @F@.epA_houtTy
    (fun hc hp e hB => @F@.epA_runFacts hc hp e hB)
    (fun hc hp e hg hB => @F@.epA_outsCheck 1 hc hp e hg hB)
    (fun hc hp e hB => by
      obtain ⟨O, T, hA, hR0, D₀, hw, hc'⟩ := hB
      exact @F@.epA_kidsMasked O T hA hc e hR0 hw hc' hp)
    (fun hc hp e hB => @F@.epA_designCheck 1 hc hp e hB))"#

/-! ## audits -/

open Tests.Compiler.ChildVertAuditTest in
/-- `alignInst` of unit SR3e (copied): instantiate the binders of `ty`; a binder whose name matches a `shared` fvar AND whose domain is
`isDefEq` to that fvar's type is instantiated by THAT FVAR; a binder named in `gen` becomes a metavariable; any other binder a fresh fvar. -/
partial def alignInst {α : Type} (shared : Array Expr) (gen : List String) (ty : Expr)
    (k : Expr → Array String → Array String → Array (String × Expr) → MetaM α)
    (al fr : Array String := #[]) (ms : Array (String × Expr) := #[]) : MetaM α := do
  match ty with
  | .forallE n d b bi =>
    let mut hit : Option Expr := none
    for x in shared do
      if hit.isNone && (← x.fvarId!.getUserName) == n then
        if ← isDefEq d (← inferType x) then hit := some x
    match hit with
    | some x => alignInst shared gen (b.instantiate1 x) k (al.push n.toString) fr ms
    | none =>
      if gen.contains n.toString then
        let m ← mkFreshExprMVar d
        alignInst shared gen (b.instantiate1 m) k al fr (ms.push (n.toString, m))
      else
        withLocalDecl n bi d fun x => alignInst shared gen (b.instantiate1 x) k al (fr.push n.toString) ms
  | _ => k ty al fr ms

/-- Split `∃ raw D, hp ∧ (dc → B → rest)` into `(hp, dc, B, rest)` over shared `raw D` (old endpoint). -/
def splitOld (e raw D : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let e ← whnfR e
  unless e.getAppFn.isConstOf ``Exists do throwError "not ∃: {e}"
  let e1 := (e.appArg!.bindingBody!).instantiate1 raw
  unless e1.getAppFn.isConstOf ``Exists do throwError "not ∃ (2): {e1}"
  let e2 := (e1.appArg!.bindingBody!).instantiate1 D
  let hp := e2.appFn!.appArg!
  let .forallE _ dc b1 _ := e2.appArg! | throwError "no dc"
  let .forallE _ B rest _ := b1 | throwError "no B"
  return (hp, dc, B, rest)

/-- Split `∃ raw D, hp ∧ (B → rest)` into `(hp, B, rest)` (new endpoint, no `designCheck` antecedent). -/
def splitNew (e raw D : Expr) : MetaM (Expr × Expr × Expr) := do
  let e ← whnfR e
  unless e.getAppFn.isConstOf ``Exists do throwError "not ∃: {e}"
  let e1 := (e.appArg!.bindingBody!).instantiate1 raw
  unless e1.getAppFn.isConstOf ``Exists do throwError "not ∃ (2): {e1}"
  let e2 := (e1.appArg!.bindingBody!).instantiate1 D
  let hp := e2.appFn!.appArg!
  let .forallE _ B rest _ := e2.appArg! | throwError "no B"
  return (hp, B, rest)

open Tests.Compiler.ChildVertAuditTest in
/-- The in-command audit of the generated endpoint `ep` of `f` (calls `throwError` on failure). -/
def auditEndpoint (f ep : Name) : MetaM Unit := do
  stdAxioms ep
  for s in [`epA_closes, `epA_kidsMasked, `epA_runFacts, `epA_outsCheck, `epA_designCheck, `epA_houtTy, `epA_traceX,
      `epA_soundLA, `epA_composedA, `epA_hcalls, `epA_hcausal, `epA_insts] do
    stdAxioms (f ++ s)
  let ty := (← getConstInfo ep).type
  -- (1) the outer Prop premises are exactly hr, entry, closes : True
  let premises ← forallTelescope ty fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← inferType x
      if (← isProp t) then ps := ps.push s!"{(← x.fvarId!.getUserName)} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let expected := ["hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines", "closes : True"]
  unless premises.toList == expected do
    throwError "SR3i AUDIT FAILED: {ep}: outer Prop premises are {premises}, expected {expected}"
  forallTelescope ty fun xs _ => do
    let some c := xs.back? | throwError "no binder"
    unless (← whnf (← inferType c)).isConstOf ``True do throwError "SR3i AUDIT FAILED: closes is not True"
  -- (2) closure
  let cl ← depClosure ep
  let bad := hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR3i AUDIT FAILED: {ep}: old boundary in closure: {bad}"
  for must in [``Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc,
      ``Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA,
      ``Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA,
      ``Tools.ShippingParentRanA.machineRanA_main, ``Tools.ShippingMachineShipsDepth.composedG_of_NW,
      ``Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_ranA,
      ``Tools.ShippingServedRealA.machineRunJQC_of_closesA, ``Tools.ShippingParentDesignFA.core_designCheck_ranFA,
      ``Tools.ShippingParentRunFactsA.core_runFacts_ranA, ``Tools.ShippingParentPortsA.core_outsCheck_all_gate_ranA,
      ``Tools.ShippingKidsSelfA.core_kidsMaskedN_topA, ``Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA,
      ``Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids'] do
    unless cl.contains must do throwError "SR3i AUDIT FAILED: {ep}: {must} not in the closure"
  unless cl.contains (f ++ `epA_Bnd) do throwError "SR3i AUDIT FAILED: epA_Bnd not in the closure"
  -- (3) the boundary stays in the conclusion
  let (_, concl) ← forallTelescope ty fun _ c => pure ((), c)
  unless (concl.find? (·.isConstOf (f ++ `epA_Bnd))).isSome do
    throwError "SR3i AUDIT FAILED: {f ++ `epA_Bnd} not in the conclusion"
  -- (4) conclusion vs the OLD endpoint, when it exists
  let old := f ++ `machine_design_noShipsNoMaskedNR1
  if (← getEnv).contains old then
    forallTelescope ty fun newXs newC => do
      alignInst newXs ["kD", "n", "ι", "dom", "src", "ext", "extB", "C"] (← getConstInfo old).type (fun co al fr ms => do
        withLocalDeclD `raw (mkConst ``Sparkle.IR.AST.Module) fun raw =>
        withLocalDeclD `D (mkConst ``Sparkle.IR.AST.Design) fun D => do
          -- the ONLY old binder left unaligned is the old `closes` premise (over the generalised `C`); the new one is `closes : True`
          unless fr == #["closes"] do
            throwError "SR3j AUDIT FAILED: {ep}: unaligned binders of {old} remaining as fresh fvars are {fr}, expected exactly #[closes]"
          -- the aligned shared binders are exactly these, in this order (asserted, not only logged)
          unless al.toList == ["mctx", "mref", "cctx", "cref", "w", "w'", "b", "design", "hr", "entry"] do
            throwError "SR3j AUDIT FAILED: {ep}: aligned shared binders with {old} are {al}, expected exactly [mctx, mref, cctx, cref, w, w', b, design, hr, entry]"
          let mut alT : Array String := #[]
          for n in al do
            let some x ← newXs.findM? (fun x => do pure ((← x.fvarId!.getUserName).toString == n))
              | throwError "SR3j AUDIT FAILED: aligned binder {n} not among the new theorem's binders"
            alT := alT.push s!"{n} : {← ppExpr (← inferType x)}"
          logInfo m!"SR3j aligned shared arguments of {ep} with {old} ({al.size}): {alT}"
          let (hpO, dcO, _BO, restO) ← splitOld co raw D
          let (hpN, _BN, restN) ← splitNew newC raw D
          unless (dcO.find? (·.isConstOf ``Tools.ShippingDesignSV.designCheck)).isSome do
            throwError "SR3i AUDIT FAILED: old antecedent is not designCheck"
          let ok1 ← isDefEq hpN hpO
          let ok3 ← isDefEq restN restO
          unless ok1 && ok3 do
            throwError "SR3i AUDIT FAILED: conclusion differs from {old}'s (post {ok1}, rest {ok3})"
          for e in [hpN, hpO, restN, restO] ++ ms.toList.map (·.2) do
            if (← instantiateMVars e).hasMVar then
              throwError "SR3j AUDIT FAILED: {ep}: unresolved metavariables after the conclusion comparison in {← ppExpr (← instantiateMVars e)}"
          let mut sol : Array String := #[]
          for (nm, m) in ms do
            let v ← instantiateMVars m
            sol := sol.push s!"{nm} := {← ppExpr v}"
          logInfo m!"SR3i CONCLUSION CHECK OK: {ep} agrees with {old} on post-processing and the body of the run implication (shared binders {al} as fvars of the NEW theorem; generalised parameters of the old, solved: {sol}); the boundary and the `designCheck` antecedent differ")
  else
    logInfo m!"SR3i: {old} not present: conclusion comparison with the old endpoint skipped"
  logInfo m!"SR3i AUDIT OK: {ep}: standard axioms; outer Prop premises ASSERTED {premises}; closure {cl.size} constants, none of RefLaws/RefLawsCore/toAOps/toA/ChildBnd/StartV; {f ++ `epA_Bnd} (an EXISTENTIAL over O/T/AdmCtx/MachineDefines child/start world, not a proof that it holds) stays in the conclusion; soundL, composed, houtTy, hFacts, hOuts, kidsMasked, designCheck are PROVED inside, not premises"

/-! ## the command -/

/-- `#machine_seq_parent_endpoint f`: generate `f.epA_*` and the endpoint `f.epA_endpoint` (depth 1; class: see the module header). -/
elab "#machine_seq_parent_endpoint " f:ident : command => do
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  for s in [`machineData, `machine_ok, `machine_body, `machine_inits, `machine_writes, `machine_result, `machine_source,
      `machine_ext_causal, `machine_composedNR1, `machineSource, `machineInits, `machineBody, `machineResult, `machineExt,
      `machineExtB] do
    unless (← getEnv).contains (fn ++ s) do
      throwError "#machine_seq_parent_endpoint: {fn ++ s} not found (the class needs `#machine_design_svNR {fn} 1` first)"
  let callees ← liftTermElabM do
    readNames (← elabText (subst "(@F@.machineData.shape.insts.map (·.1))" fn .anonymous 0))
  let some c := callees.head? | throwError "#machine_seq_parent_endpoint: {fn} has no call instance (outside the class)"
  unless callees.all (· == c) do
    throwError "#machine_seq_parent_endpoint: {fn} calls several declarations {callees}: the class has ONE child declaration"
  for s in [`machineData, `machine_ok, `machine_body, `machine_closes, `machineSource] do
    unless (← getEnv).contains (c ++ s) do throwError "#machine_seq_parent_endpoint: {c ++ s} not found (child {c} must be a generated machine)"
  let kD ← liftTermElabM do
    reduceNat (← elabText (subst "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)" fn .anonymous 0))
  let sub := fun s => subst s fn c kD
  let childPart := if (← getEnv).contains (c ++ `epA_nk) then "" else sub childTemplate
  let src := sub openBlock ++ childPart ++ sub boundaryTemplate ++ sub composedTemplate
  try
    runCmds src
  catch e =>
    try runCmds "end" catch _ => pure ()
    throw e
  -- the endpoint: the inferred type of the term
  let ep := fn ++ `epA_endpoint
  try
    liftTermElabM do
      let some stx := (Parser.runParserCategory (← getEnv) `term (sub endpointTerm)).toOption
        | throwError "endpoint term: parse error"
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let ty ← instantiateMVars (← inferType e)
      if e.hasMVar || ty.hasMVar then throwError "#machine_seq_parent_endpoint: unassigned mvars in the endpoint term"
      addAndCompile <| .thmDecl { name := ep, levelParams := [], type := ty, value := e }
    liftTermElabM <| auditEndpoint fn ep
  finally
    runCmds "end"

end Tools.ShippingSeqParentGen
