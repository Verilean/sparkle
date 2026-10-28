import Tools.ShippingSeqParentLemmas
import Tools.ShippingChecksMaskedLeafA
import Tools.ShippingKidsSelfA
import Tools.ShippingCallsMemPinned
import Tools.ShippingParentRunFactsA
import Tools.ShippingParentDesignFA
import Tools.ShippingParentSeqComposedA
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit SR3l): only the depth > 1 refusal (message, checked before the other existence checks) changed: Tests.Compiler.SeqParentGenTest l5 exit 0.
-- BUILT (unit SR3k): several DIFFERENT leaf children: `qbuild build Tools.ShippingSeqParentGen` exit 0; `qbuild build Tests.Compiler.SeqParentGenTest` k2-k4 exit 1 (template fixes: `epA_nm` noncomputable, `nomatch` parenthesised, hcl/hon haves layout, test counts instances per (call, field)), k5 exit 0, k6 exit 0 (with the old `#machine_no_ships_masked two 1` for the conclusion comparison).
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
* every call instance of `f` (`f.machineData.shape.insts`; one per (call, used output field)) calls one of SEVERAL (unit SR3k: any
  number of) DISTINCT child declarations `c₀ … cₘ₋₁` (order of first call; any number of calls, calls whose arguments are other
  calls' fields included), each a *sequential leaf register machine* with `c.machineData`, `c.machine_closes`,
  `c.machine_leafKid`-level facts (each `c` itself has no instances: otherwise the command fails, depth > 1).  The map call position
  `k` ↦ child is the generated `f.epA_nm k` (`= (insts.map (·.1)).getD k _`, `f.epA_nm_eq`), every child-keyed datum of the closing /
  the checks (`epA_nameK/nkK/outsK/insK k`) is looked up by it and the equation to child `j`'s OWN data is the generated
  `f.epA_K_j`; `f.epA_Bnd` states `MachineDefines` for EACH distinct child (`m` conjuncts; one when all calls are of one child);
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
set_option linter.unusedSimpArgs false
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

/-! ### the per-parent text assembled from the list of DISTINCT child declarations `cs` (in order of first call) -/

/-- Replace `@C@` / `@J@` of a per-child snippet. -/
def childText (s : String) (c : Name) (j : Nat) : String :=
  (s.replace "@C@" c.toString).replace "@J@" (toString j)

/-- Indent every line but the first by `n` spaces. -/
def indentBy (n : Nat) (s : String) : String := s.replace "\n" ("\n" ++ "".pushn ' ' n)

/-- `if n = ``c0 then (g c0) else if n = ``c1 then (g c1) else dflt`. -/
def chain (cs : List Name) (g : Name → String) (dflt : String) : String :=
  cs.foldr (fun c acc => s!"if n = ``{c} then {g c} else {acc}") dflt

/-- `if ``cj = ``c0` ... rewrites that select the child `j` in a `chain` over `cs`. -/
def ifRed (cs : List Name) (j : Nat) : String :=
  let negs := ((cs.take j).map fun ci => s!"if_neg (show (``{cs[j]!} ≠ ``{ci}) by decide)")
  "rw [" ++ ", ".intercalate (negs ++ ["if_pos rfl"]) ++ "]"

/-- The per-child case split used inside the parent proofs: `k hk y hy` in scope, `hy : RealChildA O (insts[k]).1 y`.  The snippet
`body` (placeholders `@C@`, `@J@`) is run in each case, after the goal's child-keyed functions were rewritten. -/
def disp (cs : List Name) (body : String) : String :=
  let pat := " | ".intercalate (cs.map fun _ => "h")
  let cases := (cs.zipIdx).map fun (c, j) =>
    "· " ++ indentBy 2 (childText ("rw [h] at hy\nobtain ⟨e1, e2, e3, e4⟩ := @F@.epA_K_@J@ k hk h\ntry simp only [e1, e2, e3, e4]\n" ++ body) c j)
  "rcases @F@.epA_mem k hk with " ++ pat ++ "\n" ++ "\n".intercalate cases

/-- The per-parent snippets: `(marker, indentation of the marker line, body)`. -/
def dispBodies : List (String × Nat × String) :=
  [("kid", 6, "exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD
    (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O @C@.machineData @C@.machine_ok
      @C@.machine_body (by decide) (by decide) hR@J@ (fun mc cc => @C@.machine_closes mc _ cc _) hy))
  (fun hx => nomatch hx)"),
   ("kidM", 4, "exact Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA (nDecl := @C@.machineData.nIn) O @C@.machineData
  @C@.machine_ok @C@.machine_body (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  hR@J@ (fun mc cc => @C@.machine_closes mc _ cc _) hy"),
   ("kidP", 4, "exact (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O @C@.machineData @C@.machine_ok @C@.machine_body
  (by decide) (by decide) hR@J@ (fun mc cc => @C@.machine_closes mc _ cc _) hy).outsIn"),
   ("kidT", 4, "exact Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA (O := O) @C@.machineData @C@.machine_ok @C@.machine_body
  (by decide) (by decide) (by decide) (by decide) hR@J@
  (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => @C@.machine_closes mctx' _ cctx' _ (Tools.ShippingChildInv.profLogIO b) w r w' hr) hy"),
   ("kidAA", 6, "exact Tools.ShippingParentRunFactsA.leaf_real_kidAA O @C@.machineData @C@.machine_ok @C@.machine_body
  (by decide) (by decide) (by decide) (by decide) hR@J@ hcl@J@ hy"),
   ("kidRA", 6, "exact Tools.ShippingParentRunFactsA.leaf_real_kidRA O @C@.machineData @C@.machine_ok @C@.machine_body
  (by decide) (by decide) hR@J@ hcl@J@ hy"),
   ("portsIn", 6, "exact Tools.ShippingParentDesignFA.leaf_real_portsInA O @C@.machineData @C@.machine_ok @C@.machine_body
  (nDecl := @C@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR@J@ hcl@J@ hon@J@ (by decide) hy"),
   ("inW", 6, "exact Tools.ShippingParentDesignFA.leaf_real_inWidthsA O @C@.machineData @C@.machine_ok
  @C@.machine_body (nDecl := @C@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR@J@ hcl@J@ hy j q hq"),
   ("clk", 6, "exact Tools.ShippingParentDesignFA.leaf_real_clkA O @C@.machineData @C@.machine_ok @C@.machine_body
  (nDecl := @C@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR@J@ hcl@J@ hy"),
   ("kidK", 6, "exact Tools.ShippingParentDesignFA.leaf_real_kidK_regA O @C@.machineData @C@.machine_ok @C@.machine_body
  (nDecl := @C@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) (by decide) hR@J@ hcl@J@ hon@J@ (by decide) hy")]

def boundaryTemplate : String := r#"
def _root_.@F@.epA_Bnd : CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    @BNDDEFS@
    ∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))

/-- The callee of instance `k` (the child declaration). -/
noncomputable def _root_.@F@.epA_nm (k : Nat) : Name := (@F@.machineData.shape.insts.map (·.1)).getD k Lean.Name.anonymous

theorem _root_.@F@.epA_nm_eq : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length),
    @F@.epA_nm k = (@F@.machineData.shape.insts[k]).1 := by
  first | decide | decide +kernel | (intro k hk; simp [@F@.epA_nm, List.getD_eq_getElem?_getD, hk])

/-- Every call instance calls one of the (distinct) child declarations. -/
theorem _root_.@F@.epA_mem : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length),
    @MEMDISJ@ := by first | decide | decide +kernel

theorem _root_.@F@.epA_notF : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length),
    (@F@.machineData.shape.insts[k]).1 ≠ ``@F@ := by first | decide | decide +kernel

/-- The child-keyed data of the closing / of the checks, as functions of the callee name. -/
noncomputable def _root_.@F@.epA_nkOf (n : Name) : Nat := @NKCH@
noncomputable def _root_.@F@.epA_outsOf (n : Name) := @OUTSCH@
noncomputable def _root_.@F@.epA_insOf (n : Name) := @INSCH@
noncomputable def _root_.@F@.epA_nameK (k : Nat) : String := Sparkle.IR.ModuleName.ofDecl (@F@.epA_nm k)
noncomputable def _root_.@F@.epA_nkK (k : Nat) : Nat := @F@.epA_nkOf (@F@.epA_nm k)
noncomputable def _root_.@F@.epA_outsK (k : Nat) := @F@.epA_outsOf (@F@.epA_nm k)
noncomputable def _root_.@F@.epA_insK (k : Nat) := @F@.epA_insOf (@F@.epA_nm k)

@KLEMMAS@

theorem _root_.@F@.epA_outs_clean :
    ∀ o ∈ @F@.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem _root_.@F@.epA_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk @F@.machineData @KD@ @F@.epA_insK = true := by
  first | decide | decide +kernel

theorem _root_.@F@.epA_houtTy : ∀ o ∈ @F@.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem _root_.@F@.epA_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    @HRB@ :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``@F@ @F@.machineData.shape := by
  have hent : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length),
      ∃ j, j < @F@.machineData.shape.instFields.length ∧ Tools.ShippingInstTagged.originAt @F@.machineData.shape k = .field j := by
    first | decide | decide +kernel
  have hkid : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt @F@.machineData.shape k)
        (@F@.machineData.shape.insts[k]).1 y →
      Tools.ShippingMemCloses.ChildIfaceP (@F@.epA_nameK k) (@F@.epA_nkK k)
        ((@F@.epA_outsK k).map (·.name)) [] y.1 y.2 := by
    intro k hk y hy0
    obtain ⟨j, -, ho⟩ := hent k hk
    rw [ho] at hy0
    rcases hy0 with hy0 | ⟨-, hy⟩
    · exact absurd hy0 (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · @D_kid@
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := @KD@) O T hA @F@.machineData
    @F@.machine_ok @F@.machine_body (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    @F@.epA_nameK @F@.epA_nkK
    (fun k => (@F@.epA_outsK k).map (·.name)) (fun _ => [])
    hkid (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun k hk k' hk' hn => by
      obtain ⟨j, -, h2⟩ := hent k hk
      obtain ⟨j', -, h2'⟩ := hent k' hk'
      refine ⟨?_, by rw [h2, h2'] <;> rfl⟩
      have h3 := Tools.ShippingModuleName.ofDecl_injective (a := @F@.epA_nm k) (b := @F@.epA_nm k') hn
      rw [@F@.epA_nm_eq k hk, @F@.epA_nm_eq k' hk'] at h3
      exact h3)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (by rw [@F@.epA_nm_eq k hk]; exact @F@.epA_notF k hk))
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ @F@.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => nomatch hx)
    (fun k hk k' hk' _ => ⟨fun hx => (nomatch hx), fun x hx => (nomatch hx)⟩)

theorem _root_.@F@.epA_kidsMasked {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``@F@ [] false)
      mctx mref cctx cref w (raw, D) w1)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@F@ @F@.machineData.shape)
    @HRB@
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true := by
  have hkidM : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (@F@.machineData.shape.insts[k]).1 y →
      Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true := by
    intro k hk y hy
    @D_kidM@
  exact Tools.ShippingKidsSelfA.core_kidsMaskedN_topA O hA T @F@.machineData @F@.machine_ok
    @F@.machine_body (nDecl := @KD@) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) hkidM
    hcore entry (@F@.epA_closes O T hA @HRA@) hw hc hpost

theorem _root_.@F@.epA_runFacts {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``@F@ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref ``@F@ @F@.machineData.shape)
    (hBnd : @F@.epA_Bnd mctx mref cctx cref w raw D) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b := by
  obtain ⟨O, T, hA, @HRP@, D₀, hw, hc⟩ := hBnd
  have ran := Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (@F@.epA_closes O T hA @HRA@) hw hc
  have hkidP : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (@F@.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ Tools.ShippingInstStmtG.inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst" := by
    intro k hk y hy
    @D_kidP@
  have hkidT : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (@F@.machineData.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (@F@.epA_outsK k) y.1 := by
    intro k hk y hy
    @D_kidT@
  exact Tools.ShippingParentRunFactsA.core_runFacts_ranA (nDecl := @KD@) O @F@.machineData @F@.machine_ok @F@.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) hkidP
    (Tools.ShippingParentRunFactsA.hkidW_of_dataA O
      (kidOuts := @F@.epA_outsK)
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
  obtain ⟨O, T, hA, @HRP@, D₀, hw, hc⟩ := hBnd
  have ran := Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (@F@.epA_closes O T hA @HRA@) hw hc
  @CLHAVES@
  exact Tools.ShippingParentPortsA.core_outsCheck_all_gate_ranA (nDecl := @KD@) O @F@.machineData @F@.machine_ok
    @F@.machine_body (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun k hk y hy => by
      @D_kidAA@)
    (fun k hk y hy => by
      @D_kidRA@)
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
  obtain ⟨O, T, hA, @HRP@, D₀, hw, hc⟩ := hBnd
  have ran := Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (@F@.epA_closes O T hA @HRA@) hw hc
  @CLHAVES@
  @HONHAVES@
  have hkidP : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (@F@.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ Tools.ShippingInstStmtG.inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst" := by
    intro k hk y hy
    @D_kidP@
  have hkidT : ∀ (k : Nat) (hk : k < @F@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      RealChildA O (@F@.machineData.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (@F@.epA_outsK k) y.1 := by
    intro k hk y hy
    @D_kidT@
  exact Tools.ShippingParentDesignFA.core_designCheck_ranFA (nDecl := @KD@) O @F@.machineData @F@.machine_ok
    @F@.machine_body (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) hkidP
    (Tools.ShippingParentRunFactsA.hkidW_of_dataA O
      (kidOuts := @F@.epA_outsK)
      (by first | decide | decide +kernel) hkidT)
    (fun k hk y hy => by
      @D_portsIn@)
    (kidIns := @F@.epA_insK) @F@.epA_callArgs
    (fun k hk y hy j q hq => by
      @D_inW@)
    (fun k hk y hy => by
      @D_clk@)
    (fun k hk y hy => by
      @D_kidK@)
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
      (@BSC@)
      (@OUTSC@)
      (@SC@)
      (@RUNC@) :=
  (old_seqparent% hcalls @F@) m design

theorem _root_.@F@.epA_traceX {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    @HRB@
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
    (Tools.ShippingServedRealA.machineRunJQC_of_closesA O hA hcore entry (@F@.epA_closes O T hA @HRA@) hw hc)

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
  obtain ⟨O, T, hA, @HRP@, D₀, hw, hc⟩ := hBnd
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, -, tr⟩ :=
    @F@.epA_traceX O T hA @HRA@ hw hc hcore entry
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
  obtain ⟨O, T, hA, @HRP@, D₀, hw, hc⟩ := hBnd
  have h := @F@.epA_traceX O T hA @HRA@ hw hc hcore entry
  refine Tools.ShippingMachineShipsDepth.composedG_of_NW ?_
  exact Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA 1 O h (by decide) @KD@ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (@BSC@)
    (@OUTSC@)
    (@SC@)
    (@RUNC@)
    (@F@.epA_hcalls m design)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < @F@.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = (@F@.machineData.shape.insts[k]).1 := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        exact (Option.some.inj hc').symm
      rcases @F@.epA_mem k hk with @MPAT@
      @CASES@)
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
      obtain ⟨O, T, hA, @HRP@, D₀, hw, hc'⟩ := hB
      exact @F@.epA_kidsMasked O T hA hc e @HRA@ hw hc' hp)
    (fun hc hp e hB => @F@.epA_designCheck 1 hc hp e hB))"#


/-- The text of one parent: all placeholders replaced, for the DISTINCT child declarations `cs` (in order of first call). -/
def assemble (f : Name) (cs : List Name) (kD : Nat) : String := Id.run do
  let idx := cs.zipIdx
  let hrb := " ".intercalate (idx.map fun (c, j) => childText
    "(hR@J@ : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)" c j)
  let hra := " ".intercalate (idx.map fun (_, j) => s!"hR{j}")
  let hrp := ", ".intercalate (idx.map fun (_, j) => s!"hR{j}")
  let bndDefs := "\n    ".intercalate (idx.map fun (c, j) => childText
    "MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape ∧" c j)
  let memDisj := " ∨ ".intercalate (cs.map fun c => s!"(@F@.machineData.shape.insts[k]).1 = ``{c}")
  let kLemmas := "\n\n".intercalate (idx.map fun (c, j) => childText
    ("theorem _root_.@F@.epA_K_@J@ (k : Nat) (hk : k < @F@.machineData.shape.insts.length)
    (h : (@F@.machineData.shape.insts[k]).1 = ``@C@) :
    @F@.epA_nameK k = Sparkle.IR.ModuleName.ofDecl ``@C@ ∧ @F@.epA_nkK k = @C@.epA_nk ∧
    @F@.epA_outsK k = @C@.machineData.shape.layout.outs ∧
    @F@.epA_insK k = Tools.ShippingPortWidthsPure.declWidths @C@.machineData := by
  have hn : @F@.epA_nm k = ``@C@ := (@F@.epA_nm_eq k hk).trans h
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold @F@.epA_nameK; rw [hn]
  · unfold @F@.epA_nkK; rw [hn]; all_goals first | rfl | (unfold @F@.epA_nkOf; " ++ ifRed cs j ++ ")
  · unfold @F@.epA_outsK; rw [hn]; all_goals first | rfl | (unfold @F@.epA_outsOf; " ++ ifRed cs j ++ ")
  · unfold @F@.epA_insK; rw [hn]; all_goals first | rfl | (unfold @F@.epA_insOf; " ++ ifRed cs j ++ ")") c j)
  let clHaves := "\n".intercalate (idx.map fun (c, j) => childText
    "have hcl@J@ : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``@C@ @C@.machineData.shape :=
    fun mc cc => @C@.machine_closes mc _ cc _" c j)
  let honHaves := "\n".intercalate (idx.map fun (c, j) => childText
    "have hon@J@ : ∀ o ∈ @C@.machineData.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
    fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (@C@.epA_outs_clean o ho)" c j)
  let c0 := cs.head!
  let bsc := "fun n => " ++ chain cs (fun c => s!"{c}.machineData.bsIn") "[]"
  let outsc := "fun n => " ++ chain cs (fun c => s!"{c}.machineData.shape.layout.outs") "[]"
  let sc := "fun i n => " ++ chain cs (fun c => childText
    "fun vals =>
          @C@.machineSource Sparkle.Core.Domain.defaultDomain
            (Tools.ShippingMachineChild.boolsOf @C@.machineData.bsIn vals)
            (Tools.ShippingMachineChild.bitsOf @C@.machineData.bsIn vals)" c 0) "fun vals => []"
  let runOf := fun (c : Name) => s!"fun mc => Tools.ShippingGateChild.MachineRun ``{c} {c}.machineData.shape mc"
  let runc := "fun n => " ++ chain cs runOf (runOf c0)
  let mpat := " | ".intercalate (cs.map fun _ => "h")
  let cases := "\n".intercalate (idx.map fun (c, j) => childText
    ("· have hcj : c = ``@C@ := hck.trans h
  subst hcj
  have hmr : Tools.ShippingGateChild.MachineRun ``@C@ @C@.machineData.shape mc :=
    ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR@J@,
      @C@.machine_closes mctx' _ cctx' _⟩
  first
    | exact hmr
    | (dsimp only; " ++ ifRed cs j ++ "; exact hmr)
    | (" ++ ifRed cs j ++ "; exact hmr)") c j)
  let mut src := openBlock ++ boundaryTemplate ++ composedTemplate
  for (nm, ind, body) in dispBodies do
    src := src.replace s!"@D_{nm}@" (indentBy ind (disp cs body))
  let reps : List (String × String) :=
    [("@HRB@", hrb), ("@HRA@", hra), ("@HRP@", hrp), ("@BNDDEFS@", bndDefs), ("@MEMDISJ@", memDisj),
     ("@KLEMMAS@", kLemmas), ("@CLHAVES@", indentBy 2 clHaves), ("@HONHAVES@", indentBy 2 honHaves),
     ("@NKCH@", chain cs (fun c => s!"{c}.epA_nk") "0"),
     ("@OUTSCH@", chain cs (fun c => s!"{c}.machineData.shape.layout.outs") "[]"),
     ("@INSCH@", chain cs (fun c => s!"Tools.ShippingPortWidthsPure.declWidths {c}.machineData") "[]"),
     ("@BSC@", bsc), ("@OUTSC@", outsc), ("@SC@", sc), ("@RUNC@", runc), ("@MPAT@", mpat), ("@CASES@", indentBy 6 cases)]
  for (a, b) in reps do src := src.replace a b
  return subst src f c0 kD


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
def auditEndpoint (f ep : Name) (cs : List Name) : MetaM Unit := do
  stdAxioms ep
  for s in [`epA_closes, `epA_kidsMasked, `epA_runFacts, `epA_outsCheck, `epA_designCheck, `epA_houtTy, `epA_traceX,
      `epA_soundLA, `epA_composedA, `epA_hcalls, `epA_hcausal, `epA_mem, `epA_nm_eq, `epA_notF] ++
      (List.range cs.length).map fun j => Name.mkSimple s!"epA_K_{j}" do
    stdAxioms (f ++ s)
  -- the boundary quantifies `MachineDefines` for EACH distinct child (its definition mentions every child's `machineData`)
  let bndVal := (← getConstInfo (f ++ `epA_Bnd)).value!
  for c in cs do
    unless (bndVal.find? (·.isConstOf (c ++ `machineData))).isSome do
      throwError "SR3k AUDIT FAILED: {f ++ `epA_Bnd} does not mention the child {c}"
  unless (bndVal.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineDefines)).isSome do
    throwError "SR3k AUDIT FAILED: {f ++ `epA_Bnd} does not mention MachineDefines"
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
  if callees.isEmpty then throwError "#machine_seq_parent_endpoint: {fn} has no call instance (outside the class)"
  -- the DISTINCT child declarations, in order of first call
  let cs := callees.foldl (fun acc c => if acc.contains c then acc else acc ++ [c]) []
  for c in cs do
    for s in [`machineData] do
      unless (← getEnv).contains (c ++ s) do throwError "#machine_seq_parent_endpoint: {c ++ s} not found (child {c} must be a generated machine)"
    -- the class is depth 1: every child is a leaf (no call instance of its own)
    let nInsts ← liftTermElabM do
      reduceNat (← elabText (subst "@F@.machineData.shape.insts.length" c .anonymous 0))
    unless nInsts == 0 do
      let gcs ← liftTermElabM do
        readNames (← elabText (subst "(@F@.machineData.shape.insts.map (·.1))" c .anonymous 0))
      throwError "#machine_seq_parent_endpoint (unit SR3l): DEPTH 2 REFUSED: the child {c} itself has {nInsts} call instance(s), of the grandchild declaration(s) {gcs.eraseDups}.  \
        OPEN, no lemma on the new boundary: the interface of a `RealChildA O {c} y` whose machine has calls.  \
        `Tools.ShippingSeqChildIfaceA.seqChild_of_realA` needs `d.shape.insts = []` and concludes `ChildIfaceG … y.1 y.2`; this leaf-only conclusion cannot be applied to a child with calls, whose grandchildren's design must be kept, so every child-keyed fact of the parent (`kidsMasked`, `runFacts`, `outsCheck`, `designCheck`, `MachineClosesAtA` through `memKids'`) would need \
        a depth-2 analogue of `GenKid`/`KidFacts` (`Tools/ShippingGenKid.lean`, old boundary, built from `mid.closes_deep`) over `RealChildA`/`RefLawsATele`; it is NOT in the repository and is not assumed here."
    for s in [`machine_ok, `machine_body, `machine_closes, `machineSource] do
      unless (← getEnv).contains (c ++ s) do throwError "#machine_seq_parent_endpoint: {c ++ s} not found (child {c} must be a generated machine)"
  let kD ← liftTermElabM do
    reduceNat (← elabText (subst "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)" fn .anonymous 0))
  let sub := fun s => subst s fn cs.head! kD
  let mut childPart := ""
  for c in cs do
    unless (← getEnv).contains (c ++ `epA_nk) do childPart := childPart ++ childText childTemplate c 0
  let src := openBlock ++ childPart ++ (assemble fn cs kD).drop openBlock.length
  try
    runCmds src
  catch e =>
    try runCmds "end" catch _ => pure ()
    throw e
  -- the endpoint: the inferred type of the term
  let ep := fn ++ `epA_endpoint
  let hra := " ".intercalate ((List.range cs.length).map fun j => s!"hR{j}")
  let hrp := ", ".intercalate ((List.range cs.length).map fun j => s!"hR{j}")
  try
    liftTermElabM do
      let some stx := (Parser.runParserCategory (← getEnv) `term (((sub endpointTerm).replace "@HRA@" hra).replace "@HRP@" hrp)).toOption
        | throwError "endpoint term: parse error"
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let ty ← instantiateMVars (← inferType e)
      if e.hasMVar || ty.hasMVar then throwError "#machine_seq_parent_endpoint: unassigned mvars in the endpoint term"
      addAndCompile <| .thmDecl { name := ep, levelParams := [], type := ty, value := e }
    liftTermElabM <| auditEndpoint fn ep cs
    logInfo m!"SR3k: {fn} calls {cs.length} distinct child declaration(s) {cs}; {fn ++ `epA_Bnd} states `MachineDefines` for EACH of them (an existential boundary, not a proof that it holds)"
  finally
    runCmds "end"

end Tools.ShippingSeqParentGen
