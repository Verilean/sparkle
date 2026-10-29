import Tools.ShippingGen2GroupServed
set_option autoImplicit false
-- Built: g2s3b-2a22b7ec (exit 0); closure audit revised after review (full reachable closure, explicit bodies,
-- direct and two-helper negative controls). No `sorry`, no `axiom`, no `native_decide`.

/-! # S3 checks (scripts/gen2/S3_GROUP_FREEZE.md rev1 §6-§7)

1. **Expected types** (as Tests/Gen2/PMem4Check.lean §1: `forallTelescope` of the ORIGINAL at 649a6bf5, the copy's
   binders walked in parallel and instantiated with the original's fvars; names (macro scopes erased), binder infos and
   types compared; `==` after `instantiateMVars`, `isDefEq` fallback logged as `S3 DEFEQ`). The rule of each pair is
   a function on the original's binder types and conclusion; the set of binders it CHANGES is asserted:
   * A3 `comb_inst_runN` vs `seq_inst_runN`: rule `SeqChildRunN ↦ CombChildRunN`; `hrstP`, `hclkP` DELETED (D3);
     changed = [hrun, hout].
   * A5 `CombFactsRN` vs `SeqFactsRN` (definition): same type, value = rule(original value), same lambda binder names.
   * A6 `calls_hchildRNC` vs `calls_hchildRN`: rule "split" (`SeqFactsRN … PC k c ↦ SeqFactsRN … (seqPC PC) k c ∧
     CombFactsRN … (combPC PC) k c`); changed = [hcalls]; conclusion unchanged.
   * A7 `calls_hchildRN_viaC`: type equal to `calls_hchildRN`'s (N2).
   * B1 `ordFactsRN_of_callDec` vs `seqFactsRN_of_callDec`: `hseq` DELETED, no binder changed (so `hdec` is the
     original's, verbatim), conclusion = split(original conclusion).
   * B3 `machine_linkedT_callsServedC` vs `machine_linkedT_callsServed`: split; changed = [hcalls].
2. **Audit** (§7): (a) no binder of any new declaration is named `hseq` or has the `hseq` shape
   (`∀ …, <hyp mentioning ServedPC> → "clk" ∈ …` or its negation) — detector positive control: it finds `hseq` in
   `seqFactsRN_of_callDec`; (b) no new declaration (nor its auxiliary constants) references `seqFactsRN_of_callDec`;
   (c) B1: binder names listed, `hseq` absent, no binder type contains the literal `"clk"`;
   (d) same trace BY TYPE: B3/B4/B5 have exactly ONE `MachineTraceLBX` binder; B5's conclusion is `ChildShips p (n + 1)`
   at the `n` of its trace's `ShipsAt L P n`. BY PROOF READING ONLY (not checkable by type): `wired`/`hx`/`trace` from
   ONE `obtain` (B3, Consumer:87 verbatim), B4/B5 pass the one `h` unchanged, `hcalls` built at the `intro`'d
   `i bools bits` (B2, B4's lambda), the A6 `by_cases` after `intro … mc …`.
3. **P1** (non-vacuous): the toy combinational module `mcT` (`o := a`): `CombChildRunN … n mcT …` at EVERY `n`
   (proved), and `comb_inst_runN` on concrete `connsG mcT ["wa"] [(0, "o")] ["wo"]`: a run exists and its output `o`
   at list index 0 is 7. **N1**: no module with a `"clk"` input is `CombChildRunN`; `seqPC` excludes `combPC`.
   **C-1/B5**: `group_childShips` from `StepStmt`'s binders (unchanged `hdec`) plus the residues.
4. `#print axioms` of every new declaration. -/

namespace Tests.Gen2.S3ReachHelperA
/-- fixture: uses the `hseq` producer directly -/
theorem helperA : True := (fun _ => trivial) @Tools.ShippingGen2.seqFactsRN_of_callDec
end Tests.Gen2.S3ReachHelperA
namespace Tests.Gen2.S3ReachHelperB
/-- fixture: a second helper, in another namespace, through `helperA` -/
theorem helperB : True := Tests.Gen2.S3ReachHelperA.helperA
end Tests.Gen2.S3ReachHelperB
namespace Tests.Gen2.S3ReachFixture
/-- closure-detector control: direct use -/
theorem badDirect : True := (fun _ => trivial) @Tools.ShippingGen2.seqFactsRN_of_callDec
/-- closure-detector control: use through two helpers in other namespaces -/
theorem badIndirect : True := Tests.Gen2.S3ReachHelperB.helperB
/-- closure-detector control: unrelated (must NOT be flagged) -/
theorem goodUnrelated : True := trivial
end Tests.Gen2.S3ReachFixture

namespace Tests.Gen2.S3GroupCheck
open Lean Meta Elab Command

/-! ## 1. Expected types -/

/-- `==` after `instantiateMVars`; on a mismatch log it and fall back to `isDefEq` (logged); else fail. -/
def s3CheckEq (what : String) (a e : Expr) : MetaM Unit := do
  let a ← instantiateMVars a
  let e ← instantiateMVars e
  if a == e then return
  logInfo m!"S3 NOTE {what}: not syntactically equal, trying isDefEq:{indentExpr a}\nexpected{indentExpr e}"
  if (← isDefEq a e) then
    logInfo m!"S3 DEFEQ {what}: accepted by isDefEq (NOT syntactic)"
  else
    throwError "S3 CHECK FAILED {what}:{indentExpr a}\nexpected{indentExpr e}"

/-- Rule `SeqChildRunN ↦ CombChildRunN` (constant replacement; same argument list). -/
def s3SeqToComb (e : Expr) : Expr :=
  e.replace fun x =>
    if x.isConstOf ``Tools.ShippingMachineDepth.SeqChildRunN then
      some (mkConst ``Tools.ShippingGen2.CombChildRunN x.constLevels!)
    else none

/-- The position of `PC` among `SeqFactsRN`'s 18 parameters (checked below). -/
def s3PCIdx : Nat := 15
def s3FactsArity : Nat := 18

/-- Rule "split" (D1(a)): every full application `SeqFactsRN a₀ … PC k c` becomes
`SeqFactsRN a₀ … (seqPC PC) k c ∧ CombFactsRN a₀ … (combPC PC) k c`. -/
def s3SplitPC (e : Expr) : Expr :=
  e.replace fun x =>
    if x.isAppOfArity ``Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN s3FactsArity then
      let args := x.getAppArgs.toList
      let pc := args.getD s3PCIdx x
      let setPC (v : Expr) : Array Expr := (args.take s3PCIdx ++ [v] ++ args.drop (s3PCIdx + 1)).toArray
      some (mkApp2 (mkConst ``And)
        (mkAppN (mkConst ``Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN)
          (setPC (mkApp (mkConst ``Tools.ShippingGen2.seqPC) pc)))
        (mkAppN (mkConst ``Tools.ShippingGen2.CombFactsRN)
          (setPC (mkApp (mkConst ``Tools.ShippingGen2.combPC) pc))))
    else none

/-- The binder names of a constant's type (macro scopes erased). -/
def s3BinderNames (c : Name) : MetaM (List Name) := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ =>
    xs.toList.mapM fun x => return (← x.fvarId!.getDecl).userName.eraseMacroScopes

/-- The expected-type check of one (original, copy) pair under `rule`, with `drops` deleted and `changed` the exact
list of binders the rule changes. -/
def s3CheckPair (orig copy : Name) (drops changed : List Name) (rule : Expr → Expr) : MetaM Unit := do
  let ciO ← getConstInfo orig
  let ciC ← getConstInfo copy
  unless ciO.levelParams == ciC.levelParams do
    throwError "S3 CHECK FAILED {copy}: universe parameters {ciC.levelParams} vs {ciO.levelParams}"
  forallTelescope ciO.type fun xs bodyO => do
    let decls ← xs.mapM (·.fvarId!.getDecl)
    for dn in drops do
      unless decls.any (·.userName == dn) do
        throwError "S3 CHECK FAILED: the original {orig} has no binder {dn}"
    -- a deleted binder: nothing later depends on it
    for i in [0:xs.size] do
      if drops.contains decls[i]!.userName then
        let fv := xs[i]!.fvarId!
        if bodyO.hasAnyFVar (· == fv) || decls.any (fun d => d.type.hasAnyFVar (· == fv)) then
          throwError "S3 CHECK FAILED {orig}: the deleted binder {decls[i]!.userName} is used later"
    let mut t := ciC.type
    let mut chg : List Name := []
    for i in [0:xs.size] do
      let dO := decls[i]!
      if drops.contains dO.userName then continue
      let .forallE n ty b bi := t
        | throwError "S3 CHECK FAILED {copy}: fewer binders than the original (at original binder {i}, {dO.userName})"
      unless n.eraseMacroScopes == dO.userName.eraseMacroScopes do
        throwError "S3 CHECK FAILED {copy}: binder {i} is named {n}, the original's is {dO.userName}"
      unless bi == dO.binderInfo do
        throwError "S3 CHECK FAILED {copy}: binder {n} has a different binder info"
      let exp := rule dO.type
      if exp != dO.type then chg := chg ++ [dO.userName.eraseMacroScopes]
      s3CheckEq s!"{copy} binder {n}" ty exp
      t := b.instantiate1 xs[i]!
    unless chg == changed do
      throwError "S3 CHECK FAILED {copy}: the rule changes binders {chg}, expected {changed}"
    s3CheckEq s!"{copy} conclusion" t (rule bodyO)
  logInfo m!"S3 TYPE OK {copy} against {orig}: deleted {drops}, changed {changed}"

/-- A5: a copied DEFINITION: same type, value = rule(original value), same lambda binder names. -/
def s3CheckDef (orig copy : Name) (rule : Expr → Expr) : MetaM Unit := do
  let ciO ← getConstInfo orig
  let ciC ← getConstInfo copy
  unless ciO.levelParams == ciC.levelParams do
    throwError "S3 CHECK FAILED {copy}: universe parameters differ"
  s3CheckEq s!"{copy} type" ciC.type ciO.type
  let some vO := ciO.value? | throwError "S3 CHECK FAILED: {orig} has no value"
  let some vC := ciC.value? | throwError "S3 CHECK FAILED: {copy} has no value"
  if rule vO == vO then throwError "S3 CHECK FAILED: the rule does not change {orig}'s value"
  s3CheckEq s!"{copy} value" vC (rule vO)
  let nO ← lambdaTelescope vO fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getDecl).userName
  let nC ← lambdaTelescope vC fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getDecl).userName
  unless nO == nC do throwError "S3 CHECK FAILED {copy}: lambda binders {nC}, the original's {nO}"
  logInfo m!"S3 DEF OK {copy} against {orig} (SeqChildRunN ↦ CombChildRunN)"

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  -- the split rule's position of `PC`, on both definitions
  let nS ← s3BinderNames ``Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
  let nC ← s3BinderNames ``Tools.ShippingGen2.CombFactsRN
  unless nS.length == s3FactsArity && nS.getD s3PCIdx .anonymous == `PC do
    throwError "S3 CHECK FAILED: SeqFactsRN's binders {nS} (PC not at {s3PCIdx} of {s3FactsArity})"
  unless nC == nS do throwError "S3 CHECK FAILED: CombFactsRN's binders {nC} vs SeqFactsRN's {nS}"
  -- A3, A5, A6, B1, B3
  s3CheckPair ``Tools.ShippingMachineDepth.seq_inst_runN ``Tools.ShippingGen2.comb_inst_runN
    [`hrstP, `hclkP] [`hrun, `hout] s3SeqToComb
  s3CheckDef ``Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN ``Tools.ShippingGen2.CombFactsRN s3SeqToComb
  s3CheckPair ``Tools.ShippingMachineCallsLinkedTNR.calls_hchildRN ``Tools.ShippingGen2.calls_hchildRNC
    [] [`hcalls] s3SplitPC
  s3CheckPair ``Tools.ShippingGen2.seqFactsRN_of_callDec ``Tools.ShippingGen2.ordFactsRN_of_callDec
    [`hseq] [] s3SplitPC
  s3CheckPair ``Tools.ShippingGen2Consumer.machine_linkedT_callsServed
    ``Tools.ShippingGen2Consumer.machine_linkedT_callsServedC [] [`hcalls] s3SplitPC
  -- A7 / N2: the accepted statement, verbatim
  s3CheckEq "calls_hchildRN_viaC type" (← getConstInfo ``Tools.ShippingGen2.calls_hchildRN_viaC).type
    (← getConstInfo ``Tools.ShippingMachineCallsLinkedTNR.calls_hchildRN).type
  logInfo m!"S3 TYPES OK: A3, A5, A6, A7 (viaC = calls_hchildRN), B1 (hseq deleted, hdec unchanged), B3"

/-! ## 2. Audit -/

/-- Every new declaration of S3 stages A/B. -/
def s3New : List Name :=
  [``Tools.ShippingGen2.any_clkrst_false, ``Tools.ShippingGen2.connsG_keys_comb,
   ``Tools.ShippingGen2.connsG_field_comb, ``Tools.ShippingGen2.comb_inst_runN, ``Tools.ShippingGen2.seqPC,
   ``Tools.ShippingGen2.combPC, ``Tools.ShippingGen2.isSeqChild_of_seqRunN, ``Tools.ShippingGen2.isSeqChild_of_combRunN,
   ``Tools.ShippingGen2.CombFactsRN, ``Tools.ShippingGen2.calls_hchildRNC, ``Tools.ShippingGen2.hcallsC_of_seq,
   ``Tools.ShippingGen2.calls_hchildRN_viaC, ``Tools.ShippingGen2.ordFactsRN_of_callDec,
   ``Tools.ShippingGen2.groupHcalls_of_dec, ``Tools.ShippingGen2Consumer.machine_linkedT_callsServedC,
   ``Tools.ShippingGen2.group_composedNW, ``Tools.ShippingGen2.group_childShips]

/-- The literal `"clk"` occurs in `e`. -/
def s3HasClk (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .lit (.strVal s) => s == "clk"
    | _ => false).isSome

/-- The `hseq` shape: `∀ …, <a hypothesis mentioning ServedPC> → "clk" ∈ …` (or `∉`). -/
def s3HseqShaped (ty : Expr) : MetaM Bool :=
  forallTelescope ty fun ys body => do
    let mut served := false
    for y in ys do
      if (← inferType y).getUsedConstants.contains ``Tools.ShippingGen2.ServedPC then served := true
    let b := if body.isAppOfArity ``Not 1 then body.appArg! else body
    return served && b.isAppOf ``Membership.mem && s3HasClk b

/-- The binders of `c`'s type that are named `hseq` or have the `hseq` shape. -/
def s3HseqBinders (c : Name) : MetaM (List Name) := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => do
    let mut r : List Name := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName.eraseMacroScopes == `hseq || (← s3HseqShaped d.type) then
        r := r ++ [d.userName.eraseMacroScopes]
    return r

/-- The body of a constant, read EXPLICITLY per kind (C4KidTest:132-134: `value?` is not trusted for theorems here):
theorem / definition / opaque value; `none` for axioms, inductives, constructors, recursors, quotients. -/
def s3Body? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

/-- Result of the reachable-closure search from one root. -/
structure S3Reach where
  /-- a path root → … → target, if `target` is reached -/
  hit : Option (List Name) := none
  /-- constants visited -/
  visited : Nat := 0
  /-- reached constants without a body (axioms / inductives / ctors / recursors / quot): types followed, no body -/
  noBody : Nat := 0
  /-- reached `opaque` constants (incl. `partial` wrappers): their stored value is followed, but an `implemented_by`
  / `_unsafe_rec` implementation is not part of the kernel term and is not followed -/
  opaques : Array Name := #[]
  deriving Inhabited

/-- Breadth-first search of the FULL dependency closure of `root` (type and explicit body of every reached constant,
in every namespace), for `target`. Throws if the visit cap is exceeded (then non-reference is NOT established). -/
def s3Reach (target root : Name) (cap : Nat := 3000000) : MetaM S3Reach := do
  let env ← getEnv
  let mut out : S3Reach := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then
      throwError "S3 AUDIT INCOMPLETE at {root}: more than {cap} constants; non-reference NOT established"
    let some ci := env.find? c | continue
    let body := s3Body? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques.push c }
    let used := ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[]
    for u in used do
      if u == target then
        return { out with hit := some (path ++ [u]) }
      unless seen.contains u do
        seen := seen.insert u
        queue := queue.push (u, path ++ [u])
  return out

/-- The number of binders of `c`'s type whose type is an application of `head`. -/
def s3CountBinders (c head : Name) : MetaM Nat := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => do
    let mut k := 0
    for x in xs do
      if (← inferType x).isAppOf head then k := k + 1
    return k

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  -- (a) detector positive control, then every new declaration
  let ctl ← s3HseqBinders ``Tools.ShippingGen2.seqFactsRN_of_callDec
  unless ctl == [`hseq] do
    throwError "S3 AUDIT FAILED: the hseq detector finds {ctl} in seqFactsRN_of_callDec, expected [hseq]"
  for c in s3New do
    let r ← s3HseqBinders c
    unless r.isEmpty do throwError "S3 AUDIT FAILED {c}: hseq-shaped binders {r}"
  -- (b) no reference to the `hseq` producer: full reachable closure (every namespace), explicit bodies.
  -- Detector controls with the SAME search: a direct use and a use through two helpers in other namespaces are
  -- found; an unrelated theorem is not.
  let tgt := ``Tools.ShippingGen2.seqFactsRN_of_callDec
  let r ← s3Reach tgt ``Tests.Gen2.S3ReachFixture.badDirect
  unless r.hit.isSome do throwError "S3 AUDIT FAILED: the closure detector misses a direct use (badDirect)"
  logInfo m!"S3 REACH CONTROL badDirect: found via {r.hit.getD []}"
  let r ← s3Reach tgt ``Tests.Gen2.S3ReachFixture.badIndirect
  unless r.hit.isSome do throwError "S3 AUDIT FAILED: the closure detector misses a use through two helpers (badIndirect)"
  logInfo m!"S3 REACH CONTROL badIndirect: found via {r.hit.getD []}"
  let r ← s3Reach tgt ``Tests.Gen2.S3ReachFixture.goodUnrelated
  if r.hit.isSome then throwError "S3 AUDIT FAILED: the closure detector flags an unrelated theorem (goodUnrelated)"
  logInfo m!"S3 REACH CONTROL goodUnrelated: not found (visited {r.visited})"
  for c in s3New do
    let r ← s3Reach tgt c
    if let some p := r.hit then
      throwError "S3 AUDIT FAILED {c}: references seqFactsRN_of_callDec via {p}"
    logInfo m!"S3 REACH {c}: seqFactsRN_of_callDec not in the closure (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques.size}: implementations of opaque/partial constants are not kernel terms and are not followed)"
  -- (c) B1
  let ns ← s3BinderNames ``Tools.ShippingGen2.ordFactsRN_of_callDec
  if ns.contains `hseq then throwError "S3 AUDIT FAILED: ordFactsRN_of_callDec has a binder hseq"
  let ci ← getConstInfo ``Tools.ShippingGen2.ordFactsRN_of_callDec
  forallTelescope ci.type fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if s3HasClk d.type then throwError "S3 AUDIT FAILED: ordFactsRN_of_callDec's binder {d.userName} mentions \"clk\""
  logInfo m!"S3 AUDIT B1: ordFactsRN_of_callDec binders {ns} (no hseq, no \"clk\" literal; hdec = the original's, §1)"
  -- (d) same trace by type
  for c in [``Tools.ShippingGen2Consumer.machine_linkedT_callsServedC, ``Tools.ShippingGen2.group_composedNW,
      ``Tools.ShippingGen2.group_childShips] do
    let k ← s3CountBinders c ``Tools.ShippingMachineTraceX.MachineTraceLBX
    unless k == 1 do throwError "S3 AUDIT FAILED {c}: {k} MachineTraceLBX binders, expected 1"
  -- B5: `ChildShips p (n + 1)` at the trace's `ShipsAt L P n`
  let ci5 ← getConstInfo ``Tools.ShippingGen2.group_childShips
  forallTelescope ci5.type fun xs body => do
    let decls ← xs.mapM (·.fvarId!.getDecl)
    let some iN := decls.findIdx? (·.userName == `n) | throwError "S3 AUDIT FAILED: group_childShips has no n"
    let some iH := decls.findIdx? (·.userName == `h) | throwError "S3 AUDIT FAILED: group_childShips has no h"
    let nF := xs[iN]!
    unless body.isAppOf ``Tools.ShippingGen2.ChildShips do
      throwError "S3 AUDIT FAILED: group_childShips' conclusion is not ChildShips"
    let some nArg := body.getAppArgs[3]? | throwError "S3 AUDIT FAILED: ChildShips arity"
    let nPlus1 ← mkAppM ``HAdd.hAdd #[nF, mkNatLit 1]
    unless (← isDefEq nArg nPlus1) do
      throwError "S3 AUDIT FAILED: group_childShips' height is {nArg}, not n + 1"
    let hasAt := (decls[iH]!.type.find? fun e =>
      e.isAppOfArity ``Tools.ShippingGen2.ShipsAt 7 && e.appArg! == nF).isSome
    unless hasAt do throwError "S3 AUDIT FAILED: group_childShips' trace is not over ShipsAt L P n (the same n)"
  logInfo m!"S3 AUDIT OK: no hseq binder (detector control found it in seqFactsRN_of_callDec), no reference to seqFactsRN_of_callDec, one trace binder in B3/B4/B5, B5 at n + 1 over ShipsAt n"

end Tests.Gen2.S3GroupCheck

/-! ## 3. P1, N1, C-1 -/
namespace Tests.Gen2.S3GroupCheckP1
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingMachineDepth
open Tools.ShippingMachineLinkedT (connsG)
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.IR.Machine (OutField)
open Sparkle.Compiler.Elab (MixedGateBinder)
open Tools.ShippingMachineClose (Zip₂)

/-- The toy combinational module: one input `a`, one output `o`, `o := a`. -/
def mcT : Module :=
  { name := "s3ToyComb", inputs := [{ name := "a", ty := .bitVector 8 }],
    outputs := [{ name := "o", ty := .bitVector 8 }], wires := [], body := [.assign "o" (.ref "a")] }

def oT : OutField := { name := "o", lo := 0, width := 8, ty := .bitVector 8 }
def bsT : List (Lean.Name × MixedGateBinder) := [(`a, .bits 8)]
/-- Its interface function: the output at list index `j` is the argument value of `vals j`. -/
def ST : (Nat → List Nat) → List (Nat → Nat) := fun v => [fun j => (v j).headD 0]

theorem mcT_instFree : instFree mcT.body := by
  intro st hst
  simp only [mcT, List.mem_singleton] at hst
  subst hst
  rfl

theorem mcT_argPorts : argPorts mcT = [{ name := "a", ty := .bitVector 8 }] := by
  first
    | (simp [argPorts, mcT]; done)
    | rfl
    | decide

theorem bsT_filter : (bsT.filter fun b => b.2 != .domain) = [(`a, .bits 8)] := by
  first
    | rfl
    | (simp [bsT]; done)
    | decide

theorem inRange7 : Tools.ShippingMachineChild.InRange [7] (bsT.filter fun b => b.2 != .domain) := by
  rw [bsT_filter]
  exact Zip₂.cons (by show 7 < 2 ^ 8; decide) Zip₂.nil

/-- **P1**: the toy module is a combinational child run at EVERY depth (`RunOn_instFree`). -/
theorem mcT_combRunN (children : String → Option (Module × WEnv)) (dsn : Design) (n : Nat) :
    Tools.ShippingGen2.CombChildRunN children dsn n mcT bsT [oT] ST := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · first | (simp [mcT]; done) | decide
  · first | (simp [mcT]; done) | decide
  · first | (simp [mcT]; done) | decide
  · first | (simp [mcT]; done) | decide
  · first
      | (rw [mcT_argPorts, bsT_filter] <;> rfl)
      | rfl
      | (simp [mcT, bsT, argPorts]; done)
  · intro T ins s vals _ hports _
    rw [RunOn_instFree children mcT mcT_instFree]
    have hstep : ∀ (k : Nat) (st : String → Nat) (mems : MEnv), k < T →
        ∃ e, evalAssigns (Sparkle.IR.RegDedup.declWidth mcT) mems mcT.body (seedIn mcT ins k st) = some e ∧
          e "o" = ins k "a" := by
      intro k st mems _
      refine ⟨fun x => if x = "o" then seedIn mcT ins k st "a" else seedIn mcT ins k st x, ?_, ?_⟩
      · first | rfl | (simp [mcT, evalAssigns, evalExpr]; done)
      · first
          | (simp [seedIn, mcT]; done)
          | (show (if "o" = "o" then seedIn mcT ins k st "a" else seedIn mcT ins k st "o") = ins k "a"; rw [if_pos rfl]; unfold seedIn; rw [if_pos (by first | rfl | decide | (simp [mcT]; done))])
    have hall : mcT.body.all Sparkle.IR.RegDedup.isAssign = true := by
      first | rfl | decide | (simp [mcT, Sparkle.IR.RegDedup.isAssign]; done)
    obtain ⟨envs, hrun, hlen, hR⟩ := Tools.ShippingGateDesign.runModule_assigns_total
      (we := Sparkle.IR.RegDedup.declWidth mcT) (seed := seedIn mcT ins)
      (R := fun t e => e "o" = ins t "a") (N := T) hall hstep T (stOf n s) (memsOf n s) (Nat.le_refl T)
    refine ⟨envs, hrun, hlen, ?_⟩
    intro j hj k o f ho hf
    have hjT : j < T := by omega
    cases k with
    | succ k => simp [oT] at ho
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ho
      subst ho
      simp only [ST, List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      have hp := hports (T - 1 - j) (by omega)
      rw [show T - 1 - (T - 1 - j) = j by omega, mcT_argPorts] at hp
      have h1 := hR j hj (T - 1 - j) (by omega)
      show (envs[j]'hj) "o" = (vals j).headD 0
      rw [← hp]
      exact h1

/-- A4 on the toy module: the compiler's `instStmtG` connects no clock/reset to it. -/
example (children : String → Option (Module × WEnv)) (dsn : Design) (n : Nat) :
    Tools.ShippingInstStmtG.isSeqChild mcT = false :=
  Tools.ShippingGen2.isSeqChild_of_combRunN children (mcT_combRunN children dsn n)

def kidT : KT 0 := ({ st := fun _ => 0, mems := fun _ _ => 0 } : Tools.ShippingHierState.KidState)

/-- The parent's wires: argument wire `wa` and output wire `wo` both carry 7. -/
def PwT : Nat → Env := fun _ x => if x = "wa" then 7 else if x = "wo" then 7 else 0

theorem kidT_reset (dsn : Design) : ResetN dsn 0 mcT kidT := by
  unfold ResetN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r c rs inp init h
    simp [mcT] at h
  · intro nm i
    rfl
  · intro nm aw dw c wa wd we ra rd cr ew er h
    simp [mcT] at h
  · exact True.intro

/-- **P1 (concrete instance)**: `comb_inst_runN` with every premise discharged on concrete data: the instance of the
toy module, connected by `connsG mcT ["wa"] [(0, "o")] ["wo"]`, has a 3-cycle run whose output `o` at list index 0
is 7. -/
theorem comb_inst_toy (children : String → Option (Module × WEnv)) (dsn : Design) :
    ∃ cenvs, runKS (KSn children 0) mcT (Sparkle.IR.RegDedup.declWidth mcT)
        (inConns mcT.outputs (connsG mcT ["wa"] [(0, "o")] ["wo"])) PwT 3 kidT = some cenvs ∧
      (cenvs[0]?).map (· "o") = some 7 := by
  have hlen : ["wa"].length = (argPorts mcT).length := by rw [mcT_argPorts] <;> rfl
  have hfields : ∀ f ∈ [((0 : Nat), "o")].map (·.2), f ∈ mcT.outputs.map (·.name) := by
    first | (simp [mcT]; done) | decide
  have hrange : ∀ τ, τ < 3 → Tools.ShippingMachineChild.InRange ((fun _ => [7]) τ)
      (bsT.filter fun b => b.2 != .domain) := fun _ _ => inRange7
  have hargs : ∀ t, t < 3 → ["wa"].map (PwT t) = (fun (_ : Nat) => [7]) (3 - 1 - t) := by
    intro t _
    first | (simp [PwT]; done) | rfl
  have hout : ∀ (idx : Nat) (e : Nat × String) (w : String), [((0 : Nat), "o")][idx]? = some e →
      ["wo"][idx]? = some w →
      ∃ (bsC' : List (Lean.Name × MixedGateBinder)) (outsC' : List OutField)
        (S' : (Nat → List Nat) → List (Nat → Nat)),
        Tools.ShippingGen2.CombChildRunN children dsn 0 mcT bsC' outsC' S' ∧
        (∀ τ, τ < 3 → Tools.ShippingMachineChild.InRange ((fun _ => [7]) τ)
          (bsC'.filter fun b => b.2 != .domain)) ∧
        ∃ (k : Nat) (o : OutField) (f : Nat → Nat), outsC'[k]? = some o ∧ o.name = e.2 ∧
          (S' (fun _ => [7]))[k]? = some f ∧ ∀ t, t < 3 → PwT t w = f (3 - 1 - t) := by
    intro idx e w he hw
    cases idx with
    | succ i => simp at he
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he hw
      subst he
      subst hw
      refine ⟨bsT, [oT], ST, mcT_combRunN children dsn 0, fun _ _ => inRange7, 0, oT,
        fun j => ((fun (_ : Nat) => [7]) j).headD 0, rfl, rfl, rfl, ?_⟩
      intro t _
      first | (simp [PwT]; done) | rfl
  obtain ⟨cenvs, hrun, hobs⟩ := Tools.ShippingGen2.comb_inst_runN children dsn 0 (mcT_combRunN children dsn 0)
    ["wa"] [((0 : Nat), "o")] ["wo"] PwT 3 kidT (fun _ => [7]) hlen hfields hrange hargs (kidT_reset dsn) hout
  have hlk : (connsG mcT ["wa"] [((0 : Nat), "o")] ["wo"]).lookup "o" = some (.ref "wo") := by
    first
      | (simp [connsG, mcT, List.lookup]; done)
      | rfl
      | decide
  have hmem : ({ name := "o", ty := .bitVector 8 } : Port) ∈ mcT.outputs := by
    first | (simp [mcT]; done) | exact List.mem_singleton.mpr rfl
  have h7 : some (PwT (3 - 1 - 0) "wo") = some 7 := by
    first | (simp [PwT]; done) | rfl
  exact ⟨cenvs, hrun, (hobs 0 (by decide) _ hmem "wo" hlk).trans h7⟩

/-- **N1**: a module with a `"clk"` input is never a combinational child run. -/
def mcClk : Module :=
  { name := "s3ToyClk", inputs := [{ name := "clk", ty := .bit }], outputs := [], wires := [], body := [] }

theorem n1_not_comb (children : String → Option (Module × WEnv)) (dsn : Design) (n : Nat)
    (bsC : List (Lean.Name × MixedGateBinder)) (outsC : List OutField) (S : (Nat → List Nat) → List (Nat → Nat)) :
    ¬ Tools.ShippingGen2.CombChildRunN children dsn n mcClk bsC outsC S :=
  fun h => h.2.2.1 (by first | (simp [mcClk]; done) | decide)

/-- **N1**: the two branch predicates exclude each other. -/
theorem n1_branch (PC : Lean.Name → Module → Prop) (c : Lean.Name) (mc : Module) :
    Tools.ShippingGen2.seqPC PC c mc → ¬ Tools.ShippingGen2.combPC PC c mc :=
  fun h1 h2 => (And.right h2) (And.right h1)

end Tests.Gen2.S3GroupCheckP1

/-! ### C-1 (§5): `StepStmt`'s binders (Defs:301-313, `hdec` unchanged) plus the residues give `ChildShips` at
`n + 1` by B5. -/
section C1
open Tools.ShippingGen2
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (dv)

example {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom)
    -- `StepStmt`'s binders
    (p : Pkg ι dom) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design)
    (_hP : P p.decl = some p) (hA : AdmCtx L.O.quiet mctx cctx)
    (_hJ : Tools.ShippingChildCacheA.JQC L.O (dv w) w)
    (_hrun : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore p.decl [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (_hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    -- the residues: the trace at a FIXED `n` (G-SERVED + G-LIFT), the data rows, the case
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ []) :
    ChildShips p (n + 1) b D :=
  group_childShips L P p hdata hext hins hfe hsl hA hpost ran hdec n h

end C1

/-! ## 4. Axioms -/
#print axioms Tools.ShippingGen2.any_clkrst_false
#print axioms Tools.ShippingGen2.connsG_keys_comb
#print axioms Tools.ShippingGen2.connsG_field_comb
#print axioms Tools.ShippingGen2.comb_inst_runN
#print axioms Tools.ShippingGen2.isSeqChild_of_seqRunN
#print axioms Tools.ShippingGen2.isSeqChild_of_combRunN
#print axioms Tools.ShippingGen2.calls_hchildRNC
#print axioms Tools.ShippingGen2.hcallsC_of_seq
#print axioms Tools.ShippingGen2.calls_hchildRN_viaC
#print axioms Tools.ShippingGen2.ordFactsRN_of_callDec
#print axioms Tools.ShippingGen2.groupHcalls_of_dec
#print axioms Tools.ShippingGen2Consumer.machine_linkedT_callsServedC
#print axioms Tools.ShippingGen2.group_composedNW
#print axioms Tools.ShippingGen2.group_childShips
#print axioms Tests.Gen2.S3GroupCheckP1.mcT_combRunN
#print axioms Tests.Gen2.S3GroupCheckP1.comb_inst_toy
#print axioms Tests.Gen2.S3GroupCheckP1.n1_not_comb
#print axioms Tests.Gen2.S3GroupCheckP1.n1_branch

-- Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), for every new theorem and control.
run_cmd do
  for name in [``Tools.ShippingGen2.any_clkrst_false, ``Tools.ShippingGen2.connsG_keys_comb,
      ``Tools.ShippingGen2.connsG_field_comb, ``Tools.ShippingGen2.comb_inst_runN,
      ``Tools.ShippingGen2.isSeqChild_of_seqRunN, ``Tools.ShippingGen2.isSeqChild_of_combRunN,
      ``Tools.ShippingGen2.calls_hchildRNC, ``Tools.ShippingGen2.hcallsC_of_seq,
      ``Tools.ShippingGen2.calls_hchildRN_viaC, ``Tools.ShippingGen2.ordFactsRN_of_callDec,
      ``Tools.ShippingGen2.groupHcalls_of_dec, ``Tools.ShippingGen2Consumer.machine_linkedT_callsServedC,
      ``Tools.ShippingGen2.group_composedNW, ``Tools.ShippingGen2.group_childShips,
      ``Tests.Gen2.S3GroupCheckP1.mcT_combRunN, ``Tests.Gen2.S3GroupCheckP1.comb_inst_toy,
      ``Tests.Gen2.S3GroupCheckP1.n1_not_comb, ``Tests.Gen2.S3GroupCheckP1.n1_branch] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
