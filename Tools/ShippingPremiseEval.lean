import Tools.ShippingMachineDepthCommand
import Tools.ShippingMachineShipsHierHCommand
import Tools.ShippingHierSVRunH
import Tools.ShippingHierPremises
import Tools.ShippingHierShipsSV
import Tools.ShippingDesignSV
import Tools.ShippingDesignSVBack
import Tools.ShippingShipsDesignSVCommand

/-! # Evaluating the shipping theorems' premises on a real compile

A generated shipping theorem is conditional. That it was generated says
nothing about whether its premises hold. This file evaluates them on the
modules of an actual compile and returns a `Verdict` with FIXED fields — one
per kind of premise — so that nothing unverified can be read as verified:

* `checker` — the theorem's own bundled checker (`shipsHierCheck` /
  `shipsHierHCheck`, the very function the theorem names), evaluated;
* `childBound` — the children's output bound (`kidsMaskedN`, `kidsMasked` /
  `kidsMem`, the width-typed run), evaluated;
* `boundaryChecks` — decidable facts at the run boundary (`extendsAwayB`,
  `noInstOfB`, `kidsComb`), evaluated; and facts the wiring DERIVES (a memory
  call's instance is the built memory module: `MachineWired`, from the
  compiler's own `memSelf` check, `find_memModule`), evaluated as a
  cross-check;
* `traces` — the run boundaries themselves (the module an instance resolves
  to is a run of its child's entry). The compiler's sub-synthesis is an
  `IO.Ref`, opaque in the logic: these stay PREMISES of the theorem. Here
  they are MEASURED by compiling the child again and comparing modules —
  a trace, never a proof, in its own field;
* `svParent` — the decidable premises of the emitted-Verilog theorem of the
  shipped module (`shippedSVCheck` / `svHCheck`, the theorems' own checkers)
  and the children's bound on the shipped module;
* `svChildren` — the children's own emitted Verilog: not connected (the
  parent's Verilog runs against an ORACLE for the children's outputs);
* `useConditions` — premises about the run's inputs and initial state: the
  caller's obligations when using the theorem, not facts of the modules;
* `reflection` — the reflection boundary (`MachineDefines`, `EntryDefines`).

The module verdict is `PREM` only when the checker, the child bound and
every boundary check HOLD; `NOPREM` when one fails; otherwise `UNKNOWN`.
The trace verdict is `MATCHED` only when at least one trace was taken and
every trace matched; an untraced boundary is `UNTRACED`, never matched.
The trace verdict is `NOTREQUIRED` when the route needs no run boundary
beyond facts derived from the run (memory reads). A theorem counts as
applying to the run — GIVEN its run-boundary premises, measured but not
discharged — only with `MOD:PREM` and `TRACE:MATCHED` / `TRACE:NOTREQUIRED`
(`Verdict.applies`). -/
namespace Tools.ShippingPremiseEval
open Lean Meta
open Sparkle.IR.AST
open Sparkle.IR.Machine (moduleByName)

/-- A decidable premise's status. `unknown` is never success. -/
inductive Status | holds | fails (why : String) | unknown (why : String)
  deriving BEq, Repr, Inhabited

/-- A measured run boundary. Never a proof. -/
inductive Trace | matched | mismatch (why : String) | untraced (why : String)
  deriving BEq, Repr, Inhabited

/-- What the route needs at the run boundary: traces of child runs
(`required`), or nothing beyond facts a general theorem derives from the
run (`notRequired`, e.g. memory reads: `MachineWired` / `find_memModule`). -/
inductive BoundaryReq | required | notRequired (why : String)
  deriving BEq, Repr, Inhabited

def Status.ofBool (b : Bool) (why : String) : Status := if b then .holds else .fails why

def Status.str : Status → String
  | .holds => "holds" | .fails w => s!"FAILS ({w})" | .unknown w => s!"UNKNOWN ({w})"

def Trace.str : Trace → String
  | .matched => "matched (measured, not proved)" | .mismatch w => s!"MISMATCH ({w})"
  | .untraced w => s!"UNTRACED ({w})"

structure Verdict where
  theoremName : String
  checker : Status := .unknown "not evaluated"
  childBound : Status := .unknown "not evaluated"
  boundaryChecks : List (String × Status) := []
  traces : List (String × Trace) := []
  boundaryReq : BoundaryReq := .required
  route : String := ""
  svParent : Status := .unknown "not evaluated"
  /-- the children's emitted texts: `holds` = the structural `designCheck`
  holds on the shipped design, so the CONDITIONAL forward theorem
  `design_sv_runN` applies given its width premises `SVBounds` (a run
  premise, not derived) — not a complete closed statement; `fails` =
  `designCheck` rejects it; `unknown` = not connected (why) -/
  svChildren : Status := .unknown "not connected (the parent's Verilog runs against an oracle for the children's outputs)"
  /-- the kernel-checked source → `DesignSV` endpoint
  (`f.machine_design_svN{n}`, `ships_design_svN`), if generated -/
  designEndpoint : Option Name := none
  /-- `outsCheck` (every child writes its outputs: assigned, or a leaf's
  combinational read target): with `designCheck`, there
  is AT MOST ONE closed run from given seeding and states within the emitted
  widths, and any closed run is the IR run (`design_sv_backN`,
  `design_sv_unique`) — a structural guarantee under those preconditions,
  NOT a statement that the run boundary or the use conditions hold, and
  apart from `SVCHILD:SOURCE` / the traces -/
  uniqueCheck : Status := .unknown "not evaluated"
  useConditions : List String := []
  reflection : List String := []
  deriving Inhabited

def Verdict.moduleTag (v : Verdict) : String :=
  let all : List (String × Status) :=
    [("checker", v.checker), ("childBound", v.childBound)] ++ v.boundaryChecks
  let fails := all.filter fun (_, s) => match s with | .fails _ => true | _ => false
  let unknowns := all.filter fun (_, s) => match s with | .unknown _ => true | _ => false
  let names (l : List (String × Status)) := ",".intercalate (l.map fun p => (p.1.take 40).toString)
  if !fails.isEmpty then "MOD:NOPREM:" ++ names fails
  else if !unknowns.isEmpty then "MOD:UNKNOWN:" ++ names unknowns
  else "MOD:PREM"

def Verdict.traceTag (v : Verdict) : String :=
  match v.boundaryReq, v.traces with
  | .notRequired _, [] => "TRACE:NOTREQUIRED"
  | .required, [] => "TRACE:UNTRACED"
  | _, ts =>
    let bad := ts.filter fun (_, t) => t != .matched
    let mism := bad.filter fun (_, t) => match t with | .mismatch _ => true | _ => false
    if !mism.isEmpty then "TRACE:MISMATCH"
    else if !bad.isEmpty then "TRACE:UNTRACED"
    else "TRACE:MATCHED"

def Verdict.svTag (v : Verdict) : String :=
  match v.svParent with
  | .holds => "SV:PARENT"
  | .fails _ => "SV:NO"
  | .unknown _ => "SV:UNKNOWN"

/-- The record: module premises, the boundary traces, the parent's emitted
Verilog, and the children's emitted Verilog (always open here). -/
def Verdict.svChildTag (v : Verdict) : String :=
  match v.svChildren with
  | .holds => match v.designEndpoint with
    -- structure checked AND the source theorem composed with the width
    -- derivation and design_sv_runN, kernel-checked
    | some _ => "SVCHILD:SOURCE"
    -- structure checked only: design_sv_runN applies given SVBounds
    | none => "SVCHILD:CHECKED"
  | .fails _ => "SVCHILD:NO"
  | .unknown _ => "SVCHILD:OPEN"

def Verdict.uniqTag (v : Verdict) : String :=
  match v.svChildren, v.uniqueCheck with
  | .holds, .holds => "CLOSED:AT-MOST-ONE"
  | .holds, _ => "CLOSED:UNPROVEN"
  | _, _ => "CLOSED:NA"

def Verdict.tag (v : Verdict) : String :=
  s!"{v.moduleTag}|{v.traceTag}|{v.svTag}|{v.svChildTag}|{v.uniqTag}"

/-- The theorem applies to the run GIVEN its run-boundary premises: the
module premises hold, and every required run boundary was MEASURED as
matching (or the route needs none beyond facts derived from the run). The
run boundaries stay premises of the theorem — a matching trace is a
measurement of them, not their discharge. -/
def Verdict.applies (v : Verdict) : Bool :=
  v.moduleTag == "MOD:PREM" &&
    (v.traceTag == "TRACE:MATCHED" || v.traceTag == "TRACE:NOTREQUIRED")

def Verdict.report (v : Verdict) : String :=
  let l1 := [s!"  checker: {v.checker.str}", s!"  childBound: {v.childBound.str}"]
  let l2 := v.boundaryChecks.map fun (n, s) => s!"  boundary check {n}: {s.str}"
  let l3 := (match v.boundaryReq with
      | .required => s!"  run boundaries: required (premises of the theorem; measured below, not proved)"
      | .notRequired w => s!"  run boundaries: none required ({w})") ::
    v.traces.map fun (n, t) => s!"  trace {n}: {t.str}"
  let l4 := [s!"  svParent: {v.svParent.str}",
    s!"  svChildren (structural designCheck): {v.svChildren.str}",
    s!"  at most one closed run under the seeding/state width preconditions (designCheck + outsCheck; design_sv_backN / design_sv_unique; structural, not a discharge of premises): {v.uniqueCheck.str}",
    match v.designEndpoint with
    | some e => s!"  source → DesignSV endpoint (svBounds_of_checks + design_sv_runN composed with the shipping theorem, kernel-checked): {e}"
    | none => "  source → DesignSV endpoint: not generated for this declaration (ships_design_svN not applied here; structure checked only)"]
  let l5 := v.useConditions.map fun u => s!"  use condition (caller's obligation): {u}"
  let l6 := v.reflection.map fun r => s!"  reflection boundary: {r}"
  "\n".intercalate (s!"{v.theoremName} [{v.route}]: {v.tag}" :: l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6)

/-- The instance modules of a body, resolved in a design. -/
def instMods (ms : List Sparkle.IR.AST.Module) (body : List Stmt) :
    List (String × Option Sparkle.IR.AST.Module) :=
  body.filterMap fun st => match st with
    | .inst mn _ _ => some (mn, moduleByName ms mn)
    | _ => none

def fullEntry (c : Name) : MetaM Sparkle.IR.AST.Module :=
  return (← Sparkle.Compiler.Elab.synthesizeCombinational c).1

/-- The calls' premise of a composed theorem with combinational children
(`R k mc`: the call's module is its child's full-entry run). With calls of
one child, `BoundH_of_each` reduces it to: every instance module is that
child's full-entry run — traced. With calls of several children the precise
premise (`BoundH`, by the call–instance correspondence) needs the wiring's
call ports, which this measurement does not reconstruct: UNTRACED. -/
def traceRuns (pre : String) (children : List Name) (ms : List Sparkle.IR.AST.Module)
    (body : List Stmt) : MetaM (List (String × Trace) × List String) := do
  let kids := children.eraseDups
  if kids.length != 1 then
    return ([(s!"{pre}calls of {kids.length} different children",
      .untraced "the call–instance correspondence (BoundH) is not reconstructed")],
      kids.map fun c => s!"{c}: EntryDefines / MachineDefines")
  let c := kids.head!
  let mcc ← fullEntry c
  let mut out : List (String × Trace) := []
  for (mn, mc?) in instMods ms body do
    match mc? with
    | none => out := out ++ [(s!"{pre}instance {mn}", .mismatch "does not resolve in the design")]
    | some mc =>
      out := out ++ [(s!"{pre}instance {mn} is the full-entry run of {c}",
        if mcc == mc then .matched else .mismatch "a recompile of the child gives another module")]
  return (out, [s!"{c}: EntryDefines / MachineDefines"])

structure BndEval where
  /-- a non-memory child was met: its run boundary is required -/
  required : Bool := false
  checks : List (String × Status) := []
  traces : List (String × Trace) := []
  reflection : List String := []

def BndEval.append (a b : BndEval) : BndEval :=
  ⟨a.required || b.required, a.checks ++ b.checks, a.traces ++ b.traces, a.reflection ++ b.reflection⟩

/-- The run boundary `Bnd raw D` of `c`'s composed theorem at depth `dep`,
on its core run `(raw, D)`: the decidable facts evaluated, the run
boundaries traced. -/
partial def evalBnd (pre : String) (c : Name) (dep : Nat) (raw : Sparkle.IR.AST.Module)
    (D : Design) : MetaM BndEval := do
  let r ← Tools.ShippingMachineCommand.readMachine c
  let calls := r.shape.insts.map (·.1)
  if r.shape.instFields.isEmpty then
    let (tr, refl) ← traceRuns pre calls D.modules raw.body
    return { required := true, checks := [(s!"{pre}kidsComb {c}",
               .ofBool (Tools.ShippingMachineDepthH.kidsComb D.modules raw.body) "a child is not assignments-only / local / wired")],
             traces := tr, reflection := refl }
  let seqKids := (calls.filter fun k => (Tools.ShippingMachineMemCommand.memWidths? k).isNone).eraseDups
  let mut out : BndEval := {}
  let insts := instMods D.modules raw.body
  for (mn, mc?) in insts do
    let some mc := mc? | out := out.append { traces := [(s!"{pre}instance {mn}", .mismatch "does not resolve")] }; continue
    -- a memory instance: no run boundary of its own — `MachineWired` DERIVES
    -- that it is the built memory module (the compiler's `memSelf` check,
    -- `find_memModule`); cross-checked here
    if let some (cb, aw, dw) := Sparkle.Compiler.MachMemory.memParams? mc then
      out := out.append { checks := [(s!"{pre}memory instance {mn} is the built memory module (derived: MachineWired / find_memModule)",
        .ofBool (decide (mc = (Sparkle.Compiler.MachMemory.memModule cb aw dw).1)) "not the built memory module")] }
  -- the boundary AS STATED: `BoundaryOf k` / `BoundaryOfN k` quantify over
  -- EVERY instance module of the body (`InstOfCall` does not bind the call
  -- index to the instance), so each sequential child's premise is evaluated
  -- on every instance — a memory instance or another child's instance makes
  -- it false (MISMATCH), not merely unmeasured
  for k in seqKids do
    out := out.append { required := true }
    let kr ← Tools.ShippingMachineCommand.readMachine k
    if kr.shape.insts.isEmpty then
      let mk ← fullEntry k
      for (mn, mc?) in insts do
        let some mc := mc? | continue
        out := out.append { traces := [(s!"{pre}BoundaryOf {k}: instance {mn} is the full-entry run of {k} (MachineRun)",
                              if mk == mc then .matched
                              else .mismatch s!"BoundaryOf {k} quantifies over every instance (InstOfCall does not bind the call); {mn} is not a run of {k}")] }
      out := out.append { reflection := [s!"{k}: MachineDefines / MachineCloses"] }
    else
      let (rawk, Dk) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore k [] false
      let dz := Sparkle.IR.ZeroWidth.dropZeroWidthModule rawk
      out := out.append {
        checks := [(s!"{pre}ExtendsAway {k}", .ofBool (Tools.ShippingHierPremisesBase.extendsAwayB rawk.name Dk.modules D.modules) "the designs disagree"),
                   (s!"{pre}NoInstOf {k}", .ofBool (Tools.ShippingHierPremisesBase.noInstOfB rawk.name rawk.body) "self-instance")],
        reflection := [s!"{k}: MachineDefines / MachineCloses"] }
      for (mn, mc?) in insts do
        let some mc := mc? | continue
        let same := dz == mc || Sparkle.IR.RefineCheck.mergeChecked dz == mc
        out := out.append { traces := [(s!"{pre}BoundaryOfN {k}: instance {mn} is the post-processing of a core run of {k} (MachineRunN)",
                              if same then .matched
                              else .mismatch s!"BoundaryOfN {k} quantifies over every instance (InstOfCall does not bind the call); {mn} is not a run of {k}")] }
      if dep == 0 then
        out := out.append { checks := [(s!"{pre}{k} has children", .fails "depth 0 is too shallow")] }
      else
        out := out.append (← evalBnd s!"{pre}{k} > " k (dep - 1) rawk Dk)
  return out

/-- The sequential / memory route: `f.machine_ships_hier` (depth `none`) or
`f.machine_ships_hierN{n}`. -/
def evalShipsHierSeq (declName : Name) (dep : Option Nat) : MetaM Verdict := do
  let (raw, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false
  let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
  let o := Sparkle.IR.OptCheck.checkedOptimize b
  let C := Tools.ShippingMachineLinked.childMap D.modules
  let wof := Tools.SVParser.RoundtripProof.moduleWof o
  let name := match dep with
    | some n => s!"{declName}.machine_ships_hierN{n}"
    | none => s!"{declName}.machine_ships_hier"
  -- the bound of the theorem GENERATED for this route (shared with the generator)
  let routeKind ← Tools.ShippingMachineShipsHierCommand.hierRoute declName
  let env ← getEnv
  let (route, bd, bdO) ← match dep with
    | some n => pure (s!"depth {n}: KSn, kidsMaskedN",
                  Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body,
                  Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules o.body)
    | none => do
      match routeKind with
      | .seq => pure ("depth 0, sequential children (memory reads among them): Reset1, kidsMixed",
                  Tools.ShippingMachineShipsHier.kidsMixed C b.body, Tools.ShippingMachineShipsHier.kidsMixed C o.body)
      | .mem => pure ("depth 0, memory reads: ResetM, kidsMem",
                  Tools.ShippingMachineShipsHier.kidsMem C b.body, Tools.ShippingMachineShipsHier.kidsMem C o.body)
  let bnd ← evalBnd "" declName (dep.getD 0) raw D
  let svc := Tools.ShippingHierShipsSV.shippedSVCheck C o wof
  return {
    theoremName := name
    checker := .ofBool (Tools.ShippingHierPremisesBase.shipsHierCheck C b) "shipsHierCheck rejects the run's module"
    childBound := .ofBool bd "a child's outputs are not bounded"
    boundaryChecks := bnd.checks
    traces := bnd.traces
    boundaryReq := if bnd.required then .required
      else .notRequired "memory reads only: a memory call's instance is the built memory module (MachineWired / find_memModule)"
    route := route
    svParent := .ofBool (svc && bdO) (if svc then "the shipped module's children are not bounded" else "shippedSVCheck rejects the shipped module")
    designEndpoint :=
      let e := match dep with
        | some n => declName ++ Name.mkSimple s!"machine_design_svN{n}"
        | none => declName ++ `machine_design_sv0
      if env.contains e then some e else none
    uniqueCheck := .ofBool (Tools.ShippingDesignSVBack.outsCheck C (dep.getD 0) o) "a child does not assign all its outputs"
    svChildren := match dep with
      | some n => .ofBool (Tools.ShippingDesignSV.designCheck C n o) s!"designCheck {n} rejects the shipped design"
      | none => match routeKind with
        | .seq => .ofBool (Tools.ShippingDesignSV.designCheck C 0 o) "designCheck 0 rejects the shipped design"
        -- memory children: the step IS flatKS = KSn _ 0 (composedG_of_Tmem); a
        -- memory leaf runs as `LeafRun` (combinational reads `.reads`, synchronous
        -- reads with their read latch), accepted by `leafCheck`
        | .mem => .ofBool (Tools.ShippingDesignSV.designCheck C 0 o) "designCheck 0 rejects the shipped design (a memory leaf fails leafCheck)"
    useConditions := ["the children start at reset (Reset1 / ResetM / ResetNk)",
                      "the inputs are within the declared and the emitted widths",
                      "the start registers are within their widths"]
    reflection := s!"{declName}: MachineDefines / MachineCloses" :: bnd.reflection }

/-- The combinational route: `f.machine_ships_hierH`. -/
def evalShipsHierH (declName : Name) : MetaM Verdict := do
  let (raw, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false
  let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
  let o := Sparkle.IR.OptCheck.checkedOptimize b
  let r ← Tools.ShippingMachineCommand.readMachine declName
  let (tr, refl) ← traceRuns "" (r.shape.insts.map (·.1)) D.modules raw.body
  let wof := Tools.SVParser.RoundtripProof.moduleWof o
  return {
    theoremName := s!"{declName}.machine_ships_hierH"
    checker := .ofBool (Tools.ShippingHierPremises.shipsHierHCheck D.modules b) "shipsHierHCheck rejects the run's module"
    -- the combinational route's child bound: the width-typed run (in its checker too)
    childBound := .ofBool (Tools.ShippingHierTyped.hierTyped (Tools.ShippingMachineLinked.childMap D.modules) b)
      "the body is not width-typed"
    traces := tr
    route := "combinational children: runModuleH, hierTyped"
    svParent := .ofBool (Tools.ShippingHierShipsSV.svHCheck D.modules o wof) "svHCheck rejects the shipped module"
    uniqueCheck := .ofBool (Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0 o)
      "a child does not assign all its outputs"
    -- the combinational linked run IS the depth-0 flatKS run when the
    -- children are kidsComb (runModuleTG_flat_of_H)
    designEndpoint := if (← getEnv).contains (declName ++ `machine_design_svH)
      then some (declName ++ `machine_design_svH) else none
    svChildren := .ofBool (Tools.ShippingMachineDepthH.kidsComb D.modules o.body &&
        Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0 o)
      "kidsComb or designCheck 0 rejects the shipped design"
    useConditions := ["the inputs are within the declared and the emitted widths",
                      "the start state is within its widths off the output ports"]
    reflection := s!"{declName}: MachineDefines / MachineCloses" :: refl }

/-- One measurement record and its details: `<tag>|GEN:FAIL:<why>` when the
theorem cannot be generated; `GEN:EXISTS` when it was already in the
environment (generation skipped, the evaluation still runs);
`<tag>|GEN:OK|EVAL:FAIL:<why>` when its premises could not be evaluated;
otherwise `<tag>|GEN:OK|<Verdict.tag>` and the verdict's report (every
field with its reason, persisted by the measurement). -/
def measure (tag : String) (exists_ : Bool) (gen : MetaM Unit) (eval : MetaM Verdict) :
    MetaM (String × String) := do
  let clean (m : MessageData) : MetaM String := do
    return (((← m.toString).replace "\n" " ").replace "|" "/").take 300 |>.toString
  let genTag := if exists_ then "GEN:EXISTS" else "GEN:OK"
  unless exists_ do
    try gen
    catch ex => return (s!"{tag}|GEN:FAIL:{← clean ex.toMessageData}", "")
  try
    let v ← eval
    return (s!"{tag}|{genTag}|{v.tag}", v.report)
  catch ex => return (s!"{tag}|{genTag}|EVAL:FAIL:{← clean ex.toMessageData}", "")

end Tools.ShippingPremiseEval
