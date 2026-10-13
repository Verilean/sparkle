import Lean.Elab.Command
import Tools.ShippingLeafSweepCommand
import Tools.ShippingCombLeafClosedCommand
import Tools.ShippingGateDesignCommand
import Tools.ShippingDesignCoverage

/-! # `#corpus_design_sweep`: the design-level generators on the declarations of ONE file (round par/b-36)

WRITTEN, NOT BUILT. NOT RUN on any corpus file. The command behind
`scripts/shipping-coverage/design_tail.lean.in` (driver:
`scripts/shipping-coverage/design_sweep.sh`; plan and cost model:
`docs/parallel/B-corpus-plan.md`).

    #corpus_design_sweep "ROWS" "TOPS" "LABEL" "MODE"

* `ROWS`: a file; one line is APPENDED per candidate, after its chain (and
  one `…|FILE-DONE|…` line at the end). Nothing is truncated.
* `TOPS`: a file of identifiers (one per line: what the driver's `grep`
  found after `#synthesizeVerilog` & co.); may be missing or empty.
* `LABEL`: the corpus file's path, copied into every row.
* `MODE`: `"marked"` — candidates are the definitions DECLARED IN THE FILE
  BEING ELABORATED that are `@[hardware_module]`, or named in `TOPS`, or
  already carry generated data (`f.machineData` / `f.gateValue`); `"all"` —
  in addition every other local definition the machine reader reads.

No list from a previous measurement is read (`machine_decls.txt` is the
output of the full-corpus pass 1): the class of a candidate is what the
READERS say in this environment —

    machine route:  `Tools.ShippingMachineCommand.readMachine f` succeeds
      LEAF-REG      no call entry, ≥ 1 register slot   → generate f; #leaf_sweep f
      LEAF-COMB     no call entry, no slot             → generate f; #comb_closed_sweep f
      PARENT        ≥ 1 call entry                     → NOT ATTEMPTED in this version
                    (the row records slots, callees, structure fields)
    GATE            the reader refuses; `mixedCertifiedShape?` (no instance
                    predicate) takes the entry constant → #gate_design_sweep f
    GATE-INST       taken only WITH the instance predicate (a parent without
                    a register over combinational calls) → NOT ATTEMPTED (no generator)
    NOT-MACHINE     none of them (legacy route, or not hardware): the
                    reader's message is the row's note

The predicted class is the READER's, not the route a real compile took;
they can differ. A row is `COVERED <form>` only when the design-level
constant exists AFTER the chain and passes the census re-check
(`Tools.ShippingDesignCoverage.recheck`: 0 NOT ALLOWED premises, no checker
constant, a `DesignSV` conclusion) — a statement whose premises are the run
and the reflection, so a wrong prediction cannot produce a false theorem.

Every step: a `CORPUS START <decl> <step>` line on stderr BEFORE it runs,
its own `try`, the environment put back on an exception. The sweeps called
(`#leaf_sweep`, `#comb_closed_sweep`, `#gate_design_sweep`) are themselves
never an error. The command is an error in no case; it does not assert a
class or a count.

No reflected data is evaluated in compiled code: the classification reads
`readMachine`'s result (Meta values).

Row format (`|`-separated, one line):

    LABEL|decl|flags|class|outcome|form|ms|note

`flags`: `tagged`, `top`, `data`, `read` (why it is a candidate);
`outcome`: `COVERED`, `NOT-COVERED` (chain ran, no endpoint passing the
re-check), `NOT-ATTEMPTED`, `ERROR`. -/
namespace Tools.ShippingCorpusSweep
open Lean Meta Elab Command
open Sparkle.Compiler.Elab

private def flat (s : String) (n : Nat) : String :=
  let t := (s.replace "\n" " ").replace "|" "/"
  if t.length ≤ n then t else String.ofList (t.toList.take n) ++ " …"

/-- The design-level leaf forms this version can generate. -/
def leafForms : List String := ["machine_design_leaf0", "machine_design_comb0", "gate_design0"]

/-- Prefixes of the last component of GENERATED constants (`f.machineData`,
`f.gate_child`, …): a local definition `p.s` with `p` a definition and `s`
starting with one of these is never a candidate. -/
def generatedMarks : List String :=
  ["machineData", "machineSource", "machineInits", "machineCall", "machineExt", "machineObs",
   "machine_", "gateValue", "gateDom", "gateBinders", "gateSort", "gateTerm", "gateBpos",
   "gateVpos", "gateVw", "gate_", "oneout_", "closes_"]

private def prefixIsDef (env : Environment) (n : Name) : Bool :=
  match n with
  | .str p _ => match env.find? p with
    | some (.defnInfo _) => true
    | _ => false
  | _ => false

private def lastStr (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => ""

/-- The user-facing string of a (possibly private) name. -/
def userString (n : Name) : String :=
  match Lean.privateToUserName? n with
  | some u => toString u
  | none => toString n

/-- One candidate. -/
structure Cand where
  decl : Name
  flags : List String

/-- The candidates of the file being elaborated (file header). -/
def candidates (env : Environment) (tops : List String) (all : Bool) : MetaM (Array Cand) := do
  let locals : List Name := env.constants.map₂.foldl (fun acc c _ => c :: acc) []
  let mut out : Array Cand := #[]
  for c in locals do
    let isDef : Bool := match env.find? c with
      | some (.defnInfo _) => true
      | _ => false
    unless isDef do continue
    if c.isInternal then continue
    if (["match_", "proof_", "eq_", "sizeOf", "inst"].any fun m => (lastStr c).startsWith m) then continue
    let last := lastStr c
    if prefixIsDef env c && (generatedMarks.any fun m => last.startsWith m) then continue
    if last.endsWith "_regen" || last.endsWith "_gap" then continue
    let us := userString c
    let mut flags : List String := []
    if Sparkle.Compiler.isHardwareModule env c then flags := flags ++ ["tagged"]
    if tops.any fun t => t == us || us.endsWith ("." ++ t) then flags := flags ++ ["top"]
    if env.contains (c ++ `machineData) || env.contains (c ++ `gateValue) then
      flags := flags ++ ["data"]
    if flags.isEmpty && all then
      let ok ← try
          discard <| Tools.ShippingMachineCommand.readMachine c
          pure true
        catch _ => pure false
      if ok then flags := ["read"]
    unless flags.isEmpty do out := out.push { decl := c, flags }
  return out.qsort fun a b => a.decl.toString < b.decl.toString

/-- The class of a candidate by the readers, and a note. -/
def classify (env : Environment) (f : Name) : MetaM (String × String) := do
  let r? ← try
      let r ← Tools.ShippingMachineCommand.readMachine f
      pure (Except.ok r)
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (Except.error msg)
  match r? with
  | .ok r =>
    let slots := r.shape.layout.slots.length
    let calls := (r.shape.insts.map (·.1)).eraseDups
    if calls.isEmpty then
      if slots == 0 then return ("LEAF-COMB", "no call entry, no register slot")
      else return ("LEAF-REG", s!"no call entry, {slots} register slot(s)")
    else
      return ("PARENT", s!"{slots} register slot(s), callees {calls}, structure fields {r.shape.instFields}")
  | .error msg =>
    let gate : Option (Bool × Bool) ← try
        let ci0 ← getConstInfo f
        let ci := entryConst true false [] ci0 (instancePredicate env) (userInliner env)
          (structEnv env)
        let first : Bool := (certifiedShape? false [] ci).isSome
        let plain : Bool := first || (mixedCertifiedShape? false [] ci).isSome
        let withI : Bool := (mixedCertifiedShape? false [] ci (instancePredicate env)).isSome
        pure (some (plain, withI))
      catch _ => pure none
    match gate with
    | some (true, _) => return ("GATE", s!"the machine reader refuses it ({flat msg 160}); a combinational gate takes the entry constant")
    | some (false, true) => return ("GATE-INST", s!"the machine reader refuses it ({flat msg 160}); the mixed gate takes it only with the instance predicate")
    | _ => return ("NOT-MACHINE", flat msg 300)

/-- The design-level leaf constants of `f` in the environment that pass the
census re-check, and those that do not. -/
def covered (f : Name) : MetaM (List String × List String) := do
  let env ← getEnv
  let mut ok : List String := []
  let mut bad : List String := []
  for s in leafForms do
    let c := f ++ Name.mkSimple s
    if env.contains c then
      let ch ← Tools.ShippingDesignCoverage.recheck c
      if ch.ok then ok := ok ++ [s] else bad := bad ++ [s]
  return (ok, bad)

private def appendRow (path : String) (line : String) : IO Unit := do
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn line
  h.flush

/-- One step in its own `try`: on an exception the environment and the
message log are put back and the message is returned. -/
def step (decl : Name) (name : String) (x : CommandElabM Unit) : CommandElabM (Option String) := do
  IO.eprintln s!"CORPUS START {decl} {name}"
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    x
    return none
  catch ex =>
    let msg ← ex.toMessageData.toString
    setEnv savedEnv
    modify fun st => { st with messages := savedMsgs }
    return some s!"{name}: {flat msg 200}"

elab "#corpus_design_sweep " rows:str tops:str label:str mode:str : command => do
  let rowsPath := rows.getString
  let lbl := label.getString
  let all : Bool := mode.getString == "all"
  IO.eprintln s!"CORPUS START-FILE {lbl}"
  let topsL : List String ← try
      let ls ← IO.FS.lines tops.getString
      pure ((ls.toList.map fun l =>
        String.ofList (l.toList.filter fun ch => !ch.isWhitespace)).filter (· != ""))
    catch _ => pure []
  let env0 ← getEnv
  let cands ← liftTermElabM (candidates env0 topsL all)
  logInfo m!"CORPUS CANDIDATES {lbl}: {cands.size} ({cands.toList.map fun c => userString c.decl}); tops given {topsL}; mode {mode.getString}"
  let mut nCov : Nat := 0
  for c in cands do
    let f := c.decl
    let t0 ← IO.monoMsNow
    IO.eprintln s!"CORPUS START {f} classify"
    let (cls, note0) ← liftTermElabM (classify (← getEnv) f)
    let id : Ident := mkIdent f
    let mut notes : List String := [note0]
    let mut attempted : Bool := true
    if cls == "LEAF-REG" || cls == "LEAF-COMB" then
      unless (← getEnv).contains (f ++ `machine_sound) do
        if let some e ← step f "generate"
            (discard <| liftTermElabM (Tools.ShippingMachineCommand.generate f (checkCloses := false))) then
          notes := notes ++ [e]
      if cls == "LEAF-REG" then
        if let some e ← step f "leaf_sweep" (do elabCommand (← `(command| #leaf_sweep $id))) then
          notes := notes ++ [e]
      else
        if let some e ← step f "comb_closed_sweep"
            (do elabCommand (← `(command| #comb_closed_sweep $id))) then
          notes := notes ++ [e]
    else if cls == "GATE" then
      if let some e ← step f "gate_design_sweep"
          (do elabCommand (← `(command| #gate_design_sweep $id))) then
        notes := notes ++ [e]
    else
      attempted := false
    IO.eprintln s!"CORPUS START {f} recheck"
    let cov : List String × List String ← try
        liftTermElabM (covered f)
      catch _ => pure ([], [])
    let outcome : String :=
      if !cov.1.isEmpty then "COVERED"
      else if !attempted then "NOT-ATTEMPTED"
      else "NOT-COVERED"
    if !cov.1.isEmpty then nCov := nCov + 1
    unless cov.2.isEmpty do
      notes := notes ++ [s!"present but not passing the re-check: {cov.2}"]
    let ms := (← IO.monoMsNow) - t0
    let form := if cov.1.isEmpty then "-" else String.intercalate "," cov.1
    let line := s!"{lbl}|{userString f}|{String.intercalate "," c.flags}|{cls}|{outcome}|{form}|{ms}|{flat (String.intercalate "; " notes) 500}"
    logInfo m!"CORPUS ROW {line}"
    try
      appendRow rowsPath line
    catch ex =>
      logInfo m!"CORPUS: the row could not be written to {rowsPath}: {← ex.toMessageData.toString}"
  let done := s!"{lbl}|-|-|FILE-DONE|{cands.size} candidates, {nCov} COVERED|-|0|every candidate of this file has its row above"
  logInfo m!"CORPUS ROW {done}"
  try
    appendRow rowsPath done
  catch _ => pure ()
  IO.eprintln s!"CORPUS END-FILE {lbl}"

end Tools.ShippingCorpusSweep
