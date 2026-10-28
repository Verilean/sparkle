import Tools.ShippingMachineCommand

/-! # `#shared_leaf_census`: the G8 class-coverage census (measurement only)

Frozen plan: `scripts/gaps/G8_CENSUS_FREEZE.md` (approved at c3e979f1). Test-only tool: not imported by
the compiler, no theorem.

For every constant of the listed modules (universe `U`, no name filter), a `defnInfo` constant is read by
`Tools.ShippingMachineCommand.readMachine` (the generators' reader) and the T0 conditions are evaluated in
the frozen order on the shapes of it, its wrappers and its leaf:
* common: R0 read, P1 slots, P2 insts / instFields, P3 ordinary non-memory entries, P4 paired entries, R1
  wrappers read;
* M (C4): M1 one shared leaf `L` called by every wrapper, M2 ordinary wrapper entries, M3 `L` read and every
  entry of `L` a memory;
* Q (C5): Q1 wrapper entries are `L` or one memory name per wrapper, Q2 `L` read with no entries, Q3 `L` not a
  memory name.

T0 PASS is a candidate only (`group`, the GEN-SHAPE fields and the full-data checks are not evaluated); a T0
FAIL is a non-membership relative to the `MachineDefines` shape tie. Every read runs with a fresh heartbeat
budget at the default limit; a runtime exception (heartbeats, recursion depth) is READ-TIMEOUT (unknown). -/

namespace Tools.ShippingSharedLeafCensus
open Lean Meta Elab Command
open Sparkle.Compiler.Elab (MachineShape)

/-- The outcome of one read. -/
inductive ReadRes where
  | ok (s : MachineShape)
  | fail (msg : String)
  | timeout (msg : String)

/-- `readMachine` with a fresh heartbeat budget, state restored, runtime exceptions caught. -/
def readOne (c : Name) : MetaM ReadRes :=
  withoutModifyingState <| withCurrHeartbeats <|
    tryCatchRuntimeEx
      (do let r ← Tools.ShippingMachineCommand.readMachine c; pure (.ok r.shape))
      (fun ex => do
        let msg := ((← ex.toMessageData.toString).splitOn "\n").headD ""
        if ex.isRuntime then pure (.timeout msg) else pure (.fail msg))

/-- A per-command cache of reads (callees are read once). -/
abbrev Cache := Std.HashMap Name ReadRes

def readC (cache : IO.Ref Cache) (c : Name) : MetaM ReadRes := do
  if let some r := (← cache.get).get? c then return r
  let r ← readOne c
  cache.modify (·.insert c r)
  return r

/-- A T0 verdict: `PASS`, `FAIL:<cond>`, or `UNKNOWN:<cond>` (a callee read timed out). -/
abbrev Verdict := String

def isMemName (c : Name) : Bool := (Sparkle.Compiler.MachMemory.memChild? c).isSome

/-- P1–P4 on the top's shape: the wrapper list (entries `2i`) or the failing condition. -/
def common (s : MachineShape) : Except String (List Name) := do
  if s.layout.slots.isEmpty then throw "P1"
  if s.insts.isEmpty || s.instFields.isEmpty then throw "P2"
  for x in s.instTagged do
    if x.2.child?.isSome || isMemName x.1 then throw "P3"
  let ns := s.instTagged.map (·.1)
  if ns.length % 2 != 0 then throw "P4"
  let mut ws : List Name := []
  for i in [0:ns.length / 2] do
    let a := ns.getD (2 * i) .anonymous
    let b := ns.getD (2 * i + 1) .anonymous
    if a != b then throw "P4"
    ws := ws ++ [a]
  return ws

/-- Read every name; the shapes, or `FAIL:<cond>` / `UNKNOWN:<cond>`. -/
def readAll (cache : IO.Ref Cache) (cond : String) (ws : List Name) :
    MetaM (Except Verdict (List MachineShape)) := do
  let mut out : List MachineShape := []
  for w in ws do
    match ← readC cache w with
    | .ok s => out := out ++ [s]
    | .fail _ => return .error s!"FAIL:{cond}"
    | .timeout _ => return .error s!"UNKNOWN:{cond}"
  return .ok out

/-- M1–M3 on the wrappers' shapes. -/
def verdictM (cache : IO.Ref Cache) (wss : List MachineShape) : MetaM Verdict := do
  let names := wss.flatMap (fun s => s.insts.map (·.1))
  if wss.any (fun s => s.insts.isEmpty) || names.eraseDups.length != 1 then return "FAIL:M1"
  if wss.any (fun s => s.instTagged.any (fun x => x.2.child?.isSome)) then return "FAIL:M2"
  let l := names.headD .anonymous
  match ← readC cache l with
  | .fail _ => return "FAIL:M3"
  | .timeout _ => return "UNKNOWN:M3"
  | .ok sl =>
    if sl.instTagged.all (fun x => x.2.child?.isSome) then return "PASS" else return "FAIL:M3"

/-- Q1–Q3 on the wrappers' shapes (`PASS-noleafcall` when no wrapper calls a non-memory name). -/
def verdictQ (cache : IO.Ref Cache) (wss : List MachineShape) : MetaM Verdict := do
  for s in wss do
    let memNs := ((s.insts.map (·.1)).filter isMemName).eraseDups
    if memNs.length > 1 then return "FAIL:Q1"
  let ords := (wss.flatMap (fun s => (s.insts.map (·.1)).filter (!isMemName ·))).eraseDups
  if ords.length > 1 then return "FAIL:Q1"
  let some l := ords.head? | return "PASS-noleafcall"
  match ← readC cache l with
  | .fail _ => return "FAIL:Q2"
  | .timeout _ => return "UNKNOWN:Q2"
  | .ok sl =>
    if !sl.insts.isEmpty then return "FAIL:Q2"
    if isMemName l then return "FAIL:Q3"
    return "PASS"

/-- The name category (secondary breakdown only; the census itself filters nothing). -/
def generatedMarks : List String :=
  ["machineData", "machineSource", "machineInits", "machineCall", "machineExt", "machineObs",
   "machine_", "gateValue", "gateDom", "gateBinders", "gateSort", "gateTerm", "gateBpos",
   "gateVpos", "gateVw", "gate_", "oneout_", "closes_"]

def nameCat (env : Environment) (c : Name) : String :=
  let last := match c with | .str _ s => s | _ => ""
  let prefixIsDef := match c with
    | .str p _ => match env.find? p with | some (.defnInfo _) => true | _ => false
    | _ => false
  if c.isInternal then "internal"
  else if let some m := ["match_", "proof_", "eq_", "sizeOf", "inst"].find? (last.startsWith ·) then m
  else if prefixIsDef && generatedMarks.any (last.startsWith ·) then "generated-mark"
  else if last.endsWith "_regen" then "_regen"
  else if last.endsWith "_gap" then "_gap"
  else "plain"

def kindStr : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

/-- One census row: `class`, `M`, `Q` (`-` when not evaluated). -/
structure Row where
  decl : Name
  kind : String
  cat : String
  cls : String
  m : Verdict := "-"
  q : Verdict := "-"

def Row.text (r : Row) : String := s!"{r.decl}|{r.kind}|{r.cat}|{r.cls}|M:{r.m}|Q:{r.q}"

/-- The row of one constant. -/
def censusOne (cache : IO.Ref Cache) (c : Name) : MetaM Row := do
  let env ← getEnv
  let some ci := env.find? c | throwError "{c}: unknown constant"
  let base : Row := { decl := c, kind := kindStr ci, cat := nameCat env c, cls := "" }
  unless ci matches .defnInfo _ do return { base with cls := "UNEVALUATED-KIND" }
  match ← readC cache c with
  | .fail _ => return { base with cls := "READ-FAIL" }
  | .timeout _ => return { base with cls := "READ-TIMEOUT" }
  | .ok s =>
    if s.insts.isEmpty then return { base with cls := "LEAF" }
    match common s with
    | .error p => return { base with cls := "PARENT", m := s!"FAIL:{p}", q := s!"FAIL:{p}" }
    | .ok ws =>
      match ← readAll cache "R1" ws with
      | .error v => return { base with cls := "PARENT", m := v, q := v }
      | .ok wss => return { base with cls := "PARENT", m := ← verdictM cache wss, q := ← verdictQ cache wss }

def newCache : MetaM (IO.Ref Cache) := IO.mkRef {}

/-- Counts of a list of keys, sorted. -/
def tally (ks : List String) : List (String × Nat) :=
  let m : Std.HashMap String Nat := ks.foldl (fun m k => m.insert k (m.getD k 0 + 1)) {}
  (m.toList.toArray.qsort (fun a b => a.1 < b.1)).toList

def tallyText (title : String) (ks : List String) : String :=
  title ++ ": " ++ ", ".intercalate ((tally ks).map fun (k, n) => s!"{k}={n}")

/-- The totals of a set of rows (all of `U`, then the `plain` subset as the secondary breakdown). -/
def totals (rows : List Row) : String :=
  let eligible := rows.filter (fun r => r.m.startsWith "PASS" || r.q.startsWith "PASS")
  let unknown := rows.filter (fun r => r.m.startsWith "UNKNOWN" || r.q.startsWith "UNKNOWN")
  let part (rs : List Row) : String :=
    "\n".intercalate [
      s!"constants={rs.length}",
      tallyText "class" (rs.map (·.cls)),
      tallyText "kind (UNEVALUATED-KIND)" ((rs.filter (·.cls == "UNEVALUATED-KIND")).map (·.kind)),
      tallyText "M" ((rs.filter (·.cls == "PARENT")).map (·.m)),
      tallyText "Q" ((rs.filter (·.cls == "PARENT")).map (·.q))]
  "\n".intercalate [
    "== U (all constants of the listed modules)", part rows,
    s!"T0-eligible (M or Q PASS)={eligible.length}: {eligible.map (·.decl)}",
    s!"UNKNOWN callee reads={unknown.length}: {unknown.map (·.decl)}",
    "== secondary breakdown: name category", tallyText "cat" (rows.map (·.cat)),
    "== secondary breakdown: the plain subset", part (rows.filter (·.cat == "plain"))]

syntax (name := sharedLeafCensus) "#shared_leaf_census " str " [" ident,* "]" : command

/-- `#shared_leaf_census "LABEL" [M₁, …]`: the census of every constant of the modules `Mᵢ`. Rows are logged and
recorded, with the totals, as the `String` constants `G8Census.LABEL.rows` / `G8Census.LABEL.totals`. -/
@[command_elab sharedLeafCensus] def elabCensus : CommandElab := fun stx => do
  let label := stx[1].isStrLit?.getD ""
  let mods : Array Name := stx[3].getSepArgs.map (·.getId)
  let env ← getEnv
  let mut idxs : Std.HashSet Nat := {}
  for m in mods do
    match env.getModuleIdx? m with
    | some i => idxs := idxs.insert i.toNat
    | none => throwError "#shared_leaf_census: module {m} is not imported"
  let cs : Array Name := Std.HashMap.fold (fun acc c _ =>
    match env.getModuleIdxFor? c with
    | some i => if idxs.contains i.toNat then acc.push c else acc
    | none => acc) #[] env.constants.map₁
  let cs := cs.qsort (fun a b => a.toString < b.toString)
  let rows ← liftTermElabM do
    let cache ← newCache
    cs.toList.mapM (fun c => (censusOne cache c : MetaM Row))
  let rowsText := "\n".intercalate (rows.map (·.text))
  let tot := s!"modules={mods.size}\n" ++ totals rows
  logInfo m!"G8 CENSUS {label} ROWS\n{rowsText}"
  logInfo m!"G8 CENSUS {label} TOTALS\n{tot}"
  let pre := `G8Census ++ Name.mkSimple label
  for (n, v) in [(`rows, rowsText), (`totals, tot)] do
    liftCoreM <| addDecl <| .defnDecl <|
      mkDefinitionValEx (pre ++ n) [] (mkConst ``String) (mkStrLit v) .opaque .safe [pre ++ n]

end Tools.ShippingSharedLeafCensus
