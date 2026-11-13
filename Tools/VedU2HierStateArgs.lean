/-
  H2d: the facts and tactic lines the hierarchical checker's proof script uses for the ARGUMENTS of a child
  call that reads the parent's REGISTER STATE (`Tools/VedU2HierRegEntry.lean`).

  The open parent's `#verify_elab_deep` exports the state of its top loop (`_deep_state`) and of every
  nested loop (`_deep_state_n<j>`, `Tools/DeepNestedState.lean`).  An argument that IS one register (a direct
  slot) is tied to that register's reader by the pack of the state theorem that holds it; an argument that is a
  derived net over register state reads the loop inside a term, so the state theorems rewrite the loop to its
  pack and each reader equals the IR register (`hRd`).  The text produced here is what `scriptText` splices in.
-/
import Lean

namespace Tools.VedU2HierStateArgs

/-- What the script knows about the open parent's exported facts. -/
structure DeepInfo where
  /-- widths of the open circuit's register slots -/
  regWs : List Nat
  /-- number of inputs of the open circuit (data inputs, then one per child call) -/
  nIn : Nat
  /-- the parent's register output names, slot order -/
  pm : List String
  /-- H2c-state: the register slots the exported loop-state theorem's pack holds, in pack order (the top loop's
  block of the flat register list; a nested circuit's registers are not in it) -/
  block : List Nat := []
  /-- H2d: the exported state theorems of the NESTED loops (script spelling, register slots in pack order) -/
  nested : List (String × List Nat) := []
  /-- H2d: the copies of a nested circuit's registers (slot, the slot it is equal to) and the equation's name -/
  dups : List (Nat × Nat × String) := []
  /-- the open parent, as the script spells it -/
  openUser : String := ""

/-- The spellings the lines use. -/
structure Sp where
  /-- the top state theorem -/
  state : String
  /-- the deep circuit and its slot names -/
  deep : String
  nm : String
  /-- the IR state recurrence and the inputs' join, as the script spells them -/
  irS : String
  inpU : String
  /-- the arguments the state theorems are applied to -/
  sigsAll : String
  /-- `rd<slot>`'s name, given the slot -/
  rd : Nat → String

/-- The state theorems, the readers' equalities with the IR registers and the copies' equalities, as script lines;
and the names of the facts the per-port simps use. -/
def stateFacts (sp : Sp) (di : DeepInfo) : Array String × List String := Id.run do
  let mut X : Array String := #[]
  let mut stFacts : List String := ["hstA"]
  X := X.push s!"  have hstA := {sp.state} {sp.sigsAll} t"
  let nestedSlots := di.nested.flatMap (·.2)
  for (nm, _) in di.nested, jj in List.range di.nested.length do
    X := X.push s!"  have hstN{jj} := {nm} {sp.sigsAll} t"
    stFacts := stFacts ++ [s!"hstN{jj}"]
  let rdSlots := (di.block ++ nestedSlots ++ di.dups.map (·.1)).eraseDups
  for slot in rdSlots do
    X := X.push s!"  have hRd{slot} : ({sp.rd slot} {sp.sigsAll} t).toNat = {sp.irS} ins t ({slot} : Fin {di.regWs.length}) := by"
    X := X.push s!"    unfold {sp.irS} {sp.inpU}"
    X := X.push s!"    rw [Cdo.irState_eq {sp.deep} {sp.nm} hinj]"
    X := X.push s!"    rfl"
    if di.block.contains slot || nestedSlots.contains slot then stFacts := stFacts ++ [s!"hRd{slot}"]
  for (slot, c, dn) in di.dups do
    X := X.push s!"  have hSm{slot} : {sp.irS} ins t ({slot} : Fin {di.regWs.length}) = {sp.irS} ins t ({c} : Fin {di.regWs.length}) := by"
    X := X.push s!"    rw [← hRd{slot}, ← hRd{c}, {dn} {sp.sigsAll} t]"
    stFacts := stFacts ++ [s!"hSm{slot}"]
  return (X, stFacts)

/-- The fact `hAl<bn>` for an argument `ad` that IS the register `slot`: the argument signal is the register's
Signal-level state, read from the pack of the state theorem that holds the register (the top loop's, a nested
loop's, or through the equality of a nested circuit's copy). -/
def slotLines (sp : Sp) (di : DeepInfo) (bn ad : String) (slot : Nat) : Array String := Id.run do
  let mut X : Array String := #[]
  let dupT := di.dups.find? (·.1 == slot)
  let slot0 := match dupT with | some (_, c, _) => c | none => slot
  let (stName, pos) := if di.block.contains slot0 then (sp.state, di.block.idxOf slot0) else
    match di.nested.find? (·.2.contains slot0) with
    | some (nm, b) => (nm, b.idxOf slot0)
    | none => (sp.state, (di.block.idxOf? slot0).getD slot0)
  let sel := (List.range pos).foldl (fun s _ => s ++ ".2") "x" ++ ".1"
  if !di.block.contains slot0 && (di.nested.find? (·.2.contains slot0)).isNone then
    X := X.push s!"  fail \"H2D: register slot {slot} is in no exported state block (top {di.block}, nested {di.nested}, copies {di.dups})\""
  let dupRw := match dupT with | some (_, _, dn) => s!"rw [{dn} {sp.sigsAll} t]; " | none => ""
  X := X.push s!"  have hAl{bn} : (({ad} ins).val t).toNat = {sp.irS} ins t ({slot} : Fin {di.regWs.length}) := by"
  X := X.push s!"    have hst := {stName} {sp.sigsAll} t"
  X := X.push s!"    have h1 : ({ad} ins).val t = {sp.rd slot} {sp.sigsAll} t := by {dupRw}ved_kernel_exact (congrArg (fun x => {sel}) hst)"
  X := X.push s!"    unfold {sp.irS} {sp.inpU}"
  X := X.push s!"    rw [Cdo.irState_eq {sp.deep} {sp.nm} hinj, h1]"
  X := X.push s!"    rfl"
  return X

/-- The tactic lines closing the goal of one argument of a stateful call (`fj`: the call's stream definition,
`netSimpL`: the net simp set, `fs`: the facts in scope, `stU`: the state facts when the argument is not one of the
register slots). -/
def portLines (di : DeepInfo) (dbg : Bool) (bn : String) (isSlot : Bool) (ad fj netSimpL : String) (fs : List String)
    (stU : List String) : Array String := Id.run do
  let mut X : Array String := #[]
  let obs := "Tools.VedU1Contract.PTy.obs"
  let adU := if isSlot then "" else s!"{ad}, "
  let facts := ", ".intercalate fs
  unless stU.isEmpty do
    -- the state theorem speaks of `Signal.loop (loopFOf ..)` and of the arguments `PTy.sig ins ..`; the
    -- declaration's term has the loop unfolded and the signals unfolded: bring the facts to the same form
    for h in stU.filter (·.startsWith "hst") do
      X := X.push s!"    try unfold loopFOf at {h}"
    X := X.push s!"    try simp (config := \{ maxSteps := 2000000 }) [loopFOf, {adU}{obs}, {netSimpL}] at {" ".intercalate stU}"
  if stU.isEmpty then
    X := X.push s!"    simp [{fj}, {adU}{obs}, {netSimpL}, hin, {facts}]"
  else
    -- the argument's terms keep a nested circuit folded, the state theorems have it unfolded
    X := X.push s!"    simp (config := \{ maxSteps := 2000000 }) [{fj}, {adU}{obs}, {netSimpL}, hin, {facts}]"
    if dbg then X := X.push s!"    trace \"H2D-PORT {bn} after first simp\""
    X := X.push s!"    all_goals ved_unfold_helpers {di.openUser}"
    if dbg then X := X.push s!"    trace \"H2D-PORT {bn} after helpers\""
    X := X.push s!"    all_goals (try simp (config := \{ maxSteps := 2000000 }) [apply_ite BitVec.toNat, {netSimpL}, hin, {facts}, {", ".intercalate stU}])"
  return X

end Tools.VedU2HierStateArgs
