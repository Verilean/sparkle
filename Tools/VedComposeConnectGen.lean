import Lean
import Tools.VedComposeConnect

/-!
# VED compose, connection: the generated script of the parent's one-cycle step (option `ved.compose.connect`)

`hlocLines` produces the tactic lines that replace the per-cone closers of the `ved.compose.step` script (the chain walk, the
`bundle_slice_fact` reads and the big `simp` of every register's next value and of the port) by applications of the
connection lemmas of `Tools/VedComposeConnect.lean`:

* ONE closed width fact `WOKb` for the returned module,
* ONE needed-leaf range fact (`hrangeN`) from the facts the prelude already holds (register invariant, input contract, child output width),
* ONE leaf-value fact `hV` (`VOk`) per leaf of the table (returned name ↦ deep slot),
* per register `reg_connect`, for the port `out_connect`; the fidelity theorems `_deep_fidelity_*` enter by NAME (their type
  supplies the literal), the equation `renE .. (bn .. (inl ..)) = literal` is closed.

Nothing here is a statement; the lines are pasted into the generated proof of `U2HRStmt` (unchanged).
-/

namespace Tools.VedComposeConnectGen

/-- The data the generator needs from `scriptTextR` (names and small lists only). -/
structure ConnArgs where
  mod : String
  design : String
  body : String
  deep : String
  nm : String
  irS : String
  inpU : String
  inpC : String
  /-- the open parent's deep fidelity theorems: per register slot, and for the port -/
  fidR : List String
  fidOut : String
  /-- the text of `Ow ins y t` -/
  ow : String
  pm : List String
  regWs : List Nat
  /-- the wire that feeds each register slot -/
  regIn : List String
  /-- the data input wires (deep input order), and per input its bit-vector width (`none`: a `Bool` input) -/
  dataN : List String
  dataW : List (Option Nat)
  /-- instance output wires with the index of the call (deep oracle input) they carry -/
  insts : List (String × Nat)
  /-- the width of each instance output -/
  instW : List Nat
  nCalls : Nat
  fuel : Nat
  contract : String
  outs : String
  /-- `ved_open_..._eq` and `_deep_trace` -/
  oe : String
  otrace : String
  rst : String
  /-- each register of the body with the wire that feeds it, in body order -/
  regNext : List (String × String)
  outCfg : String

def sq (s : String) : String := "\"" ++ s ++ "\""

def tabOf (a : ConnArgs) : List (String × Nat) :=
  let nReg := a.pm.length
  let nData := a.dataN.length
  (a.pm.zipIdx.map fun (x, k) => (x, k)) ++ (a.dataN.zipIdx.map fun (x, j) => (x, nReg + j)) ++
    (a.insts.map fun (y, c) => (y, nReg + nData + c))

def tabTxt (a : ConnArgs) : String :=
  "([" ++ ", ".intercalate ((tabOf a).map fun (x, j) => s!"({sq x}, {j})") ++ "] : List (String × Nat))"

def neededOf (a : ConnArgs) : List String := a.pm ++ a.dataN ++ a.insts.map (·.1)

def neededTxt (a : ConnArgs) : String :=
  "([" ++ ", ".intercalate ((neededOf a).map sq) ++ "] : List String)"

/-- The `step_local` hypotheses the connection lemmas take (the same terms the `refine` passes). -/
def hwiT : String := "hb0.2.2.2.2.1"
def hriT : String := "hb0.2.2.2.2.2.1"
def hwrT : String := "hb0.2.2.2.2.2.2"

/-- Everything after the prelude (`intro E ..`, the input / register / oracle facts) of the `hloc` goal. -/
def hlocLines (a : ConnArgs) : List String := Id.run do
  let k := a.pm.length
  let dw := s!"Tools.VedU1Contract.declWidth {a.mod}"
  let owT := s!"(fun ins y t => {a.ow})"
  let common := s!"hinj ({a.inpU} ins) t"
  let mut L : Array String := #[]
  L := L.push s!"    have hWk : Tools.VedComposeResearch.WOKb ({dw}) {a.mod} {a.body} = true := by decide +kernel"
  -- R: the needed leaves' range
  L := L.push s!"    have hrangeN : ∀ y ∈ {neededTxt a}, E y < 2 ^ {dw} y := by"
  L := L.push s!"      intro y hy"
  L := L.push s!"      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy"
  let pat := " | ".intercalate ((neededOf a).map fun _ => "rfl")
  L := L.push s!"      rcases hy with {pat}"
  for (x, i) in a.pm.zipIdx do
    L := L.push s!"      · rw [hEr{i}, show {dw} {sq x} = {a.regWs[i]!} from by decide]; exact hlS{i}"
  for x in a.dataN do
    L := L.push s!"      · rw [hE_{x}]"
    L := L.push s!"        have h := hin"
    L := L.push s!"        simp [Tools.VedU1Contract.declWidth, {a.mod}] at h ⊢"
    L := L.push s!"        omega"
  for ((y, _), j) in a.insts.zipIdx do
    L := L.push s!"      · rw [show {dw} {sq y} = {a.instW[j]!} from by decide]; exact hlto{j}"
  -- the leaf values
  L := L.push s!"    have hV : Tools.VedComposeConnect.VOk {a.deep} {a.nm} ({a.inpU} ins) t {a.mod} {a.body} ins p {owT} {tabTxt a} := by"
  L := L.push s!"      intro q hq hlt"
  L := L.push s!"      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq"
  let patT := " | ".intercalate ((tabOf a).map fun _ => "rfl")
  L := L.push s!"      rcases hq with {patT}"
  for (x, i) in a.pm.zipIdx do
    L := L.push s!"      · dsimp only"
    L := L.push s!"        rw [Tools.VedComposeConnect.leafEnv_reg (m := {a.mod}) (b0 := {a.body}) (x := {sq x}) (by decide +kernel) (by decide +kernel)]"
    L := L.push s!"        exact hR{i}"
  for (x, j) in a.dataN.zipIdx do
    L := L.push s!"      · dsimp only"
    L := L.push s!"        rw [Tools.VedComposeConnect.leafEnv_in (m := {a.mod}) (b0 := {a.body}) (x := {sq x}) (by decide +kernel)]"
    L := L.push s!"        show ins t {sq x} = (({a.inpU} ins) t ⟨{j}, by decide⟩).toNat"
    L := L.push s!"        have hD : ins t {sq x} < 2 ^ {dw} {sq x} := by"
    L := L.push s!"          have h := hin"
    L := L.push s!"          simp [Tools.VedU1Contract.declWidth, {a.mod}] at h ⊢"
    L := L.push s!"          omega"
    match a.dataW[j]! with
    | none => L := L.push s!"        exact (Tools.VedComposeConnect.bit_toNat _ (by simpa [Tools.VedU1Contract.declWidth, {a.mod}] using hD)).symm"
    | some w => L := L.push s!"        exact (Tools.VedComposeConnect.bv_toNat {w} _ (by simpa [Tools.VedU1Contract.declWidth, {a.mod}] using hD)).symm"
  for ((y, c), _) in a.insts.zipIdx do
    let jj := a.dataN.length + c
    L := L.push s!"      · dsimp only"
    L := L.push s!"        rw [Tools.VedComposeConnect.leafEnv_orc (m := {a.mod}) (b0 := {a.body}) (x := {sq y}) (by decide +kernel) (by decide +kernel)]"
    L := L.push s!"        show {owT} ins {sq y} t = (({a.inpU} ins) t ⟨{jj}, by decide⟩).toNat"
    L := L.push s!"        first | rfl | simp [{a.inpU}, {a.inpC}_at_{jj}, {a.inpC}_at_mk_{jj}, Tools.VedU1Contract.PTy.obs]"
  -- the next-value list (the register-update shape; no cone is evaluated)
  let lits := ", ".intercalate (a.regNext.map fun (o, inp) => s!"({sq o}, Sparkle.IR.Semantics.mask ({dw} {sq o}) (E {sq inp}))")
  L := L.push s!"    have hn : Sparkle.IR.Semantics.regNexts ({dw}) (fun _ _ => 0) {a.body} E = some [{lits}] := by"
  L := L.push s!"      simp (config := \{ maxSteps := 4000000 }) [Sparkle.IR.Semantics.regNexts, {a.body}, Sparkle.IR.Semantics.evalExpr, hErst]"
  L := L.push s!"    refine ⟨_, hn, ?_, ?_⟩"
  -- the port
  L := L.push s!"    · intro o ho"
  L := L.push s!"      rw [hout] at ho"
  L := L.push s!"      simp [{a.outs}] at ho"
  L := L.push s!"      subst ho"
  L := L.push s!"      show E {sq "out"} = _"
  L := L.push s!"      all_goals simp {a.outCfg}[Tools.VedU1Contract.srcOf, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.applyIns, {a.contract}, Tools.VedU1Contract.OTy.obs, Tools.VedU1Contract.PTy.obs, {a.oe}, Tools.VedU1Contract.PTy.sig]"
  L := L.push s!"      all_goals rw [{a.otrace}]"
  L := L.push s!"      have hOutA := hasgF \"out\" _ rfl"
  L := L.push s!"      ved_connect_log \"port out via out_connect (fidelity {a.fidOut})\""
  L := L.push s!"      exact Tools.VedComposeConnect.out_connect ({a.deep}) ({a.nm}) hinj ({a.inpU} ins) t _ {a.fidOut} {a.design} {a.mod} {a.body} {owT} {hwiT} {hriT} {hwrT} hWk ins p E hasgF hEin hEreg hEorc _ \"out\" hOutA {a.fuel} {a.fuel} {neededTxt a} hrangeN (by decide +kernel) (by decide +kernel) {tabTxt a} (by rfl) (by decide +kernel) hV"
  -- the registers
  let holes := ", ".intercalate ((List.range k).map fun _ => "?_")
  L := L.push s!"    · {if k == 1 then "skip" else s!"refine ⟨{holes}⟩"}"
  for (x, i) in a.pm.zipIdx do
    let fid := a.fidR[i]!
    let w := a.regWs[i]!
    let inW := a.regIn[i]!
    L := L.push s!"      · have hcon : {a.irS} ins (t + 1) ⟨{i}, by decide⟩ = E {sq inW} := Tools.VedComposeConnect.reg_connect ({a.deep}) ({a.nm}) hinj ({a.inpU} ins) t ⟨{i}, by decide⟩ _ {fid} {a.design} {a.mod} {a.body} {owT} {hwiT} {hriT} {hwrT} hWk ins p E hasgF hEin hEreg hEorc {sq inW} {a.fuel} {a.fuel} {neededTxt a} hrangeN (by decide +kernel) (by decide +kernel) {tabTxt a} (by rfl) (by decide +kernel) hV"
    L := L.push s!"        have hlN : {a.irS} ins (t + 1) ⟨{i}, by decide⟩ < 2 ^ {w} := by"
    L := L.push s!"          have := hltS ins (t + 1) ⟨{i}, by decide⟩"
    L := L.push s!"          simpa using this"
    L := L.push s!"        ved_connect_log \"register {x} (slot {i}) via reg_connect (fidelity {fid})\""
    L := L.push s!"        have hmk := Tools.VedComposeConnect.mask_next (w := {dw} {sq x}) hcon (by rw [show {dw} {sq x} = {w} from by decide]; exact hlN)"
    L := L.push s!"        simpa [Sparkle.IR.Semantics.applyNexts, List.find?] using hmk"
  return L.toList

end Tools.VedComposeConnectGen
