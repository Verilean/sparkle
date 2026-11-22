import Lean
import Tools.VedComposeConnect
import Tools.VedComposePrelude

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
  /-- measurement only (`VED_COMPOSE_NOFASTWR`): the closed width / register facts by the list-scanning `Bool`s, not the map-based ones -/
  slow : Bool := false

def sq (s : String) : String := "\"" ++ s ++ "\""

/-- The two lines that give `hin` (the conjunction of the input bounds) in the shape `simp` produced, through the once-proved
`Tools.VedComposePrelude.hin_bnd` and ONE kernel-checked equation (the list `L` is read off the declaration table). -/
def hinLines (ind : String) (binders : List String) (widths : List Nat) : List String :=
  let L := "[" ++ ", ".intercalate ((binders.zip widths).map fun (n, w) => s!"({sq ("_gen_" ++ n)}, {w})") ++ "]"
  [s!"{ind}have hin := Tools.VedComposePrelude.hin_bnd (ins t) (L := {L}) (by decide +kernel) (hok.1 t)",
   s!"{ind}simp only [Tools.VedComposePrelude.bndConj, Tools.VedComposePrelude.bndConjAux, Nat.reducePow] at hin"]

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
  L := L.push (if a.slow then s!"    have hWk : Tools.VedComposeResearch.WOKb ({dw}) {a.mod} {a.body} = true := by decide +kernel"
    else s!"    have hWk : Tools.VedComposeResearch.WOKb ({dw}) {a.mod} {a.body} = true := Tools.VedComposeConnect.wokbF_sound (by decide +kernel)")
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
  -- a one-bit port: the trace theorem is about `(bif b then 1 else 0 : BitVec 1).toNat`, the simp'd goal has `Bool.toNat b`
  L := L.push s!"      all_goals first | rw [{a.otrace}] | (rw [← Tools.VedComposePrelude.bit_obs]; erw [{a.otrace}])"
  L := L.push s!"      have hOutA := hasgF \"out\" _ rfl"
  L := L.push s!"      ved_connect_log \"port out via out_connect (fidelity {a.fidOut})\""
  -- the port cone's four closed facts: ONE map-based `specOkL` (default), or the four list-scanning evaluations (`slow`)
  let outTail := if a.slow then s!"(by decide +kernel) (by decide +kernel) {tabTxt a} (by rfl) (by decide +kernel)" else s!"hsO.1 hsO.2.1 {tabTxt a} hsO.2.2.2 hsO.2.2.1"
  unless a.slow do
    L := L.push s!"      have hAsgO : Tools.VedU2Hier.asgOf {a.body} \"out\" = some _ := rfl"
    L := L.push s!"      have hsO := Tools.VedComposeConnect.outSpecF_sound (deep := {a.deep}) (nm := {a.nm}) (d := {a.design}) (m := {a.mod}) (b0 := {a.body}) (needed := {neededTxt a}) (tab := {tabTxt a}) (nIn := {a.fuel}) (n2 := {a.fuel}) (n3 := {a.fuel}) (x := \"out\") hAsgO {a.fidOut} (by decide +kernel)"
  L := L.push s!"      exact Tools.VedComposeConnect.out_connect ({a.deep}) ({a.nm}) hinj ({a.inpU} ins) t _ {a.fidOut} {a.design} {a.mod} {a.body} {owT} {hwiT} {hriT} {hwrT} hWk ins p E hasgF hEin hEreg hEorc _ \"out\" hOutA {a.fuel} {a.fuel} {a.fuel} {neededTxt a} hrangeN {outTail} hV"
  -- ONE closed kernel check for all register slots (`RegsOk`); `regs_spec` hands each slot's four facts back
  let xsTxt := "([" ++ ", ".intercalate (a.regIn.map sq) ++ "] : List String)"
  L := L.push s!"    have hallR : Tools.VedComposeConnect.RegsOk {a.deep} {a.nm} {a.design} {a.mod} {a.body} {neededTxt a} {tabTxt a} {a.fuel} {a.fuel} {a.fuel} {xsTxt} = true := {if a.slow then "by decide +kernel" else "Tools.VedComposeConnect.regsOkF_sound (by decide +kernel)"}"
  -- the registers
  let holes := ", ".intercalate ((List.range k).map fun _ => "?_")
  L := L.push s!"    · {if k == 1 then "skip" else s!"refine ⟨{holes}⟩"}"
  for (x, i) in a.pm.zipIdx do
    let fid := a.fidR[i]!
    let w := a.regWs[i]!
    let inW := a.regIn[i]!
    L := L.push s!"      · have hsp := Tools.VedComposeConnect.regs_spec {a.deep} {a.nm} {a.design} {a.mod} {a.body} {neededTxt a} {tabTxt a} {a.fuel} {a.fuel} {a.fuel} {xsTxt} hallR ⟨{i}, by decide⟩ {sq inW} rfl _ {fid}"
    L := L.push s!"        have hcon : {a.irS} ins (t + 1) ⟨{i}, by decide⟩ = E {sq inW} := Tools.VedComposeConnect.reg_connect ({a.deep}) ({a.nm}) hinj ({a.inpU} ins) t ⟨{i}, by decide⟩ _ {fid} {a.design} {a.mod} {a.body} {owT} {hwiT} {hriT} {hwrT} hWk ins p E hasgF hEin hEreg hEorc {sq inW} {a.fuel} {a.fuel} {a.fuel} {neededTxt a} hrangeN hsp.1 hsp.2.1 {tabTxt a} hsp.2.2.2 hsp.2.2.1 hV"
    L := L.push s!"        have hlN : {a.irS} ins (t + 1) ⟨{i}, by decide⟩ < 2 ^ {w} := by"
    L := L.push s!"          have := hltS ins (t + 1) ⟨{i}, by decide⟩"
    L := L.push s!"          simpa using this"
    L := L.push s!"        ved_connect_log \"register {x} (slot {i}) via reg_connect (fidelity {fid})\""
    L := L.push s!"        have hmk := Tools.VedComposeConnect.mask_next (w := {dw} {sq x}) hcon (by rw [show {dw} {sq x} = {w} from by decide]; exact hlN)"
    L := L.push s!"        simpa [Sparkle.IR.Semantics.applyNexts, List.find?] using hmk"
  return L.toList


/-! ## The bundle-slice chain facts as one closed check

`bundleRead?`'s script lines (`Tools/VedU2HierMultiChain.lean`) prove each slice step's closed shape facts by their own kernel
evaluation.  `batchChain` reads the steps back off those lines (the shapes are fixed by the generator; a line of another shape is
left as it is), emits ONE `ChainOkF` check over all of them, and rewrites each step to take its facts from that check by index. -/

structure ChainBatch where
  sl : Array String := #[]
  cr : Array String := #[]
  wl : Array String := #[]

private def idxOrPush (a : Array String) (t : String) : Array String × Nat :=
  match a.findIdx? (· == t) with
  | some i => (a, i)
  | none => (a.push t, a.size)

/-- One line -> (the line to use, the updated batch). -/
def batchLine (hb : String) (B : ChainBatch) (l : String) : String × ChainBatch :=
  let pSlice := "    exact Tools.VedU2HierMulti.bundle_slice_fact ("
  let pRange := "    exact Tools.VedU2HierMulti.concat_range ("
  let pWd := "    have hwd : Tools.VedU1Contract.declWidth "
  if l.startsWith pSlice then
    match l.splitOn " E hasgF " with
    | [_, rest] =>
      match rest.splitOn "[" with
      | [pre, mid] =>
        match mid.splitOn "]" with
        | [names, post] =>
          let preT := (pre.splitOn " ").filter (· ≠ "")
          let postT := ((post.replace "(by decide)" "D").splitOn " ").filter (· ≠ "")
          match preT, postT with
          | [w, x, y, hi, lo], [k, "D", "D", pf, "D", "D", "D", "D", hr] =>
            let (sl, i) := idxOrPush B.sl s!"({w}, {x}, {y}, {hi}, {lo}, [{names}], {k})"
            (s!"    exact Tools.VedComposeConnect.slice_fact_F {hb} {i} E hasgF {w} {x} {y} {hi} {lo} [{names}] {k} (by decide +kernel) rfl {pf} {hr}",
             { B with sl })
          | _, _ => (l.replace "(by decide)" "(by decide +kernel)", B)
        | _ => (l.replace "(by decide)" "(by decide +kernel)", B)
      | _ => (l.replace "(by decide)" "(by decide +kernel)", B)
    | _ => (l.replace "(by decide)" "(by decide +kernel)", B)
  else if l.startsWith pRange then
    match l.splitOn " E hasgF " with
    | [_, rest] =>
      match rest.splitOn "[" with
      | [pre, mid] =>
        match mid.splitOn "]" with
        | [names, post] =>
          match (pre.splitOn " ").filter (· ≠ ""), ((post.replace "(by decide)" "D").splitOn " ").filter (· ≠ "") with
          | [z], ["D", "D"] =>
            let (cr, j) := idxOrPush B.cr s!"({z}, [{names}])"
            (s!"    exact Tools.VedComposeConnect.concat_range_F {hb} {j} E hasgF {z} [{names}] rfl", { B with cr })
          | _, _ => (l.replace "(by decide)" "(by decide +kernel)", B)
        | _ => (l.replace "(by decide)" "(by decide +kernel)", B)
      | _ => (l.replace "(by decide)" "(by decide +kernel)", B)
    | _ => (l.replace "(by decide)" "(by decide +kernel)", B)
  else if l.startsWith pWd && l.endsWith " := by decide" then
    -- `have hwd : declWidth <mod> "<n>" = <v> := by decide`
    match (l.drop pWd.length).toString.splitOn " " with
    | [m, n, "=", v, ":=", "by", "decide"] =>
      let (wl, j) := idxOrPush B.wl s!"({n}, {v})"
      (s!"    have hwd : Tools.VedU1Contract.declWidth {m} {n} = {v} := Tools.VedComposeConnect.wd_F {hb} {j} {n} {v} rfl", { B with wl })
    | _ => (l.replace "(by decide)" "(by decide +kernel)", B)
  else (l.replace "(by decide)" "(by decide +kernel)", B)

/-- The check line (at indent 2) and the rewritten step lines of every slice read of an instance block. -/
def batchChain (hb : String) (modTxt bodyTxt : String) (lss : List (Array String)) : String × List (Array String) := Id.run do
  let mut B : ChainBatch := {}
  let mut out : List (Array String) := []
  for ls in lss do
    let mut o : Array String := #[]
    for l in ls do
      let (l', B') := batchLine hb B l
      B := B'
      o := o.push l'
    out := out ++ [o]
  let lst (a : Array String) := "[" ++ ", ".intercalate a.toList ++ "]"
  (s!"  have {hb} : Tools.VedComposeConnect.ChainOkF {modTxt} {bodyTxt} {lst B.sl} {lst B.cr} {lst B.wl} = true := by decide +kernel", out)

end Tools.VedComposeConnectGen
