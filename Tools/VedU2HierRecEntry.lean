import Tools.VedU2HierEntry
import Tools.VedU2HierRecOr
import Tools.VedU2HierRecReg

/-!
# The nested entry (option `ved.compose.nested`, default OFF; CANDIDATE, Tools/VedU2HierRec.lean)

`checkU2HN` proves `U2HRStmtR c m d decl` for a REGISTER-FREE parent whose instances are NON-LEAF
(middle) modules whose own sub-designs are all leaves.  The old entries and statements are not
touched; the option gates the dispatch (`Tools/VedU2HierRegEntry.lean`, `vedU2HierEntryR`).

Per middle module `mid` (a direct child of the parent):

1. the middle module's entry runs FIRST on its own declaration (`midEntry`, the H2b entry
   `checkU2HR`: its own synthesis, its own sub-design `dC`, its own theorem `U2HRStmt ..`);
2. the CACHE: a stored theorem `mid.ved_u2r : U2HRStmtR c mid dC decl` is reused only after it is
   CHECKED against the parent's real design: the statement is the exact `U2HRStmtR` application of
   the stored constants, the stored module constant IS the parent's module (`toExpr` equality, the
   key is the module VALUE, not its name), the stored statement function is the declaration's, the
   stored design decodes to a design whose top is `mid` and whose modules are all modules of the
   parent's design; a stored theorem that fails the check is refused (never used);
3. `U2HRStmtR_of_S` converts the stored depth-1 theorem (`ved_u1`, `U2HRStmt`) to the recursive
   statement on the sub-design `dC` (an all-leaf design: `allLeafB dC = true`, decided);
4. the parent is composed from the middle module's theorem: `kid_inst_R` (the instance fact),
   `succF_of_theoremR` (success), the order facts of the real design `d` for the middle module
   (`OrderHS d mid`, kernel `decide` on `d`), and `outputsOnHSR_of_oracle`.  The grandchildren are
   NOT unfolded: they occur only through the middle module's theorem and `dC`.
-/

namespace Tools.VedU2HierRecEntry

open Lean Meta Elab Term Command
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
open Tools.VedU2HierEntry

register_option ved.compose.nested : Bool := {
  defValue := false
  descr := "nested hierarchy: a register-free parent over non-leaf (middle) modules, proved from the middle module's own theorem (statement U2HRStmtR; candidate)"
}

/-- The sub-design of a middle module: the modules of the parent's design reachable from it by
instances (a sublist of `d.modules`, in its order), the middle module as top. -/
def subDesignOf (d : Design) (cm : Sparkle.IR.AST.Module) : Design :=
  let names := Tools.VedU2HierRec.reachN d d.modules.length ((instDecls cm.body).map (·.1))
  { topModule := cm.name, modules := d.modules.filter (fun x => names.contains x.name && x.name != cm.name) }

/-- What the parent's proof needs about one middle module. -/
structure MidInfo where
  kid : Kid
  /-- the stored sub-design constant (the middle module's own design) -/
  dC : Name
  /-- the stored recursive theorem `U2HRStmtR` -/
  thmR : Name
  /-- the checked arrangement of the middle module's body in the PARENT's design -/
  bodyC : Name
  /-- the theorem was found stored (and checked), not produced by this call -/
  hit : Bool
  deriving Inhabited

/-- A non-leaf module of the parent's design, with the arrangement of its body in the PARENT's design
(`OrderHS d x`: the witness constant) and its module constant (from its own entry). -/
structure NlInfo where
  modC : Name
  bodyC : Name
  deriving Inhabited

/-- The stored recursive theorem of `cdecl`, CHECKED against the parent's module `cm` and design `d`.
Returns the refusal reason on a mismatch. -/
def checkStored (thmR : Name) (cdecl : Name) (cstmt : Lean.Expr) (cm : Sparkle.IR.AST.Module)
    (d : Design) : MetaM (Option String) := do
  let env ← getEnv
  let nmC := HNames.ofBase cdecl
  let some (.thmInfo ti) := env.find? thmR | return some s!"{thmR} is not a theorem"
  unless ti.type.getAppFn.isConstOf ``Tools.VedU2HierRec.U2HRStmtR do
    return some s!"{thmR}: the stored statement is not U2HRStmtR"
  let args := ti.type.getAppArgs
  unless args.size == 4 do return some s!"{thmR}: unexpected statement arity"
  unless args[0]! == Lean.mkConst nmC.contract && args[1]! == Lean.mkConst nmC.mod &&
      args[2]! == Lean.mkConst nmC.design do
    return some s!"{thmR}: the statement is not over the stored constants {nmC.contract}, {nmC.mod}, {nmC.design}"
  unless args[3]! == cstmt do
    return some s!"{thmR}: the stored statement function is not the declaration's own"
  -- the key: the stored module IS the parent's module (by value)
  let some (.defnInfo cmi) := env.find? nmC.mod | return some s!"{nmC.mod} is not a definition"
  unless cmi.value == toExpr cm do
    return some s!"the stored module {nmC.mod} is not the parent's module {cm.name} (same name, different module)"
  let some (.defnInfo cdi) := env.find? nmC.design | return some s!"{nmC.design} is not a definition"
  let dC ← try evalDesign cdi.value catch _ => return some s!"{nmC.design} does not decode to a design"
  unless dC.topModule == cm.name do
    return some s!"the stored design's top is {dC.topModule}, not {cm.name}"
  unless dC.modules.all (fun x => d.modules.contains x) do
    return some s!"a module of the stored design {nmC.design} is not a module of the parent's design (by value)"
  return none

/-- Ensure the middle module's recursive theorem exists and is checked; run its entry first when it
is not stored.  `midEntry cdecl` is the entry on the middle module's own declaration: its synthesis,
its design, its theorem name. -/
def ensureMid (midEntry : Name → Sparkle.IR.AST.Module → Design → CommandElabM Name)
    (decl : Name) (d : Design) (cm : Sparkle.IR.AST.Module) (parent : HNames) (idx : Nat) :
    CommandElabM MidInfo := do
  let cdecl := cm.name.toName
  let nmC := HNames.ofBase cdecl
  unless (← getEnv).contains cdecl do
    liftTermElabM <| refuse decl "child" m!"middle module {cm.name}: no declaration of that name"
  let (cstmt, cdom) ← liftTermElabM <| try specialiseDomain cdecl
    catch e => refuse decl "child" m!"middle module {cm.name}: {e.toMessageData}"
  let ctbl ← liftTermElabM <| try readTableOfType cdecl (← inferType cstmt)
    catch e => refuse decl "child" m!"middle module {cm.name}: {e.toMessageData}"
  let thmR := cdecl ++ `ved_u2r
  let kid : Kid :=
    { c := cm, decl := cdecl, nDom := cdom, tbl := ctbl,
      nm := { mod := nmC.mod, contract := nmC.contract, outs := nmC.outs, body := nmC.body, thm := thmR } }
  -- the checked arrangement of the middle module's body in the PARENT's design (`OrderHS d mid`)
  let bm := orderBodyH d cm.body
  unless decide (Tools.VedU2Hier.OrderOkHS d cm bm) do
    liftTermElabM <| refuse decl "order" m!"middle module {cm.name}: {orderDiagHS d cm bm}"
  let bodyC := parent.body ++ Name.mkSimple s!"mid{idx}"
  liftTermElabM <| addDefn bodyC (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Stmt)) (toExpr bm)
  let finish (hit : Bool) : CommandElabM MidInfo :=
    pure { kid, dC := nmC.design, thmR, bodyC, hit }
  -- (1) a stored recursive theorem: reuse it only after the check
  if (← getEnv).contains thmR then
    match ← liftTermElabM (checkStored thmR cdecl cstmt cm d) with
    | none => return ← finish true
    | some why => liftTermElabM <| refuse decl "child" m!"middle module {cm.name}: the stored theorem {thmR} is not usable (cache refused): {why}"
  -- (2) the depth-1 theorem of the middle module, stored or produced by its entry run FIRST
  let thmS := nmC.thm
  let storedBefore := (← getEnv).contains thmS
  if !storedBefore then
    -- the entry on the middle module's OWN module (the parent's module value) and its sub-design
    discard <| midEntry cdecl cm (subDesignOf d cm)
  let env ← getEnv
  let some (.thmInfo ti) := env.find? thmS
    | liftTermElabM <| refuse decl "child" m!"middle module {cm.name}: {thmS} is not a theorem"
  let expectS := mkAppN (Lean.mkConst ``Tools.VedU2Hier.U2HRStmt)
    #[Lean.mkConst nmC.contract, Lean.mkConst nmC.mod, Lean.mkConst nmC.design, cstmt]
  let expectR := mkAppN (Lean.mkConst ``Tools.VedU2HierRec.U2HRStmtR)
    #[Lean.mkConst nmC.contract, Lean.mkConst nmC.mod, Lean.mkConst nmC.design, cstmt]
  let isS := ti.type == expectS
  let isR := ti.type == expectR
  unless isS || isR do
    liftTermElabM <| refuse decl "child" m!"middle module {cm.name}: the stored theorem {thmS} is neither U2HRStmt nor U2HRStmtR over the stored constants and the declaration"
  let some (.defnInfo cmi) := env.find? nmC.mod
    | liftTermElabM <| refuse decl "child" m!"{nmC.mod} missing"
  unless cmi.value == toExpr cm do
    liftTermElabM <| refuse decl "child" m!"middle module {cm.name}: the stored module {nmC.mod} is not the parent's module (same name, different module)"
  let some (.defnInfo cdi) := env.find? nmC.design
    | liftTermElabM <| refuse decl "child" m!"{nmC.design} missing"
  let dC ← liftTermElabM <| try evalDesign cdi.value
    catch e => refuse decl "child" m!"{nmC.design}: {e.toMessageData}"
  unless dC.topModule == cm.name do
    liftTermElabM <| refuse decl "child" m!"the middle module's design has top {dC.topModule}, not {cm.name}"
  unless dC.modules.all (fun x => d.modules.contains x) do
    liftTermElabM <| refuse decl "child" m!"middle module {cm.name}: a module of its own design is not a module of the parent's design (by value)"
  if isR then
    -- the middle module's own entry is already recursive (its design has a non-leaf module)
    return { kid := { kid with nm := { kid.nm with thm := thmS } }, dC := nmC.design, thmR := thmS, bodyC, hit := storedBefore }
  unless decide (Tools.VedU2HierRec.allLeafB dC = true) do
    liftTermElabM <| refuse decl "child" m!"middle module {cm.name}: a depth-1 theorem over a design with a non-leaf module"
  -- (3) the recursive statement on the sub-design, from the stored depth-1 theorem
  let hl ← liftTermElabM <| mkEqRefl (Lean.mkConst ``Bool.true)
  let val := mkAppN (Lean.mkConst ``Tools.VedU2HierRec.U2HRStmtR_of_S)
    #[Lean.mkConst nmC.contract, Lean.mkConst nmC.mod, Lean.mkConst nmC.design, cstmt, hl, Lean.mkConst thmS]
  try
    liftTermElabM <| withOptions (fun o => o.setBool `Elab.async false) do
      addDecl (.thmDecl { name := thmR, levelParams := [], type := expectR, value := val })
  catch e => liftTermElabM <| refuse decl "child" m!"middle module {cm.name}: the kernel refused the recursive statement: {e.toMessageData}"
  finish storedBefore

/-- All non-leaf modules of the parent's design with the arrangement constants of their bodies in the PARENT's
design (`OrderHS d x`, kernel `decide` on the real design). -/
def defineNl (decl : Name) (d : Design) (parent : HNames) : CommandElabM (List NlInfo) := do
  let mut out : List NlInfo := []
  for x in d.modules do
    unless leafBody x.body do
      let bm := orderBodyH d x.body
      unless decide (Tools.VedU2Hier.OrderOkHS d x bm) do
        liftTermElabM <| refuse decl "order" m!"module {x.name}: {orderDiagHS d x bm}"
      let nmX := HNames.ofBase x.name.toName
      unless (← getEnv).contains nmX.mod do
        liftTermElabM <| refuse decl "child" m!"non-leaf module {x.name}: its entry has not run (no {nmX.mod})"
      let bodyC := parent.body ++ Name.mkSimple s!"nl{out.length}"
      liftTermElabM <| addDefn bodyC (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Stmt)) (toExpr bm)
      out := out ++ [{ modC := nmX.mod, bodyC }]
  return out

/-- The direct instances of the parent that are non-leaf modules: their theorems (entry first, cache checked). -/
def ensureMids (midEntry : Name → Sparkle.IR.AST.Module → Design → CommandElabM Name)
    (decl : Name) (d : Design) (m : Sparkle.IR.AST.Module) (parent : HNames) : CommandElabM (List MidInfo) := do
  let mut mids : List MidInfo := []
  let mut midMods : List Sparkle.IR.AST.Module := []
  for s in m.body do
    match s with
    | .inst mn iname _ =>
      let some cm := d.modules.find? (fun x => x.name == mn)
        | liftTermElabM <| refuse decl "child" m!"instance {iname}: no module {mn}"
      if leafBody cm.body then
        liftTermElabM <| refuse decl "scope" m!"nested route: instance {iname}: {mn} is a leaf (a leaf child next to middle modules is not generated yet)"
      unless midMods.contains cm do
        let mi ← ensureMid midEntry decl d cm parent mids.length
        logInfo m!"VED NESTED {decl}: middle module {cm.name}: theorem {mi.thmR} ({if mi.hit then "stored, checked" else "from its entry run"})"
        mids := mids ++ [mi]
        midMods := midMods ++ [cm]
    | _ => pure ()
  return mids

/-! ## The proof text -/

private def replaceBlock (ls : Array String) (from_ to_ : String → Bool) (new : List String) : Array String := Id.run do
  let some a := (List.range ls.size).find? (fun i => from_ ls[i]!) | return ls
  let b := ((List.range ls.size).find? (fun i => i > a && to_ ls[i]!)).getD ls.size
  return ls.extract 0 a ++ new.toArray ++ ls.extract b ls.size

/-- The nested proof text from the depth-1 parent script `base` (the register-free script of H2a, or the
script of H2b for a parent with registers): the shape, order, success and instance blocks are replaced by
the recursive ones; the open-parent / register-invariant parts are the base script's own.
`reg` : the base script is H2b's (its closed-run lemmas are renamed to their recursive analogues). -/
def transformN (base : String) (nm : HNames) (kids : List Kid) (mids : List MidInfo) (nl : List NlInfo)
    (insts : List InstInfo) (reg : Bool) : String := Id.run do
  let P := nm.user
  let T := "Tools.VedU2HierRec"
  let T2 := "Tools.VedU2Hier"
  let kids := kids.map fun k => { k with nm := namesUser k.nm }
  let mut ls : Array String := (base.splitOn "\n").toArray
  let midA := (mids.map fun mi => userName mi.dC).toArray
  let n := mids.length
  -- (1) shape
  ls := ls.map fun l =>
    if l.startsWith "  have hS : " then l.replace s!"{T2}.HierShapeS" s!"{T}.HierShapeR"
    else if l.startsWith "  have hne := " then s!"  have hne : ∀ x ∈ {P.design}.modules, x ≠ {P.mod} := ({T}.hierR_names hS).2"
    else l
  let origRefine := (ls.find? (·.startsWith "  refine ⟨by")).getD ""
  -- (2) the order facts of the real design, the middle modules' facts, the arrangement
  let mut blk : List String := []
  for (k, i) in kids.zipIdx do
    let K := k.nm
    blk := blk ++ [
      s!"  have hmemN{i} : {K.mod} ∈ {P.design}.modules := {T}.mem_of_ex1 (by decide)",
      s!"  have hnl{i} : Tools.VedU1Hier.leafBody {K.mod}.body = false := by decide",
      s!"  have hsub{i} : ∀ x ∈ {userName mids[i]!.dC}.modules, x ∈ {P.design}.modules := {T}.mem_of_ex (by decide)"]
  for (x, j) in nl.zipIdx do
    blk := blk ++ [s!"  have hnlO{j} : {T2}.OrderHS {P.design} {userName x.modC} := ⟨{userName x.bodyC}, by decide⟩"]
  -- the direct middle module `i` is the non-leaf module number `nlIdx i`
  let nlIdx (i : Nat) : Nat := (nl.zipIdx.find? (fun (x, _) => userName x.modC == kids[i]!.nm.mod)).map (·.2) |>.getD 0
  for (_, i) in kids.zipIdx do
    blk := blk ++ [s!"  have hordc{i} := hnlO{nlIdx i}"]
  let djL := " ∨ ".intercalate (midA.toList.map fun dC => s!"(∃ y ∈ {dC}.modules, y = x)")
  let djN := " ∨ ".intercalate (nl.map fun x => s!"x = {userName x.modC}")
  let patL := " | ".intercalate (List.replicate n "h")
  let patN := " | ".intercalate (List.replicate nl.length "h")
  blk := blk ++ [
    s!"  have hsplitL : ∀ x ∈ {P.design}.modules, Tools.VedU1Hier.leafBody x.body = true → {djL} := by decide",
    s!"  have hsplitN : ∀ x ∈ {P.design}.modules, Tools.VedU1Hier.leafBody x.body = false → {djN} := by decide",
    s!"  have hchR : {T}.OrderModsR {P.design} := by",
    s!"    intro x hx",
    s!"    refine ⟨fun hl => ?_, fun hl => ?_⟩",
    s!"    · rcases hsplitL x hx hl with {patL}"]
  for (k, _) in (kids.zipIdx) do
    blk := blk ++ [s!"      · obtain ⟨y, hy, rfl⟩ := h; exact ({k.nm.thm}.2.2.2.2.2.2.1 y hy).1 hl"]
  blk := blk ++ [s!"    · rcases hsplitN x hx hl with {patN}"]
  for (_, j) in nl.zipIdx do
    blk := blk ++ [s!"      · subst h; exact hnlO{j}"]
  let refineL :=
    if reg then
      (origRefine.replace "hord, hch, " "hord, hchR, ").replace s!"{T2}.exists_arrHS _ _ hord hch hne" s!"{T}.exists_arrHR _ _ hord hchR hne"
    else
      s!"  refine ⟨by decide, by decide, by decide, hS, by decide, hord, hchR, {T}.exists_arrHR _ _ hord hchR hne, ?_⟩"
  blk := blk ++ [refineL]
  ls := replaceBlock ls (·.startsWith "  have hmods") (·.startsWith "  intro arr hadm") blk
  -- (3) success of the parent
  let succInst : List String := Id.run do
    let nI := insts.length
    let patI := " | ".intercalate (insts.map fun _ => "⟨rfl, rfl, rfl⟩")
    let mut X : List String := [
      s!"  have hsucc : {T}.SuccF {P.design} arr ({T}.fuelR {P.design}) {P.mod} := by",
      s!"    refine ⟨hsupp, ?_⟩",
      s!"    intro mn i cs hin c hf",
      s!"    have hin1 : Sparkle.IR.AST.Stmt.inst mn i cs ∈ {P.body} := hb0.1.mem_iff.mpr (hadm.1.mem_iff.mp hin)",
      s!"    simp only [{P.body}, List.mem_cons, List.not_mem_nil, or_false, false_or, Sparkle.IR.AST.Stmt.inst.injEq, reduceCtorEq] at hin1"]
    if nI == 1 then X := X ++ [s!"    obtain ⟨rfl, rfl, rfl⟩ := hin1"]
    else X := X ++ [s!"    rcases hin1 with {patI}"]
    for (ii, _) in insts.zipIdx do
      let k := kids[ii.kid]!
      let dC := midA[ii.kid]!
      let G := declTerm k.decl k.nDom
      let ind := if nI == 1 then "    " else "    · "
      X := X ++ [
        s!"{ind}have hfm : Tools.VedU1Hier.findMod {P.design} {sq ii.mn} = some {k.nm.mod} := by decide",
        s!"    rw [hfm] at hf; obtain rfl := Option.some.inj hf",
        s!"    exact {T}.succF_of_theoremR {P.design} arr {P.mod} hS hadm _ hmemN{ii.kid} hnl{ii.kid} {dC} hsub{ii.kid} {k.nm.contract} {G} {k.nm.thm}"]
    return X
  ls := replaceBlock ls (·.startsWith "  have hmem0") (·.startsWith "  have hsupp") []
  let some iSupp := (List.range ls.size).find? (fun i => ls[i]!.startsWith "  have hsupp") | return "?"
  ls := ls.extract 0 (iSupp + 2) ++ succInst.toArray ++ ls.extract (iSupp + 2) ls.size
  -- (4) the final refine and the instance fact
  ls := ls.map fun l =>
    if l.startsWith "  refine Tools.VedU2Hier.outputsOnHS_of_oracle" then
      (l.replace "Tools.VedU2Hier.outputsOnHS_of_oracle" s!"{T}.outputsOnHSR_of_oracle").replace "hS hadm hnoreg hsupp hsch" "hS hadm hnoreg hsucc"
    else if l.startsWith "  refine Tools.VedU2Hier.outputsOnHS_of_stepR " then
      (l.replace "Tools.VedU2Hier.outputsOnHS_of_stepR " s!"{T}.outputsOnHSR_of_stepR ").replace "hS hadm hsupp hsch" "hS hadm hsucc"
    else l
  ls := ls.map fun l =>
    if l.contains "Tools.VedU2Hier.kid_inst " then
      let l1 := l.replace "Tools.VedU2Hier.kid_inst " s!"{T}.kid_inst_R "
      let idx := (insts.zipIdx.find? (fun (ii, _) => l1.contains s!"{sq ii.iname}")).map (·.1.kid) |>.getD 0
      let k := kids[idx]!
      let tail := s!"{k.nm.mod} (by decide)"
      (l1.replace tail s!"{k.nm.mod} (by decide) hnl{idx} hordc{idx} {userName mids[idx]!.dC} hsub{idx}").replace
        " t ht E hE _ hq" s!" ({T}.rstnd_sound (by decide)) t ht E hE _ hq"
    else l
  -- (5) the closed-run lemmas of the register script, by their recursive analogues
  if reg then
    ls := ls.map fun l =>
      ((((l.replace s!"{T2}.st0H " s!"{T}.st0HR ").replace s!"{T2}.runHS_inputs " s!"{T}.runHS_inputsR ").replace
        s!"{T2}.closed_run_asgOf " s!"{T}.closed_run_asgOfR ").replace s!"{T2}.closed_run_reg " s!"{T}.closed_run_regR ").replace
        s!"{T2}.st0H)" s!"{T}.st0HR)"
  return "\n".intercalate ls.toList

def scriptTextN (nm : HNames) (F : Name) (nDom : Nat) (tbl : DeclTable) (opn : OpenInfo)
    (mids : List MidInfo) (nl : List NlInfo) (insts : List InstInfo) : String :=
  let kids := mids.map fun mi => { mi.kid with nm := namesUser mi.kid.nm }
  transformN (scriptTextS nm F nDom tbl opn kids insts) nm (mids.map (·.kid)) mids nl insts false

/-! ## The checker -/

/-- The checker of the nested route.  `m` and `d` are the values `synthesizeCombinational` returned. -/
def checkU2HN (midEntry : Name → Sparkle.IR.AST.Module → Design → CommandElabM Name)
    (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (m : Sparkle.IR.AST.Module) (d : Design)
    (clkRstOverride : Option (Option (String × String)) := none) :
    CommandElabM (Name × Nat × Nat) := do
  let saved ← get
  let nm := HNames.ofBase decl
  try
    let tbl ← liftTermElabM <| try readTableOfType decl (← inferType stmt) catch e => refuse decl "table" e.toMessageData
    unless tbl.out.flat.length == 1 do
      liftTermElabM <| refuse decl "multi-output"
        m!"{tbl.out.flat.length} output projections (multi-output: H3), refused (nested route: one output)"
    liftTermElabM <| withEvalBudget <| do
      let mE := toExpr m
      let back ← evalModule mE
      unless decide (back = m) do
        refuse decl "artifact" m!"toExpr of the returned module does not evaluate back to it"
      let dE := toExpr d
      let backD ← evalDesign dE
      unless backD.topModule = d.topModule && decide (backD.modules = d.modules) do
        refuse decl "artifact" m!"toExpr of the returned design does not evaluate back to it"
      addDefn nm.mod (Lean.mkConst ``Sparkle.IR.AST.Module) mE
      addDefn nm.design (Lean.mkConst ``Design) dE
    unless decide (Tools.VedU2HierRec.HierShapeR d m = true) do
      liftTermElabM <| refuse decl "hier-shape" m!"HierShapeR fails (nested route)"
    unless (regsOf m.body).isEmpty do
      liftTermElabM <| refuse decl "scope" m!"nested route: the parent has registers (a register parent over non-leaf children is not generated yet)"
    let some clkRst0 := parentClkRst tbl m
      | liftTermElabM <| refuse decl "clkrst" m!"the parent has {m.inputs.length - tbl.ins.length} inputs after the declaration's {tbl.ins.length} data inputs (expected none, or exactly clock and reset)"
    let clkRst := clkRstOverride.getD clkRst0
    let cE := mkAppN (Lean.mkConst ``contractOf)
      #[toExpr tbl, toExpr ["out"], toExpr clkRst, Lean.mkConst nm.mod]
    liftTermElabM <| addDefn nm.contract (Lean.mkConst ``Contract) cE
    let c := contractOf tbl ["out"] clkRst m
    unless decide (CorrStmt c) do
      liftTermElabM <| refuse decl "table" m!"the declaration/contract correspondence (CorrStmt) fails"
    unless decide (c.clkRst = designClkRst d m) do
      liftTermElabM <| refuse decl "clkrst"
        m!"the parent contract's clock/reset pair {repr c.clkRst} is not the pair of parent inputs the instances' clock and reset ports are connected to ({repr (designClkRst d m)})"
    unless decide (ShapeCore c m) do
      liftTermElabM <| refuse decl "artifact"
        m!"the returned module does not match the declaration's ports (ShapeCore): inputs {repr m.inputs}, outputs {repr m.outputs}"
    unless decide (WidthStmt c m) do liftTermElabM <| refuse decl "artifact" m!"WidthStmt fails"
    liftTermElabM <| addDefn nm.outs (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Port))
      (toExpr c.outputs)
    let b0 := orderBodyH d m.body
    unless decide (Tools.VedU2Hier.OrderOkHS d m b0) do
      liftTermElabM <| refuse decl "order" m!"{orderDiagHS d m b0}"
    liftTermElabM <| addDefn nm.body (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Stmt))
      (toExpr b0)
    -- the parent's instances: direct children, all non-leaf (middle modules)
    let t0 ← IO.monoMsNow
    for s in m.body do
      match s with
      | .inst mn iname cs =>
        let some cm := d.modules.find? (fun x => x.name == mn)
          | liftTermElabM <| refuse decl "child" m!"instance {iname}: no module {mn}"
        if leafBody cm.body then
          liftTermElabM <| refuse decl "scope" m!"nested route: instance {iname}: {mn} is a leaf (a leaf child next to middle modules is not generated yet)"
        let cdecl := cm.name.toName
        let ctbl ← liftTermElabM <| try (do let (st, _) ← specialiseDomain cdecl; readTableOfType cdecl (← inferType st))
          catch e => refuse decl "child" m!"middle module {cm.name}: {e.toMessageData}"
        let ck := contractOf ctbl ["out"] (clkRstOf cm) cm
        unless connsIn m cm cs do
          liftTermElabM <| refuse decl "conns"
            m!"instance {iname}: an input port of {mn} is not connected to a parent input (derived or chained instance inputs are outside the nested route)"
        unless dataIn c m ck cm cs do
          liftTermElabM <| refuse decl "conns"
            m!"instance {iname}: a data port of {mn} is not connected to a parent DATA input of the same width"
      | _ => pure ()
    let mids ← ensureMids midEntry decl d m nm
    let nl ← defineNl decl d nm
    if mids.isEmpty then
      liftTermElabM <| refuse decl "scope" m!"the parent has no child instance"
    let t1 ← IO.monoMsNow
    let kids := mids.map (·.kid)
    -- the open parent and the pairing instance <-> call
    let opn ← liftTermElabM <| tryCatchRuntimeEx (withProofBudget <| genOpen decl stmt nDom tbl kids nm.mod.getPrefix)
      fun e => do if ← isRefusal e then throw e else refuse decl "open" e.toMessageData
    let mut insts : List InstInfo := []
    for s in m.body do
      match s with
      | .inst mn iname cs =>
        let some (ki, k) := (kids.zipIdx.find? fun (k, _) => k.c.name == mn).map (fun (k, i) => (i, k))
          | liftTermElabM <| refuse decl "child" m!"instance {iname}: no module {mn}"
        let y := match cs.lookup (outNameOf k.c) with | some (.ref y) => y | _ => "?"
        let args := k.tbl.binders.map fun b =>
          match cs.lookup ("_gen_" ++ b) with
          | some (.ref x) => if x.startsWith "_gen_" then (x.drop 5).toString else "?"
          | _ => "?"
        let some ci := opn.calls.findIdx? (fun c => c.kid == ki && c.args == args)
          | liftTermElabM <| refuse decl "open"
              m!"instance {iname}: the declaration's body has no call of {mn} on the parent inputs {args}"
        insts := insts ++ [{ mn, iname, cs, kid := ki, y, call := ci }]
      | _ => pure ()
    let expected := mkAppN (Lean.mkConst ``Tools.VedU2HierRec.U2HRStmtR)
      #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]
    liftTermElabM <| do
      try Meta.check expected catch e => refuse decl "type" e.toMessageData
      unless ← isProp expected do refuse decl "type" m!"expected statement is not a Prop"
    let text := "by\n" ++ scriptTextN nm stmt.getAppFn.constName! stmt.getAppNumArgs tbl opn mids nl insts
    if (← IO.getEnv "VED_HIER_DEBUG").isSome then IO.eprintln text
    liftTermElabM <| do
      let stx ← match Lean.Parser.runParserCategory (← getEnv) `term text "<ved_u2_hier_nested>" with
        | .ok s => pure s
        | .error e => refuse decl "proof" m!"generated script does not parse: {e}"
      let errsBefore := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
      let pf ← tryCatchRuntimeEx
          (withProofBudget <|
          withOptions (fun o => ((o.setBool `linter.unusedSimpArgs false).setBool
              `linter.unusedTactic false).setBool `linter.unreachableTactic false) <| withoutErrToSorry do
            let e ← elabTermEnsuringType stx expected
            synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e)
          fun e => refuse decl "proof" e.toMessageData
      let errs := (← Core.getMessageLog).toList.filter (·.severity == .error)
      if errs.length != errsBefore then
        let first ← match errs.drop errsBefore with
          | msg :: _ => msg.data.toString
          | [] => pure ""
        refuse decl "proof" m!"errors were logged while elaborating the proof; first: {first}"
      if pf.hasMVar || pf.hasFVar then refuse decl "proof" m!"proof term is not closed"
      try
        withOptions (fun o => o.setBool `Elab.async false) do
          addDecl (.thmDecl { name := nm.thm, levelParams := [], type := expected, value := pf })
      catch e => refuse decl "kernel" e.toMessageData
      let some (.thmInfo ti) := (← getEnv).find? nm.thm
        | refuse decl "kernel" m!"{nm.thm} is not a theorem in the environment"
      unless ti.type == expected do refuse decl "type" m!"stored type differs from the expected statement"
      try discard <| Tools.VedStrictAudit.strictAudit nm.thm
      catch e => refuse decl "audit" e.toMessageData
    let t2 ← IO.monoMsNow
    return (nm.thm, t1 - t0, t2 - t1)
  catch e =>
    set saved
    if ← liftTermElabM (isRefusal e) then throw e
    liftTermElabM <| refuse decl "checker" e.toMessageData

end Tools.VedU2HierRecEntry
