import Lean
import Sparkle.Compiler.Elab
import Tools.VedU1Deep
import Tools.VedU1HierEntry
import Tools.VedU2HierKid

/-!
# Stateful hierarchical entry, H2a (`#ved_u2_hier decl`)

Design: docs/VED-HIER-H2-DESIGN.md §2.2, §3, §11, §12 (unit 3).  `Sparkle/` and the H1 files are
not changed.

Scope (H2a): a REGISTER-FREE parent whose instances are leaf children (assignments and
registers; one output); every input-port connection is a `ref` of a parent INPUT.  The children
need their `#verify_elab_deep` constants (the #160 multi-register / Bool generator `#ved_u1_deep`
builds their U1 theorems), a combinational child uses the plain generator.

`vedU2HierEntry declName`, stages:

1. `table` / `multi-output` (before any synthesis): the port table is read from the declaration's
   TYPE;
2. `synthesis`: `synthesizeCombinational declName` exactly ONCE; the returned `(m, d)` is kept and
   is what everything below is about;
3. `artifact`: `declName.ved_mod := toExpr m`, `declName.ved_design := toExpr d`, each checked to
   denote the returned value;
4. `hier-shape`: `HierShapeS d m` (not a soundness check by itself);
5. `clkrst` / `artifact`: the contract is built from the declaration's table; its clock/reset pair
   is the parent's two trailing inputs and MUST equal `designClkRst d m` (the parent contract
   tie), `CorrStmt`, `ShapeCore`, `WidthStmt`;
6. `order`: `OrderOkHS d m b0` on the checked arrangement (duplicate register outputs, register
   against assign / instance-output clashes, writes to inputs, undriven reads including register
   inputs, combinational cycles through instances) — from it `hwr` is derived in the proof;
7. `scope`: the parent has no register (H2b is another unit); `conns`: every instance input is
   read from a parent input;
8. `child`: every module of `d`, taken from `d`, gets its U1 theorem under
   `declName.ved_child.<module>` (`#ved_u1_deep` generator for register children);
9. `open`: the OPEN PARENT is GENERATED from the declaration: each child call `g args` of the
   declaration's body is abstracted (`kabstract`, a construction device only) into a free signal,
   giving `declName.ved_open`; the equation `declName a b = declName.ved_open a b (g a) (g b)` is
   added to the KERNEL (`declName.ved_open_eq`, proof `rfl`);
10. `type` / `proof` / `kernel` / `audit`: the generated proof of `U2HStmt c m d decl` is
   elaborated against the full expected type, added synchronously, its stored type compared, and
   audited (standard 3 axioms).  It uses the open parent's meaning on the SAME `(m, d)`
   (`oracleIE`: instance outputs are free values), the closed/open agreement
   (`fold_oracle`), each instance's output from the child's real theorem (`kid_inst`), the
   equation, and supplies ExprsSupp, ChildSucc, htie, hwr and InputsOk itself.

A failure restores the state saved when the checker started (constants and messages), as H1.
-/

namespace Tools.VedU2HierEntry

open Lean Meta Elab Term
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
open Tools.VedU1Deep

/-! ## Diagnosis (the refusal reasons; the proof re-decides everything in the kernel) -/

/-- The first reason `connsOkS` fails, as text. -/
def connDiagS (d : Design) (m : Sparkle.IR.AST.Module) (mn iname : String)
    (cs : List (String × Sparkle.IR.AST.Expr)) : Option String :=
  match findMod d mn with
  | none => some s!"instance {iname}: module {mn} is not in the returned design"
  | some c =>
    let ports := c.inputs ++ c.outputs
    if c.isPrimitive then some s!"instance {iname}: child {mn} is a primitive module"
    else if !c.parameters.isEmpty then some s!"instance {iname}: child {mn} has parameters"
    else if !c.assertions.isEmpty then some s!"instance {iname}: child {mn} has assertions"
    else if !leafBody c.body then
      some s!"instance {iname}: child {mn} is not a leaf (memory or instance in its body: depth 1 only)"
    else if !childSane c then
      some s!"instance {iname}: child {mn} is not sane (duplicate input names, an assignment to an input, or a register output that is an input)"
    else if c.outputs.length != 1 then
      some s!"instance {iname}: child {mn} has {c.outputs.length} outputs (multi-output children: H3)"
    else if !(decide (cs.map (·.1)).Nodup) then
      some s!"instance {iname}: duplicate port connection"
    else match ports.find? (fun p => !cs.any (fun q => q.1 == p.name)) with
    | some p => some s!"instance {iname}: port {p.name} of {mn} is not connected"
    | none =>
    match cs.find? (fun q => !ports.any (fun p => p.name == q.1)) with
    | some q => some s!"instance {iname}: connection to {q.1}, which {mn} has no such port"
    | none =>
    match cs.find? (fun q => match q.2 with | .ref _ => false | _ => true) with
    | some q => some s!"instance {iname}: port {q.1} is not connected to a plain wire reference (ref only)"
    | none =>
    match cs.find? (fun q => match q.2 with
      | .ref x => !ports.any (fun p => p.name == q.1 && scalar p.ty &&
          (declWidth m x == p.ty.bitWidth || isClkRstPort c p.name))
      | _ => false) with
    | some q => some s!"instance {iname}: width mismatch on port {q.1} (wire {q.2} against the port)"
    | none => none

/-- The first reason `HierShapeS` fails, as text. -/
def hierDiagS (d : Design) (m : Sparkle.IR.AST.Module) : Option String :=
  if d.topModule != m.name then
    some s!"the design's top module {d.topModule} is not the returned module {m.name}"
  else if !(decide (d.modules.map (·.name)).Nodup) then
    some s!"duplicate child module names in the design: {d.modules.map (·.name)}"
  else if (d.modules.map (·.name)).contains m.name then
    some s!"the top module {m.name} is also listed among the design's modules"
  else match m.body.find? (fun s => !isAsgInstReg s) with
  | some s => some s!"top statement {s} is not an assignment, a register or an instance (memories at the top are not in H2)"
  | none =>
  match (m.body.filterMap fun s => match s with
      | .inst mn i cs => connDiagS d m mn i cs
      | _ => none).head? with
  | some msg => some msg
  | none =>
  if !(decide (instNames m.body).Nodup) then some "duplicate instance names"
  else match d.modules.find? (fun c => !(m.body.any (fun s => match s with
        | .inst mn _ _ => mn == c.name
        | _ => false))) with
  | some c => some s!"module {c.name} of the design is not instantiated by the top module (an unused or unsupported leftover module is refused, never dropped)"
  | none =>
  if !clkRstOk d m then
    some "clock/reset: every register-carrying instance must connect its clock and reset ports to the SAME pair of distinct parent inputs (a constant, a derived signal or another input is refused)"
  else none

/-- The first reason `OrderOkHS` fails, as text. -/
def orderDiagHS (d : Design) (m : Sparkle.IR.AST.Module) (b : List Stmt) : String :=
  if !isPermOf b m.body then "the arrangement is not a permutation of the body"
  else if !(decide (WOH d b)) then
    "no arrangement assigns every wire before it is read across assignments and instances (a combinational cycle through assignments or an instance — every child output is taken to depend on all of its inputs —, a self-read, or a wire written twice)"
  else if !b.all isAsgInstReg then "a statement is not an assignment, a register or an instance"
  else if !(decide (regOuts b).Nodup) then "a register output is declared twice (duplicate register outputs)"
  else if !b.all (fun s => (allReadsHS d s).all (fun n =>
      (inNames m).contains n || (regOuts b).contains n || (wrsH d b).contains n)) then
    "an undriven net: a read (register input expressions included) of a name that is neither an input, a register output nor written"
  else if !m.outputs.all (fun p => (regOuts b).contains p.name || (wrsH d b).contains p.name) then
    "an output port has no driver"
  else if (wrsH d b).any (fun n => (inNames m).contains n) then
    "a write to a top input (an assignment or an instance output drives an input)"
  else if (wrsH d b).any (fun n => (regOuts b).contains n) then
    "an assignment or an instance output drives a register output (multiple drivers)"
  else if (regOuts b).any (fun n => (inNames m).contains n) then "a register output is a top input"
  else "OrderOkHS fails"

/-- The parent contract's clock/reset pair: the parent's two inputs after the data inputs of the
declaration's table (none when there are no more). -/
def parentClkRst (tbl : DeclTable) (m : Sparkle.IR.AST.Module) :
    Option (Option (String × String)) :=
  match m.inputs.drop tbl.ins.length with
  | [] => some none
  | [k, r] => some (some (k.name, r.name))
  | _ => none

/-! ## The open parent, generated from the declaration -/

/-- One distinct child call of the declaration's body: the child (index into `d.modules`) and the
parent binder names its arguments are. -/
structure CallInfo where
  kid : Nat
  args : List String
  deriving BEq, Inhabited

structure OpenInfo where
  openName : Name
  eqName : Name
  calls : Array CallInfo
  deriving Inhabited

instance : Inhabited Kid :=
  ⟨{ c := { name := "", parameters := [], inputs := [], outputs := [], wires := [], body := [],
            assertions := [], isPrimitive := false },
     decl := .anonymous, nDom := 0, tbl := { binders := [], ins := [], out := .leaf .bit },
     nm := { mod := .anonymous, contract := .anonymous, outs := .anonymous, body := .anonymous,
             thm := .anonymous } }⟩

/-- Child-call subterms of `e`, outermost first-occurrence order. -/
partial def collectCalls (isKid : Name → Bool) (e : Lean.Expr) (acc : Array Lean.Expr) :
    Array Lean.Expr :=
  if e.isApp && (match e.getAppFn with | .const n _ => isKid n | _ => false) then
    if acc.contains e then acc else acc.push e
  else match e with
    | .app f a => collectCalls isKid a (collectCalls isKid f acc)
    | .lam _ t b _ => collectCalls isKid b (collectCalls isKid t acc)
    | .forallE _ t b _ => collectCalls isKid b (collectCalls isKid t acc)
    | .letE _ t v b _ => collectCalls isKid b (collectCalls isKid v (collectCalls isKid t acc))
    | .mdata _ b => collectCalls isKid b acc
    | .proj _ _ b => collectCalls isKid b acc
    | _ => acc

/-- Generate the open parent: abstract every child call of the declaration's body into a free
signal (`kabstract` is only the construction device), register the definition, and add the
equation `decl xs = open xs calls` to the KERNEL (its proof is `rfl`). -/
def genOpen (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (tbl : DeclTable) (kids : List Kid)
    (base : Name) (openSuf : String := "ved_open") : TermElabM OpenInfo := do
  let openName := base ++ Name.mkSimple openSuf
  let eqName := base ++ Name.mkSimple (openSuf ++ "_eq")
  let ty ← inferType stmt
  forallTelescope ty fun xs _ => do
    let some (.defnInfo ci) := (← getEnv).find? decl
      | refuse decl "open" m!"{decl} is not a definition"
    let dflt := Lean.mkConst ``Sparkle.Core.Domain.defaultDomain
    let args : Array Lean.Expr := (Array.replicate nDom dflt) ++ xs
    let body0 := (mkAppN ci.value args).headBeta
    let body ← zetaReduce body0
    let kidArr := kids.toArray
    let isKid := fun (n : Name) => kidArr.any (·.decl == n)
    let calls := collectCalls isKid body #[]
    let mut infos : Array CallInfo := #[]
    for call in calls do
      let .const n _ := call.getAppFn | refuse decl "open" m!"call {call}"
      let some (ki, k) := kidArr.zipIdx.find? (fun (k, _) => k.decl == n) |>.map (fun (k, i) => (i, k))
        | refuse decl "open" m!"call {call}"
      let cargs := call.getAppArgs
      unless cargs.size == k.nDom + k.tbl.ins.length do
        refuse decl "open" m!"child call {call} is not fully applied"
      let mut names : List String := []
      for a in cargs.extract k.nDom cargs.size do
        match xs.findIdx? (· == a) with
        | some j => names := names ++ [tbl.binders.getD j ""]
        | none =>
          refuse decl "open"
            m!"the argument {a} of the child call {call} is not a parent input signal (derived or chained instance inputs are outside H2a)"
      infos := infos.push { kid := ki, args := names }
    let tys ← calls.mapM fun c => inferType c
    let decls := (tys.mapIdx fun i T => (Name.mkSimple s!"o{i}", T)).toList
    withLocalDeclsDND decls.toArray fun os => do
      let mut b := body
      for (c, o) in calls.zip os do
        b := (← kabstract b c).instantiate1 o
      let openVal ← mkLambdaFVars (xs ++ os) b
      let openTy ← inferType openVal
      addDefnRegular openName openTy openVal
      let lhs := mkAppN stmt xs
      let rhs := mkAppN (Lean.mkConst openName) (xs ++ calls)
      let eqTy ← mkForallFVars xs (← mkEq lhs rhs)
      let pf ← mkLambdaFVars xs (← mkEqRefl lhs)
      try
        withOptions (fun o => o.setBool `Elab.async false) do
          addDecl (.thmDecl { name := eqName, levelParams := [], type := eqTy, value := pf })
      catch e => refuse decl "open" m!"the kernel refused the open-parent equation: {e.toMessageData}"
      return { openName, eqName, calls := infos }

/-! ## The generated proof -/

structure InstInfo where
  mn : String
  iname : String
  cs : List (String × Sparkle.IR.AST.Expr)
  kid : Nat
  y : String
  call : Nat

def ptyTxt : PTy → String
  | .bit => "Tools.VedU1Contract.PTy.bit"
  | .bv w => s!"(Tools.VedU1Contract.PTy.bv {w})"

def hwTxt : HWType → String
  | .bit => "Sparkle.IR.Type.HWType.bit"
  | .bitVector w => s!"(Sparkle.IR.Type.HWType.bitVector {w})"
  | _ => "?"

def outPTy (t : DeclTable) : PTy :=
  match t.out with
  | .leaf p => p
  | .pair _ _ => .bit

/-- The proof text of `U2HStmt P.contract P.mod P.design F`. -/
def scriptTextS (nm : HNames) (F : Name) (nDom : Nat) (tbl : DeclTable) (opn : OpenInfo)
    (kids : List Kid) (insts : List InstInfo) : String := Id.run do
  let P := nm.user
  let kids := kids.map fun k => { k with nm := namesUser k.nm }
  let kidA := kids.toArray
  let O := userName opn.openName
  let OE := userName opn.eqName
  let FT := declTerm F nDom
  let mut L : Array String := #[]
  let T2 := "Tools.VedU2Hier"
  L := L.push s!"  have hS : {T2}.HierShapeS {P.design} {P.mod} = true := by decide"
  L := L.push s!"  have hne := {T2}.hierS_ne hS"
  L := L.push s!"  have hord : {T2}.OrderHS {P.design} {P.mod} := ⟨{P.body}, by decide⟩"
  L := L.push s!"  have hOK : {T2}.OrderOkHS {P.design} {P.mod} {P.body} = true := by decide"
  L := L.push s!"  have hb0 := {T2}.orderOkHS_sound hOK"
  let modsList := "[" ++ ", ".intercalate (kids.map fun k => s!"{k.nm.mod}") ++ "]"
  L := L.push s!"  have hmods : {P.design}.modules = {modsList} := by decide"
  L := L.push s!"  have hch : ∀ x ∈ {P.design}.modules, Tools.VedU1Contract.OrderStmt x := by"
  L := L.push s!"    rw [hmods]; intro x hx"
  L := L.push s!"    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx"
  let pat := " | ".intercalate (kids.map fun _ => "h")
  if kids.length == 0 then
    L := L.push s!"    exact absurd hx (by simp)"
  else if kids.length == 1 then
    for k in kids do
      L := L.push s!"    subst hx"
      L := L.push s!"    exact {k.nm.thm}.2.2.2.1"
  else
    L := L.push s!"    rcases hx with {pat}"
    for k in kids do
      L := L.push s!"    · subst h; exact {k.nm.thm}.2.2.2.1"
  L := L.push s!"  refine ⟨by decide, by decide, by decide, hS, by decide, by decide, hord, hch, {T2}.exists_arrHS _ _ hord hch hne, ?_⟩"
  L := L.push s!"  intro arr hadm"
  L := L.push s!"  have hwr := {T2}.orderOkHS_hwr hOK hadm.1"
  L := L.push s!"  have htie : {P.contract}.clkRst = {T2}.designClkRst {P.design} {P.mod} := by decide"
  L := L.push s!"  have hnoreg : Tools.VedU1Contract.regsOf {P.mod}.body = [] := by decide"
  L := L.push s!"  have hout : {P.contract}.outputs = {P.outs} := by decide"
  for (k, i) in kids.zipIdx do
    let G := declTerm k.decl k.nDom
    let K := k.nm
    L := L.push s!"  have hmem{i} : {K.mod} ∈ {P.design}.modules := by rw [hmods]; simp"
    L := L.push s!"  have hpw{i} := hadm.2.2 _ hmem{i}"
    L := L.push s!"  have hsc{i} : {T2}.ChildSucc {K.mod} (arr {K.mod}) := {T2}.childSucc_of_outputsOn {K.contract} {K.mod} (arr {K.mod}) {G} ({K.thm}.2.2.2.2 _ hpw{i}.1 hpw{i}.2)"
  L := L.push s!"  have hsch : ∀ x ∈ {P.design}.modules, {T2}.ChildSucc x (arr x) := by"
  L := L.push s!"    rw [hmods]; intro x hx"
  L := L.push s!"    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx"
  if kids.length == 0 then
    L := L.push s!"    exact absurd hx (by simp)"
  else if kids.length == 1 then
    L := L.push s!"    subst hx"
    L := L.push s!"    exact hsc0"
  else
    L := L.push s!"    rcases hx with {pat}"
    for (_, i) in kids.zipIdx do
      L := L.push s!"    · subst h; exact hsc{i}"
  L := L.push s!"  have hsupp : {T2}.ExprsSupp {P.mod} (arr {P.mod}) :="
  L := L.push s!"    {T2}.exprsSupp_perm (hb0.1.trans hadm.1.symm) (show ∀ s ∈ {P.body}, {T2}.StmtSupp (Tools.VedU1Contract.declWidth {P.mod}) s = true by decide)"
  -- the argument terms
  let nIn := tbl.ins.length
  let argTxt (bn : String) : String :=
    match (tbl.binders.zipIdx).find? (fun (b, _) => b == bn) with
    | some (_, j) => s!"(Tools.VedU1Contract.PTy.sig {ptyTxt (tbl.ins.getD j .bit)} ins {sq ("_gen_" ++ bn)})"
    | none => "?"
  let callTxt (c : CallInfo) : String :=
    let k := kidA[c.kid]!
    let G := declTerm k.decl k.nDom
    if c.args.isEmpty then G else s!"({G} {" ".intercalate (c.args.map argTxt)})"
  let obsOf (p : PTy) (sg : String) : String :=
    s!"(Tools.VedU1Contract.PTy.obs {ptyTxt p} ({sg}.val t))"
  let kidOut (ki : Nat) : PTy := outPTy kidA[ki]!.tbl
  let calls := opn.calls
  let sigBinders := " ".intercalate ((calls.toList.zipIdx).map fun (c, j) =>
    s!"(P{j} : {sigTy (kidOut c.kid)})")
  let oracleBody (sg : Nat → String) : String :=
    insts.foldr (fun (ii : InstInfo) acc =>
      s!"if y = {sq ii.y} then {obsOf (kidOut ii.kid) (sg ii.call)} else {acc}") "0"
  let openArgs := " ".intercalate ((tbl.binders.zipIdx).map fun (b, _) => argTxt b)
  let pArgs := " ".intercalate ((List.range calls.size).map fun j => s!"P{j}")
  let openApp := s!"({O} {openArgs} {pArgs})"
  let _ := nIn
  -- the open parent's meaning on the SAME (m, d): instances are free oracle values
  let hIs := insts.zipIdx.map fun (ii, j) => s!"hO{j}"
  for (ii, j) in insts.zipIdx do
    L := L.push s!"  have hO{j} : Tools.VedU1Hier.instOuts {P.design} {sq ii.mn} {connsLit ii.cs} = [{sq ii.y}] := by decide"
  let hOl := ", ".intercalate hIs
  L := L.push s!"  have hopenM : ∀ (ins : Nat → String → Nat), Tools.VedU1Contract.InputsOk {P.contract} {P.mod} ins → ∀ (t : Nat) {sigBinders}, ∃ E, Tools.VedU1Hier.evalAssignsI (Tools.VedU1Contract.declWidth {P.mod}) ({T2}.oracleIE {P.design} (fun y => {oracleBody (fun j => s!"P{j}")})) {P.body} (Tools.VedU1Contract.seedIn {P.mod} ins t (fun _ => 0)) = some E ∧ ∀ o ∈ {P.outs}, E o.name = {obsOf (outPTy tbl) (openApp)} := by"
  L := L.push s!"    intro ins hok t {" ".intercalate ((List.range calls.size).map fun j => s!"P{j}")}"
  L := L.push s!"    have hin := hok.1 t"
  L := L.push s!"    simp [{P.contract}, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.Contract.dataInputs, {P.mod}, Tools.VedU1Contract.declWidth] at hin"
  -- the oracle values are in range (a bit-vector signal's value is below `2 ^ w`)
  for (c, j) in calls.toList.zipIdx do
    match kidOut c.kid with
    | .bv w => L := L.push s!"    have hlt{j} : (P{j}.val t).toNat < 2 ^ {w} := (P{j}.val t).isLt"
    | .bit => L := L.push s!"    have hlt{j} : Bool.toNat (P{j}.val t) < 2 ^ 1 := by cases (P{j}.val t) <;> simp"
  let hltl := ", ".intercalate ((List.range calls.size).map fun j => s!"hlt{j}")
  L := L.push s!"    simp [Tools.VedU1Hier.evalAssignsI, Tools.VedU1Hier.cellVals, {T2}.oracleIE, {hOl}, {P.body}, {P.outs}, {O}, Tools.VedU1Contract.seedIn, {P.mod}, Tools.VedU1Contract.declWidth, Sparkle.IR.Semantics.widthOf, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalExpr.go, Tools.VedU1Hier.upd, Tools.VedU1Contract.PTy.obs, Tools.VedU1Contract.PTy.sig, Tools.VedU1Entry.or_mod _ _ _ _ rfl, Nat.shiftRight_eq_div_pow, Tools.VedU1Lemmas.evalOp_not_lit, Tools.VedU1Lemmas.compl_val, Tools.VedU1Lemmas.evalOp_and_lit, Tools.VedU1Lemmas.evalOp_or_lit, Tools.VedU1Lemmas.evalOp_xor_lit, Tools.VedU1Lemmas.and_val, Tools.VedU1Lemmas.or_val, Tools.VedU1Lemmas.xor_val, Tools.VedU1Lemmas.evalOp_add_lit, Tools.VedU1Lemmas.add_val, BitVec.toNat_add, Tools.VedU1Lemmas.evalOp_sub_lit, Tools.VedU1Lemmas.sub_val, BitVec.toNat_sub, Tools.VedU1Lemmas.evalOp_mux_lit, Tools.VedU1Lemmas.mux_val, Seq.seq, Sparkle.Core.Signal.Signal.seq, Sparkle.Core.Signal.Signal.ap, BitVec.toNat_append, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, Nat.mod_eq_of_lt, Functor.map, Sparkle.Core.Signal.Signal.map, BitVec.toNat_not, BitVec.toNat_ofNat, hin, {hltl}]"
  L := L.push s!"    try omega"
  L := L.push s!"    try (split <;> simp <;> omega)"
  -- the oracle of the run
  let owBody := oracleBody (fun j => callTxt calls[j]!)
  L := L.push s!"  refine {T2}.outputsOnHS_of_oracle {P.contract} {P.mod} {P.design} arr {FT} hS hadm hnoreg hsupp hsch {P.body} (hadm.1.trans hb0.1.symm) hb0.2.1 (fun ins y t => {owBody}) ?_ ?_"
  -- hkid
  L := L.push s!"  · intro ins hok K envs sts hrun mn i cs hin t ht E hE y hy"
  L := L.push s!"    have hin0 := hin"
  L := L.push s!"    have hin1 : Sparkle.IR.AST.Stmt.inst mn i cs ∈ {P.body} := hb0.1.mem_iff.mpr hin"
  L := L.push s!"    simp only [{P.body}, List.mem_cons, List.not_mem_nil, or_false, Sparkle.IR.AST.Stmt.inst.injEq, reduceCtorEq] at hin1"
  let nI := insts.length
  let patI := " | ".intercalate (insts.map fun _ => "⟨rfl, rfl, rfl⟩")
  if nI == 1 then
    L := L.push s!"    obtain ⟨rfl, rfl, rfl⟩ := hin1"
  else
    L := L.push s!"    rcases hin1 with {patI}"
  for (ii, j) in insts.zipIdx do
    let k := kidA[ii.kid]!
    let K := k.nm
    let G := declTerm k.decl k.nDom
    let outPort := k.c.outputs.headD ⟨"out", .bit⟩
    let outName := outPort.name
    let ks := if nI == 1 then "" else "    · "
    let ind := if nI == 1 then "    " else "      "
    let first := if nI == 1 then "    " else "    · "
    let lines : List String := [
      s!"have hy' : y = {sq ii.y} := by\n  have h1 := hO{j}\n  rw [h1] at hy\n  simpa using hy",
      s!"subst hy'",
      s!"have hq : (⟨{sq outName}, {hwTxt outPort.ty}⟩ : Sparkle.IR.AST.Port) ∈ {K.mod}.outputs := by simp [{K.mod}]",
      s!"obtain ⟨x, hx, hv⟩ := {T2}.kid_inst {P.design} arr {P.mod} hS hadm hwr {P.contract} htie ins hok K envs sts hrun {sq ii.mn} {sq ii.iname} {connsLit ii.cs} hin0 {K.mod} (by decide) {K.contract} {G} {K.thm} (by decide) ({T2}.connsIn_sound (by decide)) ({T2}.dataIn_sound (by decide)) t ht E hE _ hq",
      s!"have hx' : x = {sq ii.y} := by\n  have h2 : ({connsLit ii.cs}).lookup {sq outName} = some (Sparkle.IR.AST.Expr.ref {sq ii.y}) := by decide\n  rw [h2] at hx\n  simpa using hx.symm",
      s!"subst hx'",
      s!"rw [hv]",
      s!"simp [Tools.VedU1Contract.srcOf, Tools.VedU1Contract.applyIns, {K.contract}, Tools.VedU1Contract.contractOf, {T2}.insCIn, List.lookup, Tools.VedU1Contract.OTy.obs, Tools.VedU1Contract.PTy.obs, Tools.VedU1Contract.PTy.sig]"]
    let _ := ks
    let mut firstL := true
    for l in lines do
      if firstL then
        L := L.push (first ++ l.replace "\n" ("\n" ++ ind))
        firstL := false
      else
        L := L.push (ind ++ l.replace "\n" ("\n" ++ ind))
  -- hopen
  L := L.push s!"  · intro ins hok t"
  L := L.push s!"    obtain ⟨E, hE, hP⟩ := hopenM ins hok t {" ".intercalate (calls.toList.map callTxt)}"
  L := L.push s!"    refine ⟨E, hE, ?_⟩"
  L := L.push s!"    intro o ho"
  L := L.push s!"    rw [hout] at ho"
  L := L.push s!"    rw [hP o ho]"
  L := L.push s!"    simp [{P.outs}] at ho"
  L := L.push s!"    subst ho"
  L := L.push s!"    simp [Tools.VedU1Contract.srcOf, Tools.VedU1Contract.applyIns, {P.contract}, Tools.VedU1Contract.contractOf, {OE}, Tools.VedU1Contract.OTy.obs, Tools.VedU1Contract.PTy.obs, Tools.VedU1Contract.PTy.sig]"
  return "\n".intercalate L.toList

/-! ## The checker and the entry -/

/-- The checker under the entry: `m` and `d` are the values `synthesizeCombinational` returned.
On a failure it restores the state saved when it started and throws a refusal.  The optional
`clkRstOverride` is for the controls only: it replaces the contract's clock/reset pair (the entry
derives it from the parent's trailing inputs). -/
def checkU2H (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (m : Sparkle.IR.AST.Module) (d : Design)
    (clkRstOverride : Option (Option (String × String)) := none) :
    TermElabM (Name × Nat × Nat) := do
  let nm := HNames.ofBase decl
  let saved ← saveState
  tryCatchRuntimeEx (do
    let tbl ← try readTableOfType decl (← inferType stmt) catch e => refuse decl "table" e.toMessageData
    unless tbl.out.flat.length == 1 do
      refuse decl "multi-output"
        m!"{tbl.out.flat.length} output projections (multi-output: H3), refused (H2a: one output)"
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
    if let some msg := hierDiagS d m then refuse decl "hier-shape" msg
    unless HierShapeS d m do refuse decl "hier-shape" m!"HierShapeS fails"
    -- the contract: the declaration's table, the parent's trailing inputs as clock / reset
    let some clkRst0 := parentClkRst tbl m
      | refuse decl "clkrst" m!"the parent has {m.inputs.length - tbl.ins.length} inputs after the declaration's {tbl.ins.length} data inputs (expected none, or exactly clock and reset)"
    let clkRst := clkRstOverride.getD clkRst0
    let cE := mkAppN (Lean.mkConst ``contractOf)
      #[toExpr tbl, toExpr ["out"], toExpr clkRst, Lean.mkConst nm.mod]
    addDefn nm.contract (Lean.mkConst ``Contract) cE
    let c := contractOf tbl ["out"] clkRst m
    unless decide (CorrStmt c) do
      refuse decl "table" m!"the declaration/contract correspondence (CorrStmt) fails"
    unless decide (c.clkRst = designClkRst d m) do
      refuse decl "clkrst"
        m!"the parent contract's clock/reset pair {repr c.clkRst} is not the pair of parent inputs the instances' clock and reset ports are connected to ({repr (designClkRst d m)})"
    unless decide (ShapeCore c m) do
      refuse decl "artifact"
        m!"the returned module does not match the declaration's ports (ShapeCore): inputs {repr m.inputs}, outputs {repr m.outputs}"
    unless decide (WidthStmt c m) do refuse decl "artifact" m!"WidthStmt fails"
    addDefn nm.outs (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Port))
      (toExpr c.outputs)
    let b0 := orderBodyH d m.body
    unless OrderOkHS d m b0 do refuse decl "order" m!"{orderDiagHS d m b0}"
    addDefn nm.body (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Stmt))
      (toExpr b0)
    unless (regsOf m.body).isEmpty do
      refuse decl "scope" m!"the parent has registers (H2b: a parent with registers is another unit)"
    if d.modules.isEmpty then
      refuse decl "scope" m!"the parent has no child instance (a register-free parent without instances is `#ved_u1`)"
    -- every module of the design: its declaration and port table
    let mut pre : List (Sparkle.IR.AST.Module × Name × Lean.Expr × Nat × DeclTable) := []
    for cm in d.modules do
      let cdecl := cm.name.toName
      unless (← getEnv).contains cdecl do
        refuse decl "child" m!"child module {cm.name}: no declaration of that name"
      let (cstmt, cdom) ← try specialiseDomain cdecl
        catch e => refuse decl "child" m!"child {cm.name}: {e.toMessageData}"
      let ctbl ← try readTableOfType cdecl (← inferType cstmt)
        catch e => refuse decl "child" m!"child {cm.name}: {e.toMessageData}"
      pre := pre ++ [(cm, cdecl, cstmt, cdom, ctbl)]
    -- scope: every instance input is read from a parent input (data port from a data input)
    for s in m.body do
      match s with
      | .inst mn iname cs =>
        let some (cm, _, _, _, ctbl) := pre.find? (fun x => x.1.name == mn)
          | refuse decl "child" m!"instance {iname}: no module {mn}"
        let ck := contractOf ctbl ["out"] (clkRstOf cm) cm
        unless connsIn m cm cs do
          refuse decl "conns"
            m!"instance {iname}: an input port of {mn} is not connected to a parent input (derived or chained instance inputs are outside H2a)"
        unless dataIn c m ck cm cs do
          refuse decl "conns"
            m!"instance {iname}: a data port of {mn} is not connected to a parent DATA input of the same width"
      | _ => pure ()
    -- the children's U1 theorems
    let t0 ← IO.monoMsNow
    let mut kids : List Kid := []
    for (cm, cdecl, cstmt, cdom, ctbl) in pre do
      let base := (decl ++ `ved_child) ++ cdecl
      let proofSrc : ProofSrc :=
        if (regsOf cm.body).isEmpty then .generated else .built (buildDeepWith cdecl cdecl ctbl)
      try discard <| checkU1E cdecl base cstmt cm proofSrc
      catch e => refuse decl "child" m!"child {cm.name}: {e.toMessageData}"
      kids := kids ++ [{ c := cm, decl := cdecl, nDom := cdom, tbl := ctbl, nm := Names.ofBase base }]
    let t1 ← IO.monoMsNow
    -- the open parent, generated from the declaration
    let opn ← genOpen decl stmt nDom tbl kids nm.mod.getPrefix
    let mut insts : List InstInfo := []
    for s in m.body do
      match s with
      | .inst mn iname cs =>
        let some (ki, k) := (kids.zipIdx.find? fun (k, _) => k.c.name == mn).map (fun (k, i) => (i, k))
          | refuse decl "child" m!"instance {iname}: no module {mn}"
        let y := match cs.lookup (outNameOf k.c) with | some (.ref y) => y | _ => "?"
        let args := k.tbl.binders.map fun b =>
          match cs.lookup ("_gen_" ++ b) with
          | some (.ref x) => if x.startsWith "_gen_" then (x.drop 5).toString else "?"
          | _ => "?"
        let some ci := opn.calls.findIdx? (fun c => c.kid == ki && c.args == args)
          | refuse decl "open"
              m!"instance {iname}: the declaration's body has no call of {mn} on the parent inputs {args}"
        insts := insts ++ [{ mn, iname, cs, kid := ki, y, call := ci }]
      | _ => pure ()
    let expected := mkAppN (Lean.mkConst ``U2HStmt)
      #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]
    try check expected catch e => refuse decl "type" e.toMessageData
    unless ← isProp expected do refuse decl "type" m!"expected statement is not a Prop"
    let text := "by\n" ++ scriptTextS nm stmt.getAppFn.constName! stmt.getAppNumArgs tbl opn kids insts
    if (← IO.getEnv "VED_HIER_DEBUG").isSome then IO.eprintln text
    let stx ← match Lean.Parser.runParserCategory (← getEnv) `term text "<ved_u2_hier>" with
      | .ok s => pure s
      | .error e => refuse decl "proof" m!"generated script does not parse: {e}"
    let errsBefore := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
    let pf ← try
        withOptions (fun o => ((o.setBool `linter.unusedSimpArgs false).setBool
            `linter.unusedTactic false).setBool `linter.unreachableTactic false) <| withoutErrToSorry do
          let e ← elabTermEnsuringType stx expected
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
      catch e => refuse decl "proof" e.toMessageData
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
    return (nm.thm, t1 - t0, t2 - t1)) fun e => do
    saved.restore (restoreInfo := true)
    if ← isRefusal e then throw e
    refuse decl "checker" e.toMessageData

/-- The entry: ONE `synthesizeCombinational`, the returned `(m, d)` is what is proved about. -/
def vedU2HierEntry (declName : Name) :
    TermElabM (Sparkle.IR.AST.Module × Design × Name × Nat × Stats) := do
  let (stmt, nDom) ← try specialiseDomain declName catch e => refuse declName "table" e.toMessageData
  let tbl ← try readTableOfType declName (← inferType stmt) catch e => refuse declName "table" e.toMessageData
  unless tbl.out.flat.length == 1 do
    refuse declName "multi-output"
      m!"{tbl.out.flat.length} output projections (multi-output: H3), refused (H2a: one output)"
  let t0 ← IO.monoMsNow
  let (m, d) ← try Sparkle.Compiler.Elab.synthesizeCombinational declName
    catch e => refuse declName "synthesis" e.toMessageData
  let t1 ← IO.monoMsNow
  let (thm, childMs, proofMs) ← checkU2H declName stmt nDom m d
  return (m, d, thm, nDom, { synthMs := t1 - t0, childMs, proofMs, peakKb := ← peakKb })

/- The command `#ved_u2_hier` is defined in `Tools/VedU2HierRegEntry.lean` (H2b): a register-free
parent is `checkU2H` above, as in H2a. -/

end Tools.VedU2HierEntry
