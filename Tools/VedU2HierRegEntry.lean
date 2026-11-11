import Tools.VedU2HierEntry
import Tools.VedU2HierReg
import Tools.VedU2HierNet
import Tools.DeepElab

/-!
# Stateful hierarchical entry, H2b: a parent WITH REGISTERS (`#ved_u2_hier decl`)

Design: docs/VED-HIER-H2-DESIGN.md §1.2, §12; record: docs/VED-HIER-H2B.md.  `Tools/VedU2HierEntry.lean`
(`checkU2H`, `vedU2HierEntry`, the H2a statement `U2HStmt`) is NOT changed; its `[scope]` refusal of
a parent with registers is still what `checkU2H` does.  This file adds `checkU2HR` /
`vedU2HierEntryR` and moves the `#ved_u2_hier` command here: a register-free parent goes through
`checkU2H` exactly as in H2a (statement `U2HStmt`), a parent with registers through `checkU2HR`
(statement `U2HRStmt`).

Scope (H2b): depth 1, single-output leaf children (registers allowed), every instance input
connected straight to a parent INPUT, the parent may carry registers.

The new part is how the parent's registers are supplied.  They come from facts that are GENERATED
and KERNEL-CHECKED, never from hypotheses: the entry generates the open parent (`decl.ved_open`:
the child calls abstracted into free signals, the equation `decl xs = ved_open xs calls` added to
the kernel, as in H2a) and runs `#verify_elab_deep` on it (the deep route's facts
`_deep`, `_nm`, `_inp`, `_deep_trace`, `_deep_next`, `_deep_inits`, `_deep_out`, exactly the ones
`#ved_u1_deep` uses).  The proof then discharges the invariant of `outputsOnHS_of_stepR` on the
parent's own registers: slot `i` of the open circuit is the returned module's register
`(regsOf m.body)[i]` (a mapping the generated proof checks: a wrong one fails in the kernel), its
value at cycle `t` is `Cdo.irState`, its initial value is `st0Of m`, and one cycle of the checked
arrangement (instances as free oracle values) evaluated by `simp` is compared with the compiled
`next`.
-/

namespace Tools.VedU2HierRegEntry

open Lean Meta Elab Term Command
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU1Deep

/-! ## A simproc for the slot arithmetic of the open circuit's input lookups

With more than a few inputs the context lookup of an input slot is `Fin.mk (↑k - nReg) _` (a
subtraction of the register count from a numeral `Fin` value), which neither `Fin.reduceFinMk`
(first argument not a literal) nor `reduceFinVal` (not under `Fin.mk`) reduces, so the generated
`_inp_at_<j>` lemmas, stated at a literal `j`, do not fire.  The simproc evaluates the closed
first argument and returns the literal; the result is definitionally the same term. -/

open Lean Meta Elab Tactic in
/-- Replace every `Fin.mk a h` whose first argument is a closed, non-literal numeral expression by
the literal `(value : Fin n)`, and every `Fin.val` of a numeral by its value (definitionally the
same term). -/
def finNormExpr (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun x => do
    match x.getAppFnArgs with
    | (``Fin.mk, #[n, a, _]) =>
      if a.isRawNatLit || a.isAppOfArity ``OfNat.ofNat 3 || a.hasFVar || a.hasMVar then return .done x
      let some nv ← natLit? n | return .done x
      let some av ← natLit? a | return .done x
      if nv == 0 || av ≥ nv then return .done x
      let ty := mkApp (mkConst ``Fin) n
      let r ← try mkAppOptM ``OfNat.ofNat #[some ty, some (mkRawNatLit av), none]
        catch _ => mkAppOptM ``OfNat.ofNat #[some (mkApp (mkConst ``Fin) (toExpr nv)), some (mkRawNatLit av), none]
      return .done r
    | (``Fin.val, #[n, x]) =>
      -- `Fin.val (k : Fin n)` of a numeral
      unless x.isAppOfArity ``OfNat.ofNat 3 do return .continue
      let some k := (x.getArg! 1).rawNatLit? | return .continue
      let some nv ← natLit? n | return .continue
      if nv == 0 then return .continue
      return .done (toExpr (k % nv))
    | _ => return .continue)

open Lean Meta Elab Tactic in
/-- `ved_fin_norm`: normalise those input-slot indices in the goal (definitional change). -/
elab "ved_fin_norm" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let ty' ← finNormExpr ty
  if ty' != ty then replaceMainGoal [← g.replaceTargetDefEq ty']

/-! ## H2c: instance data inputs read from a NET computed from the parent's data inputs only -/

/-- `x` is a parent data input or an assigned wire all of whose reads are (recursively, with fuel)
parent data inputs or such wires: a pure function of the data inputs (no register output, no
instance output, no clock/reset). -/
def pureNetB (dataIns : List String) (b : List Stmt) : Nat → String → Bool
  | 0, _ => false
  | fuel + 1, x =>
    dataIns.contains x ||
      match asgOf b x with
      | some r => (refsOf r).all (pureNetB dataIns b fuel)
      | none => false

/-- The assigned wires `x` is computed from (itself included), input names excluded. -/
def netChain (dataIns : List String) (b : List Stmt) : Nat → String → List String
  | 0, _ => []
  | fuel + 1, x =>
    if dataIns.contains x then []
    else match asgOf b x with
      | some r => x :: (refsOf r).flatMap (netChain dataIns b fuel)
      | none => []

/-- The first leaf of a net that is not a parent data input, with its kind. -/
def badLeaf (d : Design) (dataIns : List String) (b : List Stmt) : Nat → String → Option String
  | 0, x => some s!"{x} (the net is too deep)"
  | fuel + 1, x =>
    if dataIns.contains x then none
    else if (regOuts b).contains x then
      some s!"{x} is a parent register output (a register-driven instance input has no closed Lean term over the parent inputs when the register is a loop: H2c covers nets computed from parent data inputs only)"
    else if (instOutsOf d b).contains x then
      some s!"{x} is another instance's output (a chained instance input)"
    else match asgOf b x with
      | some r => (refsOf r).findSome? (badLeaf d dataIns b fuel)
      | none => some s!"{x} is neither a parent data input nor assigned (the clock/reset or an undriven name)"

/-- Why a net is not a pure function of the parent data inputs. -/
def netWhy (d : Design) (dataIns : List String) (b : List Stmt) (x : String) : String :=
  match badLeaf d dataIns b b.length x with
  | some msg => s!"{x} is computed from a net that is not a function of the data inputs: {msg}"
  | none => s!"{x} is not a pure net"

/-- The first reason an instance's connections are outside H2b/H2c (plain inputs for the clock and
reset ports; each data port a parent data input or a net computed from the data inputs only). -/
def connDiagNet (d : Design) (c : Contract) (m : Sparkle.IR.AST.Module) (b : List Stmt)
    (ck : Contract) (cm : Sparkle.IR.AST.Module) (iname : String)
    (cs : List (String × Sparkle.IR.AST.Expr)) : Option String :=
  let dataIns := c.dataInputs.map (·.name)
  if !connsNet m cm ck cs then
    some s!"instance {iname}: a clock/reset port of {cm.name} is not connected to a parent input (or a port is not a plain wire reference)"
  else
    ck.dataInputs.findSome? fun p =>
      match cs.lookup p.name with
      | some (.ref x) =>
        if declWidth m x != declWidth cm p.name then
          some s!"instance {iname}: data port {p.name} of {cm.name} is not connected to a parent input or net of the same width"
        else if pureNetB dataIns b b.length x then none
        else some s!"instance {iname}: data port {p.name} of {cm.name} is not connected to a parent input or to a net computed from parent inputs only: {netWhy d dataIns b x}"
      | _ => some s!"instance {iname}: data port {p.name} of {cm.name} is not connected to a plain wire reference"

/-- The expression of a net with every assigned wire inlined (the net as a function of the parent
data inputs); two instances with equal inlined nets on every data port compute the same stream. -/
partial def inlineNet (dataIns : List String) (b : List Stmt) : Nat → Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr
  | 0, e => e
  | fuel + 1, e =>
    match e with
    | .ref x =>
      if dataIns.contains x then e
      else match asgOf b x with
        | some r => inlineNet dataIns b fuel r
        | none => e
    | .op o as => .op o (as.map (inlineNet dataIns b fuel))
    | .concat as => .concat (as.map (inlineNet dataIns b fuel))
    | .slice x hi lo => .slice (inlineNet dataIns b fuel x) hi lo
    | .index a i => .index (inlineNet dataIns b fuel a) (inlineNet dataIns b fuel i)
    | e => e

/-- The instance reads a derived net (some data port is not a parent data input). -/
def instDerived (c : Contract) (ck : Contract) (cs : List (String × Sparkle.IR.AST.Expr)) : Bool :=
  let dataIns := c.dataInputs.map (·.name)
  ck.dataInputs.any fun p => match cs.lookup p.name with
    | some (.ref x) => !dataIns.contains x
    | _ => false

/-! ## The generated proof of `U2HRStmt` -/

structure DeepInfo where
  /-- widths of the open circuit's register slots -/
  regWs : List Nat
  /-- number of inputs of the open circuit (data inputs, then one per child call) -/
  nIn : Nat
  /-- the parent's register output names, slot order -/
  pm : List String

/-- The name of the stream definition `ved_F<j>` of derived call `j`. -/
def fDefName (opn : OpenInfo) (j : Nat) : Name :=
  Name.mkStr opn.openName.getPrefix (opn.openName.getString! ++ s!"_F{j}")

/-- The simp set that evaluates a net's IR expression and the Signal term of the declaration's
argument. -/
def netSimpL : String :=
  "Sparkle.IR.Semantics.widthOf, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalExpr.go, Tools.VedU1Entry.or_mod _ _ _ _ rfl, Nat.shiftRight_eq_div_pow, Tools.VedU1Lemmas.evalOp_not_lit, Tools.VedU1Lemmas.compl_val, Tools.VedU1Lemmas.evalOp_and_lit, Tools.VedU1Lemmas.evalOp_or_lit, Tools.VedU1Lemmas.evalOp_xor_lit, Tools.VedU1Lemmas.and_val, Tools.VedU1Lemmas.or_val, Tools.VedU1Lemmas.xor_val, Tools.VedU1Lemmas.evalOp_add_lit, Tools.VedU1Lemmas.add_val, BitVec.toNat_add, Tools.VedU1Lemmas.evalOp_sub_lit, Tools.VedU1Lemmas.sub_val, BitVec.toNat_sub, Tools.VedU1Lemmas.evalOp_mux_lit, Tools.VedU1Lemmas.mux_val, Seq.seq, Sparkle.Core.Signal.Signal.seq, Sparkle.Core.Signal.Signal.ap, BitVec.toNat_append, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, Nat.mod_eq_of_lt, Functor.map, Sparkle.Core.Signal.Signal.map, BitVec.toNat_not, BitVec.toNat_ofNat, Tools.VedU1Contract.PTy.obs, Tools.VedU1Contract.PTy.sig, Sparkle.IR.Semantics.mask, Sparkle.Core.Signal.Signal.pure"

def deepC (open_ : Name) (s : String) : String := toString (userName (deepName open_ s))

def scriptTextR (nm : HNames) (F : Name) (nDom : Nat) (tbl : DeclTable) (opn : OpenInfo)
    (kids : List Kid) (insts : List InstInfo) (di : DeepInfo) (dbg : Bool := false) : String := Id.run do
  let P := nm.user
  let kids := kids.map fun k => { k with nm := namesUser k.nm }
  let kidA := kids.toArray
  let O := userName opn.openName
  let OE := userName opn.eqName
  let FT := declTerm F nDom
  let T2 := "Tools.VedU2Hier"
  let ODeep := deepC opn.openName "_deep"
  let ONm := deepC opn.openName "_nm"
  let OInp := deepC opn.openName "_inp"
  let OTrace := deepC opn.openName "_deep_trace"
  let ONext := deepC opn.openName "_deep_next"
  let OInits := deepC opn.openName "_deep_inits"
  let OOut := deepC opn.openName "_deep_out"
  let inpU := toString (userName (opn.openName ++ `ved_inpU))
  let irS := toString (userName (opn.openName ++ `ved_irS))
  let k := di.regWs.length
  let mut L : Array String := #[]
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
  L := L.push s!"  refine ⟨by decide, by decide, by decide, hS, by decide, hord, hch, {T2}.exists_arrHS _ _ hord hch hne, ?_⟩"
  L := L.push s!"  intro arr hadm"
  L := L.push s!"  have hwr := {T2}.orderOkHS_hwr hOK hadm.1"
  L := L.push s!"  have htie : {P.contract}.clkRst = {T2}.designClkRst {P.design} {P.mod} := by decide"
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
  let argTxt (bn : String) : String :=
    match (tbl.binders.zipIdx).find? (fun (b, _) => b == bn) with
    | some (_, j) => s!"(Tools.VedU1Contract.PTy.sig {ptyTxt (tbl.ins.getD j .bit)} ins {sq ("_gen_" ++ bn)})"
    | none => "?"
  let callTxt (c : CallInfo) : String :=
    let k := kidA[c.kid]!
    let G := declTerm k.decl k.nDom
    if c.derived then s!"({G} {" ".intercalate (c.argDefs.map fun n => s!"({userName n} ins)")})"
    else if c.args.isEmpty then G else s!"({G} {" ".intercalate (c.args.map argTxt)})"
  let obsOf (p : PTy) (sg : String) : String :=
    s!"(Tools.VedU1Contract.PTy.obs {ptyTxt p} ({sg}.val t))"
  let kidOut (ki : Nat) : PTy := outPTy kidA[ki]!.tbl
  let calls := opn.calls
  let oracleBody (sg : Nat → String) : String :=
    insts.foldr (fun (ii : InstInfo) acc =>
      s!"if y = {sq ii.y} then {obsOf (kidOut ii.kid) (sg ii.call)} else {acc}") "0"
  let _ := O
  -- the instances' outputs are single wires, known from the design
  for (ii, j) in insts.zipIdx do
    L := L.push s!"  have hO{j} : Tools.VedU1Hier.instOuts {P.design} {sq ii.mn} {connsLit ii.cs} = [{sq ii.y}] := by decide"
  let hOl := ", ".intercalate (insts.zipIdx.map fun (_, j) => s!"hO{j}")
  -- the invariant: parent register slot i is `irS ins t i`
  let regsTxt := "[" ++ ", ".intercalate (di.pm.map sq) ++ "]"
  let rTerm : String :=
    "(fun (ins : Nat → String → Nat) (t : Nat) (p : String → Nat) => " ++
      " ∧ ".intercalate ((List.range k).map fun i =>
        s!"p {sq di.pm[i]!} = {irS} ins t ⟨{i}, by decide⟩") ++ ")"
  let owBody := oracleBody (fun j => callTxt calls[j]!)
  L := L.push s!"  have hinj : ∀ i j, {ONm} i = {ONm} j → i = j := by decide"
  L := L.push s!"  have hltS : ∀ (ins : Nat → String → Nat) (t : Nat), ∀ i : Fin {k}, {irS} ins t i < 2 ^ ([{", ".intercalate (di.regWs.map toString)}].get ⟨i.val, by simp⟩) := by"
  L := L.push s!"    intro ins t i"
  L := L.push s!"    unfold {irS}"
  L := L.push s!"    rw [Cdo.irState_eq {ODeep} {ONm} hinj]"
  L := L.push s!"    exact BitVec.isLt _"
  L := L.push s!"  refine {T2}.outputsOnHS_of_stepR {P.contract} {P.mod} {P.design} arr {FT} hS hadm hsupp hsch {P.body} (hadm.1.trans hb0.1.symm) hb0.2.1 hb0.2.2.2.1 hb0.2.2.1 (fun ins y t => {owBody}) ?_ {rTerm} ?_ ?_"
  -- hkid (as in H2a)
  L := L.push s!"  · intro ins hok K envs sts hrun mn i cs hin t ht E hE y hy"
  L := L.push s!"    have hin0 := hin"
  L := L.push s!"    have hin1 : Sparkle.IR.AST.Stmt.inst mn i cs ∈ {P.body} := hb0.1.mem_iff.mpr hin"
  L := L.push s!"    simp only [{P.body}, List.mem_cons, List.not_mem_nil, or_false, false_or, Sparkle.IR.AST.Stmt.inst.injEq, reduceCtorEq] at hin1"
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
    let ind := if nI == 1 then "    " else "      "
    let first := if nI == 1 then "    " else "    · "
    let plainLines : List String := [
      s!"have hy' : y = {sq ii.y} := by\n  have h1 := hO{j}\n  rw [h1] at hy\n  simpa using hy",
      s!"subst hy'",
      s!"have hq : (⟨{sq outName}, {hwTxt outPort.ty}⟩ : Sparkle.IR.AST.Port) ∈ {K.mod}.outputs := by simp [{K.mod}]",
      s!"obtain ⟨x, hx, hv⟩ := {T2}.kid_inst {P.design} arr {P.mod} hS hadm hwr {P.contract} htie ins hok K envs sts hrun {sq ii.mn} {sq ii.iname} {connsLit ii.cs} hin0 {K.mod} (by decide) {K.contract} {G} {K.thm} (by decide) ({T2}.connsIn_sound (by decide)) ({T2}.dataIn_sound (by decide)) t ht E hE _ hq",
      s!"have hx' : x = {sq ii.y} := by\n  have h2 : ({connsLit ii.cs}).lookup {sq outName} = some (Sparkle.IR.AST.Expr.ref {sq ii.y}) := by decide\n  rw [h2] at hx\n  simpa using hx.symm",
      s!"subst hx'",
      s!"rw [hv]",
      s!"simp [Tools.VedU1Contract.srcOf, Tools.VedU1Contract.applyIns, {K.contract}, Tools.VedU1Contract.contractOf, {T2}.insCIn, List.lookup, Tools.VedU1Contract.OTy.obs, Tools.VedU1Contract.PTy.obs, Tools.VedU1Contract.PTy.sig]"]
    -- H2c: an instance whose data ports read derived parent nets
    let derivedLines : List String := Id.run do
      let call : CallInfo := opn.calls[ii.call]!
      let Fj := toString (userName (fDefName opn ii.call))
      let ports : List (String × PTy × Name) := k.tbl.binders.zip (k.tbl.ins.zip call.argDefs)
      let hwList := "[" ++ ", ".intercalate (ports.map fun (bn, (pt, _)) =>
        s!"(⟨{sq ("_gen_" ++ bn)}, {hwTxt pt.hw}⟩ : Sparkle.IR.AST.Port)") ++ "]"
      let pat : String := if ports.length ≤ 1 then "rfl" else " | ".intercalate (ports.map fun _ => "rfl")
      let mut X : Array String := #[]
      X := X.push s!"have hdl : {K.contract}.dataInputs = {hwList} := by decide"
      X := X.push s!"have hrange : ∀ t, ∀ p ∈ {K.contract}.dataInputs, {Fj} ins t p.name < 2 ^ Tools.VedU1Contract.declWidth {K.mod} p.name := by"
      X := X.push s!"  intro t p hp"
      X := X.push s!"  rw [hdl] at hp"
      X := X.push s!"  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp"
      X := X.push s!"  rcases hp with {pat}"
      for (bn, (pt, ad)) in ports do
        let nm := "_gen_" ++ bn
        let A := s!"(({toString (userName ad)} ins).val t)"
        X := X.push s!"  · show {Fj} ins t {sq nm} < 2 ^ Tools.VedU1Contract.declWidth {K.mod} {sq nm}"
        X := X.push s!"    have hw : Tools.VedU1Contract.declWidth {K.mod} {sq nm} = {pt.width} := by decide"
        X := X.push s!"    rw [hw]"
        match pt with
        | .bv _ =>
          X := X.push s!"    have h := {A}.isLt"
          X := X.push s!"    simpa [{Fj}, Tools.VedU1Contract.PTy.obs] using h"
        | .bit =>
          X := X.push s!"    have h : Bool.toNat {A} < 2 ^ 1 := by cases {A} <;> simp"
          X := X.push s!"    simpa [{Fj}, Tools.VedU1Contract.PTy.obs] using h"
      X := X.push s!"have hrunF : ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ p ∈ {K.contract}.dataInputs, ∃ x, ({connsLit ii.cs}).lookup p.name = some (Sparkle.IR.AST.Expr.ref x) ∧ E x = {Fj} ins t p.name := by"
      X := X.push s!"  intro t ht E hE p hp"
      X := X.push s!"  have hasgF := {T2}.closed_run_asgOf {P.design} arr {P.mod} hadm {P.body} (hadm.1.trans hb0.1.symm) hb0.2.1 (Tools.VedU1Contract.seedFwd {P.mod} K ins) K ({T2}.st0H {P.design} {P.mod}) envs sts hrun t ht E hE"
      X := X.push s!"  have hEin : ∀ x ∈ {T2}.inNames {P.mod}, E x = ins t x := fun x hx => by"
      X := X.push s!"    have := {T2}.runHS_inputs {P.design} arr {P.mod} hadm hwr ins K K (Nat.le_refl K) _ envs sts hrun t ht E hE x hx"
      X := X.push s!"    simpa using this"
      X := X.push s!"  have hin := hok.1 t"
      X := X.push s!"  simp [{P.contract}, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.Contract.dataInputs, {P.mod}, Tools.VedU1Contract.declWidth] at hin"
      let dataNames := tbl.binders.map ("_gen_" ++ ·)
      let mut facts : List String := []
      for n in dataNames do
        X := X.push s!"  have hE_{n} : E {sq n} = ins t {sq n} := hEin _ (by decide)"
        facts := facts ++ [s!"hE_{n}"]
      let mut lts : List String := []
      for ((w, wd), wi) in ii.chain.zipIdx do
        X := X.push s!"  have e_{wi} := hasgF {sq w} _ rfl"
        X := X.push s!"  simp [{netSimpL}, Tools.VedU1Contract.declWidth, {P.mod}, hin, {", ".intercalate (facts ++ lts)}] at e_{wi}"
        X := X.push s!"  have f_{wi} := e_{wi}.symm"
        if dbg && wi + 1 == ii.chain.length then X := X.push s!"  fail \"TRACE\""
        X := X.push s!"  have hlt_{wi} : E {sq w} < 2 ^ {wd} := by first | omega | (rw [f_{wi}]; exact Nat.and_lt_two_pow _ (by omega)) | (rw [f_{wi}]; exact Nat.or_lt_two_pow (by omega) (by omega)) | (rw [f_{wi}]; exact Nat.xor_lt_two_pow (by omega) (by omega))"
        facts := facts ++ [s!"f_{wi}"]
        lts := lts ++ [s!"hlt_{wi}"]
      X := X.push s!"  rw [hdl] at hp"
      X := X.push s!"  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp"
      X := X.push s!"  rcases hp with {pat}"
      for (bn, (_, ad)) in ports do
        let nm := "_gen_" ++ bn
        let wire := match ii.cs.lookup nm with | some (.ref x) => x | _ => "?"
        X := X.push s!"  · refine ⟨{sq wire}, by decide, ?_⟩"
        X := X.push s!"    simp [{Fj}, {toString (userName ad)}, {netSimpL}, hin, {", ".intercalate (facts ++ lts)}]"
        X := X.push s!"    try omega"
      X := X.push s!"obtain ⟨x, hx, hv⟩ := {T2}.kid_inst_net {P.design} arr {P.mod} hS hadm hwr {P.contract} htie ins hok K envs sts hrun {sq ii.mn} {sq ii.iname} {connsLit ii.cs} hin0 {K.mod} (by decide) {K.contract} {G} {K.thm} (by decide) ({T2}.connsNet_sound (m := {P.mod}) (c := {K.mod}) (ck := {K.contract}) (cs := {connsLit ii.cs}) (by decide)).1 ({T2}.connsNet_sound (m := {P.mod}) (c := {K.mod}) (ck := {K.contract}) (cs := {connsLit ii.cs}) (by decide)).2 ({Fj} ins) hrange hrunF t ht E hE _ hq"
      -- the signals the child's theorem is applied to are the declaration's arguments
      X := X.push s!"generalize hNS : {T2}.netIn {K.contract} ({connsLit ii.cs}) ins ({Fj} ins) = NS at hv"
      let mut sigFacts : List String := []
      for ((bn, (pt, ad)), kk) in ports.zipIdx do
        let nm := "_gen_" ++ bn
        let lem := match pt with | .bv w => s!"{T2}.sig_of_obs_bv {w}" | .bit => s!"{T2}.sig_of_obs_bit"
        X := X.push s!"have hsig{kk} := {lem} (({toString (userName ad)}) ins) NS {sq nm} (fun t => by rw [← hNS]; simp [{T2}.netIn, {K.contract}, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.Contract.dataInputs, {Fj}, Tools.VedU1Contract.PTy.obs])"
        sigFacts := sigFacts ++ [s!"hsig{kk}"]
      X := X.push s!"have hx' : x = {sq ii.y} := by\n  have h2 : ({connsLit ii.cs}).lookup {sq outName} = some (Sparkle.IR.AST.Expr.ref {sq ii.y}) := by decide\n  rw [h2] at hx\n  simpa using hx.symm"
      X := X.push s!"subst hx'"
      X := X.push s!"rw [hv]"
      X := X.push s!"simp [Tools.VedU1Contract.srcOf, Tools.VedU1Contract.applyIns, {K.contract}, Tools.VedU1Contract.contractOf, List.lookup, Tools.VedU1Contract.OTy.obs, Tools.VedU1Contract.PTy.obs, {", ".intercalate sigFacts}]"
      return X.toList
    let lines : List String := if ii.derived then
      -- the shared prefix of the plain lines (the instance's output wire) stays; the child's
      -- theorem is applied through `kid_inst_net`
      (plainLines.take 3) ++ derivedLines else plainLines
    let mut firstL := true
    for l in lines do
      if firstL then
        L := L.push (first ++ l.replace "\n" ("\n" ++ ind))
        firstL := false
      else
        L := L.push (ind ++ l.replace "\n" ("\n" ++ ind))
  -- h0: the parent's own initial registers are the open circuit's inits
  L := L.push s!"  · intro ins hok"
  L := L.push s!"    simp [{T2}.st0Of, {T2}.initsOf, Tools.VedU1Contract.regsOf, {P.mod}, Sparkle.IR.Semantics.encodeInit, Sparkle.IR.Semantics.mask, Tools.VedU1Contract.declWidth, {irS}, Cdo.irState, {OInits}, {ONm}, List.lookup, -Fin.isValue]"
  -- hstep
  L := L.push s!"  · intro ins hok t p hR"
  L := L.push s!"    have hin := hok.1 t"
  L := L.push s!"    have hrst := hok.2 t"
  for i in [0:k] do
    let proj := (List.range i).foldl (fun s _ => s ++ ".2") "hR" ++ (if i + 1 < k then ".1" else "")
    L := L.push s!"    have hR{i} := {proj}"
    L := L.push s!"    have hl{i} := hltS ins t ⟨{i}, by decide⟩"
  -- the oracle values are in range (a bit-vector signal's value is below `2 ^ w`)
  for (c, j) in calls.toList.zipIdx do
    let sg := callTxt c
    match kidOut c.kid with
    | .bv w => L := L.push s!"    have hlo{j} : ({sg}.val t).toNat < 2 ^ {w} := ({sg}.val t).isLt"
    | .bit => L := L.push s!"    have hlo{j} : Bool.toNat ({sg}.val t) < 2 ^ 1 := by cases ({sg}.val t) <;> simp"
  L := L.push s!"    simp [{P.contract}, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.Contract.dataInputs, {P.mod}, Tools.VedU1Contract.declWidth] at hin hrst"
  let locs := " ".intercalate (((List.range k).map fun i => s!"hR{i}") ++ ((List.range k).map fun i => s!"hl{i}") ++
    ((List.range calls.size).map fun j => s!"hlo{j}"))
  let locsU := " ".intercalate (((List.range k).map fun i => s!"hR{i}") ++ ((List.range k).map fun i => s!"hl{i}"))
  let hRs := ", ".intercalate ((List.range k).map fun i => s!"hR{i}")
  let hMods := ", ".intercalate (((List.range k).map fun i => s!"Nat.mod_eq_of_lt hl{i}") ++
    ((List.range calls.size).map fun j => s!"Nat.mod_eq_of_lt hlo{j}"))
  let inpL := ", ".intercalate ((List.range di.nIn).flatMap fun j =>
    [s!"{OInp}_at_{j}", s!"{OInp}_at_mk_{j}"]) ++ ", Tools.VedU1Contract.PTy.sig"
  let argDefsL := ", ".intercalate (calls.toList.flatMap fun c => c.argDefs.map fun n => toString (userName n))
  let evalL := s!"{if argDefsL.isEmpty then "" else argDefsL ++ ", "}Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalExpr.go, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalOp, envOfC, weOfC, chainMap, List.finRange, {ONm}, Tools.VedU1Deep.reduceFinVal, natJoin, Sparkle.IR.Semantics.widthOf, Sparkle.IR.Semantics.mask, Nat.shiftRight_eq_div_pow, Tools.VedU1Entry.or_mod _ _ _ _ rfl, {inpL}"
  L := L.push s!"    simp [hout, {P.outs}, Tools.VedU1Hier.evalAssignsI, Tools.VedU1Hier.cellVals, {T2}.oracleIE, {hOl}, {P.body}, Sparkle.IR.Semantics.regNexts, {T2}.regOuts, Tools.VedU1Contract.regsOf, {T2}.restrictTo, Tools.VedU1Contract.seedIn, {P.mod}, Tools.VedU1Contract.declWidth, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalExpr.go, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalOp, Sparkle.IR.Semantics.widthOf, Tools.VedU1Hier.upd, Sparkle.IR.Semantics.mask, Sparkle.IR.Semantics.applyNexts, Tools.VedU1Entry.or_mod _ _ _ _ rfl, Nat.shiftRight_eq_div_pow, hrst]"
  L := L.push s!"    constructor"
  -- the output
  L := L.push s!"    · try rw [if_pos rfl]"
  L := L.push s!"      all_goals simp [Tools.VedU1Contract.srcOf, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.applyIns, {P.contract}, Tools.VedU1Contract.OTy.obs, Tools.VedU1Contract.PTy.obs, {OE}, Tools.VedU1Contract.PTy.sig]"
  L := L.push s!"      all_goals rw [{OTrace}]"
  L := L.push s!"      all_goals unfold {irS} {inpU} at {locsU}"
  L := L.push s!"      all_goals simp only [CExpr.compile, {OOut}]"
  L := L.push s!"      all_goals simp [{evalL}] at {locs} ⊢"
  L := L.push s!"      all_goals ved_fin_norm"
  L := L.push s!"      all_goals try simp [{evalL}] at ⊢"
  L := L.push s!"      all_goals try simp only [{hRs}]"
  L := L.push s!"      all_goals try simp only [{hMods}]"
  if dbg then L := L.push s!"      all_goals trace_state"
  L := L.push s!"      all_goals (first | omega | ((repeat' split) <;> omega) | ((repeat' split) <;> simp_all <;> omega))"
  -- the next values
  let holes := ", ".intercalate ((List.range k).map fun _ => "?_")
  L := L.push s!"    · {if k == 1 then "skip" else s!"refine ⟨{holes}⟩"}"
  L := L.push s!"      all_goals try simp only [List.find?, {ONm}]"
  L := L.push s!"      all_goals unfold {irS} at *"
  L := L.push s!"      all_goals simp only [Cdo.irState, {ONext}, CExpr.compile]"
  L := L.push s!"      all_goals unfold {inpU} at *"
  L := L.push s!"      all_goals simp [{evalL}, Signal.map, cond_eq_ite, bne_iff_ne, ne_eq, Tools.VedU1Contract.PTy.obs] at {locs} ⊢"
  L := L.push s!"      all_goals ved_fin_norm"
  L := L.push s!"      all_goals try simp [{evalL}, Signal.map, cond_eq_ite, bne_iff_ne, ne_eq, Tools.VedU1Contract.PTy.obs] at ⊢"
  L := L.push s!"      all_goals (try simp only [{hRs}])"
  L := L.push s!"      all_goals (try simp only [{hMods}])"
  if dbg then L := L.push s!"      all_goals trace_state"
  L := L.push s!"      all_goals (first | omega | ((repeat' split) <;> omega) | ((repeat' split) <;> simp_all <;> omega))"
  return "\n".intercalate L.toList

/-! ## The checker -/

/-- What the first phase (everything before the deep facts) returns. -/
structure Phase1 where
  tbl : DeclTable
  opn : OpenInfo
  kids : List Kid
  insts : List InstInfo
  childMs : Nat
  t1 : Nat

/-- Everything up to and including the generation of the open parent, for a parent with registers.
(The same stages and refusals as `checkU2H`, minus the register-free scope clause.) -/
def phase1 (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (m : Sparkle.IR.AST.Module) (d : Design)
    (clkRstOverride : Option (Option (String × String))) : TermElabM Phase1 := do
  let nm := HNames.ofBase decl
  let tbl ← try readTableOfType decl (← inferType stmt) catch e => refuse decl "table" e.toMessageData
  unless tbl.out.flat.length == 1 do
    refuse decl "multi-output"
      m!"{tbl.out.flat.length} output projections (multi-output: H3), refused (H2b: one output)"
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
      m!"the parent contract's clock/reset pair {repr c.clkRst} is not the pair of parent inputs the registers and the instances' clock and reset ports are connected to ({repr (designClkRst d m)})"
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
  if d.modules.isEmpty then
    refuse decl "scope" m!"the parent has no child instance (a parent without instances is `#ved_u1` / `#ved_u1_deep`)"
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
  for s in m.body do
    match s with
    | .inst mn iname cs =>
      let some (cm, _, _, _, ctbl) := pre.find? (fun x => x.1.name == mn)
        | refuse decl "child" m!"instance {iname}: no module {mn}"
      let ck := contractOf ctbl ["out"] (clkRstOf cm) cm
      unless connsIn m cm cs && dataIn c m ck cm cs do
        -- H2c: a data port may read a net computed from the parent data inputs only
        if let some msg := connDiagNet d c m b0 ck cm iname cs then refuse decl "conns" m!"{msg}"
    | _ => pure ()
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
  -- `#verify_elab_deep` declares some of its constants under the ident's LAST component at the root
  -- namespace, so the open parent's last component is made unique per declaration
  let openSuf := "ved_open_" ++ "_".intercalate (decl.components.map toString)
  let opn ← genOpen decl stmt nDom tbl kids nm.mod.getPrefix openSuf (allowDerived := true)
  let mut insts : List InstInfo := []
  let mut usedDerived : List Nat := []
  let mut derivedKeys : List (List Sparkle.IR.AST.Expr × Nat) := []
  let dataInsP := c.dataInputs.map (·.name)
  -- in the order of the CHECKED arrangement (the proof's case split follows `{P.body}`'s order)
  for s in b0 do
    match s with
    | .inst mn iname cs =>
      let some (ki, k) := (kids.zipIdx.find? fun (k, _) => k.c.name == mn).map (fun (k, i) => (i, k))
        | refuse decl "child" m!"instance {iname}: no module {mn}"
      let y := match cs.lookup (outNameOf k.c) with | some (.ref y) => y | _ => "?"
      let args := k.tbl.binders.map fun b =>
        match cs.lookup ("_gen_" ++ b) with
        | some (.ref x) => if x.startsWith "_gen_" then (x.drop 5).toString else "?"
        | _ => "?"
      let ck := contractOf k.tbl ["out"] (clkRstOf k.c) k.c
      if instDerived c ck cs then
        -- a derived net: the declaration's call is the next unused derived call of this child
        let key := ck.dataInputs.map fun p => match cs.lookup p.name with
          | some (.ref x) => inlineNet dataInsP b0 b0.length (.ref x)
          | _ => .ref "?"
        let some ci := (match derivedKeys.find? (fun kj => kj.1 == key && opn.calls[kj.2]!.kid == ki) with
          | some kj => some kj.2
          | none => (List.range opn.calls.size).find? (fun j =>
            opn.calls[j]!.derived && opn.calls[j]!.kid == ki && !usedDerived.contains j))
          | refuse decl "open"
              m!"instance {iname}: the declaration's body has no call of {mn} on a derived argument (the call's arguments must be closed terms over the parent inputs); calls found: {opn.calls.toList.map fun c => (c.kid, c.derived)}, matched so far: {usedDerived}, instances so far: {insts.map (·.iname)}"
        usedDerived := usedDerived ++ [ci]
        derivedKeys := derivedKeys ++ [(key, ci)]
        let chain := ((ck.dataInputs.map fun p => match cs.lookup p.name with
          | some (.ref x) => netChain dataInsP b0 b0.length x
          | _ => []).flatten).reverse.eraseDups.map fun w => (w, declWidth m w)
        insts := insts ++ [{ mn, iname, cs, kid := ki, y, call := ci, derived := true, chain }]
      else
        let some ci := opn.calls.findIdx? (fun c => c.kid == ki && c.args == args && !c.derived)
          | refuse decl "open"
              m!"instance {iname}: the declaration's body has no call of {mn} on the parent inputs {args}"
        insts := insts ++ [{ mn, iname, cs, kid := ki, y, call := ci }]
    | _ => pure ()
  return { tbl, opn, kids, insts, childMs := t1 - t0, t1 }

/-- The second phase: the deep facts of the open parent exist; build the invariant's constants,
the proof of `U2HRStmt`, and check it. -/
def phase2 (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (m : Sparkle.IR.AST.Module) (p1 : Phase1) :
    TermElabM (Name × Nat) := do
  let nm := HNames.ofBase decl
  let opn := p1.opn
  let kids := p1.kids
  let tbl := p1.tbl
  for s in deepParts do
    unless (← getEnv).contains (deepName opn.openName s) do
      refuse decl "deep" m!"{deepName opn.openName s} missing: #verify_elab_deep of the open parent did not produce it"
  let deepCi ← getConstInfo (deepName opn.openName "_deep")
  unless deepCi.type.getAppFn.constName? == some ``Cdo do
    refuse decl "deep" m!"the open parent's deep circuit is not a Cdo (memories are outside H2b)"
  let regWs ← try readWidths (deepCi.type.getAppArgs[0]!) catch e => refuse decl "deep" e.toMessageData
  let inWs ← try readWidths (deepCi.type.getAppArgs[1]!) catch e => refuse decl "deep" e.toMessageData
  let pm := (regsOf m.body).map (·.1)
  unless pm.length == regWs.length do
    refuse decl "deep"
      m!"the parent has {pm.length} registers, the open parent's circuit has {regWs.length}"
  unless inWs.length == tbl.binders.length + opn.calls.size do
    refuse decl "deep" m!"the open circuit has {inWs.length} inputs, expected {tbl.binders.length + opn.calls.size}"
  let di : DeepInfo := { regWs, nIn := inWs.length, pm }
  let kidA := kids.toArray
  let kidsU := kids.map fun k => { k with nm := namesUser k.nm }
  let _ := kidsU
  -- the auxiliary definitions the invariant uses
  let argTxt (bn : String) : String :=
    match (tbl.binders.zipIdx).find? (fun (b, _) => b == bn) with
    | some (_, j) => s!"(Tools.VedU1Contract.PTy.sig {ptyTxt (tbl.ins.getD j .bit)} ins {sq ("_gen_" ++ bn)})"
    | none => "?"
  let callTxt (c : CallInfo) : String :=
    let k := kidA[c.kid]!
    let G := declTerm k.decl k.nDom
    if c.derived then s!"({G} {" ".intercalate (c.argDefs.map fun n => s!"({userName n} ins)")})"
    else if c.args.isEmpty then G else s!"({G} {" ".intercalate (c.args.map argTxt)})"
  let sigsAll := " ".intercalate (tbl.binders.map argTxt ++ opn.calls.toList.map callTxt)
  let parseTerm (txt : String) : TermElabM Term := do
    match Lean.Parser.runParserCategory (← getEnv) `term txt "<ved_u2_hier_reg>" with
    | .ok s => pure ⟨s⟩
    | .error e => refuse decl "proof" m!"generated term does not parse: {e}"
  let OInp := deepC opn.openName "_inp"
  let ODeep := deepC opn.openName "_deep"
  let ONm := deepC opn.openName "_nm"
  let inpUn := opn.openName ++ `ved_inpU
  let irSn := opn.openName ++ `ved_irS
  try
    addTermDef inpUn (← parseTerm s!"fun (ins : Nat → String → Nat) (t : Nat) j => ({OInp} {sigsAll} j).val t")
    addTermDef irSn (← parseTerm s!"fun (ins : Nat → String → Nat) (t : Nat) => Cdo.irState {ODeep} {ONm} ({toString (userName inpUn)} ins) t")
    -- H2c: the stream a derived call's data ports read
    for (c, j) in opn.calls.toList.zipIdx do
      if c.derived then
        let k := kidA[c.kid]!
        let ports := k.tbl.binders.zip (k.tbl.ins.zip c.argDefs)
        let body := ports.foldr (fun (bn, (pt, ad)) acc =>
          s!"if n = {sq ("_gen_" ++ bn)} then Tools.VedU1Contract.PTy.obs {ptyTxt pt} (({toString (userName ad)} ins).val t) else {acc}") "0"
        addTermDef (fDefName opn j) (← parseTerm s!"fun (ins : Nat → String → Nat) (t : Nat) (n : String) => {body}")
  catch e => refuse decl "deep" m!"auxiliary definitions: {e.toMessageData}"
  let expected := mkAppN (Lean.mkConst ``U2HRStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]
  try check expected catch e => refuse decl "type" e.toMessageData
  unless ← isProp expected do refuse decl "type" m!"expected statement is not a Prop"
  let text := "by\n" ++ scriptTextR nm stmt.getAppFn.constName! stmt.getAppNumArgs tbl opn kids p1.insts di ((← IO.getEnv "VED_HIER_TRACE").isSome)
  if (← IO.getEnv "VED_HIER_DEBUG").isSome then IO.eprintln text
  let stx ← match Lean.Parser.runParserCategory (← getEnv) `term text "<ved_u2_hier_reg>" with
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
  return (nm.thm, t2 - p1.t1)

/-- The checker for a parent WITH registers.  `m` and `d` are the values `synthesizeCombinational`
returned.  On any failure the command state saved at the start (constants and messages) is
restored and a refusal thrown. -/
def checkU2HR (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (m : Sparkle.IR.AST.Module) (d : Design)
    (clkRstOverride : Option (Option (String × String)) := none) :
    CommandElabM (Name × Nat × Nat) := do
  let saved ← get
  try
    let p1 ← liftTermElabM (phase1 decl stmt nDom m d clkRstOverride)
    let msgs0 := (← get).messages
    let nErr0 := msgs0.toList.filter (·.severity == .error) |>.length
    let stx ← `(command| #verify_elab_deep $(mkIdent p1.opn.openName))
    -- the deep constants are declared in the CURRENT namespace under the ident's last component;
    -- inside the namespace `decl` they are `decl.ved_open_deep…` (`deepName` of the open parent)
    try withScope (fun sc => { sc with currNamespace := decl }) (elabCommand stx)
    catch e => liftTermElabM <| refuse decl "deep" m!"#verify_elab_deep of the open parent {p1.opn.openName}: {e.toMessageData}"
    let errs := (← get).messages.toList.filter (·.severity == .error)
    if errs.length != nErr0 then
      let first ← match errs.drop nErr0 with
        | msg :: _ => msg.data.toString
        | [] => pure ""
      liftTermElabM <| refuse decl "deep" m!"#verify_elab_deep of the open parent {p1.opn.openName} failed; first: {first}"
    if (← IO.getEnv "VED_HIER_DEBUG").isSome then
      for msg in (← get).messages.toList.drop msgs0.toList.length do
        IO.eprintln s!"[deep] {← msg.data.toString}"
    modify fun s => { s with messages := msgs0 }
    let (thm, proofMs) ← liftTermElabM (phase2 decl stmt nDom m p1)
    return (thm, p1.childMs, proofMs)
  catch e =>
    set saved
    if ← liftTermElabM (isRefusal e) then throw e
    liftTermElabM <| refuse decl "checker" e.toMessageData

/-- The entry: ONE `synthesizeCombinational`; a register-free parent is H2a's `checkU2H`
(statement `U2HStmt`), a parent with registers is `checkU2HR` (statement `U2HRStmt`). -/
def vedU2HierEntryR (declName : Name) :
    CommandElabM (Sparkle.IR.AST.Module × Design × Name × Nat × Stats) := do
  let (stmt, nDom) ← liftTermElabM <| try specialiseDomain declName catch e => refuse declName "table" e.toMessageData
  let tbl ← liftTermElabM <| try readTableOfType declName (← inferType stmt) catch e => refuse declName "table" e.toMessageData
  unless tbl.out.flat.length == 1 do
    liftTermElabM <| refuse declName "multi-output"
      m!"{tbl.out.flat.length} output projections (multi-output: H3), refused (H2b: one output)"
  let t0 ← IO.monoMsNow
  let (m, d) ← liftTermElabM <| try Sparkle.Compiler.Elab.synthesizeCombinational declName
    catch e => refuse declName "synthesis" e.toMessageData
  let t1 ← IO.monoMsNow
  if (regsOf m.body).isEmpty then
    let (thm, childMs, proofMs) ← liftTermElabM (checkU2H declName stmt nDom m d)
    return (m, d, thm, nDom, { synthMs := t1 - t0, childMs, proofMs, peakKb := ← peakKb })
  else
    let (thm, childMs, proofMs) ← checkU2HR declName stmt nDom m d
    return (m, d, thm, nDom, { synthMs := t1 - t0, childMs, proofMs, peakKb := ← peakKb })

/-- `#ved_u2_hier decl`: the stateful hierarchical entry (H2a and H2b); prints the theorem, its audit,
the design and the measurements; otherwise the refusal. -/
elab "#ved_u2_hier " id:ident : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  let (m, d, thm, nDom, st) ← vedU2HierEntryR decl
  Command.liftTermElabM do
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U2 HIER OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}\nchildren: {d.modules.map (·.name)}\nsynthesis {st.synthMs} ms, children {st.childMs} ms, parent proof {st.proofMs} ms, peak {st.peakKb} kB\n{repr m}"

end Tools.VedU2HierRegEntry
