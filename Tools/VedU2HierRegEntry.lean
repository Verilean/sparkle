import Tools.VedU2HierDbg
import Tools.VedU2HierClose
import Tools.VedU2HierEntry
import Tools.VedU2HierReg
import Tools.VedU2HierNet
import Tools.VedU2HierStGen
import Tools.VedU2HierStep
import Tools.DeepElab
import Tools.DeepHelpers
import Tools.DeepHelpersTac
import Tools.VedU2HierStateArgs
import Tools.VedU2HierBvAppend
import Tools.VedU2HierBudget
import Tools.VedU2HierLoopRw

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

H2c-state (a child call whose argument is the parent's register state; docs/VED-HIER-H2C-STATE.md), the LIMITED
method: the open parent is a PROOF AID only (it supplies the registers' state; no equation between it and the
declaration is claimed).  The declaration is joined to its call by the kernel equation `decl xs = g a` (`_ceq`)
and the call's argument to the registers by the argument-state equation, also in the kernel, from the exported
state theorem of the open parent's deep run.  The statement `U2HRStmt` is unchanged.  A failure of the deep run
is tolerated ONLY for ports the proof does not use, and then recorded (`VED U2 HIER PARTIAL-DEEP`); every
other deep failure is refused at `[deep]`.
-/

namespace Tools.VedU2HierRegEntry

open Lean Meta Elab Term Command
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU2HierStateArgs
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

/-- Does the net of `x` read a leaf of `leaves` (parent register outputs), through assigned wires? -/
def netReadsB (leaves : List String) (b : List Stmt) : Nat → String → Bool
  | 0, _ => false
  | fuel + 1, x =>
    leaves.contains x ||
      match asgOf b x with
      | some r => (refsOf r).any (netReadsB leaves b fuel)
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
    (cs : List (String × Sparkle.IR.AST.Expr)) (allowRegs : Bool := false) : Option String :=
  -- H2c-state: for a COMBINATIONAL child the parent's register outputs are leaves of the net too
  let dataIns := c.dataInputs.map (·.name) ++ (if allowRegs then regOuts b else [])
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

/-- The register slots a state theorem's pack holds: the reader constants `<..>_deep_rd<n>` in the order they
occur in the right side of its equation (`(rd_b .., (rd_b' .., ()))`, a Bool register's reader under `== 1#1`). -/
def stateBlockOf (thm : Name) : MetaM (List Nat) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun _ body => do
    let some (_, _, rhs) := body.eq? | return []
    let rec go (e : Lean.Expr) (fuel : Nat) (acc : List Nat) : List Nat :=
      match fuel with
      | 0 => acc
      | f + 1 =>
        if e.isAppOfArity ``Prod.mk 4 then
          let a := e.getArg! 2
          let idx := (a.foldConsts ([] : List Name) (fun c l => c :: l)).findSome? fun c =>
            match c.getString!.splitOn "_deep_rd" with
            | [_, n] => n.toNat?
            | _ => none
          go (e.getArg! 3) f (match idx with | some n => acc ++ [n] | none => acc)
        else acc
    return go rhs 64 []

/-- The register a duplicate-copy equation `<..>_deep_dup_r<n> : rd<n> .. = rd<m> ..` identifies `rd<n>` with: `m`. -/
def dupTargetOf (thm : Name) : MetaM (Option Nat) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun _ body => do
    let some (_, _, rhs) := body.eq? | return none
    return (rhs.getAppFn.constName?.bind fun c => match c.getString!.splitOn "_deep_rd" with
      | [_, n] => n.toNat?
      | _ => none)

/-- The name of the stream definition `ved_F<j>` of derived call `j`. -/
def fDefName (opn : OpenInfo) (j : Nat) : Name :=
  Name.mkStr opn.openName.getPrefix (opn.openName.getString! ++ s!"_F{j}")

/-- The range-free forms of the operators (`Tools.VedU1Lemmas`): they apply to what the range-guarded forms of
`netSimpL` left as `evalOp`. -/
def rawOpL : String :=
  "Tools.VedU1Lemmas.evalOp_not_raw, Tools.VedU1Lemmas.evalOp_and_raw, Tools.VedU1Lemmas.evalOp_or_raw, Tools.VedU1Lemmas.evalOp_xor_raw, Tools.VedU1Lemmas.evalOp_sub_raw"

/-- The simp set that evaluates a net's IR expression and the Signal term of the declaration's
argument. -/
def netSimpL : String :=
  "Sparkle.IR.Semantics.widthOf, Sparkle.IR.Semantics.widthOf.go, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalExpr.go, Tools.VedU1Entry.or_mod _ _ _ _ rfl, Nat.shiftRight_eq_div_pow, -Nat.shiftLeft_zero, Tools.VedU2Hier.shl_zero, Tools.VedU2Hier.or_shl_add_of_lt, Tools.VedU1Lemmas.evalOp_not_lit, Tools.VedU1Lemmas.compl_val, Tools.VedU1Lemmas.evalOp_and_lit, Tools.VedU1Lemmas.evalOp_or_lit, Tools.VedU1Lemmas.evalOp_xor_lit, Tools.VedU1Lemmas.and_val, Tools.VedU1Lemmas.or_val, Tools.VedU1Lemmas.xor_val, Tools.VedU1Lemmas.evalOp_add_lit, Tools.VedU1Lemmas.add_val, BitVec.toNat_add, Tools.VedU1Lemmas.evalOp_sub_lit, Tools.VedU1Lemmas.sub_val, BitVec.toNat_sub, Tools.VedU1Lemmas.evalOp_mux_lit, Tools.VedU1Lemmas.mux_val, Seq.seq, Sparkle.Core.Signal.Signal.seq, Sparkle.Core.Signal.Signal.ap, BitVec.toNat_append, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, Nat.mod_eq_of_lt, Functor.map, Sparkle.Core.Signal.Signal.map, BitVec.toNat_not, BitVec.toNat_ofNat, Tools.VedU1Contract.PTy.obs, Tools.VedU1Contract.PTy.sig, Sparkle.IR.Semantics.mask, Sparkle.Core.Signal.Signal.pure"

def deepC (open_ : Name) (s : String) : String := toString (userName (deepName open_ s))

/-- The constant `#verify_elab_deep open_` declares for the fact `s`, spelled exactly as it is in the
environment: the namespace the command ran in is kept as it is (for a PRIVATE declaration it is the
mangled `_private…` name, which `deepName` strips). -/
def deepNameP (open_ : Name) (s : String) : Name :=
  match open_ with
  | .str p l => .str p (l ++ s)
  | n => n.appendAfter s

/-- Are the bits `lo ..= hi` of `e` exactly one register's output?  Through renaming assignments, slices
(composed) and concatenations (the synthesiser bundles the registers of one `circuit do` and slices the
bundle).  Returns the register's slot. -/
partial def stateBitsOf (b : List Stmt) (regs : List String) (wd : String → Nat) (fuel : Nat)
    (e : Sparkle.IR.AST.Expr) (hi lo : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | f + 1 =>
    match e with
    | .ref r =>
      match regs.idxOf? r with
      | some i => if lo == 0 && hi + 1 == wd r then some i else none
      | none => match asgOf b r with
        | some e' => stateBitsOf b regs wd f e' hi lo
        | none => none
    | .slice inner h l => stateBitsOf b regs wd f inner (l + hi) (l + lo)
    | .concat es =>
      -- msb first: element widths, offsets from the right
      let ws : List (Option Nat) := es.map fun el => match el with
        | .ref x => some (wd x)
        | .slice _ h l => some (h - l + 1)
        | .const _ w => some w
        | _ => none
      if ws.any (·.isNone) then none
      else
        let wsN := ws.map (·.getD 0)
        let offs := (List.range es.length).map fun k => ((wsN.drop (k + 1)).foldl (· + ·) 0)
        match (List.range es.length).find? fun k => offs[k]! ≤ lo && hi < offs[k]! + wsN[k]! with
        | some k => stateBitsOf b regs wd f es[k]! (hi - offs[k]!) (lo - offs[k]!)
        | none => none
    | _ => none

/-- The register slot a wire is (all its bits), see `stateBitsOf`. -/
def stateSlotOf (b : List Stmt) (regs : List String) (wd : String → Nat) (fuel : Nat) (w : String) : Option Nat :=
  stateBitsOf b regs wd fuel (.ref w) (wd w - 1) 0

def scriptTextR (nm : HNames) (F : Name) (nDom : Nat) (tbl : DeclTable) (opn : OpenInfo)
    (kids : List Kid) (insts : List InstInfo) (di : DeepInfo) (dbg : Bool := false) : String := Id.run do
  let P := nm.user
  let kids := kids.map fun k => { k with nm := namesUser k.nm }
  let kidA := kids.toArray
  let O := userName opn.openName
  let OE := userName opn.eqName
  let CEq : String := match opn.callEqName with | some n => toString (userName n) | none => ""
  let FT := declTerm F nDom
  let T2 := "Tools.VedU2Hier"
  let ptag := match opn.port with | some p => s!"_{p}" | none => ""
  let ODeep := deepC opn.openName (ptag ++ "_deep")
  let ONm := deepC opn.openName "_nm"
  let OInp := deepC opn.openName "_inp"
  let OState := deepC opn.openName (ptag ++ "_deep_state")
  let OTrace := deepC opn.openName (ptag ++ "_deep_trace")
  let ONext := deepC opn.openName (ptag ++ "_deep_next")
  let OInits := deepC opn.openName (ptag ++ "_deep_inits")
  let OOut := deepC opn.openName (ptag ++ "_deep_out")
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
  let sigsAll := " ".intercalate (tbl.binders.map argTxt ++ calls.toList.map callTxt)
  let spn : Sp :=
  { state := OState, deep := ODeep, nm := ONm, irS := irS, inpU := inpU, sigsAll := sigsAll
    rd := (fun slot => deepC opn.openName (ptag ++ s!"_deep_rd{slot}")) }
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
  let st := insts.any (·.stateArg)
  if st then
    -- H2c-state: the instance fact is asked at cycle t under the invariant (goals: h0, hkid, hstep)
    L := L.push s!"  refine {T2}.outputsOnHS_of_stepRK {P.contract} {P.mod} {P.design} arr {FT} hS hadm hsupp hsch {P.body} (hadm.1.trans hb0.1.symm) hb0.2.1 hb0.2.2.2.1 hb0.2.2.1 (fun ins y t => {owBody}) {rTerm} ?_ ?_ ?_"
  else
    L := L.push s!"  refine {T2}.outputsOnHS_of_stepR {P.contract} {P.mod} {P.design} arr {FT} hS hadm hsupp hsch {P.body} (hadm.1.trans hb0.1.symm) hb0.2.1 hb0.2.2.2.1 hb0.2.2.1 (fun ins y t => {owBody}) ?_ {rTerm} ?_ ?_"
  let hkStart := L.size
  -- hkid (as in H2a)
  if st then
    L := L.push s!"  · intro ins hok K envs sts hrun t ht S E hS' hE hR mn i cs hin y hy"
  else
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
      if ii.stateArg then
        X := X.push s!"have hrunF : ∀ p ∈ {K.contract}.dataInputs, ∃ x, ({connsLit ii.cs}).lookup p.name = some (Sparkle.IR.AST.Expr.ref x) ∧ E x = {Fj} ins t p.name := by"
        X := X.push s!"  intro p hp"
      else
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
      let mut stFacts : List String := []
      let mut loopFs : List String := []
      if ii.stateArg then
        -- the parent's registers at cycle t: the pre-update state, which the invariant speaks about
        X := X.push s!"  have hregE := {T2}.closed_run_reg {P.design} arr {P.mod} hadm {P.body} (hadm.1.trans hb0.1.symm) hb0.2.1 hb0.2.2.2.2.2.2 hb0.2.2.2.2.2.1 ins K envs sts hrun t ht S E hS' hE"
        for i in [0:di.regWs.length] do
          let proj := (List.range i).foldl (fun s _ => s ++ ".2") "hR" ++ (if i + 1 < di.regWs.length then ".1" else "")
          X := X.push s!"  have hEr{i} : E {sq di.pm[i]!} = {irS} ins t ({i} : Fin {di.regWs.length}) := by"
          X := X.push s!"    rw [hregE _ (by decide)]"
          X := X.push s!"    exact {proj}"
          X := X.push s!"  have hlS{i} : {irS} ins t ({i} : Fin {di.regWs.length}) < {2 ^ di.regWs[i]!} := by"
          X := X.push s!"    have := hltS ins t ⟨{i}, by decide⟩"
          X := X.push s!"    simpa using this"
          facts := facts ++ [s!"hEr{i}", s!"hlS{i}"]
        -- H2d (`Tools/VedU2HierStateArgs.lean`): an argument that is a derived net over the register state reads
        -- the loop inside a term; the state theorems rewrite it to its pack
        let derivedArgs := ports.any fun (bn, _) =>
          (ii.slots.lookup (match ii.cs.lookup ("_gen_" ++ bn) with | some (.ref x) => x | _ => "?")).isNone
        if derivedArgs then
          let (ls, fs, lfs) := stateFacts spn di
          X := X ++ ls
          stFacts := fs
          loopFs := lfs
        -- the argument signal is the register's Signal-level state (the exported state theorem)
        for (bn, (_, ad)) in ports do
          let nm := "_gen_" ++ bn
          let wire := match ii.cs.lookup nm with | some (.ref x) => x | _ => "?"
          -- an argument that is not one of the parent's register slots (a data input, or a derived
          -- net) has no state fact; defaulting it to slot 0 gave a type mismatch (H2d)
          let some slot := ii.slots.lookup wire | continue
          X := X ++ slotLines spn di bn (toString (userName ad)) slot
          facts := facts ++ [s!"hAl{bn}"]
      let mut lts : List String := []
      for ((w, wd), wi) in ii.chain.zipIdx do
        X := X.push s!"  have e_{wi} := hasgF {sq w} _ rfl"
        X := X.push s!"  simp (config := \{ maxSteps := 2000000 }) [{netSimpL}, Tools.VedU1Contract.declWidth, {P.mod}, hin, {", ".intercalate (facts ++ lts)}] at e_{wi}"
        -- an operator whose operand has no range fact (`~~~` of a computed value: the checksum's complement) stays
        -- `evalOp`: the range-free forms evaluate it
        X := X.push s!"  try simp (config := \{ maxSteps := 2000000 }) [{rawOpL}, {netSimpL}, Tools.VedU1Contract.declWidth, {P.mod}, hin, {", ".intercalate (facts ++ lts)}] at e_{wi}"
        X := X.push s!"  have f_{wi} := e_{wi}.symm"
        X := X.push s!"  have hlt_{wi} : E {sq w} < {2 ^ wd} := by first | omega | (rw [f_{wi}]; show _ < 2 ^ {wd}; exact Nat.and_lt_two_pow _ (by omega)) | (rw [f_{wi}]; show _ < 2 ^ {wd}; exact Nat.or_lt_two_pow (by omega) (by omega)) | (rw [f_{wi}]; show _ < 2 ^ {wd}; exact Nat.xor_lt_two_pow (by omega) (by omega)) | (rw [f_{wi}]; show _ < 2 ^ {wd}; (repeat' split) <;> (first | omega | exact Nat.and_lt_two_pow _ (by omega) | exact Nat.or_lt_two_pow (by omega) (by omega) | exact Nat.xor_lt_two_pow (by omega) (by omega)))"
        facts := facts ++ [s!"f_{wi}"]
        lts := lts ++ [s!"hlt_{wi}"]
      X := X.push s!"  rw [hdl] at hp"
      X := X.push s!"  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp"
      X := X.push s!"  rcases hp with {pat}"
      for (bn, (_, ad)) in ports do
        let nm := "_gen_" ++ bn
        let wire := match ii.cs.lookup nm with | some (.ref x) => x | _ => "?"
        X := X.push s!"  · refine ⟨{sq wire}, by decide, ?_⟩"
        if dbg then X := X.push s!"    trace \"H2D-PORT {bn} begin\""
        if ii.stateArg then
          -- a non-register argument (a constant, a data input, a derived net) is unfolded like the stateless case
          let isSlot := (ii.slots.lookup wire).isSome
          X := X ++ portLines di dbg bn isSlot (toString (userName ad)) Fj netSimpL (facts ++ lts)
            (if isSlot then [] else stFacts) (if isSlot then [] else loopFs)
        else
          X := X.push s!"    simp [{Fj}, {toString (userName ad)}, {netSimpL}, hin, {", ".intercalate (facts ++ lts)}]"
        -- H2e: the pack is read back and a complement `x ^^^ 65535` rewritten, with the context cleared of what
        -- `omega` cannot read, before `omega` (`omega` on the unread goal in the full context, and `split <;> omega`,
        -- do not terminate on a checksum)
        if ii.stateArg && dbg then X := X.push s!"    all_goals (ved_eprint_state \"P1-before-close {bn}\")"
        if ii.stateArg && dbg then X := X.push s!"    all_goals (try (ved_port_ctx; ved_eprint_state \"P2-cleared {bn}\"))"
        if ii.stateArg then X := X.push s!"    all_goals (try (ved_port_ctx; ved_hier_close))"
        if ii.stateArg && dbg then X := X.push s!"    all_goals (ved_eprint_state \"P3-after-close {bn}\")"
        X := X.push s!"    try omega"
        if ii.stateArg then X := X.push s!"    all_goals (try (split <;> omega))"
      if ii.stateArg then
        X := X.push s!"obtain ⟨x, hx, hv⟩ := {T2}.kid_step {P.design} arr {P.mod} hS hadm hwr {P.contract} htie ins hok K envs sts hrun {sq ii.mn} {sq ii.iname} {connsLit ii.cs} hin0 {K.mod} (by decide) (by decide) {K.contract} {G} {K.thm} (by decide) ({T2}.connsNet_sound (m := {P.mod}) (c := {K.mod}) (ck := {K.contract}) (cs := {connsLit ii.cs}) (by decide)).1 ({T2}.connsNet_sound (m := {P.mod}) (c := {K.mod}) (ck := {K.contract}) (cs := {connsLit ii.cs}) (by decide)).2 ({Fj} ins) hrange t ht E hE hrunF _ hq"
      else
        X := X.push s!"obtain ⟨x, hx, hv⟩ := {T2}.kid_inst_net {P.design} arr {P.mod} hS hadm hwr {P.contract} htie ins hok K envs sts hrun {sq ii.mn} {sq ii.iname} {connsLit ii.cs} hin0 {K.mod} (by decide) {K.contract} {G} {K.thm} (by decide) ({T2}.connsNet_sound (m := {P.mod}) (c := {K.mod}) (ck := {K.contract}) (cs := {connsLit ii.cs}) (by decide)).1 ({T2}.connsNet_sound (m := {P.mod}) (c := {K.mod}) (ck := {K.contract}) (cs := {connsLit ii.cs}) (by decide)).2 ({Fj} ins) hrange hrunF t ht E hE _ hq"
      -- the signals the child's theorem is applied to are the declaration's arguments
      X := X.push s!"generalize hNS : {T2}.netIn {K.contract} ({connsLit ii.cs}) ins ({Fj} ins) = NS at hv"
      let mut sigFacts : List String := []
      for ((bn, (pt, ad)), kk) in ports.zipIdx do
        let nm := "_gen_" ++ bn
        let lem := match pt with | .bv w => s!"{T2}.sig_of_obs_bv {w}" | .bit => s!"{T2}.sig_of_obs_bit"
        X := X.push s!"have hsig{kk} := {lem} (({toString (userName ad)}) ins) NS {sq nm} (fun t => by rw [← hNS]; simp (config := \{ maxSteps := 2000000 }) [{T2}.netIn, {K.contract}, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.Contract.dataInputs, {Fj}, Tools.VedU1Contract.PTy.obs])"
        sigFacts := sigFacts ++ [s!"hsig{kk}"]
      X := X.push s!"have hx' : x = {sq ii.y} := by\n  have h2 : ({connsLit ii.cs}).lookup {sq outName} = some (Sparkle.IR.AST.Expr.ref {sq ii.y}) := by decide\n  rw [h2] at hx\n  simpa using hx.symm"
      X := X.push s!"subst hx'"
      X := X.push s!"rw [hv]"
      X := X.push s!"simp (config := \{ maxSteps := 2000000 }) [Tools.VedU1Contract.srcOf, Tools.VedU1Contract.applyIns, {K.contract}, Tools.VedU1Contract.contractOf, List.lookup, Tools.VedU1Contract.OTy.obs, Tools.VedU1Contract.PTy.obs, {", ".intercalate sigFacts}]"
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
  let hkEnd := L.size
  L := L.push s!"  · intro ins hok"
  L := L.push s!"    simp [{T2}.st0Of, {T2}.initsOf, Tools.VedU1Contract.regsOf, {P.mod}, Sparkle.IR.Semantics.encodeInit, Sparkle.IR.Semantics.mask, Tools.VedU1Contract.declWidth, {irS}, Cdo.irState, {OInits}, {ONm}, List.lookup, -Fin.isValue]"
  if st then
    -- the goals of `outputsOnHS_of_stepRK` are h0, hkid, hstep: move h0 in front of hkid
    let h0Block := L.extract hkEnd L.size
    L := L.extract 0 hkStart ++ h0Block ++ L.extract hkStart hkEnd
  -- hstep
  L := L.push s!"  · intro ins hok t p hR"
  L := L.push s!"    have hin := hok.1 t"
  L := L.push s!"    have hrst := hok.2 t"
  L := L.push s!"    have hinpU : ∀ (ins : Nat → String → Nat) (t : Nat) j, {inpU} ins t j = ({OInp} {sigsAll} j).val t := fun _ _ _ => rfl"
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
  -- the next-value goals do not read the child's output: its range fact is dropped there (it would be unfolded, with the
  -- derived arguments, into the loop terms of the call's inputs)
  let locsN := " ".intercalate (((List.range k).map fun i => s!"hR{i}") ++ ((List.range k).map fun i => s!"hl{i}"))
  let hModsN := ", ".intercalate ((List.range k).map fun i => s!"Nat.mod_eq_of_lt hl{i}")
  let inpL := ", ".intercalate ((List.range di.nIn).flatMap fun j =>
    [s!"{OInp}_at_{j}", s!"{OInp}_at_mk_{j}"]) ++ ", Tools.VedU1Contract.PTy.sig"
  let argDefsL := ", ".intercalate (calls.toList.flatMap fun c => c.argDefs.map fun n => toString (userName n))
  let evalL := s!"{if argDefsL.isEmpty then "" else argDefsL ++ ", "}Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalExpr.go, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalOp, envOfC, weOfC, chainMap, List.finRange, {ONm}, Tools.VedU1Deep.reduceFinVal, natJoin, Sparkle.IR.Semantics.widthOf, Sparkle.IR.Semantics.widthOf.go, Sparkle.IR.Semantics.mask, Nat.shiftRight_eq_div_pow, Tools.VedU1Entry.or_mod _ _ _ _ rfl, {inpL}"
  L := L.push s!"    simp (config := \{ maxSteps := 4000000 }) [hout, {P.outs}, Tools.VedU1Hier.evalAssignsI, Tools.VedU1Hier.cellVals, {T2}.oracleIE, {hOl}, {P.body}, Sparkle.IR.Semantics.regNexts, {T2}.regOuts, Tools.VedU1Contract.regsOf, {T2}.restrictTo, Tools.VedU1Contract.seedIn, {P.mod}, Tools.VedU1Contract.declWidth, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalExpr.go, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalOp, Sparkle.IR.Semantics.widthOf, Sparkle.IR.Semantics.widthOf.go, Tools.VedU1Hier.upd, Sparkle.IR.Semantics.mask, Sparkle.IR.Semantics.applyNexts, Tools.VedU1Entry.or_mod _ _ _ _ rfl, Nat.shiftRight_eq_div_pow, hrst]"
  L := L.push s!"    constructor"
  -- the output
  L := L.push s!"    · try rw [if_pos rfl]"
  if st then
    -- H2c-state: the declaration IS the call on its closed argument; the output is the oracle value
    -- (`{CEq}` is the kernel equation `decl xs = g a`; the conversion itself is left to the kernel)
    L := L.push s!"      all_goals simp [Tools.VedU1Contract.srcOf, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.applyIns, {P.contract}, Tools.VedU1Contract.OTy.obs, Tools.VedU1Contract.PTy.obs, Tools.VedU1Contract.PTy.sig]"
    if dbg then L := L.push s!"      all_goals ved_eprint_state"
    L := L.push s!"      all_goals ved_kernel_rfl"
  else
    L := L.push s!"      all_goals simp [Tools.VedU1Contract.srcOf, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.applyIns, {P.contract}, Tools.VedU1Contract.OTy.obs, Tools.VedU1Contract.PTy.obs, {OE}, Tools.VedU1Contract.PTy.sig]"
    L := L.push s!"      all_goals rw [{OTrace}]"
    L := L.push s!"      all_goals unfold {irS} {inpU} at {locsU}"
    L := L.push s!"      all_goals simp only [CExpr.compile, {OOut}]"
    L := L.push s!"      all_goals simp (config := \{ maxSteps := 4000000 }) [{evalL}] at {locs} ⊢"
    L := L.push s!"      all_goals ved_fin_norm"
    L := L.push s!"      all_goals try simp (config := \{ maxSteps := 4000000 }) [{evalL}] at ⊢"
    L := L.push s!"      all_goals try simp only [{hRs}]"
    L := L.push s!"      all_goals try simp only [{hMods}]"
    if dbg then L := L.push s!"      all_goals ved_eprint_state"
    L := L.push s!"      all_goals ved_hier_close"
  -- the next values
  let holes := ", ".intercalate ((List.range k).map fun _ => "?_")
  L := L.push s!"    · {if k == 1 then "skip" else s!"refine ⟨{holes}⟩"}"
  -- `hR` (the conjunction) repeats the `hR{i}` with `Fin.mk` indices; `omega` would compare its register atoms with the
  -- literal-index ones of the goal by unfolding the IR state recurrence (a recursion-depth error in the closer)
  L := L.push s!"      all_goals (try clear hR)"
  for j in [0:calls.size] do
    L := L.push s!"      all_goals (try clear hlo{j})"
  L := L.push s!"      all_goals try simp only [List.find?, {ONm}]"
  if dbg then L := L.push s!"      all_goals ved_eprint_state"
  L := L.push s!"      all_goals unfold {irS} at *"
  L := L.push s!"      all_goals simp (config := \{ maxSteps := 4000000 }) only [Cdo.irState, {ONext}, CExpr.compile]"
  if dbg then L := L.push s!"      all_goals ved_eprint_state"
  -- only the APPLIED `inpU ins t j` is unfolded: the register atoms `deep.irState nm (inpU ins) t i` keep their
  -- small shape (unfolding the environment inside them copied the child's argument terms into every atom)
  L := L.push s!"      all_goals simp (config := \{ maxSteps := 4000000 }) only [hinpU] at *"
  if dbg then L := L.push s!"      all_goals ved_eprint_state"
  L := L.push s!"      all_goals simp (config := \{ maxSteps := 4000000 }) [{evalL}, Signal.map, cond_eq_ite, bne_iff_ne, ne_eq, Tools.VedU1Contract.PTy.obs] at {locsN} ⊢"
  if dbg then L := L.push s!"      all_goals ved_eprint_state"
  L := L.push s!"      all_goals ved_fin_norm"
  L := L.push s!"      all_goals try simp (config := \{ maxSteps := 4000000 }) [{evalL}, Signal.map, cond_eq_ite, bne_iff_ne, ne_eq, Tools.VedU1Contract.PTy.obs] at ⊢"
  L := L.push s!"      all_goals (try simp only [{hRs}])"
  L := L.push s!"      all_goals (try simp only [{hModsN}])"
  if dbg then L := L.push s!"      all_goals ved_eprint_state"
  L := L.push s!"      all_goals ved_hier_close"
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
        -- H2c: a data port may read a net computed from the parent data inputs only; H2c-state: for a
        -- COMBINATIONAL child (no registers) also from the parent's register outputs
        if let some msg := connDiagNet d c m b0 ck cm iname cs (allowRegs := (regsOf cm.body).isEmpty) then
          refuse decl "conns" m!"{msg}"
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
  -- H2c-state: an instance of a combinational child whose data port reads parent register outputs
  let regLeaves := regOuts b0
  let stateInsts : List String := b0.filterMap fun s => match s with
    | .inst mn iname cs =>
      match kids.find? (fun k => k.c.name == mn) with
      | some k =>
        let ck := contractOf k.tbl ["out"] (clkRstOf k.c) k.c
        if (regsOf k.c.body).isEmpty && ck.dataInputs.any (fun p => match cs.lookup p.name with
            | some (.ref x) => netReadsB regLeaves b0 b0.length x
            | _ => false) then some iname else none
      | none => none
    | _ => none
  let useState := !stateInsts.isEmpty
  let opn ← if useState then do
      unless kids.length == 1 && (b0.filter fun s => match s with | .inst .. => true | _ => false).length == 1 do
        refuse decl "open" m!"H2c-state covers one child instance (the instances reading register outputs: {stateInsts}; instances in total: {(b0.filter fun s => match s with | .inst .. => true | _ => false).length})"
      Tools.VedU2HierStGen.genOpenSt decl stmt nDom tbl kids[0]! nm.mod.getPrefix openSuf
    else genOpen decl stmt nDom tbl kids nm.mod.getPrefix openSuf (allowDerived := true)
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
      if useState then
        let chain := ((ck.dataInputs.map fun p => match cs.lookup p.name with
          | some (.ref x) => netChain (dataInsP ++ regLeaves) b0 b0.length x
          | _ => []).flatten).reverse.eraseDups.map fun w => (w, declWidth m w)
        let slots := (ck.dataInputs.filterMap fun p => match cs.lookup p.name with
          | some (.ref x) => (stateSlotOf b0 ((regsOf m.body).map (·.1)) (declWidth m) 32 x).map fun i => (x, i)
          | _ => none)
        insts := insts ++ [{ mn, iname, cs, kid := ki, y, call := 0, derived := true, chain, stateArg := true, slots }]
      else if instDerived c ck cs then
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
  -- H2c-state: the deep facts come from the first port of the open parent that exported its loop state
  let opn ← if p1.insts.any (·.stateArg) then do
      let env ← getEnv
      if opn.ports.isEmpty then pure opn else
      match opn.ports.find? (fun p => env.contains (deepNameP opn.openName s!"_{p}_deep_state")) with
      | some p => pure { opn with port := some p }
      | none => refuse decl "deep" m!"no port of the open parent exported its loop state (ports: {opn.ports})"
    else pure opn
  let ptag := match opn.port with | some p => s!"_{p}" | none => ""
  for s in deepParts ++ (if p1.insts.any (·.stateArg) then ["_deep_state"] else []) do
    -- `_nm` and `_inp` are shared by all ports of the open parent
    let tg := if s == "_nm" || s == "_inp" then "" else ptag
    unless (← getEnv).contains (deepNameP opn.openName (tg ++ s)) do
      refuse decl "deep" m!"{deepNameP opn.openName (tg ++ s)} missing: #verify_elab_deep of the open parent did not produce it"
  let deepCi ← getConstInfo (deepNameP opn.openName (ptag ++ "_deep"))
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
  let block ← if p1.insts.any (·.stateArg) then
      stateBlockOf (deepNameP opn.openName (ptag ++ "_deep_state"))
    else pure []
  let mut nested : List (String × List Nat) := []
  if p1.insts.any (·.stateArg) then
    for j in List.range 16 do
      let n := deepNameP opn.openName (ptag ++ s!"_deep_state_n{j}")
      if (← getEnv).contains n then
        nested := nested ++ [(deepC opn.openName (ptag ++ s!"_deep_state_n{j}"), ← stateBlockOf n)]
  let mut dups : List (Nat × Nat × String) := []
  if p1.insts.any (·.stateArg) then
    for slot in List.range regWs.length do
      let n := deepNameP opn.openName (ptag ++ s!"_deep_dup_r{slot}")
      if (← getEnv).contains n then
        if let some c ← dupTargetOf n then
          dups := dups ++ [(slot, c, deepC opn.openName (ptag ++ s!"_deep_dup_r{slot}"))]
  let di : DeepInfo := { regWs, nIn := inWs.length, pm, block, nested, dups, openUser := toString (userName opn.openName) }
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
  let ODeep := deepC opn.openName (ptag ++ "_deep")
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
          `linter.unusedTactic false).setBool `linter.unreachableTactic false) <| withoutErrToSorry <| withEnableInfoTree false do
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
  -- the elaborator's metavariable context (every goal with its local context) and caches are dead from here on: free
  -- them before the kernel checks the term (the kernel's caches are the peak of the run)
  modifyThe Lean.Meta.State fun st => { st with mctx := {} }
  modifyThe Lean.Meta.State fun st => { st with cache := {} }
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

/-- H2c-state: what the messages of the open parent's `#verify_elab_deep` say about its ports.
`msgs` are the NEW messages in order `(isError, text)`.  A port's block logs its errors and, when it completes,
the line `…<open>.<port>: PROVEN via …`; so the errors logged since the previous `PROVEN` line belong to the
port whose `PROVEN` line follows, and the errors left at the end belong to the first port that has no `PROVEN`
line (a failing block that THROWS is reported `…<port>: FAILED` after its errors and the later ports are still attempted).  Returns the errors that belong to
no port, and per port the errors tied to it (first text kept, in port order). -/
def attributeDeepErrors (ports : List String) (msgs : List (Bool × String)) :
    List String × List (String × List String) := Id.run do
  let mut pending : List String := []
  let mut tied : List (String × List String) := []
  let mut proven : List String := []
  for (isErr, txt) in msgs do
    if isErr then pending := pending ++ [txt]
    else match ports.find? (fun p => (txt.splitOn s!".{p}: PROVEN via").length > 1) with
      | some p =>
        proven := proven ++ [p]
        if !pending.isEmpty then tied := tied ++ [(p, pending)]
        pending := []
      | none =>
        -- H2d: a port whose block threw says so after its errors; they are its own
        match ports.find? (fun p => (txt.splitOn s!".{p}: FAILED").length > 1) with
        | some p =>
          if !pending.isEmpty then tied := tied ++ [(p, pending)]
          pending := []
        | none => pure ()
  let mut stray : List String := []
  if !pending.isEmpty then
    match ports.find? (fun p => !proven.contains p) with
    | some p => tied := tied ++ [(p, pending)]
    | none => stray := pending
  let byPort := ports.filterMap fun p =>
    let es := (tied.filter (·.1 == p)).flatMap (·.2)
    if es.isEmpty then none else some (p, es)
  return (stray, byPort)

/-- The verdict on the errors of the open parent's deep run: `none` (no error), `some (usedPort, failed)` when
every error is tied to a port the proof does not use (`failed`: port, number of errors, first error), or the
refusal text (first error) otherwise: an error of the used port, an error tied to no port, a parent with no
port, or a loop state that no port exported. -/
def deepVerdict (stateCalls : Bool) (ports : List String) (hasState : String → Bool)
    (msgs : List (Bool × String)) :
    Except String (Option (String × List (String × Nat × String))) :=
  let errs := msgs.filter (·.1) |>.map (·.2)
  match errs with
  | [] => .ok none
  | first :: _ =>
    let refuseWith := fun (why : String) => Except.error s!"{why}; first: {first}"
    if !stateCalls then refuseWith "the parent has no call on its register state"
    else if ports.isEmpty then refuseWith "the open parent has no port to tie the errors to"
    else
      match ports.find? hasState with
      | none => refuseWith "no port of the open parent exported its loop state"
      | some used =>
        let (stray, tied) := attributeDeepErrors ports msgs
        if !stray.isEmpty then refuseWith "an error is tied to no port"
        else if tied.any (·.1 == used) then refuseWith s!"an error of the port {used}, which the proof uses"
        else .ok (some (used, tied.map fun (p, es) => (p, es.length, es.head!)))

/-- The checker for a parent WITH registers.  `m` and `d` are the values `synthesizeCombinational`
returned.  On any failure the command state saved at the start (constants and messages) is
restored and a refusal thrown.  `tamper` (tests only) may change the `Phase1` or the messages right after the
deep run; it is `pure` in the entry. -/
def checkU2HRCore (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (m : Sparkle.IR.AST.Module) (d : Design)
    (clkRstOverride : Option (Option (String × String)) := none)
    (tamper : Phase1 → CommandElabM Phase1 := fun p => pure p) :
    CommandElabM (Name × Nat × Nat) := do
  let saved ← get
  try
    let p1 ← liftTermElabM (phase1 decl stmt nDom m d clkRstOverride)
    let msgs0 := (← get).messages
    let nMsg0 := msgs0.toList.length
    let stx ← `(command| #verify_elab_deep $(mkIdent p1.opn.openName))
    -- the deep constants are declared in the CURRENT namespace under the ident's last component;
    -- inside the namespace `decl` they are `decl.ved_open_deep…` (`deepName` of the open parent)
    try withScope (fun sc => { sc with currNamespace := decl, opts := ((sc.opts.setBool `sparkle.deepNoReplay true).setBool `sparkle.deepContinue true).setBool `sparkle.deepNoNative true }) (withEnableInfoTree false (elabCommand stx))
    catch e => liftTermElabM <| refuse decl "deep" m!"#verify_elab_deep of the open parent {p1.opn.openName}: {e.toMessageData}"
    let p1 ← tamper p1
    let newMsgs := (← get).messages.toList.drop nMsg0
    let msgTxt ← newMsgs.mapM fun msg => do pure (msg.severity == .error, ← msg.data.toString)
    -- H2c-state: the open parent's ports are proved one by one; a port the proof does not need (a port that is the
    -- trigger of the circuit, an output of a nested circuit) may fail without costing the state of the loop that
    -- another port exported.  ONLY errors tied to such a port are tolerated (`deepVerdict`), and the tolerated
    -- failure is RECORDED below (`VED U2 HIER PARTIAL-DEEP`); the facts used are those of the first port that
    -- exported its state, and the final theorem is audited (a `sorry` or a non-standard axiom in a used fact is
    -- refused there).
    let envNow ← getEnv
    let hasState := fun p => envNow.contains (deepNameP p1.opn.openName s!"_{p}_deep_state")
    let partial? ← match deepVerdict (p1.opn.calls.any (·.stateArg)) p1.opn.ports hasState msgTxt with
      | .error why => liftTermElabM <| refuse decl "deep" m!"#verify_elab_deep of the open parent {p1.opn.openName} failed: {why}"
      | .ok v => pure v
    if (← IO.getEnv "VED_HIER_DEBUG").isSome then
      for (_, t) in msgTxt do IO.eprintln s!"[deep] {t}"
    modify fun s => { s with messages := msgs0 }
    if let some (used, failed) := partial? then
      let nErr : Nat := failed.foldl (fun (n : Nat) (f : String × Nat × String) => n + f.2.1) 0
      logInfo m!"VED U2 HIER PARTIAL-DEEP {decl}: open parent {p1.opn.openName}, used port {used}, failed ports {failed.map (·.1)}, {nErr} errors tolerated (ports the proof does not use)"
      for (p, k, e) in failed do
        logInfo m!"VED U2 HIER PARTIAL-DEEP {decl}: port {p}, {k} errors, first: {e.take 400}"
    -- H2e: a limit reached while the proof is elaborated (`maxHeartbeats`, `maxRecDepth`: runtime exceptions, which `catch`
    -- does not see) is a refusal at `[proof]`, like any other failure of the proof
    let (thm, proofMs) ← liftTermElabM (tryCatchRuntimeEx (phase2 decl stmt nDom m p1) fun ex =>
      if ex.isRuntime then refuse decl "proof" ex.toMessageData else throw ex)
    return (thm, p1.childMs, proofMs)
  catch e =>
    set saved
    if ← liftTermElabM (isRefusal e) then throw e
    liftTermElabM <| refuse decl "checker" e.toMessageData

/-- `checkU2HRCore` with the elaboration limits raised (the proofs of a parent with several registers and a
nested circuit exceed the default 200000 heartbeats in `whnf`) to the floors `ved.u2.hierRecDepth` /
`ved.u2.hierHeartbeats` (H2e: options, defaults 100000 / 8000000, 0 = the caller's limit as it is; they were fixed
constants that also overrode a larger caller limit). -/
def checkU2HR (decl : Name) (stmt : Lean.Expr) (nDom : Nat) (m : Sparkle.IR.AST.Module) (d : Design)
    (clkRstOverride : Option (Option (String × String)) := none)
    (tamper : Phase1 → CommandElabM Phase1 := fun p => pure p) :
    CommandElabM (Name × Nat × Nat) :=
  withScope (fun sc => { sc with opts := Tools.VedU2HierBudget.floorOpts sc.opts Tools.VedU2HierBudget.ved.u2.hierRecDepth Tools.VedU2HierBudget.ved.u2.hierHeartbeats })
    (checkU2HRCore decl stmt nDom m d clkRstOverride tamper)

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
