import Tools.VedU1HierComp

/-!
# The hierarchical U1 statement (H1) and its proof-side lemmas

`U1HStmt c m d f`: for the returned top module `m` and the returned design `d`,
over the contract `c` read from the ORIGINAL declaration's type, the declaration
`f` is the meaning of the CLOSED hierarchical semantics (`stepH`/`runH`, defined
only from `m` and `d`), under every admissible arrangement of the bodies.

Scope (H1): the top is combinational (assignments and instances); every
instance names a combinational leaf child of `d` with one output port;
connections are `ref`s.  Everything else is refused by the checks below.
-/

namespace Tools.VedU1Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract

def defaultArgs : (ps : List PTy) → ArgSigs ps
  | [] => ()
  | .bit :: ps => ((⟨fun _ => false⟩ : Signal defaultDomain Bool), defaultArgs ps)
  | .bv w :: ps => ((⟨fun _ => 0⟩ : Signal defaultDomain (BitVec w)), defaultArgs ps)

/-- The child's fold succeeds on some seed (so, by `evalAssignsI_succ`, on every seed). -/
theorem child_succ (cc : Contract) (cm : Module) (g : cc.table.Ty) (b : List Stmt)
    (hU : U1Stmt cc cm g) (hpa : b.Perm cm.body) (hwo : WO [] b)
    (hasg : assignOnly cm.body = true) (hclk : cc.clkRst = none) : LeafSucc cm b := by
  obtain ⟨E, hE, _⟩ := child_rel cc cm g b hU hpa hwo hasg hclk (defaultArgs cc.table.ins) 0
  exact ⟨_, E, hE⟩

/-! ## The artifact checks -/

def isAsgInst : Stmt → Bool
  | .assign .. => true
  | .inst .. => true
  | _ => false

/-- Instance names of a body. -/
def instNames : List Stmt → List String
  | [] => []
  | .inst _ i _ :: r => i :: instNames r
  | _ :: r => instNames r

/-- One `inst` against the design: the child resolves, is a non-primitive, parameter-free,
assertion-free combinational leaf with ONE output; the connections are exactly the child's ports
(none missing, none extra, none duplicated), each a `ref` to a parent wire whose declared width is
the port's. -/
def connsOk (d : Design) (m : Module) (mn : String) (cs : List (String × Expr)) : Bool :=
  match findMod d mn with
  | none => false
  | some c =>
    !c.isPrimitive && c.parameters.isEmpty && c.assertions.isEmpty && assignOnly c.body &&
    c.outputs.length == 1 && decide (cs.map (·.1)).Nodup &&
    (c.inputs ++ c.outputs).all (fun p => cs.any (fun q => q.1 == p.name)) &&
    cs.all (fun q => (c.inputs ++ c.outputs).any (fun p => p.name == q.1)) &&
    cs.all (fun q => match q.2 with
      | .ref x => (c.inputs ++ c.outputs).any
          (fun p => p.name == q.1 && scalar p.ty && declWidth m x == p.ty.bitWidth)
      | _ => false)

/-- The design checks: top correspondence, unique child names, every instance resolved and
well-connected, unique instance names, and NO unused module (a module of `d` that no instance
names is refused, never dropped). -/
def HierShape (d : Design) (m : Module) : Bool :=
  d.topModule == m.name && decide (d.modules.map (·.name)).Nodup &&
  !((d.modules.map (·.name)).contains m.name) &&
  m.body.all isAsgInst &&
  m.body.all (fun s => match s with
    | .inst mn _ cs => connsOk d m mn cs
    | _ => true) &&
  decide (instNames m.body).Nodup &&
  d.modules.all (fun c => m.body.any (fun s => match s with
    | .inst mn _ _ => mn == c.name
    | _ => false))

open Sparkle.IR.Reorder in
/-- The hierarchical netlist check of one arrangement `b` of the top body (the analogue of
`OrderOk`): a permutation of the body, hierarchically well-ordered (`WOH`: no read of a later or
own write, every write once, across assignments AND instances), every read driven by an input or a
write, every output driven, no write to an input. -/
def OrderOkH (d : Design) (m : Module) (b : List Stmt) : Bool :=
  isPermOf b m.body && decide (WOH d b) && b.all isAsgInst &&
  b.all (fun s => (rdH d s).all (fun n =>
    (m.inputs.map (·.name)).contains n || (wrsH d b).contains n)) &&
  m.outputs.all (fun p => (wrsH d b).contains p.name) &&
  (wrsH d b).all (fun n => !(m.inputs.map (·.name)).contains n)

def OrderH (d : Design) (m : Module) : Prop := ∃ b, OrderOkH d m b = true

/-- An arrangement choice: per module name an arrangement of its body; the top hierarchically
well-ordered, every child well-ordered. -/
def AdmArr (d : Design) (m : Module) (arr : String → List Stmt) : Prop :=
  (arr m.name).Perm m.body ∧ WOH d (arr m.name) ∧
  ∀ c ∈ d.modules, (arr c.name).Perm c.body ∧ WO [] (arr c.name)

/-- The outputs of the CLOSED hierarchical run equal the declaration, at every cycle of every
in-range input stream, and such a run EXISTS. -/
def OutputsOnH (c : Contract) (m : Module) (d : Design) (arr : String → List Stmt)
    (f : c.table.Ty) : Prop :=
  ∀ ins, InputsOk c m ins → ∀ K, ∃ envs,
    runH d arr m (seedFwd m K ins) K (st0 c m) = some envs ∧
    ∀ t, t < K → ∀ o ∈ c.outputs, ∃ env, envs[t]? = some env ∧ env o.name = srcOf c f ins o.name t

def OutputsStmtH (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  ∀ arr, AdmArr d m arr → OutputsOnH c m d arr f

/-- The statement the hierarchical entry registers. -/
def U1HStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = none ∧ HierShape d m = true ∧ WidthStmt c m ∧
  OrderH d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧ (∃ arr, AdmArr d m arr) ∧
  OutputsStmtH c m d f

end Tools.VedU1Hier
