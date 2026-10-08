import Sparkle.IR.OptCheck

/-!
# Interface extraction for instance-bearing modules

The optimizer's output on a module with instance statements is validated by
extracting its interface: the instance statements are dropped, the wires
the instances drive become input ports, and the wires the module drives
into the instances become output ports (`openFlat`). In the open-module view
that changes nothing — an instance is a no-op whose outputs are free — so a
check on the extracted pair, with the instance statements kept and every
connection validated or untouched, carries over to the linked meaning (the
proofs: `Tools/ShippingHierOptSoundness.lean`).
-/

namespace Sparkle.IR.HierCheck

open Sparkle.IR.AST
open Sparkle.IR.Reorder (writesOf)

/-- The body without its instance statements. -/
def openBody (body : List Stmt) : List Stmt :=
  body.filter fun st =>
    match st with
    | .inst .. => false
    | _ => true

/-- Interface extraction: instance statements dropped, the given ports added
as inputs (the instance-output wires) and as outputs (assigned wires the
instances read). Declarations are untouched. -/
def openFlat (m : Module) (insX outsX : List Port) : Module :=
  { m with body := openBody m.body, inputs := m.inputs ++ insX,
           outputs := m.outputs ++ outsX }

/-- The wires a body drives: assignment targets, combinational read data,
registers. -/
def drivesOf (body : List Stmt) : List String :=
  writesOf body ++ body.filterMap fun st =>
    match st with
    | .register r .. => some r
    | _ => none

/-- Decidable: every wire an instance of `o` connects is either an output /
extracted output of `m` (validated by the checker) or is driven by neither
body (so it keeps its seeded value in both). -/
def connAgreeOk (m o : Module) (outsX : List Port) : Bool :=
  o.body.all fun st =>
    match st with
    | .inst _ _ conns =>
      conns.all fun c =>
        match c.2 with
        | .ref w =>
          ((m.outputs ++ outsX).map (·.name)).contains w ||
            (!(drivesOf m.body).contains w && !(drivesOf o.body).contains w)
        | _ => true
    | _ => true

/-- Decidable: the instance statements of `o` are instance statements of `m`. -/
def instsKept (m o : Module) : Bool :=
  o.body.all fun st =>
    match st with
    | .inst mn iname conns =>
      m.body.any fun st' =>
        match st' with
        | .inst mn' iname' conns' =>
          mn' == mn && iname' == iname &&
            decide (conns' = conns)
        | _ => false
    | _ => true

/-- The wires the instance statements connect. -/
def connRefs (body : List Stmt) : List String :=
  body.flatMap fun st =>
    match st with
    | .inst _ _ conns => conns.filterMap fun c =>
        match c.2 with
        | .ref w => some w
        | _ => none
    | _ => []

/-- The extracted inputs: connected wires the body does not write and that
are not ports (the instances drive them). -/
def openIns (m : Module) : List Port :=
  m.wires.filter fun p =>
    (connRefs m.body).contains p.name && !(drivesOf m.body).contains p.name &&
      !(m.inputs.map (·.name)).contains p.name

/-- The extracted outputs: connected wires the body writes (the instances
read them). -/
def openOuts (m : Module) : List Port :=
  m.wires.filter fun p =>
    (connRefs m.body).contains p.name && (drivesOf m.body).contains p.name

/-- `m`'s instance statement of this module and instance name. -/
def instConns? (m : Module) (mn iname : String) : Option (List (String × Expr)) :=
  m.body.findSome? fun st => match st with
    | .inst mn' iname' conns => if mn' == mn && iname' == iname then some conns else none
    | _ => none

/-- The optimizer's output `o` of `m` with its instance connections named
again: where the optimizer inlined (or copy-propagated) the value of a wire
`w` that `m` connects and assigns, the connection reads `w` again and `w`
is assigned that value just before the instance. The function is the
optimizer's; the instance statements become `m`'s, so the interface check
(`instsKept`, `connAgreeOk`, the extracted pair) can compare the two. -/
def deinlineParts (m o : Module) : List Stmt × List String := Id.run do
  let mut body : List Stmt := []
  let mut added : List String := []
  for st in o.body do
    match st with
    | .inst mn iname conns =>
      match instConns? m mn iname with
      | some mconns =>
        let mut conns' := []
        for c in conns do
          match c.2, mconns.lookup c.1 with
          | e, some (.ref w) =>
            if e == .ref w || !(drivesOf m.body).contains w then
              conns' := conns' ++ [c]
            else
              body := body ++ [.assign w e]
              added := added ++ [w]
              conns' := conns' ++ [(c.1, .ref w)]
          | _, _ => conns' := conns' ++ [c]
        body := body ++ [.inst mn iname conns']
      | none => body := body ++ [st]
    | _ => body := body ++ [st]
  return (body, added)

/-- (The declarations: `m`'s, those `o` keeps and the named wires, in `m`'s
order.) -/
def deinline (m o : Module) : Module :=
  let r := deinlineParts m o
  { o with body := r.1,
           wires := m.wires.filter fun p => o.wires.contains p || r.2.contains p.name }

theorem deinline_wires_sublist (m o : Module) : (deinline m o).wires.Sublist m.wires :=
  List.filter_sublist

theorem deinline_name (m o : Module) : (deinline m o).name = o.name := rfl

end Sparkle.IR.HierCheck
