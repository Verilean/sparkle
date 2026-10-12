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
            else if added.contains w then
              -- named once: a later instance reads the same wire
              conns' := conns' ++ [(c.1, .ref w)]
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
order.) The candidate before the guards. -/
def deinlineRaw (m o : Module) : Module :=
  let r := deinlineParts m o
  { o with body := r.1,
           wires := m.wires.filter fun p => o.wires.contains p || r.2.contains p.name }

/-! ## The guards on the candidate (fallback, never a rejection)

The interface check (`hierRefineCheck`) compares the instance statements as
a SET and the extracted pair's values; it says nothing of the candidate's
instance names being distinct nor of the ORDER of its instances and
assignments — both of which the linked meaning of the shipped module needs
(`linkedWF`, distinct instance names). Two decidable, design-free guards
close that: a candidate failing either is replaced by the input module `m`.

* G4, `instNamesOf`: the candidate's instance names are pairwise distinct.
* G2, `linkedWFX X`: with `X` the names of the wires the instances drive
  (the extracted inputs `openIns m`), reading "the wires an instance drives"
  as "its connected wires in `X`": no assignment targets or reads a wire in
  `X` connected to a LATER instance, and no wire connected to an instance is
  written afterwards (by an assignment, or as a wire in `X` connected to a
  later instance). It over-approximates an instance's outputs by all its
  connected `X`-wires, so it implies `linkedWF` for every child map whose
  instance outputs are in `X` (`Tools/ShippingGuardsSound.lean`); it also
  refuses a candidate in which an instance reads another instance's output
  wire directly (such a module ships unoptimized). -/

/-- The instance names of a body, in order. -/
def instNamesOf : List Stmt → List String
  | [] => []
  | .inst _ iname _ :: rest => iname :: instNamesOf rest
  | _ :: rest => instNamesOf rest

/-- The connected wires of an instance that are in `X`. -/
def connX (X : List String) (conns : List (String × Expr)) : List String :=
  conns.filterMap fun c =>
    match c.2 with
    | .ref w => if X.contains w then some w else none
    | _ => none

/-- The `X`-wires connected to the instances of a body. -/
def outsX (X : List String) : List Stmt → List String
  | [] => []
  | .inst _ _ conns :: rest => connX X conns ++ outsX X rest
  | _ :: rest => outsX X rest

/-- Assignment targets and the `X`-wires connected to instances. -/
def writesX (X : List String) : List Stmt → List String
  | [] => []
  | .assign l _ :: rest => l :: writesX X rest
  | .inst _ _ conns :: rest => connX X conns ++ writesX X rest
  | _ :: rest => writesX X rest

/-- G2: the linked order, with an instance's outputs read as its connected
wires in `X`. -/
def linkedWFX (X : List String) : List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    !(outsX X rest).contains l &&
      (Sparkle.IR.Reorder.refsOf r).all (fun n => !(outsX X rest).contains n) &&
      linkedWFX X rest
  | .inst _ _ conns :: rest =>
    conns.all (fun c =>
      match c.2 with
      | .ref w => !(writesX X rest).contains w
      | _ => true) && linkedWFX X rest
  | .register _ _ _ _ _ :: rest => linkedWFX X rest
  | .memory .. :: _ => false

/-- The candidate `o` when it passes both guards, else the input module. -/
def keepGuarded (m o : Module) : Module :=
  if decide (instNamesOf o.body).Nodup && linkedWFX ((openIns m).map (·.name)) o.body then o
  else m

/-- The kept module is the guarded candidate or the input module. -/
theorem keepGuarded_cases (m o : Module) :
    (keepGuarded m o = o ∧ (instNamesOf o.body).Nodup ∧
      linkedWFX ((openIns m).map (·.name)) o.body = true) ∨ keepGuarded m o = m := by
  unfold keepGuarded
  split
  · rename_i h
    rw [Bool.and_eq_true] at h
    exact Or.inl ⟨rfl, of_decide_eq_true h.1, h.2⟩
  · exact Or.inr rfl

/-- The optimizer's output with its connections named again, GUARDED: the
candidate `deinlineRaw m o` when its instance names are distinct and its
body is in the linked order, else `m`. -/
def deinline (m o : Module) : Module :=
  keepGuarded m (deinlineRaw m o)

/-- `deinline m o` is the guarded candidate or `m`. -/
theorem deinline_cases (m o : Module) :
    (deinline m o = deinlineRaw m o ∧ (instNamesOf (deinline m o).body).Nodup ∧
      linkedWFX ((openIns m).map (·.name)) (deinline m o).body = true) ∨ deinline m o = m := by
  unfold deinline
  rcases keepGuarded_cases m (deinlineRaw m o) with ⟨e, h1, h2⟩ | e
  · rw [e]
    exact Or.inl ⟨rfl, h1, h2⟩
  · exact Or.inr e

theorem deinline_wires_sublist (m o : Module) : (deinline m o).wires.Sublist m.wires := by
  rcases deinline_cases m o with ⟨e, -, -⟩ | e
  · rw [e]
    exact List.filter_sublist
  · rw [e]
    exact List.Sublist.refl _

theorem deinline_name (m o : Module) (h : o.name = m.name) : (deinline m o).name = m.name := by
  rcases deinline_cases m o with ⟨e, -, -⟩ | e
  · rw [e]
    exact h
  · rw [e]

end Sparkle.IR.HierCheck
