import Tools.ShippingMixedLiteralSoundness
import Tools.ShippingHierarchySoundness

/-! The semantic context of the certified recursion.

The recursive translation contracts speak about three body predicates: what
it means for the builder's body to RUN from an initial environment, for the
body to be TYPED, and for it to be SIMPLE (the post-pipeline's shape). The
flat instance is the open-module semantics every existing endpoint uses
(instance statements are skipped, bodies are assignment-only). The
hierarchical subclass additionally executes instance statements against a
table of linked children, so a contract proved once over the class holds in
both worlds. -/
namespace Tools.ShippingLinkCtx
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingTypedExprSoundness Tools.ShippingScalarSoundness
open Tools.ShippingBuilderSoundness Tools.ShippingPostSoundness Sparkle.IR.OptCheck
open Tools.ShippingHierarchySoundness

/-- `w` is declared in the module — as a wire or an input port — at the
given width. -/
def Declared (m : Sparkle.IR.AST.Module) (w : String) (width : Nat) : Prop :=
  ∃ q : Port, (q ∈ m.wires ∨ q ∈ m.inputs) ∧ q.name = w ∧ q.ty.bitWidth = width

/-- WIDTH LINKAGE of one instance statement, as a proposition: every
connection is a parent name declared at exactly the child port's width. -/
def Linked (m child : Sparkle.IR.AST.Module)
    (conns : List (String × Sparkle.IR.AST.Expr)) : Prop :=
  ∀ c ∈ conns, ∃ (w : String) (p : Port), c.2 = .ref w ∧
    p ∈ child.inputs ++ child.outputs ∧ p.name = c.1 ∧ Declared m w p.ty.bitWidth

theorem instNameWidth?_declared {m : Sparkle.IR.AST.Module} {w : String} {width : Nat}
    (h : instNameWidth? m w = some width) : Declared m w width := by
  unfold instNameWidth? at h
  cases hw : m.wires.find? (fun p => p.name == w) with
  | some q =>
    rw [hw] at h
    refine ⟨q, Or.inl (List.mem_of_find?_eq_some hw), ?_, ?_⟩
    · have := List.find?_some hw
      exact eq_of_beq this
    · exact Option.some.inj h
  | none =>
    rw [hw] at h
    cases hi : m.inputs.find? (fun p => p.name == w) with
    | none => rw [hi] at h; cases h
    | some q =>
      rw [hi] at h
      refine ⟨q, Or.inr (List.mem_of_find?_eq_some hi), ?_, ?_⟩
      · have := List.find?_some hi
        exact eq_of_beq this
      · exact Option.some.inj h

/-- The compiler's linkage check is sound for the linkage proposition. -/
theorem instLinked_sound {m child : Sparkle.IR.AST.Module}
    {conns : List (String × Sparkle.IR.AST.Expr)}
    (h : instLinked m child conns = true) : Linked m child conns := by
  intro c hc
  have hall := List.all_eq_true.mp h c hc
  obtain ⟨pn, rhs⟩ := c
  cases rhs with
  | ref w =>
    have hall' : (match (child.inputs ++ child.outputs).find? (fun p => p.name == pn),
        instNameWidth? m w with
      | some p, some width => width == p.ty.bitWidth
      | _, _ => false) = true := hall
    cases hp : (child.inputs ++ child.outputs).find? (fun p => p.name == pn) with
    | none => rw [hp] at hall'; cases hall'
    | some p =>
      cases hwd : instNameWidth? m w with
      | none => rw [hp, hwd] at hall'; cases hall'
      | some width =>
        rw [hp, hwd] at hall'
        have hEq : width = p.ty.bitWidth := eq_of_beq hall'
        have hname : (p.name == pn) = true :=
          List.find?_some (p := fun q : Port => q.name == pn) hp
        refine ⟨w, p, rfl, List.mem_of_find?_eq_some hp, eq_of_beq hname, ?_⟩
        rw [← hEq]
        exact instNameWidth?_declared hwd
  | _ => cases hall

/-- Linkage survives any growth of the declarations. -/
theorem Linked.mono {m m' child : Sparkle.IR.AST.Module}
    {conns : List (String × Sparkle.IR.AST.Expr)}
    (h : Linked m child conns)
    (hw : ∀ q ∈ m.wires, q ∈ m'.wires) (hi : ∀ q ∈ m.inputs, q ∈ m'.inputs) :
    Linked m' child conns := by
  intro c hc
  obtain ⟨w, p, hr, hp, hn, q, hq, hqn, hqw⟩ := h c hc
  refine ⟨w, p, hr, hp, hn, q, ?_, hqn, hqw⟩
  rcases hq with hq | hq
  · exact Or.inl (hw q hq)
  · exact Or.inr (hi q hq)

/-- The body predicates of the recursion, with exactly the closure laws the
generic node lemmas use. -/
class LinkCtx where
  Runs : WEnv → MEnv → Env → CircuitState → Env → Prop
  Typed : WEnv → CircuitState → Prop
  Simple : List Stmt → Prop
  runs_body : ∀ {we : WEnv} {mems : MEnv} {initial : Env} {s t : CircuitState} {env : Env},
    t.module.body = s.module.body → Runs we mems initial s env → Runs we mems initial t env
  runs_emit : ∀ {we : WEnv} {mems : MEnv} {initial : Env} {s : CircuitState} {prior : Env}
    {lhs : String} {rhs : Sparkle.IR.AST.Expr} {value : Nat},
    Runs we mems initial s prior → evalExpr we prior rhs = some value →
    Runs we mems initial (CircuitM.emitAssign lhs rhs s).2 (write prior lhs value)
  typed_body : ∀ {we : WEnv} {s t : CircuitState},
    t.module.body = s.module.body →
    (∀ q ∈ s.module.wires, q ∈ t.module.wires) →
    (∀ q ∈ s.module.inputs, q ∈ t.module.inputs) → Typed we s → Typed we t
  typed_emit : ∀ {we : WEnv} {s : CircuitState} {w : String} {rhs : Sparkle.IR.AST.Expr},
    Typed we s → TypedExpr we rhs (we w) → Typed we (CircuitM.emitAssign w rhs s).2
  simple_emit : ∀ {body : List Stmt} {l : String} {r : Sparkle.IR.AST.Expr},
    simpleRhs r = true → Simple body → Simple (.assign l r :: body)
  runs_nil : ∀ {we : WEnv} {mems : MEnv} {initial : Env} {s : CircuitState},
    s.module.body = [] → Runs we mems initial s initial
  typed_nil : ∀ {we : WEnv} {s : CircuitState}, s.module.body = [] → Typed we s

/-- Simple statements may be prepended in bulk. -/
theorem simple_prepend [LinkCtx] : ∀ (pre body : List Stmt),
    (∀ st ∈ pre, ∃ l r, st = Stmt.assign l r ∧ simpleRhs r = true) →
    LinkCtx.Simple body → LinkCtx.Simple (pre ++ body)
  | [], _, _, hs => hs
  | st :: pre, body, hpre, hs => by
    obtain ⟨l, r, rfl, hr⟩ := hpre st List.mem_cons_self
    exact LinkCtx.simple_emit hr
      (simple_prepend pre body (fun st' h => hpre st' (List.mem_cons_of_mem _ h)) hs)

/-- The flat (open-module) context: definitionally the predicates every
existing endpoint is stated with. -/
instance (priority := low) flatLink : LinkCtx where
  Runs := Runs
  Typed := TypedBody
  Simple := SimpleStmts
  runs_body := fun hb h => runs_of_body_eq hb h
  runs_emit := fun {we mems initial s prior lhs rhs value} h hrhs =>
    emitAssign_sound s we mems initial prior lhs rhs value h hrhs
  typed_body := fun {we s t} hb _ _ h => by
    unfold TypedBody at *
    rw [hb]
    exact h
  typed_emit := fun {we s w rhs} h typed => by
    unfold TypedBody
    rw [emitAssign_body_cons]
    intro st member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨w, rhs, rfl, typed⟩
    · exact h st member
  simple_emit := fun {body l r} hr hs => by
    intro stmt hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨l, r, rfl, hr⟩
    · exact hs stmt hmem
  runs_nil := fun {we mems initial s} hb => by
    simp [Runs, Module.finalize, hb, evalAssigns]
  typed_nil := fun {we s} hb st hs => by
    rw [hb] at hs
    cases hs

/-- A context that also EXECUTES instance statements against linked
children. The extra laws are the instance-emission steps. -/
class HierCtx extends LinkCtx where
  children : String → Option (Sparkle.IR.AST.Module × WEnv)
  runs_def : ∀ {we : WEnv} {mems : MEnv} {initial : Env} {s : CircuitState} {env : Env},
    Runs we mems initial s env ↔
      evalAssignsH we children mems s.module.finalize.body initial = some env
  typed_inst : ∀ {we : WEnv} {s : CircuitState} {mn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)} {child : Sparkle.IR.AST.Module}
    {cwe : WEnv},
    children mn = some (child, cwe) → Linked s.module child conns →
    Typed we s → Typed we { s with module := s.module.addStmt (.inst mn iname conns) }
  typed_linked : ∀ {we : WEnv} {s : CircuitState} {mn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)},
    Typed we s → Stmt.inst mn iname conns ∈ s.module.body →
    ∃ child cwe, children mn = some (child, cwe) ∧ Linked s.module child conns
  simple_all : ∀ body, Simple body

theorem evalAssignsH_append (we : WEnv) (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (mems : MEnv) : ∀ (a b : List Stmt) (env : Env),
    evalAssignsH we children mems (a ++ b) env =
      (evalAssignsH we children mems a env).bind (evalAssignsH we children mems b)
  | [], b, env => rfl
  | .assign l r :: rest, b, env => by
    show (do
      let v ← evalExpr we env r
      evalAssignsH we children mems (rest ++ b) (fun n => if n = l then v else env n)) = _
    cases hv : evalExpr we env r with
    | none => simp [evalAssignsH, hv]
    | some v =>
      simp only [evalAssignsH, hv, Option.bind_eq_bind, Option.bind_some]
      exact evalAssignsH_append we children mems rest b _
  | .inst mn iname conns :: rest, b, env => by
    cases hc : children mn with
    | none => simp [evalAssignsH, hc]
    | some cp =>
      obtain ⟨child, cwe⟩ := cp
      cases hr : evalAssigns cwe mems child.body (connEnv conns env) with
      | none => simp [evalAssignsH, hc, hr]
      | some cres =>
        simp only [List.cons_append, evalAssignsH, hc, hr, Option.bind_eq_bind,
          Option.bind_some]
        exact evalAssignsH_append we children mems rest b _
  | .register _ _ _ _ _ :: rest, b, env => by
    simp only [List.cons_append, evalAssignsH]
    exact evalAssignsH_append we children mems rest b env
  | .memory _ _ _ _ _ _ _ _ _ _ _ _ :: rest, b, env => by
    simp only [List.cons_append, evalAssignsH]
    exact evalAssignsH_append we children mems rest b env

/-- Typed bodies of the hierarchical world: typed assignments, and instance
statements of linked children that are WIDTH-LINKED against the module's
declarations. -/
def TypedBodyH (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (we : WEnv) (s : CircuitState) : Prop :=
  ∀ st ∈ s.module.body, (∃ l r, st = .assign l r ∧ TypedExpr we r (we l)) ∨
    (∃ mn iname conns child cwe, st = .inst mn iname conns ∧
      children mn = some (child, cwe) ∧ Linked s.module child conns)

/-- The hierarchical context over a table of linked children. -/
@[reducible] def hierLink (children : String → Option (Sparkle.IR.AST.Module × WEnv)) : HierCtx where
  Runs := fun we mems initial s env =>
    evalAssignsH we children mems s.module.finalize.body initial = some env
  Typed := TypedBodyH children
  Simple := fun _ => True
  runs_body := fun {we mems initial s t env} hb h => by
    show evalAssignsH we children mems t.module.finalize.body initial = some env
    have : t.module.finalize.body = s.module.finalize.body := by
      simp [Module.finalize, hb]
    rw [this]
    exact h
  runs_emit := fun {we mems initial s prior lhs rhs value} h hrhs => by
    show evalAssignsH we children mems
      (CircuitM.emitAssign lhs rhs s).2.module.finalize.body initial = _
    rw [emitAssign_body, evalAssignsH_append]
    have h' : evalAssignsH we children mems s.module.finalize.body initial = some prior := h
    rw [h']
    simp [evalAssignsH, hrhs]
    rfl
  typed_body := fun {we s t} hb hw hi h => by
    intro st member
    rw [hb] at member
    rcases h st member with ha | ⟨mn, iname, conns, child, cwe, he, hc, hl⟩
    · exact Or.inl ha
    · exact Or.inr ⟨mn, iname, conns, child, cwe, he, hc, hl.mono hw hi⟩
  typed_emit := fun {we s w rhs} h typed => by
    intro st member
    rw [emitAssign_body_cons] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl ⟨w, rhs, rfl, typed⟩
    · rcases h st member with ha | ⟨mn, iname, conns, child, cwe, he, hc, hl⟩
      · exact Or.inl ha
      · exact Or.inr ⟨mn, iname, conns, child, cwe, he, hc,
          hl.mono (fun q hq => by rw [emitAssign_wires]; exact hq) (fun q hq => hq)⟩
  simple_emit := fun _ _ => trivial
  runs_nil := fun {we mems initial s} hb => by
    simp [Module.finalize, hb, evalAssignsH]
  typed_nil := fun {we s} hb st hs => by
    rw [hb] at hs
    cases hs
  children := children
  runs_def := Iff.rfl
  typed_inst := fun {we s mn iname conns child cwe} hc hl h => by
    intro st member
    have member' : st ∈ Stmt.inst mn iname conns :: s.module.body := member
    rcases List.mem_cons.mp member' with rfl | member'
    · exact Or.inr ⟨mn, iname, conns, child, cwe, rfl, hc, hl⟩
    · exact h st member'
  typed_linked := fun {we s mn iname conns} h member => by
    rcases h _ member with ⟨l, r, he, _⟩ | ⟨mn', iname', conns', child, cwe, he, hc, hl⟩
    · cases he
    · cases he
      exact ⟨child, cwe, hc, hl⟩
  simple_all := fun _ => trivial

end Tools.ShippingLinkCtx
