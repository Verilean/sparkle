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
    t.module.body = s.module.body → Typed we s → Typed we t
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
  typed_body := fun {we s t} hb h => by
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
    {conns : List (String × Sparkle.IR.AST.Expr)},
    Typed we s → Typed we { s with module := s.module.addStmt (.inst mn iname conns) }
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

/-- Typed bodies of the hierarchical world: typed assignments and instances. -/
def TypedBodyH (we : WEnv) (s : CircuitState) : Prop :=
  ∀ st ∈ s.module.body, (∃ l r, st = .assign l r ∧ TypedExpr we r (we l)) ∨
    (∃ mn iname conns, st = .inst mn iname conns)

/-- The hierarchical context over a table of linked children. -/
@[reducible] def hierLink (children : String → Option (Sparkle.IR.AST.Module × WEnv)) : HierCtx where
  Runs := fun we mems initial s env =>
    evalAssignsH we children mems s.module.finalize.body initial = some env
  Typed := TypedBodyH
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
  typed_body := fun {we s t} hb h => by
    unfold TypedBodyH at *
    rw [hb]
    exact h
  typed_emit := fun {we s w rhs} h typed => by
    unfold TypedBodyH
    rw [emitAssign_body_cons]
    intro st member
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl ⟨w, rhs, rfl, typed⟩
    · exact h st member
  simple_emit := fun _ _ => trivial
  runs_nil := fun {we mems initial s} hb => by
    simp [Module.finalize, hb, evalAssignsH]
  typed_nil := fun {we s} hb st hs => by
    rw [hb] at hs
    cases hs
  children := children
  runs_def := Iff.rfl
  typed_inst := fun {we s mn iname conns} h => by
    intro st member
    have member' : st ∈ Stmt.inst mn iname conns :: s.module.body := member
    rcases List.mem_cons.mp member' with rfl | member'
    · exact Or.inr ⟨mn, iname, conns, rfl⟩
    · exact h st member'
  simple_all := fun _ => trivial

end Tools.ShippingLinkCtx
