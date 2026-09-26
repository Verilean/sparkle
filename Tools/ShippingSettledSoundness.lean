import Tools.ShippingDeclWidths

/-! # Simultaneous equations for emitted combinational assignments

Acyclic assignment order is stronger than output equivalence of sequential
folds. This module makes that obligation explicit and proves the connection
to simultaneous equations. It does not model delays, four-state values or
an external simulator's event scheduler.
-/
namespace Tools.ShippingSettledSoundness

open Lean Sparkle.Compiler.Elab Sparkle.IR.OptCheck
open Tools.ShippingEntrySoundness Tools.ShippingTranslateSoundness
open Tools.ShippingOptSoundness
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.SVParser.SVSemantics
open Tools.ShippingPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingPrintEntrySoundness
open Tools.ShippingSVBridge Tools.ShippingDeclWidths

/-- Each target is written once, and an RHS reads neither its own target
nor a target that will be assigned later. Names not written by the body are
external inputs. No expression shape or fixed circuit size is assumed. -/
inductive Acyclic : List Stmt → Prop
  | nil : Acyclic []
  | cons {l r rest}
      (target : l ∉ writesOf rest)
      (reads : ∀ x ∈ refsOf r, x ≠ l ∧ x ∉ writesOf rest)
      (tail : Acyclic rest) : Acyclic (.assign l r :: rest)

theorem writes_cons (l : String) (r : Sparkle.IR.AST.Expr) (rest : List Stmt) :
    writesOf (.assign l r :: rest) = l :: writesOf rest := rfl

/-- All equations are evaluated in the SAME environment. -/
def IREquations (we : WEnv) (body : List Stmt) (env : Env) : Prop :=
  ∀ l r, Stmt.assign l r ∈ body → evalExpr we env r = some (env l)

/-- Undriven names retain their supplied values. -/
def ExternalValues (body : List Stmt) (initial env : Env) : Prop :=
  ∀ x, x ∉ writesOf body → env x = initial x

theorem assign_frame {we mems body initial env} (ha : Acyclic body)
    (he : evalAssigns we mems body initial = some env) :
    ExternalValues body initial env := by
  induction ha generalizing initial with
  | nil => simp [evalAssigns] at he; subst env; exact fun _ _ => rfl
  | @cons l r rest ht hr ha ih =>
    simp only [evalAssigns, bind, Option.bind_eq_some_iff] at he
    obtain ⟨v, _, he⟩ := he
    intro x hx
    have hx' : x ≠ l ∧ x ∉ writesOf rest := by
      simpa [writes_cons] using hx
    simpa [hx'.1] using ih he x hx'.2

/-- A successful ordered fold produces a simultaneous solution. -/
theorem assign_equations {we mems body initial env} (ha : Acyclic body)
    (he : evalAssigns we mems body initial = some env) : IREquations we body env := by
  induction ha generalizing initial with
  | nil => simp [IREquations]
  | @cons l r rest ht hr ha ih =>
    simp only [evalAssigns, bind, Option.bind_eq_some_iff] at he
    obtain ⟨v, hv, he⟩ := he
    have hf := assign_frame ha he
    have hl : env l = v := by simpa using hf l ht
    have hrhs : evalExpr we env r = evalExpr we initial r :=
      evalExpr_congr _ _ _ _ (fun x hx => by simpa [(hr x hx).1] using hf x (hr x hx).2)
    intro l' r' hm
    rcases List.mem_cons.mp hm with heq | hm
    · cases heq; exact hrhs.trans (hv.trans (congrArg some hl.symm))
    · exact ih he l' r' hm

/-- A simultaneous solution with the supplied external values is uniquely
recovered by the ordered fold. This also proves uniqueness of internal wires,
not only equality of the observed output. -/
theorem equations_eval {we mems body initial env} (ha : Acyclic body)
    (hq : IREquations we body env) (hx : ExternalValues body initial env) :
    evalAssigns we mems body initial = some env := by
  induction ha generalizing initial with
  | nil =>
    have he : initial = env := funext (fun x => (hx x (by simp [writesOf])).symm)
    simp [evalAssigns, he]
  | @cons l r rest ht hr ha ih =>
    have hv : evalExpr we initial r = some (env l) := by
      rw [evalExpr_congr we initial env r (fun x hm => (hx x (by
        have := hr x hm; simpa [writes_cons] using this)).symm)]
      exact hq l r (by simp)
    simp only [evalAssigns, hv]
    apply ih (fun l r hm => hq l r (by simp [hm]))
    intro x hxr
    by_cases hxl : x = l
    · simp [hxl]
    · simpa [hxl] using hx x (by simp [writes_cons, hxl, hxr])

theorem equations_unique {we body initial env₁ env₂} (ha : Acyclic body)
    (h₁ : IREquations we body env₁) (hx₁ : ExternalValues body initial env₁)
    (h₂ : IREquations we body env₂) (hx₂ : ExternalValues body initial env₂) : env₁ = env₂ := by
  have a := equations_eval (mems := fun _ _ => 0) ha h₁ hx₁
  have b := equations_eval (mems := fun _ _ => 0) ha h₂ hx₂
  exact Option.some.inj (a.symm.trans b)

/-- The equation relation is insensitive to textual order. A permutation
need not itself be a valid topological evaluation schedule. -/
theorem equations_perm {we body body' env} (hp : body.Perm body') :
    IREquations we body env ↔ IREquations we body' env := by
  constructor
  · exact fun h l r hm => h l r (hp.mem_iff.mpr hm)
  · exact fun h l r hm => h l r (hp.mem_iff.mp hm)

/-- Two-state continuous-assignment equations at the declared target width.
All RHSs read the same environment; memory read steps are outside this relation. -/
def SVEquations (wof : String → Option Nat) (pairs : List CombStep) (env : Env) : Prop :=
  ∀ step ∈ pairs, match step with
    | .assign l rhs => ∃ width value, wof l = some width ∧
        evalSV wof env width rhs = some value ∧ env l = mask width value
    | .reads .. => False

/-- The emitted equation system is the IR equation system on bounded values.
This transfers equations, rather than executing either list of assignments. -/
theorem equations_emitted_iff {wof we body pairs env}
    (ha : Acyclic body) (hc : assignsCheck wof we body = true)
    (he : emitAssigns wof body = some pairs)
    (hb : Bounded we env)
    (hw : ∀ x width, wof x = some width → env x < 2 ^ width) :
    SVEquations wof pairs env ↔ IREquations we body env := by
  induction ha generalizing pairs with
  | nil => simp [emitAssigns] at he; subst pairs; simp [SVEquations, IREquations]
  | @cons l r rest ht hr ha ih =>
    simp only [assignsCheck, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨_, hl⟩, hwidth⟩, hsf⟩, hc⟩ := hc
    simp only [emitAssigns, bind, Option.bind_eq_some_iff] at he
    obtain ⟨sv, hsv, tail, htail, heq⟩ := he
    cases heq
    have hv := emit_sem_evalSV (sf4Check_sound hsf) hb hw hsv
    rw [hwidth] at hv
    have ih := ih hc htail
    constructor
    · intro hs l' r' hm
      rcases List.mem_cons.mp hm with heq | hm
      · cases heq
        obtain ⟨width, value, hw', heval, heq⟩ := hs (.assign l sv) (by simp)
        rw [hl] at hw'; cases hw'
        rw [hv] at heval
        have hvb := sf4_bounded (sf4Check_sound hsf) hb value heval
        rw [hwidth] at hvb
        have heq' : env l = value := by simpa [mask, Nat.mod_eq_of_lt hvb] using heq
        simpa [heq'] using heval
      · exact ih.mp (fun st hm => hs st (by simp [hm])) l' r' hm
    · intro hs st hm
      rcases List.mem_cons.mp hm with heq | hm
      · cases heq
        refine ⟨we l, env l, hl, ?_, ?_⟩
        · rw [hv]; exact hs l r (by simp)
        · simp [mask, Nat.mod_eq_of_lt (hb l)]
      · exact ih.mpr (fun l r hm => hs l r (by simp [hm])) st hm

/-- Targets of the supported emitted assignment system. -/
def svTargets (pairs : List CombStep) : List String := pairs.flatMap fun step =>
  match step with
  | .assign l _ => [l]
  | .reads _ _ _ ports => ports.map (·.2)

def SVSolution (wof : String → Option Nat) (pairs : List CombStep)
    (initial env : Env) : Prop :=
  SVEquations wof pairs env ∧ ∀ x, x ∉ svTargets pairs → env x = initial x

theorem emitted_targets {wof body pairs} (ha : Acyclic body)
    (he : emitAssigns wof body = some pairs) : svTargets pairs = writesOf body := by
  induction ha generalizing pairs with
  | nil => simp [emitAssigns] at he; subst pairs; rfl
  | @cons l r rest _ _ ha ih =>
    simp only [emitAssigns, bind, Option.bind_eq_some_iff] at he
    obtain ⟨sv, _, tail, ht, heq⟩ := he
    cases heq
    change l :: svTargets tail = l :: writesOf rest
    rw [ih ht]

theorem svEquations_perm {wof pairs pairs' env} (hp : pairs.Perm pairs') :
    SVEquations wof pairs env ↔ SVEquations wof pairs' env := by
  constructor
  · exact fun h st hm => h st (hp.mem_iff.mpr hm)
  · exact fun h st hm => h st (hp.mem_iff.mp hm)

/-- For the actual emitted tree, the ordered fold constructs the unique
bounded simultaneous solution with the supplied undriven values. The ordering
condition is explicit: it is NOT implied by the existing output-only check. -/
theorem module_settled {m : Sparkle.IR.AST.Module} {sv : SVModule} {we : WEnv}
    (hp : PrintableDecls m)
    (hshape : ∀ st ∈ m.body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (htree : emitAstModule m = some sv)
    (hwidth : astWidths sv = printWidths (m.wires ++ m.inputs ++ m.outputs))
    (hc : assignsCheck (astWidths sv) we m.body = true)
    (ha : Acyclic m.body) (mems : MEnv) (initial : Env)
    (hb : Bounded we initial)
    (hw : ∀ x width, astWidths sv x = some width → initial x < 2 ^ width) :
    ∃ pairs env, combItems sv.items = some pairs ∧
      evalAssignsSV (astWidths sv) mems pairs initial = some env ∧
      Bounded we env ∧
      (∀ x width, astWidths sv x = some width → env x < 2 ^ width) ∧
      SVSolution (astWidths sv) pairs initial env ∧
      ∀ other, Bounded we other →
        (∀ x width, astWidths sv x = some width → other x < 2 ^ width) →
        SVSolution (astWidths sv) pairs initial other → other = env := by
  have hc' := hc
  rw [hwidth] at hc'
  obtain ⟨sv', pairs, htree', hemit, hitems⟩ := module_combItems m hp hshape hc'
  rw [htree] at htree'; cases htree'
  rw [← hwidth] at hemit
  obtain ⟨pairs', env, hemit', hir, hsv, hb', hw'⟩ := emit_sem_assigns mems m.body initial hc hb hw
  rw [hemit] at hemit'; cases hemit'
  have heq := assign_equations ha hir
  have hframe := assign_frame ha hir
  have htargets := emitted_targets ha hemit
  refine ⟨pairs, env, hitems, hsv, hb', hw', ⟨?_, ?_⟩, ?_⟩
  · exact (equations_emitted_iff ha hc hemit hb' hw').mpr heq
  · simpa only [htargets, ExternalValues] using hframe
  · intro other hbo hwo hso
    exact equations_unique ha ((equations_emitted_iff ha hc hemit hbo hwo).mp hso.1)
      (by simpa only [htargets, ExternalValues] using hso.2) heq hframe

/-- The shipping source theorem strengthened to simultaneous equations.
Acyclicity of the returned optimized body is the one NEW, explicit obligation;
it is not yet derived from shipping success. All previous scope conditions
and the environment identity assumption remain unchanged. -/
theorem compiledFragment_settled {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (ha : Acyclic (checkedOptimize m).body) :
    let o := checkedOptimize m
    ∃ (sv : SVModule) (port : Nat → Option String) (pairs : List CombStep),
      emitAstModule o = some sv ∧
      renderModule o.name
        (o.wires.filter fun p => !((o.inputs ++ o.outputs).map (·.name)).contains p.name).length sv
        = some (verilogOf m) ∧
      combItems sv.items = some pairs ∧
      (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
      (∀ j, j < names.length → ∃ w, port j = some w ∧ w ∈ o.inputs.map (·.name)) ∧
      (∀ j x, j < names.length → port j = some x →
        ∃ sp ∈ sv.ports, sp.dir = .input ∧ sp.name = x ∧
          declaredPortWidth sp = some n ∧ sp.isSigned = false) ∧
      declaredOutputWidth sv "out" = some n ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) (mems : MEnv),
        let initial := inputEnv names.length port (fun j => (sigs j).val t)
        Bounded (fun x => (astWidths sv x).getD 0) initial ∧
        ∃ env, evalAssignsSV (astWidths sv) mems pairs initial = some env ∧
          env "out" = ((denoteFE n sigs fe).val t).toNat ∧
          observeUnsignedOutput sv env "out" = some ((denoteFE n sigs fe).val t).toNat ∧
          SVSolution (astWidths sv) pairs initial env ∧
          ∀ other, Bounded (fun x => (astWidths sv x).getD 0) other →
            SVSolution (astWidths sv) pairs initial other → other = env := by
  obtain ⟨sv, port, pairs, ht, htext, hi, hd, hex, hdecl, houtWidth, hsem⟩ :=
    compiledFragment_astWidths h henv hwf hn
  have hwidth := compiled_astWidths h henv hwf hn ht
  have hc := (forwardCheck_sound (compiled_forwardCheck h henv hwf hn
    (synthesized_names h henv hwf hn))).2
  rw [← hwidth] at hc
  refine ⟨sv, port, pairs, ht, htext, hi, hd, hex, hdecl, houtWidth, ?_⟩
  intro dom sigs t mems
  obtain ⟨hb, env, hev, hout, hobs⟩ := hsem sigs t mems
  have hb' : Bounded (forwardWidths (checkedOptimize m))
      (inputEnv names.length port (fun j => (sigs j).val t)) := by
    intro x
    have hh := hb x
    rw [hwidth] at hh
    exact hh
  have hwb : ∀ x width, astWidths sv x = some width →
      inputEnv names.length port (fun j => (sigs j).val t) x < 2 ^ width := by
    intro x width hx
    simpa only [hx, Option.getD_some] using hb x
  obtain ⟨pairs', env', hi', hev', _, _, hsol, huniq⟩ := module_settled
    (printed_printDecls h henv hwf hn)
    (checkedOptimize_printShape (synthesized_printFacts h henv hwf hn).2)
    ht hwidth hc ha mems _ hb' hwb
  rw [hi] at hi'; cases hi'
  rw [hev] at hev'; cases hev'
  refine ⟨hb, env, hev, hout, hobs, hsol, ?_⟩
  intro other hbo hso
  apply huniq other
  · intro x
    have hh := hbo x
    rw [hwidth] at hh
    exact hh
  · intro x width hx
    simpa only [hx, Option.getD_some] using hbo x
  · exact hso

end Tools.ShippingSettledSoundness
