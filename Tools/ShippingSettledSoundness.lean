import Tools.ShippingDeclWidths
import Tools.ShippingAssignmentOrder

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
The assignment order of the selected optimized body follows from the actual
synthesis run and the shipping acceptance check. All previous scope conditions
and the environment identity assumption remain unchanged. -/
theorem compiledFragment_settled {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    let o := checkedOptimize m
    ∃ (sv : SVModule) (port : Nat → Option String) (pairs : List CombStep),
      emitAstModule o = some sv ∧
      renderModule o.name
        (o.wires.filter fun p => !((o.inputs ++ o.outputs).map (·.name)).contains p.name).length sv
        = some (verilogOf m) ∧
      LineText (Sparkle.Backend.Verilog.commentLabel o.name) ∧
      (∃ rest, verilogOf m = Sparkle.Backend.Verilog.moduleComment o.name ++ rest) ∧
      combItems sv.items = some pairs ∧
      (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
      (∀ j, j < names.length → ∃ w, port j = some w ∧ w ∈ o.inputs.map (·.name)) ∧
      (∀ j x, j < names.length → port j = some x →
        ∃ sp ∈ sv.ports, sp.dir = .input ∧ sp.name = x ∧
          declaredPortWidth sp = some n ∧ sp.isSigned = false) ∧
      declaredOutputWidth sv "out" = some n ∧
      (∀ entry ∈ declarationTable sv, Sparkle.IR.NameHints.DataName entry.1) ∧
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
  have ha := checkedOptimize_order (synthesized_printFacts h henv hwf hn).2
    (Tools.ShippingPostSoundness.synthesized_order h henv hwf hn)
  have hwidth := compiled_astWidths h henv hwf hn ht
  have hc := (forwardCheck_sound (compiled_forwardCheck h henv hwf hn
    (synthesized_names h henv hwf hn))).2
  rw [← hwidth] at hc
  obtain ⟨hlabel, hprefix⟩ := renderModule_comment htext
  refine ⟨sv, port, pairs, ht, htext, hlabel, hprefix, hi, hd, hex, hdecl, houtWidth,
    compiled_astDataNames h henv hwf hn ht, ?_⟩
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
